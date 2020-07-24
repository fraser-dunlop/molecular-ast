# molecular-ast 
Define syntax, parser, pretty-printer, random generators, inference, and unification Atomically. Combine Atoms into Molecular ASTs parameterised by the types of Atoms they contain. Compose rewrite systems from Transformations and Reductions that operate over classes of Molecules.

## Atomically define
- Parser
- Pretty Printer
- Random Generators
- Type Inference
- Unification

## Build complex Molecular AST transformations from a library of components
- Atoms.Molecule contains generic Molecular definitions
- Atoms.Elements contains a library of Atomic syntactic elements
- Atoms.Chemistry.Reductions contains rules that eliminate elements from a Molecule
- Atoms.Chemistry.Transformations contains rules that transform but do not guarantee elimination 
- Atoms.Chemistry.Cascades contains fixed point applications of Transformations 
- Atoms.Chemistry.Telescopes contains Telescopes of Reductions and Cascades
- Atoms.Chemistry.Extractions contains Extraction traversals
- Atoms.Chemistry.Solutions contains solver plugins for finding solutions to Constraints model Molecules

# What does an Atom look like?
This is the *Or* atom. It is simply a Functor over h. Hypertypes (alternatively a simpler functor Fix could be employed) and VariantF allow h to be polymorphic over the elements in the molecule to which Or belongs.

```Haskell

data Or h = Or h h  
  deriving (Eq, Ord, Show, Generic, Foldable, Traversable)

instance Functor Or where
   fmap f (Or l r) = Or (f l) (f r) 

```

Defining a random generator implementation for *Or* is simple. This is dispatched to from a Molecule generator. A better implementation of Gen1 would allow for a recursion limit.

```Haskell
instance Gen1 IO Or where
  liftGen _ = Or <$> gen <*> gen

```

Pretty printing can be defined in a similar manner.

```Haskell
instance Pretty1 Or where
    liftPrintPrec prec lPrec lvl p (Or a b) =
       ((prec lvl p a) <+> Pretty.text "\\/" <+> (prec lvl p b)) & Pretty.parens 
```

Perhaps surprisingly we can define a parser by atomic dispatch too. The current implementation is very inefficient for large left recursive terms.

```Haskell
-- Discriminator allows us to ask for an LR or non-LR term
instance (Ord e) => ASumPrecLR Discriminator (ParsecT e Text m) Or where
    liftASumPrecLR NotLeftRecursive p = ( minBound, empty )
    liftASumPrecLR LeftRecursive p =
      ( 42  -- a precedence for this parser
      , try $ do
        l <- p NotLeftRecursive
        _ <- symbol "\\/" 
        r <- (try (p NotLeftRecursive)) <|> p LeftRecursive
        pure $ Or l r
      )
```

Inference and unification can also be defined generically and dispatched to the atoms of a molecule.

```Haskell
instance ( HasF Or g
         , HasF TypeBool g
         , ForAllIn Functor g
         ) => Infer1 m (Molecule (VariantF g)) Or where
    liftInferBody (Or a b) = do
       InferredChild aI aT <- inferChild a
       InferredChild bI bT <- inferChild b
       expected <- MkANode <$> newTerm (Molecule (toVariantF TypeBool))
       unify (aT ^. _ANode) (expected ^. _ANode)
       ((Molecule (toVariantF (Or aI bI)), ) . MkANode) <$> unify (aT ^. _ANode) (bT ^. _ANode)

instance HasTypeConstraints1 g Or where 
   verifyConstraints1 _ _ = Nothing

instance ZipMatchable1 g Or where
   zipJoin1 (Or ll rl) (Or lr rr) = Just (Or (ll :*: lr) (rl :*: rr)) 

```

# What do Molecular rewrite rules look like?
Rewrite rules exist at the class level and operate over categories of trees that satisfy their contraints.
```Haskell
class ( HasF Not t
      , ForAllIn Functor t
      , ForAllIn Foldable t
      , ForAllIn Traversable t
      , Follow (Locate Not t) t ~ Not 
      , FromSides (Locate Not t)
      ) => DoubleNegation t where
    doubleNegation ::  STRef s Bool
                   -> VariantF t (Pure # Molecule (VariantF t))
                   -> ST s (Pure # Molecule (VariantF t))
``` 
This is the class signature for the rule that eliminates double negation. Its class constraints permit it to operate on any AST containing the atom *Not*. The (STRef s Bool) parameter is a flag allowing the rule to say whether it changed anything and is used for applying a rule until a fixed point is reached.



Writing the instance for this rule requires testing type equality of a node in the AST to check whether it is *Not*. This is simply lifting standard pattern matching to work with Molecular AST type level machinary. 
```Haskell
instance ( HasF Not t
         , ForAllIn Functor t
         , ForAllIn Foldable t
         , ForAllIn Traversable t
         , Follow (Locate Not t) t ~ Not 
         , FromSides (Locate Not t)
         ) => DoubleNegation t where
    doubleNegation changed (VariantF (tag :: SSide ss) res) =
        case testEquality tag (fromSides @(Locate Not t)) of
            Just Refl ->
                case res of
                    Not (Pure (Molecule (VariantF (tagi :: SSide ssi) resi))) ->
                        case testEquality tagi (fromSides @(Locate Not t)) of
                            Just Refl ->
                               case resi of
                                  Not a -> do
                                     writeSTRef changed True
                                     pure a 
                            Nothing -> pure $ Pure $ Molecule (VariantF tag res) 
            Nothing -> pure $ Pure $ Molecule (VariantF tag res)
```

It would be more convenient to write this rule using standard Haskell pattern matching syntax. e.g.

```Haskell
doubleNegation (Not (Not a)) = a
doubleNegation x = x
```

To this end the Haskell parser and syntax tree can be reflected and repurposed into a DSL using Template Haskell.

We can write an equivalent rule like so.
```Haskell
[transformation|
doubleNegation (Not (Not a)) = a
|]
```
This Template Haskell Quasi Quoter will template a class and instance named DoubleNegation for us enabling the writing of concise and easy to read rules. The template fills in the default case for us which is no change to the node and updates the STRef parameter in the case of match success. [The transformation quoter supports a subset of Haskell syntax including pattern guards that is repurposed to form this DSL].


For rules of moderate complexity Template Haskell becomes necessary for the sanity of the rule writer. Tautology by variable name equality expands from this

```Haskell
[transformation|
-- p \/ !p = True
tautology ((Not (Variable a)) `Or` (Variable b)) | a == b =
  Just (Pure (Molecule (toVariantF (LitBool True))))
-- !p \/ p = True 
tautology ((Variable a) `Or` (Not (Variable b))) | a == b =
  Just (iLitBool True)
-- (x \/ !p) \/ p = True
tautology ((x `Or` (Variable a)) `Or` (Not (Variable b))) | a == b =
  Just (iLitBool True)
-- (x \/ p) \/ !p = True
tautology ((x `Or` (Not (Variable a))) `Or` (Variable b)) | a == b =
  Just (iLitBool True)
|]
```
to this 

```Haskell
class (Type.Set.VariantF.HasF LitBool f_aAb9,
       Type.Set.VariantF.HasF Not f_aAb9,
       Type.Set.VariantF.HasF Or f_aAb9,
       Type.Set.VariantF.HasF Variable f_aAb9,
       Type.Set.Variant.FromSides (Type.Set.Locate LitBool f_aAb9),
       Type.Set.Variant.FromSides (Type.Set.Locate Not f_aAb9),
       Type.Set.Variant.FromSides (Type.Set.Locate Or f_aAb9),
       Type.Set.Variant.FromSides (Type.Set.Locate Variable f_aAb9),
       Type.Set.Follow (Type.Set.Locate LitBool f_aAb9) f_aAb9 ~ LitBool,
       Type.Set.Follow (Type.Set.Locate Not f_aAb9) f_aAb9 ~ Not,
       Type.Set.Follow (Type.Set.Locate Or f_aAb9) f_aAb9 ~ Or,
       Type.Set.Follow (Type.Set.Locate Variable f_aAb9) f_aAb9
       ~ Variable,
       Type.Set.Variant.ForAllIn Functor f_aAb9,
       Type.Set.Variant.ForAllIn Foldable f_aAb9,
       Type.Set.Variant.ForAllIn Traversable f_aAb9) => Tautology f_aAb9 where
  tautology ::
    STRef s_aAba Bool
    -> Type.Set.VariantF.VariantF f_aAb9 ((#) Hyper.Type.Pure.Pure (Atoms.Molecule.AST.Molecule (Type.Set.VariantF.VariantF f_aAb9)))
       -> ST s_aAba ((#) Hyper.Type.Pure.Pure (Atoms.Molecule.AST.Molecule (Type.Set.VariantF.VariantF f_aAb9)))
instance (Type.Set.VariantF.HasF LitBool f_aAb9,
          Type.Set.VariantF.HasF Not f_aAb9,
          Type.Set.VariantF.HasF Or f_aAb9,
          Type.Set.VariantF.HasF Variable f_aAb9,
          Type.Set.Variant.FromSides (Type.Set.Locate LitBool f_aAb9),
          Type.Set.Variant.FromSides (Type.Set.Locate Not f_aAb9),
          Type.Set.Variant.FromSides (Type.Set.Locate Or f_aAb9),
          Type.Set.Variant.FromSides (Type.Set.Locate Variable f_aAb9),
          Type.Set.Follow (Type.Set.Locate LitBool f_aAb9) f_aAb9 ~ LitBool,
          Type.Set.Follow (Type.Set.Locate Not f_aAb9) f_aAb9 ~ Not,
          Type.Set.Follow (Type.Set.Locate Or f_aAb9) f_aAb9 ~ Or,
          Type.Set.Follow (Type.Set.Locate Variable f_aAb9) f_aAb9
          ~ Variable,
          Type.Set.Variant.ForAllIn Functor f_aAb9,
          Type.Set.Variant.ForAllIn Foldable f_aAb9,
          Type.Set.Variant.ForAllIn Traversable f_aAb9) =>
         Tautology f_aAb9 where
  tautology changed_aAbb node_aAbm@(VariantF tag res)
    = case
          maysum_aAbn
            [case (testEquality tag) (fromSides @(Locate Or f_aAb9)) of
               Just Refl
                 -> case res of {
                      Or (Pure (Molecule (VariantF tag0 res0)))
                         (Pure (Molecule (VariantF tag1 res1)))
                        -> case (testEquality tag0) (fromSides @(Locate Not f_aAb9)) of
                             Just Refl
                               -> case res0 of {
                                    Not (Pure (Molecule (VariantF tag0_0 res0_0)))
                                      -> case
                                             (testEquality tag0_0)
                                               (fromSides @(Locate Variable f_aAb9))
                                         of
                                           Just Refl
                                             -> case res0_0 of {
                                                  Variable var_aAbc
                                                    -> case
                                                           (testEquality tag1)
                                                             (fromSides
                                                                @(Locate Variable f_aAb9))
                                                       of
                                                         Just Refl
                                                           -> case res1 of
                                                                Variable var_aAbd
                                                                  | var_aAbc == var_aAbd
                                                                  -> Just
                                                                       (Pure
                                                                          (Molecule
                                                                             (toVariantF
                                                                                (LitBool
                                                                                   True))))
                                                                _ -> Nothing
                                                         _ -> Nothing }
                                           _ -> Nothing }
                             _ -> Nothing }
               _ -> Nothing,
             case (testEquality tag) (fromSides @(Locate Or f_aAb9)) of
               Just Refl
                 -> case res of {
                      Or (Pure (Molecule (VariantF tag0 res0)))
                         (Pure (Molecule (VariantF tag1 res1)))
                        -> case
                               (testEquality tag0) (fromSides @(Locate Variable f_aAb9))
                           of
                             Just Refl
                               -> case res0 of {
                                    Variable var_aAbe
                                      -> case
                                             (testEquality tag1)
                                               (fromSides @(Locate Not f_aAb9))
                                         of
                                           Just Refl
                                             -> case res1 of {
                                                  Not (Pure (Molecule (VariantF tag1_0 res1_0)))
                                                    -> case
                                                           (testEquality tag1_0)
                                                             (fromSides
                                                                @(Locate Variable f_aAb9))
                                                       of
                                                         Just Refl
                                                           -> case res1_0 of
                                                                Variable var_aAbf
                                                                  | var_aAbe == var_aAbf
                                                                  -> Just (iLitBool True)
                                                                _ -> Nothing
                                                         _ -> Nothing }
                                           _ -> Nothing }
                             _ -> Nothing }
               _ -> Nothing,
             case (testEquality tag) (fromSides @(Locate Or f_aAb9)) of
               Just Refl
                 -> case res of {
                      Or (Pure (Molecule (VariantF tag0 res0)))
                         (Pure (Molecule (VariantF tag1 res1)))
                        -> case (testEquality tag0) (fromSides @(Locate Or f_aAb9)) of
                             Just Refl
                               -> case res0 of {
                                    Or var_aAbi (Pure (Molecule (VariantF tag0_1 res0_1)))
                                      -> case
                                             (testEquality tag0_1)
                                               (fromSides @(Locate Variable f_aAb9))
                                         of
                                           Just Refl
                                             -> case res0_1 of {
                                                  Variable var_aAbg
                                                    -> case
                                                           (testEquality tag1)
                                                             (fromSides @(Locate Not f_aAb9))
                                                       of
                                                         Just Refl
                                                           -> case res1 of {
                                                                Not (Pure (Molecule (VariantF tag1_0
                                                                                              res1_0)))
                                                                  -> case
                                                                         (testEquality tag1_0)
                                                                           (fromSides
                                                                              @(Locate Variable f_aAb9))
                                                                     of
                                                                       Just Refl
                                                                         -> case res1_0 of
                                                                              Variable var_aAbh
                                                                                | var_aAbg
                                                                                    == var_aAbh
                                                                                -> Just
                                                                                     (iLitBool
                                                                                        True)
                                                                              _ -> Nothing
                                                                       _ -> Nothing }
                                                         _ -> Nothing }
                                           _ -> Nothing }
                             _ -> Nothing }
               _ -> Nothing,
             case (testEquality tag) (fromSides @(Locate Or f_aAb9)) of
               Just Refl
                 -> case res of {
                      Or (Pure (Molecule (VariantF tag0 res0)))
                         (Pure (Molecule (VariantF tag1 res1)))
                        -> case (testEquality tag0) (fromSides @(Locate Or f_aAb9)) of
                             Just Refl
                               -> case res0 of {
                                    Or var_aAbl (Pure (Molecule (VariantF tag0_1 res0_1)))
                                      -> case
                                             (testEquality tag0_1)
                                               (fromSides @(Locate Not f_aAb9))
                                         of
                                           Just Refl
                                             -> case res0_1 of {
                                                  Not (Pure (Molecule (VariantF tag0_1_0
                                                                                res0_1_0)))
                                                    -> case
                                                           (testEquality tag0_1_0)
                                                             (fromSides
                                                                @(Locate Variable f_aAb9))
                                                       of
                                                         Just Refl
                                                           -> case res0_1_0 of {
                                                                Variable var_aAbj
                                                                  -> case
                                                                         (testEquality tag1)
                                                                           (fromSides
                                                                              @(Locate Variable f_aAb9))
                                                                     of
                                                                       Just Refl
                                                                         -> case res1 of
                                                                              Variable var_aAbk
                                                                                | var_aAbj
                                                                                    == var_aAbk
                                                                                -> Just
                                                                                     (iLitBool
                                                                                        True)
                                                                              _ -> Nothing
                                                                       _ -> Nothing }
                                                         _ -> Nothing }
                                           _ -> Nothing }
                             _ -> Nothing }
               _ -> Nothing]
      of
        Nothing -> (pure $ Pure (Molecule node_aAbm))
        Just so_aAbs
          -> do (writeSTRef changed_aAbb) True
                pure so_aAbs
    where
        maysum_aAbn :: [Maybe a_aAbo] -> Maybe a_aAbo
        maysum_aAbn [] = Nothing
        maysum_aAbn (Just v_aAbp : _) = Just v_aAbp
        maysum_aAbn (Nothing : r_aAbq) = maysum_aAbn r_aAbq
```

Whilst templating may seem like an ugly hack the templated code is highly generic and the author believes that the benefits of this construction outweigh the costs. Since these rules are so generic testing can be greatly simplified. The rule writer may write tests on tiny Molecules of syntax containing only the fragments relevant to the test. Thus verifying the correctness of a rule can be done in a vaccuum over a universe of very simple cases.


# Further work and known bugs
- The current parser implementation is very inefficient for large left recursive terms. This is fixable by employing better expression parsing by building a parser in Text.Megaparsec.Expr style.
- Currently optimisation level is set to -O0 since anything higher causes memory exhaustion due to excessive inlining. Suspected cause is reduction rules - perhaps there is a better way of doing term elimination.


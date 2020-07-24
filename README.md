# molecular-ast 
Define syntax, parser, pretty-printer, random generators, inference, and unification Atomically. Combine Atoms into Molecular ASTs parameterised by the types of Atoms they contain. Compose rewrite systems from Transformations and Reductions that operate over classes of Molecules.

Any chemistry set you design will play nicely with others and be open to extension by pure function composition.

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
This is the class signature for the rule that eliminates double negation. Its class constraints permit it to operate on any AST containing the atom *Not*.



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
This Template Haskell Quasi Quoter will template a class and instance named DoubleNegation for us enabling the writing of concise and easy to read rules. [The transformation quoter supports a subset of Haskell syntax that is repurposed to form this DSL].


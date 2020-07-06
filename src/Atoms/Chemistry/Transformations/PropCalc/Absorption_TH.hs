{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
module Atoms.Chemistry.Transformations.PropCalc.Absorption_TH where
import Atoms.Chemistry.Utils.TH
import Atoms.Elements.Generic.Variable
import Atoms.Elements.PropCalc.And
import Atoms.Elements.PropCalc.Or
import Atoms.Elements.PropCalc.Not
import Atoms.Molecule.AST
import Data.Type.Equality
import Hyper
import Hyper.Type.Pure
import Type.Set
import Type.Set.Variant
import Type.Set.VariantF
import Data.STRef
import Control.Monad.ST


-- | This templates the AbsorptionTH class defining the rules of Absorption for Propositional calculus on Variables.
[transformation|
-- p /\ (p \/ q) --> p
-- p /\ (q \/ p) --> p
absorptionTH changed ((Variable p)                 `And` ((Variable p')       `Or` (Variable p'')))  | p == p' || p == p'' = do 
    writeSTRef changed True
    pure (iVariable p) 
-- Note that the semantics of guards is not to fall through to the next pattern as in Haskell pattern guards.
-- If they fail then the default case of identity is applied to the Node. 
-- So for function we must match out the case of both sides of the Or being variables before the blank pattern cases.
-- This avoids a variable name matching p falling through the blank pattern resulting in no change being applied.
-- p /\ (p \/ _) --> p
absorptionTH changed ((Variable p)                 `And` ((Variable p')       `Or` _))  | p == p' = do 
    writeSTRef changed True
    pure (iVariable p) 
-- p /\ (_ \/ p) --> p
absorptionTH changed ((Variable p)                 `And` (_ `Or` (Variable p')))        | p == p' = do
    writeSTRef changed True
    pure (iVariable p) 

----------------------
-- (q \/ p) /\ p --> p
-- (p \/ q) /\ p --> p
absorptionTH changed (((Variable p'')       `Or` (Variable p')) `And` (Variable z))     | z == p' || z == p'' = do 
    writeSTRef changed True
    pure (iVariable p) 
-- (p \/ _) /\ p --> p
absorptionTH changed (((Variable p')       `Or` _) `And` (Variable p))                  | p == p' = do 
    writeSTRef changed True
    pure (iVariable p) 
-- (_ \/ p) /\ p --> p
absorptionTH changed ((_ `Or` (Variable p'))       `And` (Variable q))                  | q == p' = do
    writeSTRef changed True
    pure (iVariable p) 

----------------------
-- !p /\ (!p \/ _) --> !p
absorptionTH changed ((Not (Variable p))           `And` ((Not (Variable p')) `Or` _))  | p == p' = do 
    writeSTRef changed True
    pure (iNot (iVariable p)) 

-- !p /\ (_ \/ !p) --> !p
absorptionTH changed ((Not (Variable p))           `And` (_ `Or` (Not (Variable p'))))  | p == p' = do 
    writeSTRef changed True
    pure (iNot (iVariable p)) 
--
---- (!p \/ _) /\ !p --> !p
--absorptionTH changed (((Not (Variable p')) `Or` _) `And` (Not (Variable p)))            | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 
--
---- (_ \/ !p) /\ !p --> !p
--absorptionTH changed ((_ `Or` (Not (Variable p'))) `And` (Not (Variable p)))            | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 
--
---- p \/ (p /\ _) --> p
--absorptionTH changed ((Variable p)                 `Or` ((Variable p')       `And` _))  | p == p' = do 
--    writeSTRef changed True
--    pure (iVariable p) 
--
---- p \/ (_ /\ p) --> p
--absorptionTH changed ((Variable p)                 `Or` (_ `And` (Variable p')))        | p == p' = do
--    writeSTRef changed True
--    pure (iVariable p) 
--
---- (p /\ _) \/ p --> p
--absorptionTH changed (((Variable p')       `And` _) `Or` (Variable p))                  | p == p' = do 
--    writeSTRef changed True
--    pure (iVariable p) 
--
---- (_ /\ p) \/ p --> p
--absorptionTH changed ((_ `And` (Variable p'))       `Or` (Variable p))                  | p == p' = do
--    writeSTRef changed True
--    pure (iVariable p) 
--
---- !p \/ (!p /\ _) --> !p
--absorptionTH changed ((Not (Variable p))            `Or` ((Not (Variable p')) `And` _)) | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 
--
---- !p \/ (_ /\ !p) --> !p
--absorptionTH changed ((Not (Variable p))            `Or` (_ `And` (Not (Variable p')))) | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 
--
---- (!p /\ _) \/ !p --> !p
--absorptionTH changed (((Not (Variable p')) `And` _) `Or` (Not (Variable p)))            | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 
--
---- (_ /\ !p) \/ !p --> !p
--absorptionTH changed ((_ `And` (Not (Variable p'))) `Or` (Not (Variable p)))            | p == p' = do 
--    writeSTRef changed True
--    pure (iNot (iVariable p)) 

|]

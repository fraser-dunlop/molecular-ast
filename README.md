# molecular-ast 
Make your term rewriting system Molecular today! Define your syntax, parser, pretty-printer, random generators, inference, and unification Atomically. Combine these Atoms into Molecular ASTs parameterised by the types of Atoms they contain. Compose rewrite systems from Transformations and Reductions that operate over classes of Molecules.

Any chemistry set you design will play nicely with others and be open to extension by pure function composition.

## Atomically define
- Parser
- Pretty Printer
- Random Generators
- Type Inference
- Unification

## Build a Molecular AST
- Atoms of syntax compose generically into a Molecular AST built with HyperTypes 

## Define Reactions (Typed rewrite rules that operate on any Molecule that satisfies their constraints)
- Reductions eliminate Elements from the Molecule
- Transmutations rearrange structures whilst keeping the Atomic makeup the same
- Cascades compose Transmutations and apply until fixed points are reached 
- Telescopes compose Cascades and Reductions into complex chemical processes 
- Extractions extract information from a Molecule
- Solutions find satisfying assignments to Molecules representing Contraints models

## Build complex Molecular AST transformations from a library of components
- Atoms.Molecule contains generic Molecular definitions
- Atoms.Elements contains a library of Atomic syntactic elements
- Atoms.Chemistry.Reductions contains rules that eliminate elements from a Molecule
- Atoms.Chemistry.Transformations contains rules that transform but do not guarantee elimination 
- Atoms.Chemistry.Cascades contains fixed point applications of Transformations 
- Atoms.Chemistry.Telescopes contains Telescopes of Reductions and Cascades
- Atoms.Chemistry.Extractions contains Extraction traversals
- Atoms.Chemistry.Solutions contains solver plugins for finding solutions to Constraints model Molecules

# A detailed walkthrough
coming soon...

# Simple Semantic Subtyping

Some Haskell code to implement some semantic subtyping, adapted from [Andrew Kent's tutorial (2018)](https://pnwamk.github.io/sst-tutorial/).

Here's an overview of how the code corresponds to sections in Kent's tutorial:
- [Types/Base.hs](./src/Types/Base.hs): Types represented in DNF (section 3.2)
- [Types/LazyBDD.hs](./src/Types/LazyBDD.hs): Types represented as lazy BDDs (sections 3.1, 3.4)

## Compilation Instructions
- This project compiles with GHC 9.6.6. 
- Run `stack build` to compile
- Run `stack test` to run the test suite.


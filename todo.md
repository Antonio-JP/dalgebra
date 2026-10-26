1. [x] Fix the generation of Puiseux morphism for Wrapper: the input may not be a simple number, orders must be given sometimes.
   1. Fix implementation of all puiseux morphisms to allow the new *args.
   2. Fix the computation of dalgebraic series (the format of the initial data allowing a dictionary too)
2. Fix computation of derivative for dalgebraic series.
3. Check other cases where the default behavior is used for dalgebraic.
4. Implement the morphisms for DElliptic extensions.
5. Implement the addition and multiplication of dalgebraic series.
6. Think about the TODOs remaining in the branch.
7. Prepare merge with develop.
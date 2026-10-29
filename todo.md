1. [x] Fix the generation of Puiseux morphism for Wrapper: the input may not be a simple number, orders must be given sometimes.
   1. [x] Fix implementation of all puiseux morphisms to allow the new *args.
   2. [~] Fix the computation of dalgebraic series (the format of the initial data allowing a dictionary too)
2. [~] Fix computation of derivative for dalgebraic series.
3. Check other cases where the default behavior is used for dalgebraic.
   1. Improve method for getting differential equation. When possible get the exact equation.
      - Polynomial series are usually C-d-algebraic
      - Rational series can compute their equation as a product of d-algebraic
      - D-algebraic has the equation already defined
      - Default series can not compute differential equation without Puiseux series as coefficients.
   2. Implement the addition/product of d-algebraic series. 
      - Compute the equation for each summand/factor.
      - Combine the equation is a DRing with 3 d-variables (`u`, `v`, `w`). `u` for the first, `v` for the second and `w[0] = u[0]+v[0]` or `w[0]=u[0]*v[0]`.
      - Perform elimination of d-variables to remove `u` and `v`. 
      - Return the new equation (in `w`).
   3. Add tests in the coresponding methods for these d-algebraic series.
4. Implement the morphisms for DElliptic extensions.
   1. Create the d-algebraic element. The inputs are the same as for `algebraic_element` and the user must know the initial values.
   2. Add tests in the delliptic.py file.
6. Think about the TODOs remaining in the branch.
7. Prepare merge with develop.
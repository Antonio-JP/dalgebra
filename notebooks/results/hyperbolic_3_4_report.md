# ANALYZING CASE n=3, m=4 FOR THE HYPERBOLIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3_1=-12,a_2_0=6] and a_2_1,a_3_0 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - Solution Branch [a_3_1=0,a_2_0=0] and a_2_1,a_3_0 as free variables.
  - Checking the cases for level 2:
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3_1=0,a_2_0=6] and a_2_1,a_3_0 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - Solution Branch [a_3_1=0,a_2_0=0] and a_2_1,a_3_0 as free variables.
  - Checking the cases for level 2:
  Adding new branch to total valid branches
## CENTRALIZERS CASE BY CASE:
### Starting case 0/1:
* Branch: Solution Branch [a_3_1=0,a_2_0=6] and a_2_1,a_3_0 as free variables.
* Operator: 6/cosh^2*z_1 + z_3
*Flag: [0, -4/3, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) (((-8)/cosh^3)*cosh_p)*z_1 + ((-4/3*cosh^2 + 8)/cosh^2)*z_2 + z_4
  - (2 -- 5) ((16/9*cosh^4 + 80/3*cosh^2 - 20)/cosh^4)*z_1 + (((-20)/cosh^3)*cosh_p)*z_2 + 10/cosh^2*z_3 + z_5
### Starting case 1/1:
* Branch: Solution Branch [a_3_1=-12,a_2_0=6] and a_2_1,a_3_0 as free variables.
* Operator: (((-12)/cosh^3)*cosh_p)*z_0 + 6/cosh^2*z_1 + z_3
*Flag: [0, -4/3, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) ((16*cosh^2 - 24)/cosh^4)*z_0 + (((-24)/cosh^3)*cosh_p)*z_1 + ((-4/3*cosh^2 + 8)/cosh^2)*z_2 + z_4
  - (2 -- 5) (((-160/3*cosh^2 + 80)/cosh^5)*cosh_p)*z_0 + ((16/9*cosh^4 + 200/3*cosh^2 - 80)/cosh^4)*z_1 + (((-40)/cosh^3)*cosh_p)*z_2 + 10/cosh^2*z_3 + z_5

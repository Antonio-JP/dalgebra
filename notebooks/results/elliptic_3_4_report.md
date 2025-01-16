# ANALYZING CASE n=3, m=4 FOR THE ELLIPTIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 2: (Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.) include any solution for a lower level
  Invalid branch
## CENTRALIZERS CASE BY CASE:
### Starting case 0/1:
* Branch: Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
* Operator: -(3/2*eta_p)*z_0 - (3/2*eta)*z_1 + z_3
*Flag: [0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) -(3/2*eta^2 + 2/3*g_2)*z_0 - (3*eta_p)*z_1 - (2*eta)*z_2 + z_4
  - (2 -- 5) -(5/2*eta*eta_p)*z_0 - (5*eta^2 + 2*g_2)*z_1 - (5*eta_p)*z_2 - (5/2*eta)*z_3 + z_5
### Starting case 1/1:
* Branch: Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
* Operator: -(15/8*eta_p)*z_0 - (15/4*eta)*z_1 + z_3
*Flag: [0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) -(5*eta_p)*z_1 - (5*eta)*z_2 + z_4
  - (2 -- 8) [0, 2, 0]

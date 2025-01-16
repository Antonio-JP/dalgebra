# ANALYZING CASE n=3, m=5 FOR THE ELLIPTIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 2: (Solution Branch [a_3=0,a_2=-3] and g_2,g_3 as free variables.) include any solution for a lower level
  Invalid branch
## CENTRALIZERS CASE BY CASE:
### Starting case 0/1:
* Branch: Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.
* Operator: -(3*eta_p)*z_0 - (3*eta)*z_1 + z_3
* Flag: [-1/3*g_2, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) -(35/2*eta^3 + 21/2*g_2*eta + 10*g_3)*z_1 - (35*eta*eta_p)*z_2 - (35*eta^2 + 49/3*g_2)*z_3 - (21*eta_p)*z_4 - (7*eta)*z_5 + z_7
  - (2 -- 5) -(15/2*eta^2 + 9/2*g_2)*z_1 - (10*eta_p)*z_2 - (5*eta)*z_3 + z_5
### Starting case 1/1:
* Branch: Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.
* Operator: -(3*eta_p)*z_0 - (6*eta)*z_1 + z_3
* Flag: [-11/3*g_2, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 20) [0, 0, 2]
  - (2 -- 5) (10*eta*eta_p)*z_0 + (5/2*eta^2 - 19/2*g_2)*z_1 - (15*eta_p)*z_2 - (10*eta)*z_3 + z_5

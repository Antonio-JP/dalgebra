# ANALYZING CASE n=3, m=7 FOR THE ELLIPTIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3=-6,a_2=-12,g_2=0] and g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  - Checking the cases for level 5:
    [False] - Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.
    [False] - Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3=-6,a_2=-9/2] and g_2,g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  - Checking the cases for level 5:
    [False] - Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.
    [False] - Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 2: (Solution Branch [a_3=3/2,a_2=-9/2] and g_2,g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  - Checking the cases for level 5:
    [False] - Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.
    [False] - Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 3: (Solution Branch [a_3=-15/2,a_2=-15/2,g_2=0] and g_3 as free variables.) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0] and g_2,g_3 as free variables.
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=-3/8,a_2=-3/4] and g_2,g_3 as free variables.
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=-15/8,a_2=-15/4,g_2=0] and g_3 as free variables.
    [False] - Solution Branch [a_3=-3/2,a_2=-3/2] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3/2] and g_2,g_3 as free variables.
  - Checking the cases for level 5:
    [False] - Solution Branch [a_3=-3,a_2=-6] and g_2,g_3 as free variables.
    [False] - Solution Branch [a_3=-3,a_2=-3] and g_2,g_3 as free variables.
    [Invalid] Solution Branch [a_3=0,a_2=-3] and g_2,g_3 as free variables.
  Adding new branch to total valid branches
* Checking case 4: (Solution Branch [a_3=0,a_2=-15/2,g_2=0] and g_3 as free variables.) include any solution for a lower level
  Invalid branch
## CENTRALIZERS CASE BY CASE:
### Starting case 0/3:
* Branch: Solution Branch [a_3=3/2,a_2=-9/2] and g_2,g_3 as free variables.
* Operator: (3/2*eta_p)*z_0 - (9/2*eta)*z_1 + z_3
*Flag: [-19/4*g_3, 0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) ((35/4*eta^2 + 7/2*g_2)*eta_p)*z_0 + (35/2*eta^3 + 77/4*g_2*eta + 15/2*g_3)*z_1 + (35/2*eta*eta_p)*z_2 - (21/2*g_2)*z_3 - (35/2*eta_p)*z_4 - (21/2*eta)*z_5 + z_7
  - (2 -- 8) (55/2*eta^4 + 105/4*g_2*eta^2 + 20*g_3*eta + 55/24*g_2^2)*z_0 + ((55*eta^2 + 39/2*g_2)*eta_p)*z_1 + (55*eta^3 + 44*g_2*eta + 15*g_3)*z_2 + (20*eta*eta_p)*z_3 - (15*eta^2 + 39/2*g_2)*z_4 - (26*eta_p)*z_5 - (12*eta)*z_6 + z_8
### Starting case 1/3:
* Branch: Solution Branch [a_3=-6,a_2=-9/2] and g_2,g_3 as free variables.
* Operator: -(6*eta_p)*z_0 - (9/2*eta)*z_1 + z_3
*Flag: [-19/4*g_3, 0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) ((70*eta^2 + 21*g_2)*eta_p)*z_0 + (245/4*eta^3 + 91/2*g_2*eta + 25*g_3)*z_1 - (35/2*eta*eta_p)*z_2 - (105/2*eta^2 + 28*g_2)*z_3 - (35*eta_p)*z_4 - (21/2*eta)*z_5 + z_7
  - (2 -- 8) (405/2*eta^4 + 170*g_2*eta^2 + 120*g_3*eta + 205/24*g_2^2)*z_0 + ((230*eta^2 + 119/2*g_2)*eta_p)*z_1 + (55*eta^3 + 44*g_2*eta + 15*g_3)*z_2 - (80*eta*eta_p)*z_3 - (90*eta^2 + 89/2*g_2)*z_4 - (46*eta_p)*z_5 - (12*eta)*z_6 + z_8
### Starting case 2/3:
* Branch: Solution Branch [a_3=-15/2,a_2=-15/2,g_2=0] and g_3 as free variables.
* Operator: -(15/2*eta_p)*z_0 - (15/2*eta)*z_1 + z_3
*Flag: [55/12*g_3, 0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) (525/4*eta^2*eta_p)*z_0 + (525/2*eta^3 + 225/2*g_3)*z_1 + (245/2*eta*eta_p)*z_2 - (35*eta^2)*z_3 - (105/2*eta_p)*z_4 - (35/2*eta)*z_5 + z_7
  - (2 -- 11) ((67375/4*eta^4 + 5500*g_3*eta)*eta_p)*z_0 + (67375/2*eta^5 + 50875/2*g_3*eta^2)*z_1 + ((67375/2*eta^3 + 12375/2*g_3)*eta_p)*z_2 + (21175*eta^4 + 25575/2*g_3*eta)*z_3 + (17325/2*eta^2*eta_p)*z_4 + (1925*eta^3 + 550*g_3)*z_5 - (165*eta*eta_p)*z_6 - (330*eta^2)*z_7 - (275/2*eta_p)*z_8 - (55/2*eta)*z_9 + z_11
### Starting case 3/3:
* Branch: Solution Branch [a_3=-6,a_2=-12,g_2=0] and g_3 as free variables.
* Operator: -(6*eta_p)*z_0 - (12*eta)*z_1 + z_3
*Flag: [187/3*g_3, 0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) (385*eta^3 + 235*g_3)*z_1 + (420*eta*eta_p)*z_2 + (70*eta^2)*z_3 - (70*eta_p)*z_4 - (28*eta)*z_5 + z_7
  - (2 -- 14) [0, 2, 0]

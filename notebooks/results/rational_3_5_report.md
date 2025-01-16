# ANALYZING CASE n=3, m=5 FOR THE RATIONAL COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3=24,a_2=-24].) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0].
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=3,a_2=-3].
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=12,a_2=-6].
    [False] - Solution Branch [a_3=15,a_2=-15].
    [Invalid] Solution Branch [a_3=0,a_2=-6].
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3=24,a_2=-12].) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0].
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=3,a_2=-3].
  - Checking the cases for level 4:
    [False] - Solution Branch [a_3=12,a_2=-6].
    [False] - Solution Branch [a_3=15,a_2=-15].
    [Invalid] Solution Branch [a_3=0,a_2=-6].
  Adding new branch to total valid branches
* Checking case 2: (Solution Branch [a_3=0,a_2=-12].) include any solution for a lower level
  Invalid branch
## CENTRALIZERS CASE BY CASE:
### Starting case 0/1:
* Branch: Solution Branch [a_3=24,a_2=-12].
* Operator: 24/x^3*z_0 + ((-12)/x^2)*z_1 + z_3
*Flag: [0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 7) ((-1120)/x^6)*z_1 + 1120/x^5*z_2 + ((-560)/x^4)*z_3 + 168/x^3*z_4 + ((-28)/x^2)*z_5 + z_7
  - (2 -- 5) ((-120)/x^4)*z_1 + 80/x^3*z_2 + ((-20)/x^2)*z_3 + z_5
### Starting case 1/1:
* Branch: Solution Branch [a_3=24,a_2=-24].
* Operator: 24/x^3*z_0 + ((-24)/x^2)*z_1 + z_3
*Flag: [0, 0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 20) [0, 0, 2]
  - (2 -- 5) ((-320)/x^5)*z_0 + 40/x^4*z_1 + 120/x^3*z_2 + ((-40)/x^2)*z_3 + z_5

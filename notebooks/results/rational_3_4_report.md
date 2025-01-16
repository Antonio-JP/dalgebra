# ANALYZING CASE n=3, m=4 FOR THE RATIONAL COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: (Solution Branch [a_3=12,a_2=-6].) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0].
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=3,a_2=-3].
  Adding new branch to total valid branches
* Checking case 1: (Solution Branch [a_3=15,a_2=-15].) include any solution for a lower level
  - Checking the cases for level 1:
    [Invalid] Solution Branch [a_3=0,a_2=0].
  - Checking the cases for level 2:
    [False] - Solution Branch [a_3=3,a_2=-3].
  Adding new branch to total valid branches
* Checking case 2: (Solution Branch [a_3=0,a_2=-6].) include any solution for a lower level
  Invalid branch
## CENTRALIZERS CASE BY CASE:
### Starting case 0/1:
* Branch: Solution Branch [a_3=12,a_2=-6].
* Operator: 12/x^3*z_0 + ((-6)/x^2)*z_1 + z_3
* Flag: [0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) ((-24)/x^4)*z_0 + 24/x^3*z_1 + ((-8)/x^2)*z_2 + z_4
  - (2 -- 5) 80/x^5*z_0 + ((-80)/x^4)*z_1 + 40/x^3*z_2 + ((-10)/x^2)*z_3 + z_5
### Starting case 1/1:
* Branch: Solution Branch [a_3=15,a_2=-15].
* Operator: 15/x^3*z_0 + ((-15)/x^2)*z_1 + z_3
* Flag: [0, 0, 1]
* Centralizer:
  - (0 -- 0) z_0
  - (1 -- 4) 40/x^3*z_1 + ((-20)/x^2)*z_2 + z_4
  - (2 -- 8) [0, 2, 0]

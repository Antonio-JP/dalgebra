# ANALYZING CASE $n=3$, $m=4$ FOR THE RATIONAL COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=12,a_{2}=-6\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  Adding new branch to total valid branches
* Checking case 1: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=15,a_{2}=-15\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  Adding new branch to total valid branches
* Checking case 2: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-6\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  Adding new branch to total valid branches
## CENTRALIZERS CASE BY CASE:
### Starting case 1/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-6\right\}$
* Operator: $\left(\frac{-6}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = \left(\frac{8}{x^{3}}\right){z}_{(1)} + \left(\frac{-8}{x^{2}}\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = \left(\frac{-20}{x^{4}}\right){z}_{(1)} + \left(\frac{20}{x^{3}}\right){z}_{(2)} + \left(\frac{-10}{x^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
### Starting case 2/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=12,a_{2}=-6\right\}$
* Operator: $\left(\frac{12}{x^{3}}\right){z}_{(0)} + \left(\frac{-6}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = \left(\frac{-24}{x^{4}}\right){z}_{(0)} + \left(\frac{24}{x^{3}}\right){z}_{(1)} + \left(\frac{-8}{x^{2}}\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = \left(\frac{80}{x^{5}}\right){z}_{(0)} + \left(\frac{-80}{x^{4}}\right){z}_{(1)} + \left(\frac{40}{x^{3}}\right){z}_{(2)} + \left(\frac{-10}{x^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
### Starting case 3/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=15,a_{2}=-15\right\}$
* Operator: $\left(\frac{15}{x^{3}}\right){z}_{(0)} + \left(\frac{-15}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 2
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = \left(\frac{40}{x^{3}}\right){z}_{(1)} + \left(\frac{-20}{x^{2}}\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $8$) $G_2 = G_1^2$
* Orders: $\left[0, 4, 8\right]$

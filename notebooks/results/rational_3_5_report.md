# ANALYZING CASE $n=3$, $m=5$ FOR THE RATIONAL COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=24,a_{2}=-24\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  - Checking the cases for level 4:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=12,a_{2}=-6\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=15,a_{2}=-15\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-6\right\}$
  Adding new branch to total valid branches
* Checking case 1: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=24,a_{2}=-12\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  - Checking the cases for level 4:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=12,a_{2}=-6\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=15,a_{2}=-15\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-6\right\}$
  Adding new branch to total valid branches
* Checking case 2: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-12\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=3,a_{2}=-3\right\}$
  - Checking the cases for level 4:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=12,a_{2}=-6\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=15,a_{2}=-15\right\}$
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-6\right\}$
  Adding new branch to total valid branches
## CENTRALIZERS CASE BY CASE:
### Starting case 1/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-12\right\}$
* Operator: $\left(\frac{-12}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $7$) $G_1 = \left(\frac{224}{x^{5}}\right){z}_{(2)} + \left(\frac{-224}{x^{4}}\right){z}_{(3)} + \left(\frac{112}{x^{3}}\right){z}_{(4)} + \left(\frac{-28}{x^{2}}\right){z}_{(5)} + {z}_{(7)}$
  - ($2$ -- $5$) $G_2 = \left(\frac{40}{x^{3}}\right){z}_{(2)} + \left(\frac{-20}{x^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 7, 5\right]$
### Starting case 2/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=24,a_{2}=-12\right\}$
* Operator: $\left(\frac{24}{x^{3}}\right){z}_{(0)} + \left(\frac{-12}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $7$) $G_1 = \left(\frac{-1120}{x^{6}}\right){z}_{(1)} + \left(\frac{1120}{x^{5}}\right){z}_{(2)} + \left(\frac{-560}{x^{4}}\right){z}_{(3)} + \left(\frac{168}{x^{3}}\right){z}_{(4)} + \left(\frac{-28}{x^{2}}\right){z}_{(5)} + {z}_{(7)}$
  - ($2$ -- $5$) $G_2 = \left(\frac{-120}{x^{4}}\right){z}_{(1)} + \left(\frac{80}{x^{3}}\right){z}_{(2)} + \left(\frac{-20}{x^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 7, 5\right]$
### Starting case 3/3:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{3}=24,a_{2}=-24\right\}$
* Operator: $\left(\frac{24}{x^{3}}\right){z}_{(0)} + \left(\frac{-24}{x^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 0, 1\right]$
* Algebraic generators: 2
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $10$) $G_1 = G_2^2$
  - ($2$ -- $5$) $G_2 = \left(\frac{-320}{x^{5}}\right){z}_{(0)} + \left(\frac{40}{x^{4}}\right){z}_{(1)} + \left(\frac{120}{x^{3}}\right){z}_{(2)} + \left(\frac{-40}{x^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 10, 5\right]$

# ANALYZING CASE $n=3$, $m=4$ FOR THE HYPERBOLIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=6,a_{3}=0\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=0,a_{3}=0\right\}$
  - Checking the cases for level 2:
  Adding new branch to total valid branches
* Checking case 1: ($\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=6,a_{3}=-12\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=0,a_{3}=0\right\}$
  - Checking the cases for level 2:
  Adding new branch to total valid branches
## CENTRALIZERS CASE BY CASE:
### Starting case 1/2:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=6,a_{3}=0\right\}$
* Operator: $\left(\frac{6}{\mathit{cosh}^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, -\frac{4}{3}, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = \left(\left(\frac{-8}{\mathit{cosh}^{3}}\right) \mathit{cosh}'\right){z}_{(1)} + \left(\frac{-\frac{4}{3} \mathit{cosh}^{2} + 8}{\mathit{cosh}^{2}}\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = \left(\frac{\frac{16}{9} \mathit{cosh}^{4} + \frac{80}{3} \mathit{cosh}^{2} - 20}{\mathit{cosh}^{4}}\right){z}_{(1)} + \left(\left(\frac{-20}{\mathit{cosh}^{3}}\right) \mathit{cosh}'\right){z}_{(2)} + \left(\frac{10}{\mathit{cosh}^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
### Starting case 2/2:
* Branch: $\texttt{Solution}\left[\right]\left(\left(0\right)\mathbb{Q}[a_{2}, a_{3}]\right)\left\{a_{2}=6,a_{3}=-12\right\}$
* Operator: $\left(\left(\frac{-12}{\mathit{cosh}^{3}}\right) \mathit{cosh}'\right){z}_{(0)} + \left(\frac{6}{\mathit{cosh}^{2}}\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, -\frac{4}{3}, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = \left(\frac{16 \mathit{cosh}^{2} - 24}{\mathit{cosh}^{4}}\right){z}_{(0)} + \left(\left(\frac{-24}{\mathit{cosh}^{3}}\right) \mathit{cosh}'\right){z}_{(1)} + \left(\frac{-\frac{4}{3} \mathit{cosh}^{2} + 8}{\mathit{cosh}^{2}}\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = \left(\left(\frac{-\frac{160}{3} \mathit{cosh}^{2} + 80}{\mathit{cosh}^{5}}\right) \mathit{cosh}'\right){z}_{(0)} + \left(\frac{\frac{16}{9} \mathit{cosh}^{4} + \frac{200}{3} \mathit{cosh}^{2} - 80}{\mathit{cosh}^{4}}\right){z}_{(1)} + \left(\left(\frac{-40}{\mathit{cosh}^{3}}\right) \mathit{cosh}'\right){z}_{(2)} + \left(\frac{10}{\mathit{cosh}^{2}}\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
## SUMMARY OF THE CASES (by FAMILIES):
### Family 1:
* Number of cases: 2
* Orders: (4, 5)
* Relations: 
* Points: $\left\{(6, 0), (6, -12)\right\}$

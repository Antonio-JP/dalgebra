# ANALYZING CASE $n=3$, $m=4$ FOR THE ELLIPTIC COEFFICIENTS
## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL
* Checking case 0: ($\texttt{Solution}\left[g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{15}{8},a_{2}=-\frac{15}{4},g_{2}=0\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{3}{8},a_{2}=-\frac{3}{4}\right\}$
  Adding new branch to total valid branches
* Checking case 1: ($\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{3}{2},a_{2}=-\frac{3}{2}\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{3}{8},a_{2}=-\frac{3}{4}\right\}$
  Adding new branch to total valid branches
* Checking case 2: ($\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-\frac{3}{2}\right\}$) include any solution for a lower level
  - Checking the cases for level 1:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=0\right\}$
  - Checking the cases for level 2:
    [False] - $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{3}{8},a_{2}=-\frac{3}{4}\right\}$
  Adding new branch to total valid branches
## CENTRALIZERS CASE BY CASE:
### Starting case 1/3:
* Branch: $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=0,a_{2}=-\frac{3}{2}\right\}$
* Operator: $-\left(\frac{3}{2} \eta\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = -\left(\frac{1}{6} g_{2}\right){z}_{(0)} - \left(\eta'\right){z}_{(1)} - \left(2 \eta\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = -\left(\frac{5}{4} \eta^{2} + \frac{3}{4} g_{2}\right){z}_{(1)} - \left(\frac{5}{2} \eta'\right){z}_{(2)} - \left(\frac{5}{2} \eta\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
### Starting case 2/3:
* Branch: $\texttt{Solution}\left[g_{\mathit{{2}}},g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{3}{2},a_{2}=-\frac{3}{2}\right\}$
* Operator: $-\left(\frac{3}{2} \eta'\right){z}_{(0)} - \left(\frac{3}{2} \eta\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 3
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = -\left(\frac{3}{2} \eta^{2} + \frac{2}{3} g_{2}\right){z}_{(0)} - \left(3 \eta'\right){z}_{(1)} - \left(2 \eta\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $5$) $G_2 = -\left(\frac{5}{2} \eta \eta'\right){z}_{(0)} - \left(5 \eta^{2} + 2 g_{2}\right){z}_{(1)} - \left(5 \eta'\right){z}_{(2)} - \left(\frac{5}{2} \eta\right){z}_{(3)} + {z}_{(5)}$
* Orders: $\left[0, 4, 5\right]$
### Starting case 3/3:
* Branch: $\texttt{Solution}\left[g_{\mathit{{3}}}\right]\left(\left(0\right)\mathbb{Q}[g_{2}, g_{3}, a_{2}, a_{3}]\right)\left\{a_{3}=-\frac{15}{8},a_{2}=-\frac{15}{4},g_{2}=0\right\}$
* Operator: $-\left(\frac{15}{8} \eta'\right){z}_{(0)} - \left(\frac{15}{4} \eta\right){z}_{(1)} + {z}_{(3)}$
* Flag: $\left[0, 0, 1\right]$
* Algebraic generators: 2
* Found rank: 1
* Centralizer:
  - ($0$ -- $0$) $G_0 = {z}_{(0)}$
  - ($1$ -- $4$) $G_1 = -\left(5 \eta'\right){z}_{(1)} - \left(5 \eta\right){z}_{(2)} + {z}_{(4)}$
  - ($2$ -- $8$) $G_2 = G_1^{ *2}$
* Orders: $\left[0, 4, 8\right]$
## SUMMARY OF THE CASES (by FAMILIES):
### Family 1:
* Number of cases: 2
* Orders: (4, 5)
* Relations: 
* Points: $\left\{('Unknown',), ('Unknown',)\right\}$
### Family 2:
* Number of cases: 1
* Orders: (4, 8)
* Relations: G_2^* - G_1^{ *2}
* Points: $\left\{('Unknown',)\right\}$

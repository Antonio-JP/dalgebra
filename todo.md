# Things TO DO

## Issue 34

* Integrate the implementation of differential polynomials and `dExtensions`.

## Operations required for the DExtension (Chapter 1 on Bronstein)

* [x] For univariate polynomials: Euclidean division -> `quo_rem` method
* [x] For univariate polynomials: pseudo-polynomial division -> check where is in SageMath.
* [x] For integral domains where `quo_rem` is implemented: GCD -> check the `gcd` and use it
* [x] For integral domains where `quo_rem` is implemented: extended GCD -> must be done somewhere.
* For euclidean domains: partial fraction decomposition -> check where in SageMath
* For euclidean domains: full partial fraction decomposition -> check where in SageMath
* For univariate/multivariate polynomials: content and primitive parts -> check in SageMath
* Check for squarefree factorization on SageMath -> guarantee it for univariate polynomials (Yun's and Musser's implementation)

* Check method `remove_var` from `DExtension` -> useful to transform things into univariate polynomials.
* Check method `polynomial` to go to univariate polynomials -> it must go to a specific `DExtension` going over the DExtension factory.
* Check for a flattening morphism from these special `Dextension` to those created from the factory.

## Chapter 2 of Bronstein's: rational function integration

* Use the framework above to implement a simple integrator of rational functions.
  * Bernoulli Algorithm
  * Hermite Reduction
  * Horowitz-Ostrogradsky Algorithm
  * Rothstein-Trager Algorithm
  * Lazard-Rioboo-Trager Algorithm
  * Czichowski Algorithm (it uses Gröbner basis)
  * Newton-Leibniz-Bernoulli (`LaurentSeries` & `FullPartialFraction` & `IntegrateRationalFunction`)
  * Rioboo's for Real Rational (`LogToAtan` & `LogToReal`)
  * In-Field integration

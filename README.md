# **Difference and Differential Algebra** 

``dalgebra`` is a [SageMath](https://www.sagemath.org) package that allow to create, manipulate, and study *differential* and *difference* structures.

This package is based on the work of the following research articles and books:
* *E.R. Kolchin*: **Differential Algebra & Algebraic Groups**. [ISBN:9780080873695](https://www.elsevier.com/books/differential-algebra-and-algebraic-groups/kolchin/978-0-12-417650-8)
* *M. Bronstein*: **Symbolic Integration I**. [ISBN:978-3-662-03386-9](https://link.springer.com/book/10.1007/978-3-662-03386-9)

**Some information about the repository**
- _Author_: Antonio Jiménez-Pastor
- _License_: GNU Public License v3.0
- _Home page_: https://github.com/Antonio-JP/dalgebra
- _Documenation_: https://antonio-jp.github.io/dalgebra/
- _Online demo_: [(NOT READY)![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dalgebra/master?labpath=notebooks%2F.ipynb)

## **Main use-case**

Let $R$ be a ring and $\sigma: R \rightarrow R$ a map such that $\sigma(r+s) = \sigma(r) + \sigma(r)$. The package `dalgebra` allows to create the combined structure $(R,\sigma)$ and 
their elements will know about this operation over themselves. The main cases for this $\sigma$ are the *shifts* and the *derivations*, which defines the behavior of $\sigma$ with respect
to the multiplication of $R$:
  - *Shifts*: $\sigma(rs) = \sigma(r) \sigma(s)$.
  - *Derivations*: $\sigma(rs) = \sigma(r) s + r \sigma(s)$.

From these structures there is plenty of theory about how to perform symbolic integration or summation, how to manipulate difference/differential polynomials, study monomial extension, etc.
This software will allow to create these structures and perform some of the algorithms described in the references mentioned above to study these structures.rger algorithm will succeed. 

## **Installation**

This package can be installed, used, modified and distributed freely under the conditions of the 
[GNU General Public License v3](https://www.gnu.org/licenses/gpl-3.0.html) (see the file [LICENSE](https://github.com/Antonio-JP/dalgebra/blob/master/LICENSE)).

There are two different ways of installing the package into your SageMath distribution:

### _Install from souce code_

The package can be obtained from the public git repository on GitHub:
* by clicking [here](https://github.com/Antonio-JP/dalgebra) for the webpage view,
* or by cloning the repository by [https](https://github.com/Antonio-JP/dalgebra.git),
* or downloading the latest version in [zip](https://github.com/Antonio-JP/dalgebra/archive/master.zip) format.

After cloning or downloading the source cose, you may install it by running the following command line from the main folder of the repository:
```
    make install
```

### _Install via pip_

Another option to install this package is to use the pip functionality within SageMath. This will install the latest stable version of the package and will take care of any dependencies that may be required.

To install it via pip, run the following in a terminal where ``sage`` can be executed:
```
    sage -pip install [--user] git+https://github.com/Antonio-JP/dd_functions.git
```

The optional argument _--user_ allows to install the package just for the current user instead of a global installation.

### _Pre-refactor version_

This repository has suffered a big refactor and has lost some of its functionalities (temporary). The version fo the code before this refactoring can be obtained
from the tag [`v0.0.3.pre-refactor`](https://github.com/Antonio-JP/dalgebra/tree/v0.0.3.pre-refactor). This version of the software (`v0.0.20220513.1339`)
can be obtained using the same procedures as described above but with small differences:

* From source code: [use this .zip file](https://github.com/Antonio-JP/dalgebra/archive/refs/tags/v0.0.3.pre-refactor.zip).
* From pip: ``sage -pip install [--user] git+https://github.com/Antonio-JP/dalgebra.git@v0.0.3.pre-refactor``.

### _Loading the package_

Once installed, the full functionality of the pacakge can be used after importing it with the command:

```Sage
    sage: from dalgebra import *
```

## **Dependencies**

This package has been developed on top of [SageMath](https://www.sagemath.org/) and currently has no other dependency. However, there are related packages 
available online that will be connected in future versions:
* [``ore_algebra``](https://github.com/mkauers/ore_algebra): developed by [M. Kauers](http://www.kauers.de/) and [M. Mezzarobba](http://marc.mezzarobba.net/).
* [``dd_functions``](https://github.com/Antonio-JP/dd_functions): developed by [A. Jiménez-Pastor](https://scholar.google.com/citations?user=1gq-jy4AAAAJ&hl=es)

## **Package under active developement**

This package is still under an active developement and further features will be included in future version of the code. This means that several bugs may exist or appear. We would thank anyone that, after detecting any error, would post it in the [issues page](https://github.com/Antonio-JP/pseries_basis/issues) of the repository using the label https://github.com/github/docs/labels/bug.

Moreover, any requested feature can be post in the [issues page](https://github.com/Antonio-JP/pseries_basis/issues) of the repository using the label https://github.com/github/docs/labels/enhancement.

### **Acknowledgements**

This package has been developed with the financial support of the following institutions:
* The Austrian Science Fund (FWF): by W1214-N15, project DK15.
* The Oberösterreich region: by the Innovatives OÖ-2010 plus program.
* The Île-de-France region: by the project "XOR".
* The Spanish Ministry of Science and Innovation (MICINN): by the grant PID2021-124473NB-I00, "Algorithmic Differential Algebra and Integrability" (ADAI)

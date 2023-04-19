r'''
**Difference and Differential Algebra** 
+++++++++++++++++++++++++++++++++++++++

``dalgebra`` is a `SageMath <https://www.sagemath.org>`_ package that allow to create, manipulate, and study *differential* and *difference* structures.

**Some information about the repository**
-----------------------------------------
- *Main Author*: Antonio Jiménez-Pastor
- *License*: GNU Public License v3.0
- *Home page*: :home:`/`
- *Documentation*: :hdoc:`/`
- *Online demo*: `Binder (not working) <https://mybinder.org/v2/gh/Antonio-JP/dalgebra/master?labpath=notebooks%2F.ipynb>`_

**Main use-case**
-----------------------------------------

Let `R` be a ring and `\sigma: R \rightarrow R` a map such that `\sigma(r+s) = \sigma(r) + \sigma(r)`. The package ``dalgebra`` allows to create the combined structure `(R,\sigma)` and 
their elements will know about this operation over themselves. The main cases for this `\sigma` are the *shifts* and the *derivations*, which defines the behavior of `\sigma` with respect
to the multiplication of `R`:

- *Shifts*: `\sigma(rs) = \sigma(r) \sigma(s)`.
- *Derivations*: `\sigma(rs) = \sigma(r) s + r \sigma(s)`.
- *Skew-Derivations*: given an homomorphism `\tau: R \rightarrow R`, `\sigma(rs) = \sigma(r) s + \tau(r) \sigma(s)`.

From these structures there is plenty of theory about how to perform symbolic integration or summation, how to manipulate difference/differential polynomials, study monomial extension, etc.
This software will allow to create these structures and perform some of the algorithms described in the references mentioned above to study these structures.

Using ``dalgebra`` is a straight-forward process to work with these type of operators over a ring::

    sage: from dalgebra import *
    sage: R = DifferentialRing(QQ[x], diff); R
    Differential Ring [[Univariate Polynomial Ring in x over Rational Field], (d/dx,)]
    sage: p = R(x^3 + 3*x - 1)
    sage: p.derivative()
    3*x^2 + 3

We can also define more elaborated derivations or differences. For example, we can create a Differential ring with the exponential function::

    sage: R = DifferentialRing(QQ['ex'], lambda p : QQ['ex']('ex')*p.derivative()) # ex is the exponential
    sage: ex = R.gens()[0]
    sage: ex.derivative()
    ex

Or we can create a differential ring with two elements that mimic the behavior of the sine and cosine functions::

    sage: R.<s,c> = QQ[]; ds,dc = R.derivation_module().gens()
    sage: DR = DifferentialRing(R, c*ds - s*dc); s,c = DR.gens()
    sage: s.derivative()
    c
    sage: c.derivative()
    -s
    sage: (s^2 + c^2).derivative()
    0


**Installation**
-----------------------------------------

This package can be installed, used, modified and distributed freely under the conditions of the 
`GNU General Public License v3 <https://www.gnu.org/licenses/gpl-3.0.html>`_ (see the file :home:`LICENSE </blob/master/LICENSE>`).

There are two different ways of installing the package into your `SageMath`_ distribution:

*Install from source code*
==========================

The package can be obtained from the public git repository on GitHub:

* by clicking :home:`here </>` for the webpage view,
* or by cloning the repository by :home:`https <.git>`,
* or downloading the latest version in :home:`zip </archive/master.zip>` format.

After cloning or downloading the source code, you may install it by running the following command line from the main folder of the repository::

    >> make install

*Install via pip*
=========================

Another option to install this package is to use the ``pip`` functionality within `SageMath`_. This will install the latest stable version 
of the package and will take care of any dependencies that may be required.

To install it via ``pip``, run the following in a terminal where ``sage`` can be executed::

    >> sage -pip install [--user] git+https://github.com/Antonio-JP/dalgebra.git


The optional argument *--user* allows to install the package just for the current user instead of a global installation.

*Pre-refactor version*
=========================

This repository has suffered a big refactor and has lost some of its functionalities (temporary). The version fo the code before this refactoring can be obtained
from the tag :tag:`v0.0.3.pre-refactor`. This version of the software (`v0.0.20220513.1339`)
can be obtained using the same procedures as described above but with small differences:

* From source code: :home:`use this .zip file </archive/refs/tags/v0.0.3.pre-refactor.zip>`.
* From pip: ``sage -pip install [--user] git+https://github.com/Antonio-JP/dalgebra.git@v0.0.3.pre-refactor``.

*Loading the package*
=========================

Once installed, the full functionality of the package can be used after importing it with the command::

    sage: from dalgebra import *


**Dependencies**
-----------------------------------------

This package has been developed on top of `SageMath`_ and currently has no other dependency. However, there are related packages 
available online that will be connected in future versions:

* :git:`mkauers/ore_algebra`: developed by `M. Kauers <http://www.kauers.de/>`_ and `M. Mezzarobba <http://marc.mezzarobba.net/>`_.
* :git:`Antonio-JP/dd_functions`: developed by `A. Jiménez-Pastor <https://scholar.google.com/citations?user=1gq-jy4AAAAJ&hl=es>`_.

**Package under active development**
-----------------------------------------

This package is still under an active development and further features will be included in future version of the code. This means that several bugs may exist or appear. 
We would thank anyone that, after detecting any error, would post it in the :home:`issues page </issues>` of the repository using 
the label :git:`bug <github/docs/labels/bug>`.

Moreover, any requested feature can be post in the :home:`issues page </issues>` of the repository using the label 
:git:`enhancement <github/docs/labels/enhancement>`.

**References**
-----------------------------------------
This package is based on the work of the following research articles and books:

- *E.R. Kolchin*: **Differential Algebra & Algebraic Groups**. `ISBN:9780080873695 <https://www.elsevier.com/books/differential-algebra-and-algebraic-groups/kolchin/978-0-12-417650-8>`_
- *M. Bronstein*: **Symbolic Integration I**. `ISBN:978-3-662-03386-9 <https://link.springer.com/book/10.1007/978-3-662-03386-9>`_

- J.J.Morales-Ruiz, S.L. Rueda, M.A. Zurro, *Factorization of KdV Schrödinger operators using differential subresultants*, Advances in Applied Mathematics, vol. 120 (**2020**). :doi:`10.1016/j.aam.2020.102065`.

**Acknowledgements**
-----------------------------------------

This package has been developed with the financial support of the following institutions:

* The Austrian Science Fund (FWF): by W1214-N15, project DK15.
* The Oberösterreich region: by the Innovatives OÖ-2010 plus program.
* The Île-de-France region: by the project "XOR".
* The Spanish Ministry of Science and Innovation (MICINN): by the grant PID2021-124473NB-I00, "Algorithmic Differential Algebra and Integrability" (ADAI)
* The Poul Due Jensen Foundation: grant 883901.
'''

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

## Configuring logger for this package
import logging

logger = logging.getLogger(__name__)
logger.setLevel(logging.ERROR)
formatter = logging.Formatter('%(asctime)s %(levelname)-8s %(message)s', datefmt='%Y-%m-%d %H:%M:%S')

#### CREATING THE HANDLERS
# first we strip the __init__p.py from __file__, then we add the relative path
path_to_logging = __file__[:-__file__[-1::-1].find('/')] + "logging/dalgebra.log" 
fh = logging.FileHandler(path_to_logging)
fh.setFormatter(formatter)
logger.addHandler(fh)
logger.propagate = False

from .ring_w_operator import * # basic ring structures
from .rwo_polynomial import * # ring of difference/differential polynomials

def dalgebra_version():
    import pkg_resources
    return pkg_resources.get_distribution('dalgebra').version
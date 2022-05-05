================================================
Differential and Difference algebra in Sage
================================================

Differential and Difference Algebra is a wide field of Mathematics that involve
algorithms such as Symbolic Integration and Summation. The main idea of this field
is to add a derivative operator `\partial` to an algebraic structure
that satisfies the following two properties:

.. MATH::

    \begin{array}{c}
        \partial(a+b) = \partial(a) + \partial(b)\\
        \partial(ab) = \partial(a)b + a\partial(b)
    \end{array}

This setting can be used in commutative and non-commutative algebra, with rings, fields, 
modules, vector spaces, etc. 

This package provides a unified interface to create these algebraic structures, manipulate
its elements and, in last instance, provide the specialized algorithms of Differential
Algebra.

For some references, the reader can follow the following texts:

* `Symbolic Integration I <https://www.springer.com/gp/book/9783662033869>`_
* `Differential Algebra <https://bookstore.ams.org/coll-33>`_

To use this module, it is enough to import it with the following Sage line::

    from dalgebra import *

From this site, you can explore all the documentation (which contains several examples of usage) for all
the modules included in this package. 

For a live demo (with no need of installation), got to (not available)

.. warning:: the demo is currently not available

List of Packages 
=================

.. toctree::
   :maxdepth: 1

   ring_w_operator
   diff_polynomial


Indices and Tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

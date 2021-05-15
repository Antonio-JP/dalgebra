
# **Differential Algebra in Sage** 

`dalgebra` is a Sage package free to get from the git repository in https://github.com/Antonio-JP/dalgebra (GitHub). 

This package is intended to allow the user to create and manipulate the structures with which Differential Algebra works,
such as Differential Rings, Fields, Modules, etc. For an extensive documentation of the package, visit https://antonio-jp.github.io/dalgebra/.

<font color="red">Currently the package is under construction and it provides no functionality.</font>

## **1. Installing the package**
There are two different ways to obtain the package.

#### **From Source Code**
The package can be obtained freely from the public _git_ repository on GitHub: click [here](https://github.com/Antonio-JP/dalgebra) for the webpage view or clone the repository by [https](https://github.com/Antonio-JP/dalgebra.git) or download the last [zip](https://github.com/Antonio-JP/dalgebra/archive/refs/heads/master.zip).

* After cloning the repository (or getting it in a zip file), use the command `make install` inside the main folder
  to install it.

#### **PiPy installation**
Another option to install and use the package is the use of _pip_ within _Sage_:
  
  `sage -pip install [--user] git+https://github.com/Antonio-JP/dd_functions.git`

## **2. Using the package**
Now that the package is installed, we can start using it importing the appropriate package:

`from dalgebra import *`

## **3. External dependencies**

Currently this package has no dependencies
## -*- encoding: utf-8 -*-
import sys
from setuptools import setup
from codecs import open # To open the README file with proper encoding

# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()
    
setup(
    name = "dalgebra",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='A Sage package for Difference/Differential Algebra',
    # long_description = readfile("README.txt"), # get the long description from the README
    # For a Markdown README replace the above line by the following two lines:
    long_description = readfile("README.md"),
    long_description_content_type="text/markdown",
    url='https://github.com/Antonio-JP/dalgebra',
    author = "Antonio Jimenez-Pastor",
    author_email = "ajpa@cs.aau.dk",
    license = "GPLv3+", # See LICENSE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 3 - Alpha',
      'Intended Audience :: Science/Research',
      'Topic :: Software Development :: Build Tools',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)',
      f'Programming Language :: Python :: {sys.version}',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "SageMath difference/differential algebra",
    packages = ["dalgebra",
                "dalgebra.dpolynomial",
                "dalgebra.hierarchies",
                "dalgebra.logging"],
    setup_requires   = [],
    install_requires = readfile("requirements.txt").split("\n"),
)
    

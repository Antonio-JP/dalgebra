# **Difference and Differential Algebra**

``dalgebra`` is a [SageMath](https://www.sagemath.org) package that allow to create, manipulate, and study *differential* and *difference* structures.

## Please check the [documentation](https://antonio-jp.github.io/dalgebra/) for detailed description of the module

### **Some information about the repository**
- _Author_: Antonio Jiménez-Pastor
- _License_: GNU Public License v3.0
- _Home page_: https://github.com/Antonio-JP/dalgebra
- _Documenation_: https://antonio-jp.github.io/dalgebra/
- _Online demo_: [(NOT READY)![Binder](https://mybinder.org/badge_logo.svg)](https://mybinder.org/v2/gh/Antonio-JP/dalgebra/master?labpath=notebooks%2F.ipynb)

### **Acknowledgements**

This package has been developed with the financial support of the following institutions:
* The Austrian Science Fund (FWF): by W1214-N15, project DK15.
* The Oberösterreich region: by the Innovatives OÖ-2010 plus program.
* The Île-de-France region: by the project "XOR".
* The Spanish Ministry of Science and Innovation (MICINN): by the grant PID2021-124473NB-I00, "Algorithmic Differential Algebra and Integrability" (ADAI)
* The Poul Due Jensen Foundation: grant 883901.

### **Release workflow (new version to main/master)**

Use this checklist before pushing a new version to the default branch.

1. Ensure you are on the version of your code you would like to push and ensure you have the latest tag updated in your branch (i.e., merge always from the branch `develop`)

	```bash
	git merge develop
	```

2. Update version metadata:

	- Edit `VERSION` with the new version:
      - If the changes are minor (bugfixes or small documentation) the third entry must be increased by one.
      - If the changes are substantial (new features, new mechanics or bigger changes) the second entry must be increased by one and the third reset to zero.
      - If this is a new full release of the code (we do not expect to add more content in a while), all tests are set, all documentation is ready and we plan it to push into SageMath or another official repository, we increase the first version number by one and reset all others to zero.

3. Run the CI-equivalent checks locally (required):

	```bash
	make lint
	make test
	```

4. (Recommended) Build docs and ensure installation still works:

	```bash
	make doc
	make install
	```

6. (Recommended) Audit newly added classes/functions/methods for docstrings/doctests:

	```bash
	make release-audit
	```

8. Create a pull request to branch `develop` in the main repository.

Notes:
- This repository CI currently targets `master`; if you migrate to `main`, update `.github/workflows/ci-dalgebra.yml` accordingly.
- `make release-audit` checks newly added classes/functions/methods since the last tag and reports whether each has both a docstring and doctest markers (`sage:` or `>>>`).
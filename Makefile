SHELL:=/bin/bash
ZIP=dalgebra# ZIP name
VERSION=$(shell cat ./VERSION)

# change to your sage command if needed
SAGE=sage

# Package folder
PACKAGE=dalgebra

all: install doc test
		
# Installing commands
install: clean_build clean_cache
	$(SAGE) -pip install --upgrade .

no-deps: clean_build
	$(SAGE) -pip install --upgrade --no-deps .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop: clean_build
	$(SAGE) -pip install --upgrade -e .

test: no-deps
	$(SAGE) -tox -e doctest -- dalgebra

coverage:
	$(SAGE) -tox -e coverage -- dalgebra

lint:
	$(SAGE) -tox -e relint,pycodestyle-minimal -- dalgebra

ready: lint test
	@echo "Repository is ready to push: check with act th actions in case of changes."
	
# Documentation commands
doc:
	cd docsrc && $(SAGE) -sh -c "make html"

doc-github: doc
	@rm -rf ./docs
	@cp -a docsrc/build/html/. ./docs
	@echo "" > ./docs/.nojekyll
		
# Cleaning commands
clean: clean_doc clean_pyc

clean_build:
	@echo "Cleaning previous build files"
	@rm -rf ./build ./$(PACKAGE).egg-info

clean_doc:
	@echo "Cleaning documentation"
	@rm -rf docs/* docs/.buildinfo docs/.nojekyll
	@cd docsrc && $(SAGE) -sh -c "make clean"
	
clean_pyc:
	@echo "Cleaning the Python precompiled files (.pyc)"
	@find . -name "*.pyc" -exec rm {} +

clean_cache:
	@echo "Cleaning the cached results in files"
	@ rm -rf dalgebra/__pycache__/*.dmp

.PHONY: all install develop test coverage clean clean_doc doc doc-pdf
	

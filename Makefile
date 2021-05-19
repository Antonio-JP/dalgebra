SHELL:=/bin/bash
ZIP=dalgebra# ZIP name
VERSION=$(shell cat ./VERSION)

# change to your sage command if needed
SAGE=sage

# Package folder
PACKAGE=dalgebra

all: install doc test
		
# Installing commands
install:
	$(SAGE) -pip install --upgrade .

no-deps:
	$(SAGE) -pip install --upgrade --no-deps .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop:
	$(SAGE) -pip install --upgrade -e .

test: install
	$(SAGE) -t --force-lib ./dalgebra

coverage:
	$(SAGE) -coverage $(PACKAGE)/*
	
# Documentation commands
doc: no-deps
	cd docsrc && $(SAGE) -sh -c "make html"

doc-github: doc
	cp -a docsrc/build/html/. ./docs
		
# Cleaning commands
clean: clean_doc clean_pyc

clean_doc:
	@echo "Cleaning documentation"
	@cd docsrc && $(SAGE) -sh -c "make clean"
	
clean_pyc:
	@echo "Cleaning the Python precompiled files (.pyc)"
	@find . -name "*.pyc" -exec rm {} +

.PHONY: all install develop test coverage clean clean_doc doc doc-pdf
	

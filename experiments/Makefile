SHELL:=/bin/bash 
SAGE=sage
BOUND_N=5
BOUND_M=15
REPEATS=10
METHODS=diff linear

all: quasi_commuting
	@echo "All experiments executed"

clean:
	@echo "Cleaning CSV files..."
	@find . -name "*.csv" -type f -delete
	@echo "Removing profiles..."
	@find . -name "*.prf" -type f -delete
	@echo "Removing text results..."
	@find . -name "\[results\]*.txt" -type f -delete

quasi_commuting: $(METHODS)
	@echo "All methods executed"

%:
	@n=2; while [[ $$n -le $(BOUND_N) ]] ; do \
		m=1; while [[ $$m -le $(BOUND_M) ]] ; do \
			t=1; while [[ $$t -le $(REPEATS) ]] ; do \
				echo -ne "++ n=$$n; m=$$m; method=$@; ($$t/$(REPEATS))\r"; \
				sage quasi_commuting.sage $$n $$m $@ ; \
				((t = t + 1)) ; \
			done ; \
			echo "" ; \
			((m = m + 1)) ; \
		done ; \
		((n = n + 1)) ; \
	done
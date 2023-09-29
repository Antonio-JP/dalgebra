SHELL:=/bin/bash 
SAGE=sage
PARALLEL=4
BOUND_N=5
BOUND_M=15
REPEATS=10
METHODS=diff linear

all: quasi_commuting
	@echo "All experiments executed"

clean:
	@rm -rf profiles/*.prf
	@for m in $(METHODS) ; do rm results/$$m.csv ; echo "n;m;time" > results/$$m.csv ; done

quasi_commuting: $(METHODS)
	@echo "All methods executed"

%:
	@tsp -S $(PARALLEL)
	@n=2; while [[ $$n -le $(BOUND_N) ]] ; do \
		m=1; while [[ $$m -le $(BOUND_M) ]] ; do \
			t=1; while [[ $$t -le $(REPEATS) ]] ; do \
				tsp "sage quasi_commuting.sage $$n $$m $@ direct" > nul; \
				tsp "sage quasi_commuting.sage $$n $$m $@ recursive" > nul; \
				((t = t + 1)) ; \
			done ; \
			((m = m + 1)) ; \
		done ; \
		((n = n + 1)) ; \
	done
	@echo "Done"

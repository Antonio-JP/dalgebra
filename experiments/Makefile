SHELL:=/bin/bash 
SAGE=sage
PARALLEL=4
BOUND_N=5
BOUND_M=10
REPEATS=10
METHODS=diff linear

all: quasi_commuting
	@echo "All experiments scheduled"

clean:
	@rm -rf profiles/*.prf
	@for m in $(METHODS) ; do rm results/$$m.csv ; echo "n;m;time" > results/$$m.csv ; done

quasi_commuting: $(METHODS)
	@echo "All methods scheduled"

%:
	@tsp -S $(PARALLEL)
	@n=2; while [[ $$n -le $(BOUND_N) ]] ; do \
		m=1; while [[ $$m -le $(BOUND_M) ]] ; do \
			t=1; while [[ $$t -le $(REPEATS) ]] ; do \
				tsp sage quasi_commuting.sage $$n $$m $@ direct; \
				tsp sage quasi_commuting.sage $$n $$m $@ recursive; \
				((t = t + 1)) ; \
			done ; \
			((m = m + 1)) ; \
		done ; \
		((n = n + 1)) ; \
	done
	@echo "Schedule all $@"

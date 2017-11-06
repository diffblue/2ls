DIRS = heap nontermination termination kiki \
       preconditions interprocedural invariants

test:
	$(foreach var,$(DIRS), make -C $(var) test || exit 1;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)

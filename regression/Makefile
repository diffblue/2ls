DIRS = \
     book-examples \
     nontermination \
	   termination \
	   kiki \
     preconditions \
	   interprocedural \
	   invariants \
	   heap \
	   heap-data \
	   memsafety \
	 instrumentation \
	 arrays

test:
	$(foreach var,$(DIRS), make -C $(var) test || exit 1;)

clean:
	$(foreach var,$(DIRS), make -C $(var) clean;)

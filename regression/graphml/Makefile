2LS = ../../../src/summarizer/2ls
CPACHECKER = $W/svncpachecker

test:
	@PWD=`pwd`; \
	for dir in `find $$PWD/* -maxdepth 1 -type d`; do \
	  cd $$dir; \
	  $(2LS) main.c --k-induction --graphml-cex cex.graphml > main.out; \
          cd $(CPACHECKER); \
          ./scripts/cpa.sh -witness-check \
            -spec $$dir/cex.graphml \
            -spec $$dir/../PropertyERROR.prp \
            $$dir/main.c >> $$dir/main.out 2>&1; \
          cd $$dir; \
          tail -n 1 main.out | grep FALSE; \
	  if [ "$$?" -eq 0 ]; then \
            echo $$dir "[PASSED]"; \
          else \
            echo $$dir "[FAILED]"; \
           fi; \
	  cd ..; \
	done;

clean:
	@rm -f *.log
	@for dir in *; do rm -f $$dir/*.out; done;

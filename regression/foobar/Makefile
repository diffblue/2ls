default: tests.log

SOLVER = --verbosity 10 --binsearch-solver

test:
	@../test.pl -c "../../../src/summarizer/summarizer $(SOLVER)"

tests.log: ../test.pl
	@../test.pl -c "../../../src/summarizer/summarizer $(SOLVER)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

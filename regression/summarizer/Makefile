default: tests.log

FLAGS = --verbosity 10 --refine

test:
	@../test.pl -c "../../../src/summarizer/summarizer $(FLAGS)"

tests.log: ../test.pl
	@../test.pl -c "../../../src/summarizer/summarizer $(FLAGS)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f *.log
	@for dir in *; do rm -f $$dir/*.out; done;

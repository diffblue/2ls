default: tests.log

FLAGS = --verbosity 10 --context-sensitive

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

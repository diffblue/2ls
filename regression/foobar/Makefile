default: goto-binaries tests.log

test:
	@../test.pl -c ../../../src/summarizer/summarizer

tests.log: ../test.pl
	@../test.pl -c ../../../src/summarizer/summarizer

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

goto-binaries:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			goto-cc "$$dir/main.c" -o "$$dir/main.o"; \
		fi; \
	done;

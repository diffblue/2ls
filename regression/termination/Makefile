default: tests.log

FLAGS = --verbosity 10 --termination

test:
	@../test.pl -p -c "../../../src/2ls/2ls $(FLAGS)"

tests.log: ../test.pl
	@../test.pl -p -c "../../../src/2ls/2ls $(FLAGS)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@rm -f *.log
	@for dir in *; do rm -f $$dir/*.out; done;

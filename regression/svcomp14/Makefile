SUM=../../src/summarizer/summarizer --error-label ERROR
EQU="$(SUM) --equalities"
ZON="$(SUM) --zones"
INT="$(SUM) --intervals"


# the Python script
RUN=python run.py

all: bitvector-tests\
	ldv-regression-tests\
	ssh-simplified-tests\
	locks-tests\
	bitvector-regression-tests

# bitvector
bitvector-tests:
	$(RUN) -t $(EQU) -o bitvector/int.csv -p $(CURDIR)/bitvector
	$(RUN) -t $(EQU) -o bitvector/equ.csv -p $(CURDIR)/bitvector
	$(RUN) -t $(ZON) -o bitvector/zon.csv -p $(CURDIR)/bitvector

# ldv-regression
ldv-regression-tests:
	$(RUN) -t $(EQU) -o ldv-regression/int.csv -p $(CURDIR)/ldv-regression
	$(RUN) -t $(EQU) -o ldv-regression/equ.csv -p $(CURDIR)/ldv-regression
	$(RUN) -t $(ZON) -o ldv-regression/zon.csv -p $(CURDIR)/ldv-regression

# ssh-simplified
ssh-simplified-tests:
	$(RUN) -t $(EQU) -o ssh-simplified/int.csv -p $(CURDIR)/ssh-simplified
	$(RUN) -t $(EQU) -o ssh-simplified/equ.csv -p $(CURDIR)/ssh-simplified
	$(RUN) -t $(ZON) -o ssh-simplified/zon.csv -p $(CURDIR)/ssh-simplified

# locks
locks-tests:
	$(RUN) -t $(EQU) -o locks/int.csv -p $(CURDIR)/locks
	$(RUN) -t $(EQU) -o locks/equ.csv -p $(CURDIR)/locks
	$(RUN) -t $(ZON) -o locks/zon.csv -p $(CURDIR)/locks

#  bitvector-regression
bitvector-regression-tests:
	$(RUN) -t $(EQU) -o bitvector-regression/int.csv -p $(CURDIR)/bitvector-regression
	$(RUN) -t $(EQU) -o bitvector-regression/equ.csv -p $(CURDIR)/bitvector-regression
	$(RUN) -t $(ZON) -o bitvector-regression/zon.csv -p $(CURDIR)/bitvector-regression
  


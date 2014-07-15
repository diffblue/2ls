SUMMARIZER=../../../src/summarizer/summarizer
CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction"
#CHECKS="--div-by-zero-check --signed-overflow-check --bounds-check --pointer-check"
SETS="bitvector bitvector-regression ldv-regression locks ssh ssh-simplified" 

TIMEOUT=900

for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f $o.log
    for f in *.c 
    do 
      echo $d/$f "using" $o
      echo "FILE:" $f >> $o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --$o)) &>> $o.log
    done
    cd ..
  done
done

for o in intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f $o.log
    for f in *.c 
    do 
      echo $d/$f "using context-sensitive" $o
      echo "FILE:" $f >> $o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --context-sensitive --$o)) &>> context_sensitive_$o.log
    done
    cd ..
  done
done

for d in $SETS 
do
  cd $d
  rm -f $o.log
  for f in *.c 
  do 
    echo $d/$f "using unwind5"
    echo "FILE:" $f >> $o.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline --unwind 5)) &>> unwind5.log
  done
  cd ..
done

for d in $SETS 
do
  cd $d
  rm -f $o.log
  for f in *.c 
  do 
    echo $d/$f "using unwind10"
    echo "FILE:" $f >> $o.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline --unwind 10)) &>> unwind10.log
  done
  cd ..
done

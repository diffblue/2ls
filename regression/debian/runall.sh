SUMMARIZER=../../../src/summarizer/summarizer
CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction --pointer-check"
#CHECKS="--div-by-zero-check --signed-overflow-check --bounds-check --pointer-check"
SETS="a2ps bison-2.5 grep-2.12"

TIMEOUT=900

for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.$o.log
    for f in *.o 
    do 
      echo $d/$f "using" $o
      echo "FILE:" $f >> ../$d.$o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --$o)) &>> ../$d.$o.log
    done
    cd ..
  done
done

for o in intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.context_sensitive_$o.log
    for f in *.o 
    do 
      echo $d/$f "using context-sensitive" $o
      echo "FILE:" $f >> ../$d.context_sensitive_$o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --context-sensitive --$o)) &>> ../$d.context_sensitive_$o.log
    done
    cd ..
  done
done

for d in $SETS 
do
  cd $d
  rm -f ../$d.unwind5.log
  for f in *.o 
  do 
    echo $d/$f "using unwind5"
    echo "FILE:" $f >> ../$d.unwind5.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline --unwind 5)) &>> ../$d.unwind5.log
  done
  cd ..
done

for d in $SETS 
do
  cd $d
  rm -f ../$d.unwind10.log
  for f in *.o 
  do 
    echo $d/$f "using unwind10"
    echo "FILE:" $f >> ../$d.unwind10.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline --unwind 10)) &>> ../$d.unwind10.log
  done
  cd ..
done

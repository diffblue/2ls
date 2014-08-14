SUMMARIZER=../../../src/summarizer/summarizer
#CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction"
CHECKS="--div-by-zero-check --signed-overflow-check --bounds-check --pointer-check"
SETS="bitvector bitvector-regression ldv-regression ssh ssh-simplified"

TIMEOUT=1800

for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.$o.log
    for f in *.c 
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
    for f in *.c 
    do 
      echo $d/$f "using context-sensitive" $o
      echo "FILE:" $f >> ../$d.context_sensitive_$o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --context-sensitive --$o)) &>> ../$d.context_sensitive_$o.log
    done
    cd ..
  done
done

for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.inline.$o.log
    for f in *.c 
    do 
      echo $d/$f "using inline" $o
      echo "FILE:" $f >> ../$d.inline.$o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --inline --$o)) &>> ../$d.inline.$o.log
    done
    cd ..
  done
done

for o in 1 2 3 4 5
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.unwind$o.havoc.log
    for f in *.c 
    do 
      echo $d/$f "using unwind " $o "havoc"
      echo "FILE:" $f >> ../$d.unwind$o.havoc.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --unwind $o)) &>> ../$d.unwind$o.havoc.log
    done
    cd ..
  done
done

for o in 1 2 3 4 5
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.inline.unwind$o.havoc.log
    for f in *.c 
    do 
      echo $d/$f "using inline unwind " $o "havoc"
      echo "FILE:" $f >> ../$d.inline.unwind$o.havoc.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --unwind $o)) &>> ../$d.inline.unwind$o.havoc.log
    done
    cd ..
  done
done

for o in havoc intervals equalities zones
do
for i in 8 16 32 64
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.partial_inline$i.$o.log
    for f in *.c 
    do 
      echo $d/$f "using partial_inline " $i $o
      echo "FILE:" $f >> ../$d.partial_inline$i.$o.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --$o --inline-partial $i)) &>> ../$d.partial_inline$i.$o.log
    done
    cd ..
  done
done
done


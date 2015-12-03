SUMMARIZER=../../../src/summarizer/summarizer
#CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction"
CHECKS="--error-label ERROR"
SETS="loops"

TIMEOUT=900

for u in 0 1 2 3 4 5
do
for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.$o.unwind$u.log
    for f in *true.c 
    do 
      echo $d/$f "using" $o "unwind" $u
      echo "FILE:" $f >> ../$d.$o.unwind$u.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --unwind $u --$o)) &>> ../$d.$o.unwind$u.log
    done
    cd ..
  done
done
done

for u in 0 1 2 3 4 5
do
for o in havoc intervals equalities zones
do
  for d in $SETS
  do
    cd $d
    rm -f ../$d.inline.$o.unwind$u.log
    for f in *true.c 
    do 
      echo $d/$f "using" "inline" $o "unwind" $u
      echo "FILE:" $f >> ../$d.inline.$o.unwind$u.log
      (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --unwind $u --$o)) &>> ../$d.inline.$o.unwind$u.log
    done
    cd ..
  done
done
done

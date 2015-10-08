SUMMARIZER=../../../src/summarizer/summarizer
#CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction"
#CHECKS="--div-by-zero-check --signed-overflow-check --bounds-check --pointer-check"
CHECKS="--termination"
SETS="ldv-regression loops"

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



SUMMARIZER=../../../src/summarizer/summarizer
#CHECKS="--div-by-zero-check --signed-overflow-check --array-abstraction --pointer-check"
CHECKS="--div-by-zero-check --signed-overflow-check --bounds-check --pointer-check"
SETS="sendmail-8.14.4"
#SETS="a2ps bison-2.5 grep-2.12 openjpeg-1.3"

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

for d in 
do
  cd $d
  rm -f ../$d.inline.havoc.log
  for f in *.o 
  do 
    echo $d/$f "using inline"
    echo "FILE:" $f >> ../$d.inline.havoc.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline)) &>> ../$d.inline.havoc.log
  done
done

for d in  
do
  cd $d
  rm -f ../$d.inline.unwind5.havoc.log
  for f in *.o 
  do 
    echo $d/$f "using inline unwind5"
    echo "FILE:" $f >> ../$d.inline.unwind5.havoc.log
    (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $CHECKS $f --havoc --inline --unwind 5)) &>> ../$d.inline.unwind5.havoc.log
  done
done



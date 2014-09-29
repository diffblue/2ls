TIMEOUT=20
SUMMARIZER=../../src/summarizer/summarizer

for f in *.c
do 
  echo $f
  (time perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $f --termination) &> tmp.txt
  grep VERIF tmp.txt
  grep user tmp.txt
  cat tmp.txt >> loopus.log
done
rm tmp.txt
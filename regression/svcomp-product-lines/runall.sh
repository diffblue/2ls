SUMMARIZER=../../src/summarizer/summarizer

TIMEOUT=900

LOG=term-context-sensitive.log
rm -f $LOG
for f in *.c 
do 
 echo $f
 echo $f >> $LOG
 (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $f --termination --context-sensitive)) &> tmp.log
 grep -e "Synth$" tmp.log 
 grep -e "]: not computed$" tmp.log 
 grep -e "]: yes$" tmp.log 
 grep -e "]: unknown$" tmp.log
 grep -e "]: no$" tmp.log
 grep user tmp.log
 grep VERIFICATION tmp.log
 cat tmp.log >> $LOG
done

LOG=term.log
rm -f $LOG
for f in *.c 
do 
 echo $f
 echo $f >> $LOG
 (time (perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $SUMMARIZER $f --termination)) &> tmp.log
 grep -e "Synth$" tmp.log 
 grep -e "]: not computed$" tmp.log 
 grep -e "]: yes$" tmp.log 
 grep -e "]: unknown$" tmp.log
 grep -e "]: no$" tmp.log
 grep user tmp.log
 grep VERIFICATION tmp.log
 cat tmp.log >> $LOG
done

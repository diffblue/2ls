PWD=`pwd`
TIMEOUT=3600
TOOL=acdls
BENCHMARKDIRS=`cat benchmarks-intv.txt`
PROGRESSLOG=${PWD}/progress.log-intervals-${TOOL}
FLAGS="--inline --acdl --decision ordered --propagate chaotic --learning first-uip" 
EXEC=/users/rajdeep/thesis-tool-webpage/acdlp_thesis_version/2ls/src/2ls/2ls
echo "Starting experiments at `date` on `hostname`" > ${PROGRESSLOG}
for DIR in $BENCHMARKDIRS
do
  echo  ${DIR}
  cd ${DIR}
  LOG=${PWD}/logintv-${DIR}
  filename=main.c
  echo "Starting to processing $DIR/$filename at `date`" >> ${PROGRESSLOG}
  runsolver -C $TIMEOUT -W $TIMEOUT -d 1 -M 32768 ${EXEC} ${FLAGS} $filename >> ${LOG}
  echo "done at `date`" >> ${PROGRESSLOG}
  cd ../
done

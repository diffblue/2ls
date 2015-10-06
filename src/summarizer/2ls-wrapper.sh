#!/bin/bash

parse_property_file()
{
  local fn=$1

  cat $fn | sed 's/[[:space:]]//g' | perl -n -e '
if(/^CHECK\(init\((\S+)\(\)\),LTL\(G(\S+)\)\)$/) {
  print "ENTRY=$1\n";
  print "PROPERTY=\"--error-label $1\"\n" if($2 =~ /^!label\((\S+)\)$/);
  print "PROPERTY=\" \"\n" if($2 =~ /^!call\(__VERIFIER_error\(\)\)$/);
  print "PROPERTY=\"--pointer-check --memory-leak-check --bounds-check\"\n" if($2 =~ /^valid-(free|deref|memtrack)$/);
  print "PROPERTY=\"--signed-overflow-check\"\n" if($2 =~ /^!SignedIntegerOverflow$/);
}'
}

parse_result()
{
  if tail -n 50 $LOG.ok | grep -q "^[[:space:]]*__CPROVER_memory_leak == NULL$" ; then
    echo 'FALSE(valid-memtrack)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*dereference failure:" ; then
    echo 'FALSE(valid-deref)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*double free$" ; then
    echo 'FALSE(valid-free)'
  elif tail -n 50 $LOG.ok | grep -q "^[[:space:]]*free argument has offset zero$" ; then
    echo 'FALSE(valid-free)'
  else
    echo FALSE
  fi
}

BIT_WIDTH="--64"
BM=""
PROP_FILE=""

while [ -n "$1" ] ; do
  case "$1" in
    --32|--64) BIT_WIDTH="$1" ; shift 1 ;;
    --propertyfile) PROP_FILE="$2" ; shift 2 ;;
    *) BM="$1" ; shift 1 ;;
  esac
done

if [ -z "$BM" ] || [ -z "$PROP_FILE" ] ; then
  echo "Missing benchmark or property file"
  exit 1
fi

if [ ! -s "$BM" ] || [ ! -s "$PROP_FILE" ] ; then
  echo "Empty benchmark or property file"
  exit 1
fi

eval `parse_property_file $PROP_FILE`
export ENTRY
export PROPERTY
export BIT_WIDTH
export BM

export LOG=`mktemp -t 2ls-log.XXXXXX`
trap "rm -f $LOG.ok" EXIT

./2ls --k-induction --competition-mode --graphml-cex /dev/stdout $BIT_WIDTH $PROPERTY --function $ENTRY $BM >> $LOG.ok 2>&1
ec=$?
cat $LOG.ok
if [ $ec -eq 0 ] 
then 
  echo "TRUE" 
fi
if [ $ec -eq 5 ] 
then 
  echo "UNKNOWN" 
fi
if [ $ec -eq 10 ] 
then 
  parse_result 
fi
exit $ec


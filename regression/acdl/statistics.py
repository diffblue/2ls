#!/usr/bin/python

import sys
import re
import subprocess
import csv
import os
import fnmatch 

def processfile():

  src_path=sys.argv[1]
  
  properties=0
  verified_prop=0
  false_prop=0
  inconclusive_prop=0
  timeout_prop=0
  memout_prop=0
  error_prop=0
  sum_runtime=0.0
  sum_peak_memory=0.0
  decisions=0
  propagations=0
  conflicts=0
  conflict_literals=0
  learnt_clauses=0
  result=""
  # temporary variable
  status=""
  f_name=""
  func_name=""
  time=0.0

  status_decision = re.compile("Decisions::") 
  status_propagation = re.compile("Propagation::") 
  status_conflict  = re.compile("Learning Iterations::")
  status_conflict_literal = re.compile("Learnt literals::")
  status_learnt_clauses = re.compile("Learnt clauses::")
  status_time = re.compile("runsolver_cputime:")
  status_result = re.compile("VERIFICATION")
  
  report_file=open('statistics.csv', 'wb')
  report = csv.writer(report_file, delimiter=',',
      quotechar='|', quoting=csv.QUOTE_MINIMAL)
  report.writerow(['decisions', 'propagations', 'conflicts', 'conflict literals', 'learnt clauses', 'Time', 'Result']) 
  for root, dirs, filenames in os.walk(src_path):
    for f in filenames:
      if fnmatch.fnmatch(f, 'logintv*'):
        #if f.endswith(".out"):
        log = open(src_path + f, 'r')
        lines=[line for line in log]
        for line in lines:
          if status_decision.search(line):
            cols=line.split('::')
            str1=cols[1].lstrip()
            dec=str1.split(' ',1)[0]
            decisions = int(dec)
          if status_propagation.search(line):
            cols=line.split('::')
            str1=cols[1].lstrip()
            prop=str1.split(' ',1)[0]
            propagations = int(prop)
          if status_conflict.search(line):
            cols=line.split('::')
            str1=cols[1].lstrip()
            #str2=st1.rstrip()
            con=str1.split(' ',1)[0]
            conflicts = int(con)
          if status_conflict_literal.search(line):
            cols=line.split('::')
            str1=cols[1].lstrip()
            lit=str1.split(' ',1)[0]
            conflict_literals = int(lit)
          if status_learnt_clauses.search(line):
            cols=line.split('::')
            str1=cols[1].lstrip()
            res=str1.split(' ',1)[0]
            learnt_clauses = int(res)
          if status_result.search(line):
            result = line 
          if status_time.search(line):
            cols=line.split(':')
            str1=cols[1].lstrip()
            t=str1.split(' ',1)[0]
            time= float(t)
        report.writerow([decisions,propagations,conflicts,conflict_literals,learnt_clauses,time,result]) 
        print root, decisions, propagations, conflicts, conflict_literals, learnt_clauses, time, result 
  
processfile()            

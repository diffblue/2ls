#!/usr/bin/perl
 
my $timeout = 1790;

################################################################################
# load data
################################################################################

sub load_data{
my $dir = $_[0];
my $run = $_[1];
my $bench = $_[2];
my $infilename = $dir . "." . $run . ".log";

print "reading file: ",$infilename,"\n";

open $infile, $infilename;

my $name;

while (my $line = <$infile>) {
  if($line =~ m/Type-checking (.*)/) {
    $name = $1;
    $name =~ s/_/\\_/g;
    print "benchmark: ",$name,"\n";
    $bench{$dir}{$name}{$run}{"time"} = 100000;
  }
  if($line =~ m/  number of solver instances: (.*)/) {
    $bench{$dir}{$name}{$run}{"solver_instances"} = $1;
  }
  if($line =~ m/  number of solver calls: (.*)/) {
    $bench{$dir}{$name}{$run}{"solver_calls"} = $1;
  }
  if($line =~ m/transformer(.*)/) {
    $bench{$dir}{$name}{$run}{"summaries_computed"} += 1;
  }
  if($line =~ m/Precondition does not hold(.*)/) {
    $bench{$dir}{$name}{$run}{"summaries_recomputed"} += 1;
  }
#  if($line =~ m/(.*)replacing by summary(.*)/) {
  if($line =~ m/(.*)holds, replacing(.*)/) {
    $bench{$dir}{$name}{$run}{"summaries_reused"} += 1;
  }
  if($line =~ m/  number of summaries used: (.*)/) {
    $bench{$dir}{$name}{$run}{"summaries_used"} += $1;
  }
  if($line =~ m/Checking precondition(.*)/) {
    $bench{$dir}{$name}{$run}{"function_calls"} += 1;
  }
  if($line =~ m/(.*) arithmetic overflow (.*): (.*)/) {
#    print "token: ",$3,"\n";
    if($3 eq "OK") { 
      $bench{$dir}{$name}{$run}{"ok"}{"arithmetic_overflow"} += 1; 
    }
    if($3 eq "FAILURE") { 
      $bench{$dir}{$name}{$run}{"fail"}{"arithmetic_overflow"} += 1; 
    }
  }
  if($line =~ m/(.*) division by zero: (.*)/) {
#    print "token: ",$2,"\n";
    if($2 eq "OK") { 
      $bench{$dir}{$name}{$run}{"ok"}{"division_by_zero"} += 1; 
    }
    if($2 eq "FAILURE") { 
      $bench{$dir}{$name}{$run}{"fail"}{"division_by_zero"} += 1; 
    }
  }
  if($line =~ m/(.*) dereference failure: pointer NULL: (.*)/) {
#    print "token: ",$3,"\n";
    if($2 eq "OK") { 
      $bench{$dir}{$name}{$run}{"ok"}{"pointer_NULL"} += 1; 
    }
    if($2 eq "FAILURE") { 
      $bench{$dir}{$name}{$run}{"fail"}{"pointer_NULL"} += 1; 
    }
  }
  if($line =~ m/(.*) dereference failure: object bounds: (.*)/) {
#    print "token: ",$3,"\n";
    if($2 eq "OK") { 
      $bench{$dir}{$name}{$run}{"ok"}{"object_bounds"} += 1; 
    }
    if($2 eq "FAILURE") { 
      $bench{$dir}{$name}{$run}{"fail"}{"object_bounds"} += 1; 
    }
  }
  if($line =~ m/(.*) array(.*): (.*)/) {
#    print "token: ",$3,"\n";
    if($3 eq "OK") { 
      $bench{$dir}{$name}{$run}{"ok"}{"array_bounds"} += 1; 
    }
    if($3 eq "FAILURE") { 
      $bench{$dir}{$name}{$run}{"fail"}{"array_bounds"} += 1; 
    }
  }
#  if($line =~ m/(.*): (.*)/) {
#    print "token: ",$2,"\n";
#    if($2 eq "OK") { 
#      $bench{$dir}{$name}{$run}{"ok"}{"other"} += 1; 
#    }
#    elsif($2 eq "FAILURE") { 
#      $bench{$dir}{$name}{$run}{"fail"}{"other"} += 1; 
#    }
#    else { print "Unexpected token: ",$2,"\n"; }
#  }
  if($line =~ m/user(.*)m(.*)s/) {
    $bench{$dir}{$name}{$run}{"time"} = 60*$1+$2;	
  }
}
close($infile);
return $bench;
}

################################################################################
# output table
################################################################################

sub output_table {
my $bench = $_[1];
my %runstats;
my $runs = $_[2];
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
print $outfile "\\hline\n";
print $outfile "\\multicolumn{1}{l}{",$dir,"}\\\\\n";
print $outfile "\\hline\n";
foreach my $name (sort keys %{$bench{$dir}}) {
  print $outfile $name;
  foreach my $run (@runs) {
    $runstats{$dir}{$run}{"time"} += $bench{$dir}{$name}{$run}{"time"};
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
      print $outfile " & \multicolumn{3}{c}{timeout} "; 
      $runstats{$dir}{$run}{"timeouts"} += 1;
    }
    else
    {
      print $outfile " & ", $bench{$dir}{$name}{$run}{"time"};
      print $name," (",$run,") (",$bench{$dir}{$name}{$run}{"time"},")\n";
      my $oksum = 0;
      if($bench{$dir}{$name}{$run}{"ok"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"ok"}}) { 
          print $_," [OK]: ",$bench{$dir}{$name}{$run}{"ok"}{$_},"\n";
          $oksum += $bench{$dir}{$name}{$run}{"ok"}{$_}; 
        }
        $runstats{$dir}{$run}{"oksum"} += $oksum; 
      }
      print "OK-sum: ",$oksum,"\n";
      print $outfile " & ",$oksum;  
      my $failsum = 0;
      if($bench{$dir}{$name}{$run}{"fail"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"fail"}}) { 
          print $_," [FAILURE]: ",$bench{$dir}{$name}{$run}{"fail"}{$_},"\n";
          $failsum += $bench{$dir}{$name}{$run}{"fail"}{$_}; 
        }
        $runstats{$dir}{$run}{"failsum"} += $failsum; 
      }
      print "FAILURE-sum: ",$failsum,"\n";
      print $outfile " & ",$failsum;
    }
  }
  print $outfile "\\\\\n";
}
print $outfile "\\hline\ntotal";
foreach my $run (@runs) {
  print $outfile " & ",$runstats{$dir}{$run}{"time"};
  print $outfile " & ",$runstats{$dir}{$run}{"oksum"};
  print $outfile " & ",$runstats{$dir}{$run}{"failsum"};
  $runstats{$run}{"time"} += $runstats{$dir}{$run}{"time"};
  $runstats{$run}{"oksum"} += $runstats{$dir}{$run}{"oksum"};
  $runstats{$run}{"failsum"} += $runstats{$dir}{$run}{"failsum"};
}
print $outfile "\\\\\n\\hline\n";
}
print $outfile "\\hline\nTOTAL";
foreach my $run (@runs) {
  print $outfile " & ",$runstats{$run}{"time"};
  print $outfile " & ",$runstats{$run}{"oksum"};
  print $outfile " & ",$runstats{$run}{"failsum"};
}
print $outfile "\\\\\n\\hline\n";
close($outfile);
}

################################################################################
# output totals
################################################################################

sub output_totals {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    $runstats{$dir}{$run}{"time"} += $bench{$dir}{$name}{$run}{"time"};
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
      $runstats{$dir}{$run}{"timeouts"} += 1;
    }
    else
    {
      my $oksum = 0;
      if($bench{$dir}{$name}{$run}{"ok"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"ok"}}) { 
          $oksum += $bench{$dir}{$name}{$run}{"ok"}{$_}; 
        }
        $runstats{$dir}{$run}{"oksum"} += $oksum; 
      }
      my $failsum = 0;
      if($bench{$dir}{$name}{$run}{"fail"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"fail"}}) { 
          $failsum += $bench{$dir}{$name}{$run}{"fail"}{$_}; 
        }
        $runstats{$dir}{$run}{"failsum"} += $failsum; 
      }
    }
  }
}
print $outfile $dir;
foreach my $run (@runs) {
  print $outfile " & ",$runstats{$dir}{$run}{"time"};
  print $outfile " & ",$runstats{$dir}{$run}{"oksum"};
  print $outfile " & ",$runstats{$dir}{$run}{"failsum"};
  $runstats{$run}{"time"} += $runstats{$dir}{$run}{"time"};
  $runstats{$run}{"oksum"} += $runstats{$dir}{$run}{"oksum"};
  $runstats{$run}{"failsum"} += $runstats{$dir}{$run}{"failsum"};
}
print $outfile "\\\\\n";
}
print $outfile "\\hline\nTOTAL";
foreach my $run (@runs) {
  print $outfile " & ",$runstats{$run}{"time"};
  print $outfile " & ",$runstats{$run}{"oksum"};
  print $outfile " & ",$runstats{$run}{"failsum"};
}
print $outfile "\\\\\n\\hline\n";
close($outfile);
}

################################################################################
# output total chart
################################################################################

sub output_total_chart {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    $runstats{$run}{"benchmarks"} += 1;
    $runstats{$run}{"solver_instances"} += 
       $bench{$dir}{$name}{$run}{"solver_instances"};
    $runstats{$run}{"solver_calls"} += 
       $bench{$dir}{$name}{$run}{"solver_calls"};
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
      $runstats{$run}{"timeouts"} += 1;
    }
    else
    {
      my $oksum = 0;
      if($bench{$dir}{$name}{$run}{"ok"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"ok"}}) { 
          $oksum += $bench{$dir}{$name}{$run}{"ok"}{$_}; 
        }
        $runstats{$dir}{$run}{"oksum"} += $oksum; 
      }
      my $failsum = 0;
      if($bench{$dir}{$name}{$run}{"fail"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"fail"}}) { 
          $failsum += $bench{$dir}{$name}{$run}{"fail"}{$_}; 
        }
        $runstats{$dir}{$run}{"failsum"} += $failsum; 
      }
    }
  }
}
foreach my $run (@runs) {
  print $run,": benchmarks: ",$runstats{$run}{"benchmarks"},"\n";
  print $run,": timeouts: ",$runstats{$run}{"timeouts"},"\n";
  print $run,": solver instances: ",$runstats{$run}{"solver_instances"},"\n";
  print $run,": solver calls: ",$runstats{$run}{"solver_calls"},"\n";
  $runstats{$run}{"oksum"} += $runstats{$dir}{$run}{"oksum"};
  $runstats{$run}{"failsum"} += $runstats{$dir}{$run}{"failsum"};
}
}
print $outfile "#run ok failure\n";
foreach my $run (@runs) {
  print $outfile $run;
  print $outfile " ",$runstats{$run}{"oksum"};
  print $outfile " ",$runstats{$run}{"failsum"};
  print $outfile "\n";
}
close($outfile);
}

################################################################################
# output solver calls chart
################################################################################

sub output_solver_chart {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    $runstats{$run}{"benchmarks"} += 1;
    $runstats{$run}{"solver_instances"} += 
       $bench{$dir}{$name}{$run}{"solver_instances"};
    $runstats{$run}{"solver_calls"} += 
       $bench{$dir}{$name}{$run}{"solver_calls"};
    $runstats{$run}{"time"} += $bench{$dir}{$name}{$run}{"time"};
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
      $runstats{$run}{"timeouts"} += 1;
    }
    $runstats{$run}{"summaries_used"} += 
      $bench{$dir}{$name}{$run}{"summaries_used"};
    $runstats{$run}{"summaries_computed"} += 
      $bench{$dir}{$name}{$run}{"summaries_computed"};
    $runstats{$run}{"summaries_recomputed"} += 
      $bench{$dir}{$name}{$run}{"summaries_recomputed"};
    $runstats{$run}{"summaries_reused"} += 
      $bench{$dir}{$name}{$run}{"summaries_reused"};
    $runstats{$run}{"function_calls"} += 
      $bench{$dir}{$name}{$run}{"function_calls"};
  }
}
foreach my $run (@runs) {
  print $run,": benchmarks: ",$runstats{$run}{"benchmarks"},"\n";
  print $run,": timeouts: ",$runstats{$run}{"timeouts"},"\n";
  print $run,": solver instances: ",$runstats{$run}{"solver_instances"},"\n";
  print $run,": solver calls: ",$runstats{$run}{"solver_calls"},"\n";
  print $run,": total time: ",$runstats{$run}{"time"},"\n";
  print $run,": function calls: ",$runstats{$run}{"function_calls"},"\n";
  print $run,": summaries computed: ",$runstats{$run}{"summaries_computed"},"\n";
  print $run,": summaries used: ",$runstats{$run}{"summaries_used"},"\n";
  print $run,": summaries recomputed: ",$runstats{$run}{"summaries_recomputed"},"\n";
  print $run,": summaries reused: ",$runstats{$run}{"summaries_reused"},"\n";
}
}
print $outfile "#run average_solver_instances average_solver_calls average_time_per_call\n";
foreach my $run (@runs) {
  print $outfile $run;
  print $outfile " ",($runstats{$run}{"solver_instances"}/$runstats{$run}{"benchmarks"});
  print $outfile " ",($runstats{$run}{"solver_calls"}/$runstats{$run}{"benchmarks"});
  if($runstats{$run}{"solver_calls"}>0) 
   { print $outfile " ",($runstats{$run}{"time"}/$runstats{$run}{"solver_calls"}); }
  else
   { print $outfile " 0"; }
  print $outfile "\n";
}
close($outfile);
}

################################################################################
# output property chart
################################################################################

sub output_property_chart {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
my %props;
print "runs: ",@runs,"\n";
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
    }
    else
    {
      if($bench{$dir}{$name}{$run}{"ok"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"ok"}}) { 
	  $props{$_} = 0;
          $runstats{$run}{$_}{"oksum"} += 
            $bench{$dir}{$name}{$run}{"ok"}{$_};
          $runstats{$run}{"oksum"} += 
            $bench{$dir}{$name}{$run}{"ok"}{$_};
        }
      }
      if($bench{$dir}{$name}{$run}{"fail"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"fail"}}) { 
	  $props{$_} = 0;
          $runstats{$run}{$_}{"failsum"} += 
            $bench{$dir}{$name}{$run}{"fail"}{$_};
          $runstats{$run}{"failsum"} += 
            $bench{$dir}{$name}{$run}{"fail"}{$_};
        }
      }
    }
  }
}
}
print $outfile "#run total_ok";
foreach my $prop (keys %props) {
  print $outfile " ",$prop;
}
print $outfile "\n";
foreach my $run (@runs) {
  print $outfile $run;
  print $outfile " ",$runstats{$run}{"oksum"};
  foreach my $prop (keys %props) {
    my $ok = $runstats{$run}{$prop}{"oksum"};
    if($ok eq "") { $ok = 0; }
    print $outfile " ",$ok;
#  print $outfile " ",$runstats{$run}{"failsum"};
  }
  print $outfile "\n";
}
close($outfile);
}

################################################################################
# output property chart 2
################################################################################

sub output_property_chart2 {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
my %props;
open $outfile, (join '',(">",$_[0]));
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
    }
    else
    {
      if($bench{$dir}{$name}{$run}{"ok"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"ok"}}) { 
	  $props{$_} = 0;
          $runstats{$run}{$_}{"oksum"} += 
            $bench{$dir}{$name}{$run}{"ok"}{$_};
        }
      }
      if($bench{$dir}{$name}{$run}{"fail"}) {
        foreach (keys %{$bench{$dir}{$name}{$run}{"fail"}}) { 
	  $props{$_} = 0;
          $runstats{$run}{$_}{"failsum"} += 
            $bench{$dir}{$name}{$run}{"fail"}{$_};
        }
      }
    }
  }
}
}
print $outfile "#run ";
foreach my $run (@runs) {
  print $outfile " ",$run;
}
print $outfile "\n";
foreach my $prop (keys %props) {
  print $outfile $prop;
  foreach my $run (@runs) {
    my $ok = $runstats{$run}{$prop}{"oksum"};
    if($ok eq "") { $ok = 0; }
    print $outfile " ",$ok;
#  print $outfile " ",$runstats{$run}{"failsum"};
  }
  print $outfile "\n";
}
close($outfile);
}

################################################################################
# output cactus
################################################################################

sub output_cactus {
my @runs = @{$_[1]};
my $bench = $_[2];
my %runstats;
foreach my $dir (sort keys %bench) {
foreach my $name (sort keys %{$bench{$dir}}) {
  foreach my $run (@runs) {
    if($bench{$dir}{$name}{$run}{"time"}>$timeout) {
      push @{$runstats{$run}},100000;
    }
    else {
      push @{$runstats{$run}},$bench{$dir}{$name}{$run}{"time"};
    }
  }
}
}
open $outfile, (join '',(">",$_[0]));
print $outfile "benchmark";
my $firstrun;
foreach my $run (@runs) {
  $firstrun = $run;
  my $benchmarks = @{$runstats{$run}};
#  print "benchmarks run: ",$benchmarks,"\n";
  for(my $i=0;$i<205;$i++) {
    if(@{$runstats{$run}}[$i] eq "") { @{$runstats{$run}}[$i] = 100000; }
  }
  print "sorting ",$run,"\n";
  print $outfile " ",$run;
  @{$runstats{$run}} = sort {$a <=> $b} @{$runstats{$run}};
}
print $outfile "\n";
for(my $i=0; $i<@{$runstats{$firstrun}}; $i++) {
print "line ",$i,": ";
print $outfile $i;
foreach my $run (@runs) {
  print " ",@{$runstats{$run}}[$i];
  print $outfile " ",@{$runstats{$run}}[$i];
}
print "\n";
print $outfile "\n";
}
close($outfile);
}


################################################################################
# main
################################################################################

my %bench;

{

my @runs = ("havoc", "intervals", "equalities", "zones", "context_sensitive_intervals", "context_sensitive_equalities", "context_sensitive_zones", "partial_inline8.havoc", "partial_inline16.havoc", "partial_inline32.havoc", "partial_inline64.havoc", "partial_inline8.intervals", "partial_inline16.intervals", "partial_inline32.intervals", "partial_inline64.intervals", "inline.intervals", "partial_inline8.equalities", "partial_inline16.equalities", "partial_inline32.equalities", "partial_inline64.equalities", "inline.equalities", "partial_inline8.zones", "partial_inline16.zones", "partial_inline32.zones", "partial_inline64.zones", "inline.zones", "unwind1.havoc", "unwind2.havoc", "unwind3.havoc", "unwind4.havoc", "unwind5.havoc", "inline.unwind1.havoc", "inline.unwind2.havoc", "inline.unwind3.havoc", "inline.unwind4.havoc", "inline.unwind5.havoc", "invariants.intervals", "invariants.equalities", "invariants.zones", "inline.intervals", "inline.equalities", "inline.zones", "inline.havoc");

my $argc = 0;
my $outfilename;
my @dirs;
foreach my $arg (@ARGV) {
#  if($argc eq 0) { $outfilename=$arg; }
  if($argc >= 0) { push @dirs,$arg; }
  $argc++;
}
if($argc<1) { die "usage: <dir-prefixes>\n"; }


foreach my $dir (@dirs)
{
foreach my $run (@runs)
{
    %bench = load_data($dir,$run,%bench);
}
}

}

#output_table("table.tex",%bench,@runs);
#output_totals("totals.tex",@runs,%bench);
#output_total_chart("total_chart.dat",%bench,@runs);

{
my @runs = ("havoc", "partial_inline8.havoc", "partial_inline16.havoc", "partial_inline32.havoc", "partial_inline64.havoc", "inline.havoc" );
output_property_chart("prop_chart_partial_inline_havoc.dat",\@runs,%bench);
output_cactus("cactus_partial_inline_havoc.dat",\@runs,%bench);
}
{
my @runs = ("intervals", "partial_inline8.intervals", "partial_inline16.intervals", "partial_inline32.intervals", "partial_inline64.intervals", "inline.intervals" );
output_property_chart("prop_chart_partial_inline_intervals.dat",\@runs,%bench);
output_cactus("cactus_partial_inline_intervals.dat",\@runs,%bench);
}
{
my @runs = ("equalities", "partial_inline8.equalities", "partial_inline16.equalities", "partial_inline32.equalities", "partial_inline64.equalities", "inline.equalities" );
output_property_chart("prop_chart_partial_inline_equalities.dat",\@runs,%bench);
output_cactus("cactus_partial_inline_equalities.dat",\@runs,%bench);
}
{
my @runs = ("zones", "partial_inline8.zones", "partial_inline16.zones", "partial_inline32.zones", "partial_inline64.zones", "inline.zones" );
output_property_chart("prop_chart_partial_inline_zones.dat",\@runs,%bench);
output_cactus("cactus_partial_inline_zones.dat",\@runs,%bench);
}
{
my @runs = ("havoc", "unwind1.havoc", "unwind2.havoc", "unwind3.havoc", "unwind4.havoc", "unwind5.havoc" );
output_property_chart("prop_chart_unwind_havoc.dat",\@runs,%bench);
output_cactus("cactus_unwind_havoc.dat",\@runs,%bench);
}
{
my @runs = ("inline.havoc", "inline.unwind1.havoc", "inline.unwind2.havoc", "inline.unwind3.havoc", "inline.unwind4.havoc", "inline.unwind5.havoc" );
output_property_chart("prop_chart_inline_unwind_havoc.dat",\@runs,%bench);
output_cactus("cactus_inline_unwind_havoc.dat",\@runs,%bench);
}
{
my @runs = ("havoc", "invariants.intervals", "invariants.equalities", "invariants.zones", "inline.havoc" );
output_property_chart("prop_chart_invariants.dat",\@runs,%bench);
output_cactus("cactus_invariants.dat",\@runs,%bench);
}
{
my @runs = ("inline.havoc", "inline.intervals", "inline.equalities", "inline.zones" );
output_property_chart("prop_chart_inline.dat",\@runs,%bench);
output_cactus("cactus_inline.dat",\@runs,%bench);
}
{
my @runs = ("havoc", "intervals", "equalities", "zones", "context_sensitive_intervals", "context_sensitive_equalities", "context_sensitive_zones", "inline.havoc", "inline.unwind5.havoc" );
output_property_chart("prop_chart.dat",\@runs,%bench);
output_cactus("cactus.dat",\@runs,%bench);
output_solver_chart("solver.dat",\@runs,%bench);
}

#output_property_chart2("prop_chart2.dat",%bench,@runs);



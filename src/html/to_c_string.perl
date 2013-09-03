#!/usr/bin/perl

use strict;
use warnings;

my @c = <STDIN>;

# print "static char* c_str = {\n";
print "// generated file\n";
foreach (@c) {
    my @s = split('');
    print qq(\t");
    printf("\\x%02x", ord($_)) foreach @s;
    print qq("\n);
}
# print "};\n";


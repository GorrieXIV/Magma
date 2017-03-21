#!/usr/bin/perl

use integer;
use strict;
use warnings;

my $Char = $ARGV[0];

while (my $line = <STDIN>) {
    chomp($line);

    if ($line =~ /^$Char/) {
	print $' . "\n";
    }
}

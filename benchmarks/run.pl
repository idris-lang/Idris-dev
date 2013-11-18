#!/usr/bin/env perl

$bmarks = `cat ALL`;
@bm = split(/\n/, $bmarks);

$total = 0;

foreach $b (@bm) {
    if ($b =~ /([a-zA-Z0-9]+)\/([a-zA-Z0-9]+)\s+(.*)/) {
        #print "Running $1 $2\n";
        chdir $1;
        $result = `/usr/bin/time ./$2 $3 2> .times`;
        $time = `cat .times`; 
        chdir "..";
        #print $time;
        @timeflds = split(/\s+/, $time);
        $user = $timeflds[3];
        print "$1 / $2 $user\n";
        $total += $user;
    }
}

print "\nTOTAL $total\n";


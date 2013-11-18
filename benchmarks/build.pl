#!/usr/bin/env perl

$bmarks = `cat ALL`;
@bm = split(/\n/, $bmarks);

foreach $b (@bm) {
    if ($b =~ /([a-zA-Z0-9]+)\/([a-zA-Z0-9]+)\s+(.*)/) {
        print "Building $1 / $2\n";
        chdir $1;
        system("idris --clean $2.ipkg");
        system("idris --build $2.ipkg");
        chdir "..";
    }
}

#!/usr/bin/perl

use strict;
use Cwd;

my $exitstatus = 0;
my @idrOpts    = ();

sub runtest {
    my ($test, $update) = @_;

    chdir($test);

    print "Running $test...\n";
    my $got = `sh ./run @idrOpts`;
    my $exp = `cat expected`;

    open my $out, '>', 'output';
    print $out $got;
    close $out;

    # $ok = system("diff output expected &> /dev/null");
    # Mangle newlines in $got and $exp
    $got =~ s/\r\n/\n/g;
    $exp =~ s/\r\n/\n/g;

    # Normalize paths in $got and $exp, so the expected outcomes don't
    # change between platforms
    while($got =~ /(^|.*?\n)(.*?)\\(.*?):(\d+):(.*)/ms) {
        $got = "$1$2/$3:$4:$5";
    }
    while($exp =~ /(^|.*?\n)(.*?)\\(.*?):(\d+):(.*)/ms) {
        $exp = "$1$2/$3:$4:$5";
    }

    if ($got eq $exp) {
    	print "Ran $test...success\n";
    }
    else {
        if ($update == 0) {
            $exitstatus = 1;
            print "Ran $test...FAILURE\n";
        } else {
            system("cp output expected");
            print "Ran $test...UPDATED\n";
        }
    }
    chdir "..";
}

my ( @tests, @opts );

if ($#ARGV>=0) {
    my $test = shift @ARGV;
    if ($test eq "all") {
        opendir my $dir, ".";
        my @list = readdir $dir;
        foreach my $file (@list) {
            if ($file =~ /[0-9][0-9][0-9]/) {
                push @tests, $file;
            }
        }
        @tests = sort @tests;
    }
    else {
	    push @tests, $test;
    }
    @opts = @ARGV;
}
else {
    print "Give a test name, or 'all' to run all.\n";
    exit;
}

my $update  = 0;
my $diff    = 0;
my $show    = 0;
my $usejava = 0;

while (my $opt = shift @opts) {
    if    ($opt eq "-u") { $update = 1; }
    elsif ($opt eq "-d") { $diff = 1; }
    elsif ($opt eq "-s") { $show = 1; }
    else { push(@idrOpts, $opt); }
}

my $idris  = $ENV{IDRIS};
my $path   = $ENV{PATH};
$ENV{PATH} = cwd() . "/" . $idris . ":" . $path;

foreach my $test (@tests) {
    if ($diff == 0 && $show == 0) {
	    runtest($test,$update);
    }
    else {
        chdir $test;

        if ($show == 1) {
            system "cat output";
        }
        if ($diff == 1) {
            print "Differences in $test:\n";
            my $ok = system "diff output expected";
            if ($ok == 0) {
                print "No differences found.\n";
            }
        }
        chdir "..";
    }
}

exit $exitstatus;

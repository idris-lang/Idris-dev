#!/usr/bin/env perl

use strict;
use Cwd;
use Cwd 'abs_path';
use Env;

my $exitstatus = 0;
my @idrOpts    = ();

sub sandbox_path {
    my ($test_dir,) = @_;
    my $sandbox = "$test_dir/../../.cabal-sandbox/bin";

    if ( -d $sandbox ) {
        my $sandbox_abs = abs_path($sandbox);
        return "PATH=\"$sandbox_abs:$PATH\"";
    } else {
        return "";
    }
}

sub runtest {
    my ($test, $update) = @_;

    my $sandbox = sandbox_path($test);

    chdir($test);

    print "Running $test...\n";
    my $got = `$sandbox ./run @idrOpts`;
    my $exp = `cat expected`;

    # Allow for variant expected output for tests by overriding expected
    # when there is an expected.<os> file in the test.
    # This should be the exception but there are sometimes valid reasons
    # for os-dependent output.
    # The endings are msys for windows, darwin for osx and linux for linux
    if ( -e "expected.$^O") {
        $exp = `cat expected.$^O`;
    }
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
            system "diff output expected";
        } else {
            system("cp output expected");
            print "Ran $test...UPDATED\n";
        }
    }
    chdir "..";
}

my ( @without, @args, @tests, @opts );

if ($#ARGV>=0) {
    my $test = shift @ARGV;
    if ($test eq "all") {
        opendir my $dir, ".";
        my @list = readdir $dir;
        foreach my $file (@list) {
            if ($file =~ /[0-9][0-9][0-9]$/) {
                push @tests, $file;
            }
        }
        @tests = sort @tests;

    } elsif ($test eq "without") {
        @args = @ARGV;
        foreach my $file (@args) {
            last if ($file =~ /--/);
            push @without, shift @ARGV;
        }

        opendir my $dir, ".";
        my @list = readdir $dir;
        foreach my $file (@list) {
            if ($file =~ /[0-9][0-9][0-9]$/) {
                if (!(grep ($_ eq $file, @without))) {
                   push @tests, $file;
                }
                else {
                   print "Omitting $file\n";
                }
            }
        }
        @tests = sort @tests;
    }
    else {
            if ($test =~ /[0-9][0-9][0-9]$/) {
	        push @tests, $test;
            }
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

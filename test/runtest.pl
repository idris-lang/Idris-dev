#!/usr/bin/perl

my $exitstatus = 0;

sub runtest {
    my ($test, $update) = @_;

    chdir($test);

    print "Running $test...";
    $got = `sh ./run @idrOpts`;
    $exp = `cat expected`;

    open(OUT,">output");
    print OUT $got;
    close(OUT);

#    $ok = system("diff output expected &> /dev/null");
# Mangle newlines in $got and $exp
    $got =~ s/\r\n/\n/g;
    $exp =~ s/\r\n/\n/g;

# Normalize paths in $got and $exp, so the expected outcomes don't change between platforms
    while($got =~ /(^|.*?\n)(.*?)\\(.*?):(\d+):(.*)/ms)
    {
        $got = "$1$2/$3:$4:$5";
    }
    while($exp =~ /(^|.*?\n)(.*?)\\(.*?):(\d+):(.*)/ms)
    {
        $exp = "$1$2/$3:$4:$5";
    }

    if ($got eq $exp) {
	print "success\n";
    } else {
	if ($update == 0) {
	    $exitstatus = 1;
	    print "FAILURE\n";
	} else {
	    system("cp output expected");
	    print "UPDATED\n";
	}
    }
    chdir("..");
}

if ($#ARGV>=0) {
    $test=shift(@ARGV);
    if ($test eq "all") {
	opendir(DIR, ".");
	@list = readdir(DIR);
	foreach $file (@list) {
	    if ($file =~ /[0-9][0-9][0-9]/) {
		push(@tests,$file);
	    }
	}
	@tests = sort @tests;
    }
    else
    {
	push(@tests, $test);
    }
    @opts = @ARGV;
} else {
    print "Give a test name, or 'all' to run all.\n";
    exit;
}

$update=0;
$diff=0;
$show=0;
$usejava = 0;
@idrOpts=();

while ($opt=shift(@opts)) {
    if ($opt eq "-u") { $update = 1; }
    elsif ($opt eq "-d") { $diff = 1; }
    elsif ($opt eq "-s") { $show = 1; }
    else { push(@idrOpts, $opt); }
}

foreach $test (@tests) {

    if ($diff == 0 && $show == 0) {
	runtest($test,$update);
    }
    else {
	chdir($test);

	if ($show == 1) {
	    system("cat output");
	}
	if ($diff == 1) {
	    print "Differences in $test:\n";
	    $ok = system("diff output expected");
	    if ($ok == 0) {
		print "No differences found.\n";
	    }
	}
	chdir("..");
    }

}
exit $exitstatus;

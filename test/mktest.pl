#!/usr/bin/env perl

if ($#ARGV>=0) {
    $test=shift(@ARGV);
} else {
    print "What's its name?\n";
    exit;
}

mkdir($test);

chdir($test);
open(FOO,">run");

print FOO "#!/usr/bin/env bash\n";
print FOO "\${IDRIS:-idris} \$@ $test.idr -o $test\n";
print FOO "./$test\n";print FOO "rm -f $test *.ibc\n";

close(FOO);

system("chmod +x run");

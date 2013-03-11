#!/usr/bin/perl

if ($#ARGV>=0) {
    $test=shift(@ARGV);
} else {
    print "What's its name?\n";
    exit;
}

mkdir($test);

chdir($test);
open(FOO,">run_java");

print FOO "#!/bin/bash\n";
print FOO "idris \$@ $test.idr -o $test.java --target Java\n";
print FOO "export CLASSPATH=../../java/idris.jar:\$CLASSPATH\n";
print FOO "javac $test.java\n";
print FOO "java $test\n";
print FOO "rm -f $test.java *.class\n";

close(FOO);

system("chmod +x run_java");

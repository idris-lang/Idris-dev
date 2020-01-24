#!/usr/bin/env bash

${IDRIS:-idris} $@ reg029.idr -o reg029
unset IDRIS_REG029_NONEXISTENT_VAR
export IDRIS_REG029_EXISTENT_VAR='exists!'

IsJava=`echo "$@" | grep -E "\-\-codegen([[:space:]]+)Java\>"`
if [ -z "$IsJava" ]
then
  ./reg029
else
  javac -cp reg029:. Reg029Wrapper.java
  java -cp reg029:. Reg029Wrapper
fi
${IDRIS:-idris} $@ reg029.idr --execute
rm -f reg029 *.ibc *.class


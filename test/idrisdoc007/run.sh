#!/usr/bin/env bash
# Tests that documentation only is written when safe
mkdir do_not_delete_doc
${IDRIS:-idris} $@ --mkdoc package.ipkg > nowhere
echo Exit status \(expects 1\): $?
rm -rf do_not_delete_doc *.ibc nowhere

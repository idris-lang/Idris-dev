#!/usr/bin/env bash
# Tests that documentation properly is merged with existent.
${IDRIS:-idris} $@ --mkdoc package_a.ipkg
[ -f test_merge_doc/IdrisDoc ] && echo "IdrisDoc file written"
${IDRIS:-idris} $@ --mkdoc package_b.ipkg
ls -1p test_merge_doc/docs
if grep -q "href\\=\"docs/A.fully.Qualified.NAME\\.html\"" test_merge_doc/index.html; then
  echo A.fully.Qualified.NAME is in the index
else
  echo A.fully.Qualified.NAME is NOT in the index
fi
if grep -q "href\\=\"docs/B\\.html\"" test_merge_doc/index.html; then
  echo B is in the index
else
  echo B is NOT in the index
fi
rm -rf *.ibc *_doc A/fully/Qualified/NAME.ibc

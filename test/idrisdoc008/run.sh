#!/usr/bin/env bash
# Tests that documentation is generated for both public and abstract members.
${IDRIS:-idris} $@ --mkdoc visibility.ipkg
[ -f visibility_doc/docs/Abstract.html ] && echo "Abstract members are documented"
[ -f visibility_doc/docs/Visible.html ] && echo "Public members are documented"
rm -rf *.ibc *_doc

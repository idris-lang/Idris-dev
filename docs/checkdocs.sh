#  ------------------------------------------------------------ [ checkdocs.sh ]
#  Module    : checkdocs.sh
#  Copyright : (c) The Idris Community
#  License   : see LICENSE
#  --------------------------------------------------------------------- [ EOH ]

# A numpty test to determine if the sphinx docs can be built or not.
#
# Adapted in part from [PyMSQL project](https://github.com/pymssql/pymssql)

test -z "$(make SPHINXOPTS='-q' html 2>&1 | egrep -w 'SEVERE:|ERROR:')"

#  --------------------------------------------------------------------- [ EOF ]

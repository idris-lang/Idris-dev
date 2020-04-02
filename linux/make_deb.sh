#!/usr/bin/env sh

set -euo pipefail

if [ "$#" -lt 1 ]; then
    echo "Usage $0 [version number]"
    echo ""
    echo "The first argument is the version number"
    exit 1
fi

VERSION=${1:-}

echo "==> Building version-$VERSION"
echo ""
echo "Q: Have you: (a) set the release flag & (b) checked the demos and the tutorial?"
read ${FOO:-}

echo "==> Establishing details"
echo ""

MACHINE=$(uname -m)
case "$MACHINE" in
  x86_64) ARCHITECTURE=amd64;;
  i686)   ARCHITECTURE=i386;;
  i386)   ARCHITECTURE=i386;;
esac

ARTIFACTS="${ARTIFACTS:-/artifacts}"
DEBVER=$VERSION
BASE=idris-$DEBVER-$ARCHITECTURE
DIST=`pwd`/$BASE
DEST=$DIST/usr/local
COPYRIGHT=$DEST/share/doc/idris/copyright

echo "===> Machine is: ${MACHINE}"
echo "===> Version to be installed is: ${DEBVER}"
echo "===> Base is: ${BASE}"
echo "===> Dist is: ${DIST}"
echo "===> Dest is: ${DEST}"
echo "===> Copyright goes to: ${COPYRIGHT}"
echo ""

echo "Q: Do you want to continue?"
read ${FOO:-}

echo "==> Removing old build."
rm -rf ${DEST}

mkdir -p ${DEST}/bin ${DEST}/lib ${DEST}/share

echo "==> Building & Copying Idris ${DEBVER}"

cabal v1-update
cabal v1-sandbox init
cabal v1-install --only-dependencies

cabal v1-configure \
      --prefix=/usr/local \
      --datasubdir="\$pkg/\$version" \
      --docdir="\$datadir/doc/\$pkg"

cabal v1-build

echo "==> Copying files"
cabal v1-copy --destdir=${DIST}

echo "==> Preparing to build package"

echo "==> Setting Permissions"
find $DIST -type d | xargs chmod 755

echo "==> Stripping"
strip $DEST/bin/idris*

echo "==> Compressing Man Page"
gzip -9 $DEST/share/man/man1/idris.1

echo "==> Moving Copyright across"
cp LICENSE $COPYRIGHT
echo "" >> $COPYRIGHT

echo "==> Setting CONTROL"
INSTALLED_SIZE=$(du -k -s $DEST | awk '{print $1}')
mkdir $DIST/DEBIAN
perl -pe "s/VERSION/$DEBVER/" linux/control.in \
  | perl -pe "s/ARCHITECTURE/$ARCHITECTURE/" \
  | perl -pe "s/INSTALLED_SIZE/$INSTALLED_SIZE/" \
  > $DIST/DEBIAN/control

echo "==> Creating Package"
fakeroot dpkg-deb --build $DIST
rm -rf $DIST

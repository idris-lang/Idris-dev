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
read -r ${FOO:-}

echo "==> Establishing details"
echo ""

MACHINE=$(uname -m)
case "$MACHINE" in
  x86_64) ARCHITECTURE=amd64;;
  i686)   ARCHITECTURE=i386;;
  i386)   ARCHITECTURE=i386;;
esac

DEBVER=$VERSION
BASE=idris-$DEBVER-$ARCHITECTURE
DIST=$(pwd)/$BASE
DEST=$DIST/usr/local
COPYRIGHT=$DEST/share/doc/idris/copyright

echo "===> Machine is: ${MACHINE}"
echo "===> Version to be installed is: ${DEBVER}"
echo "===> Base is: ${BASE}"
echo "===> Dist is: ${DIST}"
echo "===> Dest is: ${DEST}"
echo "===> Copyright goes to: ${COPYRIGHT}"
echo ""

echo "==> Removing old build."
rm -rf "${DEST}"

echo "==> Building & Copying Idris ${DEBVER}"

cabal v1-update
cabal v1-sandbox init
cabal v1-install --only-dependencies

GHCEXE=$(which ghc)
GHCVER=$(${GHCEXE} --numeric-version)
export LD_PRELOAD="/opt/ghc/${GHCVER}/lib/ghc-${GHCVER}/rts/libffi.so.7"

cabal v1-configure \
      -O \
      --prefix=/usr/local \
      --docdir="\$datadir/doc/\$pkg" \
      --datasubdir="\$pkg/\$version" \
      -fFFI \
      -fGMP \
      -f-release \
      -f-freestanding

cabal v1-build

echo "==> Copying files"
cabal v1-copy \
      exe:idris \
      exe:idris-codegen-c \
      exe:idris-codegen-javascript \
      exe:idris-codegen-node \
      --destdir="${DIST}"

echo "==> Preparing to build package"

echo "==> Setting Permissions"
find "$DIST" -type d | xargs chmod 755

echo "==> Stripping"
strip "$DEST"/bin/idris*

echo "==> Compressing Man Page"
gzip -9 "$DEST"/share/man/man1/idris.1

echo "==> Moving Copyright across"
cp LICENSE "$COPYRIGHT"
echo "" >> "$COPYRIGHT"

echo "==> Setting CONTROL"
INSTALLED_SIZE=$(du -k -s "$DEST" | awk '{print $1}')
mkdir "$DIST"/DEBIAN
perl -pe "s/VERSION/$DEBVER/" linux/control.in \
  | perl -pe "s/ARCHITECTURE/$ARCHITECTURE/" \
  | perl -pe "s/INSTALLED_SIZE/$INSTALLED_SIZE/" \
  > "$DIST"/DEBIAN/control

echo "==> Creating Package"
fakeroot dpkg-deb --build "$DIST"
rm -rf "$DIST"

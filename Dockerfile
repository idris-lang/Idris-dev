FROM haskell:7
RUN cabal update
ADD . Idris-dev
WORKDIR Idris-dev
RUN make
WORKDIR ..

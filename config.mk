UNAME_INFO      := $(shell uname -a)

ifeq ($(filter , $(findstring MSYS, $(UNAME_INFO)) $(findstring MINGW, $(UNAME_INFO))),)
	ifeq (cc,$(CC))
		# In MSYS2, when using the mingw version of gcc, there is no cc -> gcc
		# symlink. We can't use ?= here because CC is set implicitly to cc.
		# Cross compiling users can set CC to their cross compiler.
		CC		=gcc
	endif
endif

RANLIB          ?=ranlib

CABAL           :=cabal
# IDRIS_ENABLE_STATS should not be set in final release
# Any flags defined here which alter the RTS API must also be added to src/IRTS/CodegenC.hs
CFLAGS          :=-O2 -Wall -DHAS_PTHREAD -DIDRIS_ENABLE_STATS $(CFLAGS)

# CABALFLAGS	:=
CABALFLAGS      += --enable-tests
## Disable building of Effects
#CABALFLAGS :=-f NoEffects $(CABALFLAGS)


ifneq (, $(findstring bsd, $(MACHINE)))
	GMP_INCLUDE_DIR      :=
else
	GMP_INCLUDE_DIR      :=-I/usr/local/include
endif

MACHINE         := $(shell $(CC) -dumpmachine)
ifneq (, $(findstring darwin, $(MACHINE)))
	OS      :=darwin
else ifneq (, $(findstring cygwin, $(MACHINE)))
	OS      :=windows
else ifneq (, $(findstring mingw, $(MACHINE)))
	OS      :=windows
else ifneq (, $(findstring windows, $(MACHINE)))
	OS      :=windows
else
	OS      :=unix
endif

ifeq ($(OS),darwin)
	SHLIB_SUFFIX    :=.dylib
else ifeq ($(OS),windows)
	SHLIB_SUFFIX    :=.DLL
else
	SHLIB_SUFFIX    :=.so
endif

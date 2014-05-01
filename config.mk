CC              ?=cc
CABAL           :=cabal
CFLAGS          :=-O2 -Wall $(CFLAGS)
#CABALFLAGS	:=
## Disable building of Effects
#CABALFLAGS :=-f NoEffects

ifneq (, $(findstring bsd, $(MACHINE)))
	GMP_INCLUDE_DIR      :=
else
	GMP_INCLUDE_DIR      :=-I/usr/local/include
endif

MACHINE         := $(shell $(CC) -dumpmachine)
ifneq (, $(findstring darwin, $(MACHINE)))
	OS      :=darwin
else
ifneq (, $(findstring cygwin, $(MACHINE)))
	OS      :=windows
else
ifneq (, $(findstring mingw, $(MACHINE)))
	OS      :=windows
else
	OS      :=unix
endif
endif
endif

ifeq ($(OS),darwin)
	SHLIB_SUFFIX    :=.dylib
else
ifeq ($(OS),windows)
	SHLIB_SUFFIX    :=.DLL
else
	SHLIB_SUFFIX    :=.so
endif
endif


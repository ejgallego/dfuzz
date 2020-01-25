# Program main file
MAIN=_build/install/default/bin/dfuzz

.PHONY: all clean

all::
	dune build

clean::
	dune clean




# Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

# Copying of this file is authorized to those who have read and agreed with the
# terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
# the Nqthm file "basis.lisp".

# This file is a Unix makefile for compiling Nqthm-1992, building a save image,
# and running some examples.  If this makefile does not work for you, you are
# advised not to use the `make' command to build Nqthm-1992, but instead to use
# the simple, manual instructions for Nqthm-1992 installation found in the
# `README' file.  This file is not necessary for building Nqthm-1992, but is
# provided as a convenience to users who wish to build Nqthm-1992 under Unix.
# To build an executable Nqthm-1992 image, invoke

#    % make LISP=xxx

# where xxx is the command for running your Common Lisp.  xxx defaults to
# `lisp'.  Currently, this save-image-build process works only for AKCL, Lucid,
# Allegro, and CMU Lisp.  For other Lisps, it will be necessary to edit files
# in the ./make/ subdirectory, in particular to add the appropriate command to
# save an image, in the file ./make/save.lisp.

# As a result of this make, a very small, executable file named `nqthm-1992'
# will be created on this directory.  This small file `points' to a large save
# file, which is also created by the make.  After the make has completed, the
# file `nqthm-1992' may optionally be copied with `cp' (not moved, with `mv')
# to a bin directory, e.g., with the command

#    % cp nqthm-1992 /usr/local/bin

# The choice of bin directory varies a lot from site to site, and the copying
# may even require special privileges, so we do not try to automate it.  There
# is absolutely no necessity of copying the above file anywhere -- putting it
# on a bin path does nothing besides give users the convenience of not having
# to precede `nqthm-1992' with some directory pathname to start it up.

# As a secondary result of the make command above, a very short little test
# will be run.  If a `looks ok' message gets printed at the end of the make,
# then the compilation and saving probably went ok.

# Once the first make has succeeded, a somewhat longer test can be invoked via

#    % make small-test

# which will run the file ./examples/basic/proveall.events, and if successful,
# create the files ./examples/proveall.proofs and ./examples/proveall.proved,
# and print out a message indicating that this small test worked.  You can
# monitor progress with `ls -lt examples/basic/proveall.proofs'.

# A large set of tests, generating about 150 megabytes of files, and possibly
# requiring cpu days to complete, can be invoked via

#    % make giant-test

# Before running this form, read the file `examples/README'.  You can monitor
# progress with the command `ls -lt examples/*/* | head'.

# The same set of tests can also be invoked via

#    % make giant-test-alt

# which differs from giant-test mainly in that each test is performed in a
# separate process.

# To build a TAGS file for use with Gnu Emacs, invoke

#   % make TAGS

# To remove files created by building under AKCL, Lucid, Allegro, and CMU
# Common Lisps, invoke

#    % make clean

# To remove files created by running the giant test, invoke

#    % make clean-giant-examples

# `make clean-giant-examples' should be executed before trying the giant
# examples afresh, if they have ever been tried before at your site; otherwise
# the make will resume where it was last aborted or failed.  This resumption
# feature is a real feature, not a bug:  running the giant tests takes so long
# that there is a palpable chance that something external like a power failure
# or a network crash will occur during execution, so resumption is a common
# necessity.

LISP=lisp

SOURCES=nqthm.lisp basis.lisp events.lisp genfact.lisp code-1-a.lisp \
  code-b-d.lisp code-e-m.lisp code-n-r.lisp code-s-z.lisp io.lisp ppr.lisp

all: nqthm-1992 make/tiny-test.lisp


make/compile-success: ${SOURCES}
	${LISP} < make/compile.lisp


nqthm-1992 saved_nqthm-1992: make/compile-success
# We pass the Lisp command name and the current directory to Lisp via the file
# nqthm-1992-tmp.  The file nqthm-1992-tmp will then be written by Lisp to
# contain an appropriate command with which to start up the saved image file.
	echo '"'${LISP}'" "'`pwd`'"' > nqthm-1992-tmp
	${LISP} < make/save.lisp
	mv nqthm-1992-tmp nqthm-1992
	chmod a+x nqthm-1992


make/tiny-test.lisp: nqthm-1992
	cd make; ../nqthm-1992 < tiny-tester.lisp


small-test: nqthm-1992
	cd examples/basic; ../../nqthm-1992 < ../../make/small-tester.lisp


giant-test: nqthm-1992
	cd examples; cat dir.lisp driver.lisp driver-sk.lisp | ../nqthm-1992


giant-test-alt: nqthm-1992
	cd examples; csh driver


TAGS: ${SOURCES}
	etags ${SOURCES}


clean:
	rm -f make/compile-success nqthm-1992 TAGS
	rm -f *.o *.c *.h *.data *.sbin *.lbin *.fasl *.sparcf \
	 make/tiny-test.* *saved_nqthm-1992 make/tmp.* *.log


clean-giant-examples:
	cd ./examples ; rm -f */*.lisp */*.lib */*.trans */*.err */*.log \
	  */*.proofs* */*.proved */*.STARTED */tmp.* */*.fail \
	  */*.o */*.fasl */*.lbin */*.sbin */*.sparcf \
	  */*.data */*.c */*.h */[0123456789]*

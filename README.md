# nqthm
nqthm - the original Boyer-Moore theorem prover, from 1992

This is the original Boyer-Moore theorem prover, developed from 1972 to 1992.
The sources for this program were last revised in 1992, and can be found here:

ftp://ftp.cs.utexas.edu/pub/boyer/nqthm/index.html

With very minor modifications, the program can be run under GNU "clisp".
This repository contains a version runnable today.

This program is primarily of historical interest as a milestone in 
logic-based artificial intelligence.  New work in this area should use
the newer ACL2 theorem prover, also by Boyer and Moore.

Current status: the prover will run using the LISP commands in the
README file below.  However, the UNIX makefiles are not yet working
on Linux.  Fetch all the files from this repository with "git", "cd"
to the directory "nqthm-1992", and follow the directions under "COMPILE"
and "LOAD".

Once you have the theorem prover loaded, try

    (load "examples/basic/proveall.events")
    
and watch the system prove the basic theorems of number theory
in a few seconds.  There are many other examples provided, but
"proveall" is a classic and a basis for most other theories.

John Nagle
August, 2016.


The original README file follows.

--------------------


This is the `README' file for the 1998 distribution of Nqthm-1992, the
Boyer-Moore prover.  This distribution of Nqthm corresponds to the second
edition of the book `A Computational Logic Handbook', Boyer and Moore,
Academic Press, 1998, ISBN 0-12-122955-6.  That book provides a comprehensive
user's manual for this distribution, including installation instructions, a
definition of the logic for which Nqthm-1992 is a theorem prover,
documentation of all the user commands, and short introductions to the
hundreds of sample input files, which cover many areas of computing and
mathematics.


                              LICENSES INVOLVED

It is the basic intention of those who have contributed to this distribution
of Nqthm that the entire distribution may be freely copied and freely used.
However, the evolution of the concept of `free software' has resulted in the
creation of certain licenses that spell out what `free' means, and those who
need or wish to know these fine details should continue reading this section
on licenses.

All of the files in this Nqthm distribution whose copyright is held by any
subset of {Boyer, Moore, Computational-Logic-Inc} is licensed to the public
under the terms of the Gnu General Public License, a copy of which may be
found in the file `gnu-general-public-license.text'.  In particular, the Gnu
license covers all of the Common Lisp sources for Nqthm.  The Gnu licensing
of material in this Nqthm distribution is in addition to, and in no way in
conflict with, permissions granted in the various files of this distribution
for use under the Nqthm Public Software License, under public domain
declarations, or under other licenses.  However, please note that in this
distribution, we also distribute by permission some example files that are
the work of others, and this licensing under the Gnu General Public License
does not apply to those files.  See individual files under the `events'
directory for specific licensing information.  Similarly, the documentation
directory `doc' contains some information that is copyright by Academic Press
and is distributed under the terms of a letter from Academic Press that may
be found on that directory.

In addition, copying and use of Nqthm-1992 is authorized under the terms
stated in the Nqthm-1992 General Public Software License, which may be found
at the beginning of the Nqthm file `basis.lisp' and also in the files
`nqthm-public-software-license.doc' and `nqthm-public-software-license.ps'.

The user may choose to operate under either of these `free software'
licenses.


			     OBTAINING NQTHM-1992

It is best to obtain Nqthm-1992 via the Internet as the URL

   ftp://ftp.cs.utexas.edu/pub/boyer/nqthm/nqthm-2nd-edition.tar.Z

If for some reason you cannot make use of that single file, e.g., because you
cannot uncompress a .Z file or untar a .tar file, then you may obtain obtain
Nqthm-1992 by ftp a file at a time.  Connect to ftp.cs.utexas.edu with the
login name `anonymous' and your email address as the password.  Ftp all of
the files on the /pub/boyer/nqthm/nqthm-1992/ directory and its sub- and
subsub-directories, and then go to the COMPILE instruction of this README
file.  Because there are over a hundred files and over a dozen
subdirectories, making sure that you have gotten all of the files in this way
can be tedious!


				  UNCOMPRESS

To uncompress the file nqthm-2nd-edition.tar.Z, do

   % uncompress nqthm-2nd-edition.tar.Z

				     UNTAR

To untar the file nqthm-2nd-edition.tar, do

   % tar xvf nqthm-2nd-edition.tar

This `tar' command will create a subdirectory named `nqthm-1992', which
contains the sources and examples.  This will take up an additional 23
megabytes.  You may now delete the file nqthm-2nd-edition.tar to save space.


				    COMPILE

To compile Nqthm, execute the following commands:

    % cd nqthm-1992
    % lisp  ; Or whatever commands starts your Common Lisp.
    > (load "nqthm.lisp")
    > (proclaim '(optimize (speed 3) (safety 0) (space 0)))
    > (in-package "USER")
    > (compile-nqthm) ; takes a few minutes on a contemporary workstation
    > (bye)  ; however you get out, if you can.

If you encounter problems at this stage, please consult the installation
chapter in the user's manual, which describes many sorts of environmental
problems you may be encountering and some work arounds.

To use Nqthm under Lispworks 3.2.0, execute the following immediately after
loading "nqthm.lisp" to workaround two problems with Lispworks.

   (progn (shadow 'comment)
          (setf (svref ccl::*funny-symbol-char-table* (char-code #\.)) t))


				     LOAD

Having compiled Nqthm, one may now load it as follows:

    % lisp
    > (load "nqthm.lisp")
    > (in-package "USER")
    > (load-nqthm)
    > ; Nqthm is now ready to use.  Here is a simple test.
    > (boot-strap nqthm)
    > (assoc-of-app)

The last form should result in a few pages of terminal output proving the
associativity of the function `app'.  If it does, you (probably) have a
working Nqthm and can now try any of the commands described in the reference
guide chapter of the documentation.

You may find it convenient to save a binary image of Nqthm-1992.  This may be
done after the (load-nqthm) command.  The saving of an image is very
dependent upon the Lisp implementation being used, and may require many
megabytes of space.  Repeatedly loading the compiled code whenever one wants
to use Nqthm-1992 is sufficiently fast that one can comfortably get by
without an image.  But having a saved image is slightly more convenient and
may provide an economy under certain operating systems.

MCL Note: To use Nqthm under MCL 2.0, start by loading the file
mcl-nqthm-startup.lisp from the EVAL window.

Lispworks Note: To use Nqthm under Lispworks 3.2.0, execute the following
immediately after loading "nqthm.lisp" to work around two problems.

   (progn (shadow 'comment)
          (setf (svref ccl::*funny-symbol-char-table* (char-code #\.)) t))



	     FOR UNIX:  MAKING A SAVE IMAGE and TESTING VIA `make'

Nqthm-1992 is not tied to any particular operating system or Common Lisp
implementation.  However the creation of an executable Nqthm-1992 save image
and the running of certain tests has been automated for Unix and for certain
Lisp implementations.  Instead of following the preceding simple compiling
and loading commands, one can instead merely invoke `make' under some
versions of Unix and with some Lisps to do the compilation, save an
executable Lisp image named `nqthm-1992', and then test that image.  Issue
the single command

   make LISP=xxx

where `xxx' is the command to run your Lisp.  `lisp' is used for `xxx' by
default.  This `make' works only for GCL, Allegro, CMU, Lispworks, and Lucid
Common Lisps.  And it may only work on Sun Sparcs, for all we know about the
portability of Unix `makefile' code.  See the file makefile for further
details.  If this `make' command does not work for you, please use the simple
installation commands above.

If the foregoing `make' command succeeds, then a longer test of the file
examples/basic/proveall.events can be run with the command

   make small-test

If that succeeds, and if you can afford to consume perhaps several days of
cpu time and over a hundred megabytes of disk space, try

   make giant-test

				   PROBLEMS

The installation guide chapter in the user's manual describes a number of
potential installation problems and how to work around them.


				   EXAMPLES

See the file examples/README for details on how to run Nqthm-1992 on many
examples.  These examples briefly are described in Chapter 14 of the user's
manual.


				    IMAGES

For information on executable binary images of Nqthm-1992 for a variety of
computers, please fetch URL

  ftp://ftp.cs.utexas.edu/pub/boyer/nqthm/nqthm-1992-images/README


                                 MAILING LIST

There is a mailing list for discussion of Nqthm, nqthm-users@cs.utexas.edu.  To
join, send an email message to nqthm-users-request@cs.utexas.edu.  The archive
of this mailing group may be found at

  ftp://ftp.cs.utexas.edu/pub/boyer/nqthm/nqthm-users-mail-archive


                      COMPUTATIONAL LOGIC, INC., R.I.P.

On August 1, 1997, the corporation Computational Logic, Inc. closed its
doors.  Although a web site for cli.com will continue to exist for a while,
references in this Nqthm distribution to that corporation's addresses, both
physical and Internet, are now obsolete.  Much of the information that was
available from ftp.cli.com is now available via
ftp://dirleton.csres.utexas.edu and ftp://ftp.cs.utexas.edu/pub/boyer/.
Questions about Nqthm-related matters should now be addressed to Boyer and
Moore at the addresses below.


Bob Boyer                                J Moore
boyer@cs.utexas.edu                      moore@cs.utexas.edu
http://www.cs.utexas.edu/users/boyer     http://www.cs.utexas.edu/users/moore

August, 1997


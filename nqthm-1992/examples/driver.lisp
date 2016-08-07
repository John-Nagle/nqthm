#|

This file `driver.lisp' is for running the standard Nqthm-1992 examples.

Warning.  Proof-checking this entire set of examples is a fairly large data
processing crunch by the standards of 1992 workstations.  For example, if we
run this test on a Sparc 2 under AKCL, it takes about three days of cpu time.
Roughly 200 megabytes of files are created.  Under some Lisps a process with
a virtual memory size of over 87 megabytes may be created.  So your machine and
your Lisp may, therefore, perhaps be pressed to a unusual extent with respect
to the utilization of virtual memory, disk space, stack size, heap size, etc.
Further information on resource issues may be found below.  If you have trouble
replaying these examples, please read about these potential resource problems.

The various example files provided with Nqthm-1992 can each be run one at a
time by invoking, say, (PROVE-FILE-OUT "ex") for each of the example files,
say, `ex.events', in the order suggested below.  But there are so many of these
example files that we have organized them into subdirectories and coded this
driver file to automate the process.  The code in this file, `driver.lisp',
does little more than support the necessary switching between subdirectories,
before invoking PROVE-FILE-OUT.  As indicated below, this switching is slightly
operating system sensitive, unlike the rest of Nqthm-1992, which is one reason
that we have separated the code for this driver from the code for Nqthm-1992
itself.

Here are the instructions for running the Nqthm-1992 examples.

0. Cleanup.  If any previous attempts have been made to run these examples at
your site, consider deleting all files of the form *.proved in all the
subdirectories of the Nqthm-1992 `examples' directory.  If a file `ex.proved'
exists on a subdirectory of the `examples' directory, that is taken as a sign,
by this driver, that a file `ex.events' on the same subdirectory has been
successfully checked, and so running `ex.events' will be skipped.  For example,
if you are running on a Unix, and if the `examples' subdirectory of Nqthm-1992
at your site happens to be named "/usr/smith/nqthm-1992/examples/", then
consider doing something like:

 cd /usr/smith/nqthm-1992/examples/
 rm examples/*/*.proved

1. Compile and load Nqthm-1992.  To briefly review this matter, which is
covered in further detail in the installation guide, we recall that the
instructions are, when `connected' to the directory of the Nqthm sources, and
after starting your Common Lisp:

 a.  (LOAD "nqthm.lisp")
 b.  (IN-PACKAGE "USER")
 c.  (COMPILE-NQTHM)              ; unnecessary if already compiled, of course.
 d.  (LOAD-NQTHM)

2. Directory identification.  Set the variable *NQTHM-EXAMPLES-DIR* to a string
(not a pathname) that names the `examples' directory for Nqthm-1992 at your
site.  For example, on a Unix system, you might execute something like:

 (DEFPARAMETER *NQTHM-EXAMPLES-DIR* "/home/smith/nqthm-1992/examples/")

It is important that the last character of the value of *NQTHM-EXAMPLES-DIR* be
the character that separates components of a pathname under your operating
system.  This file `driver.lisp' depends on it.  On a Unix, for example, the
character will be "/".  On a Macintosh it will be ":".  On a Symbolics it will
be ">".  If your operating system does not have such a simple, single-character
convention for separating pathname components, this driver will not work for
you.  In that case, invent some other mechanism to invoke PROVE-FILE-OUT on
each of the example files, in the order suggested below.

3. Running.  LOAD this file.  For example, evaluate something like:

 (LOAD "/home/smith/nqthm-1992/examples/driver.lisp")

This will result in the evaluation of all of the examples distributed with
Nqthm-1992, excepting the few that use DEFN-SK, to run which see the file
driver-sk.lisp.

That's all there is to do.  But the computation takes quite a while!


Hint.  Because running this file may take such a long time, it may be a good
idea to run it in the background, and `nicely'.  Assume, for the moment, that
we are running on a Unix, that the Unix command `nqthm-1992' starts up a
process containing a loaded Nqthm-1992, and that we are connected to the
`examples' directory.  Then one way to run this driver would be to put a
command, such as the DEFPARAMETER above, for setting the directory variable, in
a file, say `dir.lisp', and then to invoke, at the Unix shell level, the
command:

  cat dir.lisp driver.lisp | nice nqthm-1992 >& driver.log  & 

Hint.  If a crash occurs when running this examples suite, then running this
file again, exactly as before, following steps 1, 2, and 3 but skipping the
cleanup step 0, will restart with the example file whose processing was
interrupted.  We generate an `ex.proved' file after successfully checking
`ex.events', and processing of `ex.events' will be skipped if `ex.proved'
already exists.  Such a restart may be an appropriate way to deal with such
external problems as power failure.  Some Lisps may crash during an attempt to
process all these examples at once, so repeatedly restarting, by running this
file, after each crash, is one approach to running all these examples.

Resource warning continued.  Before reporting to us a problem you may have
running these examples, please endeavor to check that the problem is not merely
one of many, many possible sorts of resource allocation or memory management
problems at your site.  Because of the many resource problems that may be
encountered, and because the symptoms of resource errors are often very
obscure, checking this set of examples can be tricky until you solve all the
resource problems.

If you run into problems, but you are not an experienced Lisp programmer who is
very familiar with both your Lisp and your operating system, please consult
locally with someone who is, if possible, before contacting us.  Diagnosing and
solving resource problems remotely seems vastly more difficult than treating
such problems with direct access to the site where the problem exists.

Here are some suggestions for how to begin to diagnose resource problems.  A
good Lisp function to use to find out about Lisp space usage is `room'.  Good
Unix commands to use to help check for running out of disk space are "df",
"du", and "pwd".  A good Unix command to use to help check for running out of
virtual memory is "pstat -s".  A good Unix command to use to check process size
is "ps -uax".  The latter two commands have to be executed while the Nqthm
process is running, of course, not after it has crashed.

Because running these examples takes so much time, we suggest that you compile
Nqthm optimizing for speed, e.g., (proclaim (quote (optimize (speed 3) (safety
0) (space 0)))).  This is the default setting for AKCL.  For Allegro, we also
suggest (debug 0).  For Lucid we also suggest (compilation-speed 0).  For CMU
Lisp, we suggest 0 settings for both debug and compilation-speed.  For CMU
Lisp, we suggest a 1 setting for SPACE to avoid a compiler bug in version
16e.

Experiences.  Here is a summary of our experiences running these examples, as
of November 1992, in several different Common Lisp implementations.

AKCL.  We have run this entire example set under Austin Kyoto Common Lisp 1.615
on a Sparc 2, in a single run of this driver file.

CMU.  We have run this entire example set under CMU Common Lisp 16(e) on a
Sparc 2.  Under CMU verison 16e, COMPILE-UNCOMPILED-DEFNS is a no-op because
COMPILED-FUNCTION-P returns T on interpreted functions.  So we start by setting
COMPILED-FUNCTION-P-FN to #'(LAMBDA (X) (NOT (EVAL:INTERPRETED-FUNCTION-P X))).

Allegro.  We have run this entire example set under Allegro Common Lisp 4.1 on
a Sparc 2.  To check one file required first executing the form
(set-pprint-dispatch '(cons (member if*)) nil) to `work around' a bug in the
Common Lisp function PRINT that causes '(if* .  t) to misprint.  We built
Allegro with the heap doubled to 120mb from 60mb and the amount of oldspace
free in the image from 512k to 1mb.

Lucid.  We have run this entire example set under Lucid Common Lisp,
Development Environment, Version 4.0.0, on a Sparc 2.  Before starting the run,
we executed (change-memory-management :growth-limit 2000) to get more heap.

MCL.  Under Macintosh Common Lisp 2.0, we have run all but the flatau events.
Experience with MCL 2.0, even on a powerbook, was extremely satisfactory, once
we found out (1) how to stop the Powerbook from `resting' or `cycling' by
option-clicking on the word `minutes' in the `Portable' item of the `Control
Panels' item of the Apple menu, which on later versions of the Powerbook is
under the `PowerBook' item of the control panels, under the menu obtained by
clicking on the Options button with the Option keep depressed, to `Don't allow
cycling' and (2) how to grant MCL permission to expand to much more than 3mb by
editing the boxed, numeric field exposed by the Get Info item under the File
menu, having clicked on the MCL 2.0 Lisp executable.

Symbolics.  Under Genera 7 on a Symbolics 3640, we have run the
`proveall.events' file in the `basic' subdirectory.

|#

(IN-PACKAGE "USER")

(FORMAT *STANDARD-OUTPUT* "~%Loading driver.lisp.")

(OR (AND (BOUNDP '*NQTHM-EXAMPLES-DIR*)
         (STRINGP *NQTHM-EXAMPLES-DIR*))
    (ERROR "~% Before running this file, please set *NQTHM-EXAMPLES-DIR* to a ~
            string ~% that names the path to the Nqthm-1992 examples ~
            directory at your~% site.  For example, on a Unix, one might ~
            execute something like~%~%    (DEFPARAMETER *NQTHM-EXAMPLES-DIR* ~
            \"/usr/smith/nqthm-1992/examples/\")~%~% It is important that the ~
            string end in the character that separates ~% subdirectory ~
            components, e.g., / on Unix, > on Symbolics, and : on Macintosh.~%"
           ))

(FORMAT *STANDARD-OUTPUT*
        "~%We will assume that the Nqthm-1992 examples directory at this site ~
         is: ~%~%   ~a~%~%We will also assume that the single character ~a is ~
         used to separate~%subdirectory components under this operating ~
         system.~%~%Starting the Nqthm-1992 examples "
        *NQTHM-EXAMPLES-DIR*
        (CHAR *NQTHM-EXAMPLES-DIR*
                       (1- (LENGTH *NQTHM-EXAMPLES-DIR*))))

(PRINT-IDATE (IDATE) *STANDARD-OUTPUT*)

(FORMAT *STANDARD-OUTPUT* ".")

(DEFUN DRIVER-PROVE-FILE-OUT (DIR ROOT)

; DRIVER-PROVE-FILE-OUT runs PROVE-FILE-OUT on ROOT.events after `connecting'
; to subdirectory DIR, by rebinding *DEFAULT-NQTHM-PATH*.  This `connecting'
; process involves operating system dependent code for dealing with the notion
; of subdirectory.  The dependence is that we assume that that a single
; character is used, in a string for a pathname, to separate subdirectory
; components.  e.g., / on Unix, > on Symbolics, and : on Macintosh.  We rely
; upon the user to inform us, implicitly, what that character is by putting it
; at the end of the value of *NQTHM-EXAMPLES-DIR*.

  (LET ((*DEFAULT-NQTHM-PATH*
         (FORMAT NIL "~A~A~A"
                 *NQTHM-EXAMPLES-DIR*
                 DIR

; Yuk.  Here we strip off the last character to use again:

                 (CHAR *NQTHM-EXAMPLES-DIR*
                       (1- (LENGTH *NQTHM-EXAMPLES-DIR*)))))
        VALUE)
    (COND ((PROBE-FILE (EXTEND-FILE-NAME ROOT FILE-EXTENSION-PROVED))
           (FORMAT *STANDARD-OUTPUT*
                   "~%Skipping ~a.~a because the file ~a.~a exists."
                   ROOT FILE-EXTENSION-EVENTS
                   ROOT FILE-EXTENSION-PROVED)
           "Skipped")
          (T (FORMAT *STANDARD-OUTPUT*
                     "~%Trying ~a.~a." ROOT FILE-EXTENSION-EVENTS)
             (FORCE-OUTPUT *STANDARD-OUTPUT*)
             (COND ((SETQ VALUE (PROVE-FILE-OUT ROOT))
                    (FORMAT *STANDARD-OUTPUT* "~%Successfully finished ~a.~a."
                            ROOT FILE-EXTENSION-EVENTS))
                   (T (ERROR "~%Failed on ~a.~a."
                             ROOT FILE-EXTENSION-EVENTS)))
             (FORCE-OUTPUT *STANDARD-OUTPUT*)
             VALUE))))
(TIME (PROGN
(DRIVER-PROVE-FILE-OUT "basic" "proveall")
(DRIVER-PROVE-FILE-OUT "basic" "fortran")
(DRIVER-PROVE-FILE-OUT "basic" "unsolv")
(DRIVER-PROVE-FILE-OUT "basic" "binomial")
(DRIVER-PROVE-FILE-OUT "basic" "controller")
(DRIVER-PROVE-FILE-OUT "basic" "peter")
(DRIVER-PROVE-FILE-OUT "basic" "pr")
(DRIVER-PROVE-FILE-OUT "basic" "quant")
(DRIVER-PROVE-FILE-OUT "basic" "rsa")
(DRIVER-PROVE-FILE-OUT "basic" "wilson")
(DRIVER-PROVE-FILE-OUT "basic" "gauss")
(DRIVER-PROVE-FILE-OUT "basic" "new-gauss")
(DRIVER-PROVE-FILE-OUT "basic" "tmi")
(DRIVER-PROVE-FILE-OUT "basic" "ztak")
(DRIVER-PROVE-FILE-OUT "basic" "alternating")
(DRIVER-PROVE-FILE-OUT "basic" "tic-tac-toe")
(DRIVER-PROVE-FILE-OUT "basic" "small-machine")
(DRIVER-PROVE-FILE-OUT "basic" "fs-examples")
(DRIVER-PROVE-FILE-OUT "basic" "fibsums")
(DRIVER-PROVE-FILE-OUT "basic" "async18")
(DRIVER-PROVE-FILE-OUT "basic" "parser")
(DRIVER-PROVE-FILE-OUT "bevier" "kit")
(DRIVER-PROVE-FILE-OUT "bronstein" "mlp")
(DRIVER-PROVE-FILE-OUT "bronstein" "corr_CIXA00")
(DRIVER-PROVE-FILE-OUT "bronstein" "corr_CSXA00")
(DRIVER-PROVE-FILE-OUT "bronstein" "acc_CSXA00")
(DRIVER-PROVE-FILE-OUT "bronstein" "macc")
(DRIVER-PROVE-FILE-OUT "bronstein" "prod0_CSXA00")
(DRIVER-PROVE-FILE-OUT "bronstein" "funacc")
(DRIVER-PROVE-FILE-OUT "bronstein" "theta")
(DRIVER-PROVE-FILE-OUT "bronstein" "corrSL")
(DRIVER-PROVE-FILE-OUT "bronstein" "counter")
(DRIVER-PROVE-FILE-OUT "bronstein" "counterR")
(DRIVER-PROVE-FILE-OUT "bronstein" "bcd")
(DRIVER-PROVE-FILE-OUT "bronstein" "serial")
(DRIVER-PROVE-FILE-OUT "bronstein" "sadder")
(DRIVER-PROVE-FILE-OUT "bronstein" "bibo_exp")
(DRIVER-PROVE-FILE-OUT "bronstein" "bcdS")
(DRIVER-PROVE-FILE-OUT "bronstein" "bcdSbi")
(DRIVER-PROVE-FILE-OUT "bronstein" "handrec")
(DRIVER-PROVE-FILE-OUT "bronstein" "multadd")
(DRIVER-PROVE-FILE-OUT "bronstein" "pplinc3")
(DRIVER-PROVE-FILE-OUT "bronstein" "pplfun3")
(DRIVER-PROVE-FILE-OUT "bronstein" "pplfadd")
(DRIVER-PROVE-FILE-OUT "bronstein" "ppltcpu")
(DRIVER-PROVE-FILE-OUT "bronstein" "ppltcpuM")
(DRIVER-PROVE-FILE-OUT "bronstein" "countstut")
(DRIVER-PROVE-FILE-OUT "bronstein" "srccpu")
(DRIVER-PROVE-FILE-OUT "fm9001-piton" "fm9001-replay")
(DRIVER-PROVE-FILE-OUT "fm9001-piton" "piton")
(DRIVER-PROVE-FILE-OUT "fm9001-piton" "big-add")
(DRIVER-PROVE-FILE-OUT "fm9001-piton" "nim-piton")
(DRIVER-PROVE-FILE-OUT "fortran-vcg" "fortran")
(DRIVER-PROVE-FILE-OUT "fortran-vcg" "fsrch")
(DRIVER-PROVE-FILE-OUT "fortran-vcg" "isqrt")
(DRIVER-PROVE-FILE-OUT "fortran-vcg" "mjrty")
(DRIVER-PROVE-FILE-OUT "cowles" "intro-eg")
(DRIVER-PROVE-FILE-OUT "cowles" "shell")
(DRIVER-PROVE-FILE-OUT "hunt" "fm8501")
(DRIVER-PROVE-FILE-OUT "kaufmann" "expr-compiler")
(DRIVER-PROVE-FILE-OUT "kaufmann" "foldr")
(DRIVER-PROVE-FILE-OUT "kaufmann" "generalize-all")
(DRIVER-PROVE-FILE-OUT "kaufmann" "koenig")
(DRIVER-PROVE-FILE-OUT "kaufmann" "locking")
(DRIVER-PROVE-FILE-OUT "kaufmann" "mergesort-demo")
(DRIVER-PROVE-FILE-OUT "kaufmann" "note-100")
(DRIVER-PROVE-FILE-OUT "kaufmann" "partial")
(DRIVER-PROVE-FILE-OUT "kaufmann" "permutationp-subbagp")
(DRIVER-PROVE-FILE-OUT "kaufmann" "ramsey")
(DRIVER-PROVE-FILE-OUT "kaufmann" "rotate")
(DRIVER-PROVE-FILE-OUT "kaufmann" "rpn")
(DRIVER-PROVE-FILE-OUT "kaufmann" "shuffle")
(DRIVER-PROVE-FILE-OUT "kunen" "ack")
(DRIVER-PROVE-FILE-OUT "kunen" "new-prime")
(DRIVER-PROVE-FILE-OUT "kunen" "paris-harrington")
(DRIVER-PROVE-FILE-OUT "kunen" "induct")
(DRIVER-PROVE-FILE-OUT "numbers" "bags")
(DRIVER-PROVE-FILE-OUT "numbers" "naturals")
(DRIVER-PROVE-FILE-OUT "numbers" "arithmetic-geometric-mean")
(DRIVER-PROVE-FILE-OUT "numbers" "integers")
(DRIVER-PROVE-FILE-OUT "numbers" "extras")
(DRIVER-PROVE-FILE-OUT "numbers" "fib2")
(DRIVER-PROVE-FILE-OUT "numbers" "nim")
(DRIVER-PROVE-FILE-OUT "numbers" "scheduler")
(DRIVER-PROVE-FILE-OUT "numbers" "tossing")
(DRIVER-PROVE-FILE-OUT "shankar" "church-rosser")
(DRIVER-PROVE-FILE-OUT "shankar" "goedel")
(DRIVER-PROVE-FILE-OUT "shankar" "tautology")
(DRIVER-PROVE-FILE-OUT "subramanian" "mutilated-checkerboard")
(DRIVER-PROVE-FILE-OUT "talcott" "mutex-atomic")
(DRIVER-PROVE-FILE-OUT "talcott" "mutex-molecular")
(DRIVER-PROVE-FILE-OUT "yu" "mc20-0")
(DRIVER-PROVE-FILE-OUT "yu" "mc20-1")
(DRIVER-PROVE-FILE-OUT "yu" "mc20-2")
(DRIVER-PROVE-FILE-OUT "yu" "amax")
(DRIVER-PROVE-FILE-OUT "yu" "asm")
(DRIVER-PROVE-FILE-OUT "yu" "bsearch")
(DRIVER-PROVE-FILE-OUT "yu" "switch")
(DRIVER-PROVE-FILE-OUT "yu" "fixnum-gcd")
(DRIVER-PROVE-FILE-OUT "yu" "fmax")
(DRIVER-PROVE-FILE-OUT "yu" "gcd")
(DRIVER-PROVE-FILE-OUT "yu" "gcd3")
(DRIVER-PROVE-FILE-OUT "yu" "isqrt")
(DRIVER-PROVE-FILE-OUT "yu" "isqrt-ada")
(DRIVER-PROVE-FILE-OUT "yu" "log2")
(DRIVER-PROVE-FILE-OUT "yu" "memchr")
(DRIVER-PROVE-FILE-OUT "yu" "memcmp")
(DRIVER-PROVE-FILE-OUT "yu" "memmove")
(DRIVER-PROVE-FILE-OUT "yu" "memcpy")
(DRIVER-PROVE-FILE-OUT "yu" "memset")
(DRIVER-PROVE-FILE-OUT "yu" "mjrty")
(DRIVER-PROVE-FILE-OUT "yu" "strcat")
(DRIVER-PROVE-FILE-OUT "yu" "strchr")
(DRIVER-PROVE-FILE-OUT "yu" "strcmp")
(DRIVER-PROVE-FILE-OUT "yu" "strcoll")
(DRIVER-PROVE-FILE-OUT "yu" "strcpy")
(DRIVER-PROVE-FILE-OUT "yu" "strcspn")
(DRIVER-PROVE-FILE-OUT "yu" "strpbrk")
(DRIVER-PROVE-FILE-OUT "yu" "strrchr")
(DRIVER-PROVE-FILE-OUT "yu" "strlen")
(DRIVER-PROVE-FILE-OUT "yu" "strncmp")
(DRIVER-PROVE-FILE-OUT "yu" "strstr")
(DRIVER-PROVE-FILE-OUT "yu" "strncat")
(DRIVER-PROVE-FILE-OUT "yu" "strncpy")
(DRIVER-PROVE-FILE-OUT "yu" "strspn")
(DRIVER-PROVE-FILE-OUT "yu" "strtok")
(DRIVER-PROVE-FILE-OUT "yu" "strxfrm")
(DRIVER-PROVE-FILE-OUT "yu" "zero")
(DRIVER-PROVE-FILE-OUT "flatau" "app-c-d-e")
(DRIVER-PROVE-FILE-OUT "flatau" "app-f")
(FORMAT T "~%~%All Nqthm-1992 tests completed successfully.~%~%")
))
(FORMAT *STANDARD-OUTPUT* "~%Finished loading driver.lisp.")

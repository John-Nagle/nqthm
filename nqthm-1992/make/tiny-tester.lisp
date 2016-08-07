#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".

|#

 #+AKCL
 (COND
  ((< SI::*LISP-MAXPAGES* 32768)
   (FORMAT *STANDARD-OUTPUT* 
           "

 WARNING: We suspect, after examing the AKCL variable SI::*LISP-MAXPAGES*,
 that you may not have enough space to complete all of the examples, especially
 those in the examples directory `fm9001-piton'.  Consider rebuilding ACKL with
 more heap, by rebuilding after redefining MAXPAGE thus in the file h/bsd.h:

  #define MAXPAGE (16384*2)

 This warning may be ignored unless you plan to try some of the very largest
 examples.
  ")))

(SETQ *THM-SUPPRESS-DISCLAIMER-FLG* T)

(BOOT-STRAP)

(ASSOC-OF-APP)

(MAKE-LIB "tiny-test" T)

(COND ((NOTE-LIB "tiny-test" T)
       (PRINC "

=============================================================================
|                                                                           |
| It looks like compilation, saving, and very simple testing of Nqthm-1992  |
| worked OK.                                                                |
|                                                                           |
| Consider copying the executable file `nqthm-1992' to a bin directory.     |
|                                                                           |
=============================================================================

") "Success."))

; Some Lisps quit when reading end of file, some don't.
 #+CMU
 (QUIT)
 #+Allegro
 (EXIT)

#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".

|#

; This file is not necessary for building Nqthm-1992, but is provided as a mere
; convenience to users who wish to build Nqthm-1992 under Unix.  See the file
; ../makefile.  Unlike the sources for Nqthm-1992, this file contains Common
; Lisp implementation dependent commands for fixing bugs and improving
; performance.

(PROGN

 #-(OR AKCL ALLEGRO CMU LUCID)
 (ERROR 
  "To build a saved image for Nqthm-1992 in this Lisp, it will be
necessary to edit the file ./make/save.lisp so as to indicate the
save command to be used.")

; Optimize for speed.  We skirt a bug in the CMU Lisp 16(e) compiler by using
; SPACE = 1.

 (PROCLAIM (QUOTE (OPTIMIZE (SAFETY 0)
                            (SPACE #+CMU 1 #-CMU 0)
                            (SPEED 3)
                            #+Allegro (DEBUG 0)
                            #+(OR CMU Lucid) (COMPILATION-SPEED 0)
                            #+CMU (EXTENSIONS:INHIBIT-WARNINGS 3))))


;  Allow for lots of growth.

 #+Lucid
 (CHANGE-MEMORY-MANAGEMENT :GROWTH-LIMIT 2000)

 #+AKCL
 (SETQ SI::*MULTIPLY-STACKS* 4)

 #+AKCL
 (COND
  ((< SI::*LISP-MAXPAGES* 32768)
   (FORMAT *STANDARD-OUTPUT* 
           "

 WARNING: We suspect, after examing the AKCL variable SI::*LISP-MAXPAGES*,
 that you may not have enough space to complete all of the examples.  
 Consider rebuilding ACKL with more heap, by rebuilding after redefining
 MAXPAGE thus in the file h/bsd.h:

  #define MAXPAGE (16384*2)

 This warning may be ignored unless you plan to try some of the very largest
 examples.
  ")))

; Silence the GC.

 #+Lucid
 (SETQ *GC-SILENCE* T)
 #+CMU
 (SETQ *GC-VERBOSE* NIL)

; Suppress redefinition warnings.

 #+Lucid
 (PROGN
  (SETQ *STYLE-WARNINGS* NIL)
  (SETQ *REDEFINITION-ACTION* NIL)
  (SETQ *RECORD-SOURCE-FILES* NIL)
  (SETQ *WARN-IF-NO-IN-PACKAGE* NIL))

 #+Allegro
 (SETQ *RECORD-SOURCE-FILE-INFO* NIL)

 #+AKCL
 (PROGN
  (SETQ COMPILER:*COMPILE-VERBOSE* NIL)
  (SETQ COMPILER:*SUPPRESS-COMPILER-NOTES* T))

; Work around a misfeature in CMU Lisp.  At least in version 16e of
; CMU Lisp, and probably subsequent versions, COMPILE-UNCOMPILED-DEFNS
; is a no-op because COMPILED-FUNCTION-P returns T on interpreted
; functions.  So we recommend the following setting of
; COMPILED-FUNCTION-P-FN in CMU Lisp, at the suggestion of
; Rob_MacLachlan@LISP-PMAX1.SLISP.CS.CMU.EDU, one of the CMU Lisp
; implementors.

 #+CMU
 (DEFPARAMETER COMPILED-FUNCTION-P-FN
   (FUNCTION (LAMBDA (X) (NOT (EVAL:INTERPRETED-FUNCTION-P X)))))

; Work around a bug in Allegro.  This is a work around for the '(if* . t)
; PRINT bug in Allegro CL 4.1 suggested by duane@Franz.COM, concering
; bug report spr6115:
 #+Allegro
 (SET-PPRINT-DISPATCH '(CONS (MEMBER IF*)) NIL)

; Prevent some false assumptions about fixnums in Allegro.  We use
; this obscure EVAL/READ-FROM-STRING approach because the AKCL reader
; barfs on #+(VERSION>= ...).
 #+Allegro
 (EVAL (READ-FROM-STRING "
  (SETQ COMPILER::DECLARED-FIXNUMS-REMAIN-FIXNUMS-SWITCH
        #'(LAMBDA (X Y Z #+(VERSION>= 4 1) D) NIL)) "))

 #+AKCL
 (PROGN

; The next three forms are a kludge that causes AKCL to rebind *READTABLE* to
; something sensible during a user interrupt if it is bound to NQTHM-READTABLE.
; The source of the problem is that NQTHM-READTABLE causes an error when
; reading a colon, but in a break it is common to want to type keywords.

  (PROCLAIM '(SPECIAL SI::ARGLIST NQTHM-READTABLE))

  (DEFPARAMETER INIT-NQTHM-READTABLE (COPY-READTABLE NIL))

  (LET ((V (SYMBOL-FUNCTION 'SI::BREAK-LEVEL)))
    (SETF
     (SYMBOL-FUNCTION 'SI::BREAK-LEVEL)
     (FUNCTION
      (LAMBDA (&REST RST)
              (COND ((AND (BOUNDP 'NQTHM-READTABLE)
                          (EQ *READTABLE* NQTHM-READTABLE))
                     (FORMAT
                      *TERMINAL-IO*
                      "~%Binding *readtable* to INIT-NQTHM-READTABLE.~%")
                     (LET ((*READTABLE* INIT-NQTHM-READTABLE))
                       (APPLY V RST)))
                    (T (APPLY V RST))))))))

; Start the loading.

 (LOAD "nqthm.lisp")

 )

(IN-PACKAGE "USER")

(PROGN

 (LOAD-NQTHM)

; We now make a saved image.  The command to use varies from Lisp to Lisp, and
; for some Lisps, the image is so large that saving an image is neither cost
; nor time effective.  If an image is not saved, then after compilation,
; Nqthm-1992 can be brought up merely by invoking (LOAD "nqthm.lisp")
; (IN-PACKAGE "USER") (LOAD-NQTHM).

 (LET ((*THM-SUPPRESS-DISCLAIMER-FLG* T))
   (BOOT-STRAP NQTHM))

 (COMPILE-UNCOMPILED-DEFNS "make/tmp")

; Form to print at startup.

 (LET* ((X (READ-FILE "nqthm-1992-tmp"))
        (LISP-COMMAND (CAR X))
        (DIRECTORY (CADR X))
        (SAVE-NAME "saved_nqthm-1992")
        (START-UP-FN
         (LET ((BUILD-DATE
                (WITH-OUTPUT-TO-STRING (STR) (PRINT-IDATE (IDATE) STR) STR)))
           #'(LAMBDA ()
                     (FORMAT T 
                             "~%Nqthm-1992.~%~
                      Initialized with (BOOT-STRAP NQTHM) on ~A.~%~%"
                             BUILD-DATE)
                     (LET ((FL (OR (PROBE-FILE "nqthm-init.lsp")
                                   (PROBE-FILE "nqthm-init.lisp"))))
                       (IF FL (LOAD FL)))))))

; When writing the tiny nqthm-1992-tmp file, we insert an absolute pathname so
; that the file can be moved to a typical bin directory.

; CMU Lisp does not dump a file that is directly executable, but rather dumps a
; file that must be invoked with something like `cmulisp -core dumped-file'.

   #+CMU
   (PROGN (WITH-OPEN-FILE
           (FILE "nqthm-1992-tmp"
                 :DIRECTION :OUTPUT
                 :IF-EXISTS :RENAME-AND-DELETE)
           (PRINC LISP-COMMAND FILE)
           (WRITE-CHAR #\Space FILE)
           (PRINC "-core " FILE)
           (PRINC DIRECTORY FILE)
           (WRITE-CHAR #\/ FILE)
           (PRINC SAVE-NAME FILE)
           (TERPRI FILE)))

   #+AKCL
   (PROGN (WITH-OPEN-FILE
           (FILE "nqthm-1992-tmp"
                 :DIRECTION :OUTPUT
                 :IF-EXISTS :RENAME-AND-DELETE)
           (PRINC #\# FILE)
           (TERPRI FILE)
           (PRINC DIRECTORY FILE)
           (PRINC #\/ FILE)
           (PRINC SAVE-NAME FILE)
           (PRINC #\Space FILE)
           (PRINC DIRECTORY FILE)
           (PRINC #\/ FILE)
           (TERPRI FILE)))

   #+(OR LUCID ALLEGRO)
   (PROGN (WITH-OPEN-FILE
           (FILE "nqthm-1992-tmp"
                 :DIRECTION :OUTPUT
                 :IF-EXISTS :RENAME-AND-DELETE)
           (PRINC DIRECTORY FILE)
           (PRINC #\/ FILE)
           (PRINC SAVE-NAME FILE)
           (TERPRI FILE)))

; We now create the dump file.

; Warning -- AKCL exits upon executing SAVE-SYSTEM.  That's why we do the
; saving of the image last, after writing the file nqthm-1992-tmp.

   #+AKCL
   (PROGN (SETQ SI::*TOP-LEVEL-HOOK* START-UP-FN)
          (SETQ COMPILER::*SPLIT-FILES* 200000)
          (SI::SET-HOLE-SIZE 500)
          (GBC NIL)
          (IF (FBOUNDP 'SI::SGC-ON) (SI::SGC-ON T))
          (SI::SAVE-SYSTEM SAVE-NAME))

   #+Lucid
   (DISKSAVE SAVE-NAME :RESTART-FUNCTION START-UP-FN)
    
   #+Allegro
   (EXCL:DUMPLISP :NAME SAVE-NAME :RESTART-FUNCTION START-UP-FN)
    
   #+CMU
   (LET ((*TERMINAL-IO*
          (MAKE-TWO-WAY-STREAM SYS:*STDIN* SYS:*STDOUT*)))
     ; In CMU Lisp, GC messages go to *TERMINAL-IO*, but
     ; we don't want this to happen, just in case this save is running
     ; unattached to any terminal.  This particular solution was kindly
     ; suggested by William Lott.
     (SAVE-LISP SAVE-NAME :INIT-FUNCTION START-UP-FN))
    
   )

 )

; Some Lisps quit when reading end of file, some don't.
 #+CMU
 (QUIT)
 #+Allegro
 (EXIT)

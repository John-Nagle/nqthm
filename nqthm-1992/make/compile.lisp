#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".

|#

; This file is not necessary for building Nqthm-1992, but is provided
; as a mere convenience to users who wish to build Nqthm-1992 under
; Unix.  See the file ../makefile.  Unlike the sources for Nqthm-1992,
; this file contains Common Lisp implementation dependent commands for
; fixing bugs and improving performance.

; It is important for practical use of Nqthm-1992 that optimization be
; set for high speed execution.  Certainly, any optimization settings
; are ok.

(PROGN

; Optimize for speed.  We skirt a bug in the CMU Lisp 16(e) compiler 
; when compiling sloop.lisp by using SPACE = 1, which is what the
; CMU folks recommend anyway.

 (PROCLAIM (QUOTE (OPTIMIZE (SAFETY 0)
                            (SPACE #+CMU 1 #-CMU 0)
                            (SPEED 3)
                            #+Allegro (DEBUG 0)
                            #+(OR CMU Lucid) (COMPILATION-SPEED 0)
                            #+CMU (EXTENSIONS:INHIBIT-WARNINGS 3))))

; We now prevent some false assumptions about fixnums in Allegro.  We use
; this obscure EVAL/READ-FROM-STRING approach because the AKCL reader
; barfs on #+(VERSION>= ...).

 #+Allegro
 (EVAL (READ-FROM-STRING "
  (SETQ COMPILER::DECLARED-FIXNUMS-REMAIN-FIXNUMS-SWITCH
        #'(LAMBDA (X Y Z #+(VERSION>= 4 1) D) NIL)) "))

; Silence the GC.

 #+Lucid
 (SETQ *GC-SILENCE* T)
 #+CMU
 (SETQ *GC-VERBOSE* NIL)

; Suppress some compiler noise.

 #+AKCL
 (PROGN
  (SETQ COMPILER:*COMPILE-VERBOSE* NIL)
  (SETQ COMPILER:*SUPPRESS-COMPILER-NOTES* T))

 #+Lucid
 (PROGN (SETQ *STYLE-WARNINGS* NIL)
        (SETQ *REDEFINITION-ACTION* NIL) 
        (SETQ *RECORD-SOURCE-FILES* NIL)
        (SETQ *WARN-IF-NO-IN-PACKAGE* NIL))

 #+Allegro
 (SETQ *RECORD-SOURCE-FILE-INFO* NIL)

 (LOAD "nqthm.lisp")

 )

(IN-PACKAGE "USER")

(PROGN 

; This function gets referenced before it is defined or proclaimed in the
; normal course of Nqthm-1992 compilation.  We proclaim it here only to avoid a
; compiler warning.

 (PROCLAIM '(FUNCTION *1*SUBRP (T) T))

 (COMPILE-NQTHM)
 (LOAD-NQTHM)
 (LET ((*THM-SUPPRESS-DISCLAIMER-FLG* T))
      (BOOT-STRAP THM))
 (WITH-OPEN-FILE 
  (FILE "make/compile-success"
        :DIRECTION :OUTPUT
        :IF-EXISTS :RENAME-AND-DELETE)
  (PRINT "COMPILE-NQTHM is done." FILE)))

; Some Lisps quit gracefully when reading end of file, some don't.

#+CMU
(QUIT)
#+Allegro
(EXIT)

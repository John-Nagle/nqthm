;  Copyright (C) 1989-1994 by Robert S. Boyer, J Strother Moore, and
;  Computational Logic, Inc. All Rights Reserved.

;  Copying of this file is authorized to those who have read and
;  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
;  LICENSE" at the beginning of the Nqthm file "basis.lisp".

;  NQTHM Version 1992

;  This file `nqthm.lisp' is the basic loader and compiler for our
;  theorem-prover.  To compile the system, after loading this file
;  into a Common Lisp, invoke (IN-PACKAGE "USER") and then
;  (COMPILE-NQTHM).  To build the system for execution, assuming
;  that it has been compiled and after loading this file, invoke
;  (IN-PACKAGE "USER") and then (LOAD-NQTHM).  One can then proceed
;  to use BOOT-STRAP, PROVE-LEMMA, and the other commands described
;  in the manual.  For further guidance in case of problems, see the
;  installation guide chapter of the manual.

;  When installing this system, before invoking (COMPILE-NQTHM) or
;  (LOAD-NQTHM), it may be desirable to set *DEFAULT-NQTHM-PATH* in
;  order to specify the directory on which the sources are located
;  and to which the objects are to be written.  For example, one
;  might wish to (SETQ *DEFAULT-NQTHM-PATH* ">usr>smith>nqthm>"),
;  after invoking (IN-PACKAGE "USER").  For some implementations of
;  Common Lisp the default setting of NIL will cause the "current"
;  or "connected" directory to be used, which is ok provided that
;  the connected directory is the one with the sources and provided
;  your operating system supports, as does Unix, the concept of a
;  `connected' directory for a process.

;  Sadly, we do everything in the USER package.  This is not the best
;  Lisp style for an old and established Common Lisp system, but it is
;  by far the simplest and clearest approach we could find given the
;  variety of implementations of Common Lisp's "Put in seven extremely
;  random user interface commands".  If your USER package contains
;  symbols that conflict with ours, we apologize but offer no fix.

;  For running in Common Lisps corresponding to CLTL2, we may create
;  the package USER.  We may also create SLOOP.

(OR (FIND-PACKAGE "USER")
    (MAKE-PACKAGE "USER" :USE (LIST (OR (FIND-PACKAGE "COMMON-LISP")
                                        (FIND-PACKAGE "LISP")))))

(OR (FIND-PACKAGE "SLOOP")
    (PROGN (MAKE-PACKAGE "SLOOP" :USE (LIST (OR (FIND-PACKAGE "COMMON-LISP")
                                                (FIND-PACKAGE "LISP"))))
           (SHADOW 'TYPE-ERROR "SLOOP")
           (SHADOW 'LOOP-FINISH "SLOOP")))

(IN-PACKAGE "USER")

(DEFUN CHK-BASE-AND-PACKAGE-1992 (BASE PACK)

;  !!!  We use three exclamation marks to remind ourselves that a
;  symbol is also defined elsewhere.  We have had some grief with
;  Common Lisps that load files into the wrong package or with the
;  wrong base, so we check these things every time that we load a
;  file.

  (OR (AND (EQL BASE (+ 1 1 1 1 1 1 1 1 1 1))
           (EQ PACK (FIND-PACKAGE "USER")))
      (ERROR "Wrong package or base.")))

(CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*)

;  Here is how to set the directory from which all files are to be
;  loaded and to which files are to be printed.  The user is free to
;  set this variable.  Should be a string, e.g. "/usr/me/nqthm/", or
;  NIL.
;  !!!
(DEFVAR *DEFAULT-NQTHM-PATH* NIL
  "IF not NIL, components from this will be used to extend pathnames.")

;  In compiling and loading this theorem-prover, we assume that the
;  source files have extension "lisp", e.g. "/usr/me/basis.lisp".  In
;  MAKE-LIB we create files with the same extension.  If your Lisp
;  requires a different extension feel free to change the value of
;  this variable.  But if you do, you will of course need to rename
;  all of the *.lisp source files that come with this system, too.
;  !!!
(DEFVAR FILE-EXTENSION-LISP "lisp")

;  We have not found a mechanism that works across all Common Lisps for both
;  specifying the name for a compiled object file and for loading that file.
;  In most Common Lisps we have tried, (load "foo") will load the compiled
;  form of foo if it is available and up to date.  This seems to work for
;  KCL, Symbolics, Lucid, and TI.  However, you may need to specify a value
;  for FILE-EXTENSION-BIN in other Common Lisps, e.g.  (SETQ
;  FILE-EXTENSION-BIN "fasl").
;  !!!
(DEFVAR FILE-EXTENSION-BIN NIL)

;  Invoking (COMPILE-NQTHM) is all it takes to compile this
;  theorem-prover.  The order of compilation and loading is
;  significant; sloop, basis, genfact, and events define macros that
;  are used in later files.
(DEFUN COMPILE-NQTHM ()
  (FLET ((LF (N)
             (LOAD (EXTEND-FILE-NAME N FILE-EXTENSION-BIN)))
         (CF (N)
             (COMPILE-FILE (EXTEND-FILE-NAME N FILE-EXTENSION-LISP))))
        (PROCLAIM-NQTHM-FILES)
        (CF "sloop")
        (LF "sloop")
        (CF "basis")
        (LF "basis")
        (CF "genfact")
        (LF "genfact")
        (CF "events")
        (LF "events")
        (CF "code-1-a")
        (CF "code-b-d")
        (CF "code-e-m")
        (CF "code-n-r")
        (CF "code-s-z")
        (CF "io")
        (CF "ppr")
        ))

;  Invoking (LOAD-NQTHM) is all it takes to build a runnable version of
;  this theorem-prover, assuming that you have compiled it.
(DEFUN LOAD-NQTHM ()
  (FLET ((LF (N)
             (LOAD (EXTEND-FILE-NAME N FILE-EXTENSION-BIN))))
; For speed on calls of built-in *1*functions:
        (PROCLAIM-NQTHM-FILE "code-1-a") 
        (LF "sloop")
        (LF "basis")
        (LF "genfact")
        (LF "events")
        (LF "code-1-a")
        (LF "code-b-d")
        (LF "code-e-m")
        (LF "code-n-r")
        (LF "code-s-z")
        (LF "io")
        (LF "ppr")))

;  With DEFUN we never define a function that returns multiple values;
;  at least we never look at any but the first value.  In some Lisps,
;  notably KCL, proclaiming this fact permits compilation of much
;  faster code.  Almost all of our functions take a fixed number of
;  arguments.  Proclaiming this also permits compilation of much
;  faster code.  Proclamations and declarations are a relatively new
;  and fragile part of Common Lisp, so we permit the complete
;  suppression of all proclamations.  If you suspect that function
;  proclamations are giving you trouble, feel free to set this
;  variable to NIL.
;  !!!
(DEFVAR *NQTHM-MAKE-PROCLAMATIONS* T)

(DEFUN PROCLAIM-NQTHM-FILES ()
  (DOLIST
      (NAME '("basis" "genfact" "events" "code-1-a" "code-b-d"
                      "code-e-m" "code-n-r" "code-s-z" "io" "ppr"))
    (PROCLAIM-NQTHM-FILE NAME)))

; About our use of PROCLAIM.  As a first approximation, proclaiming a function
; to take a certain number of arguments and return a certain number of values
; may be regarded as a no-op, a mere hint to the compiler, perhaps, about how
; to generate more efficient code.  Since about 1987, we have been mainly using
; Austin-Kyoto Common Lisp to run Nqthm, where such PROCLAIM hints give a
; considerable performance improvement.  But in 1994 it became clear that
; AKCL's semantics for PROCLAIM may differ from that given by other Common Lisp
; implementations, so we have taken the conservative action of eliminating the
; use of PROCLAIM in all Common Lisps except AKCL.  The adventuresome may wish
; to edit near the two #+AKCL forms below to permit proclaiming in their Lisp.
; We know of two problems that would arise in Lucid 4.1.1 if we used PROCLAIM
; as we do in ACKL.  (1) If a function actually returns two values, e.g., PACK,
; which ends in a call of INTERN, is it legitimate to PROCLAIM it to return
; only one value?  Lucid seems to say no, whereas AKCL says yes, acting as if
; the final form were wrapped in (VALUES ...).  (2) If a function is first
; defined and proclaimed to have n arguments, may it later be redefined and
; reproclaimed to have m/=n arguments?  Lucid seems to say no.  In the
; processing of different event files, functions may be redefined.

(DEFUN PROCLAIM-NQTHM-FILE (NAME)
; !!!
  NIL
  #+AKCL
  (WITH-OPEN-FILE 
      (FILE (EXTEND-FILE-NAME NAME FILE-EXTENSION-LISP)
            :DIRECTION :INPUT)
    (LET ((EOF (CONS NIL NIL))
          (*READ-BASE* 10)
          (*READTABLE* (COPY-READTABLE NIL))
          (*PACKAGE* (FIND-PACKAGE "USER")))
      (LOOP
       (LET ((FORM (READ FILE NIL EOF)))
         (COND ((EQ EOF FORM) (RETURN NIL))
               ((MAKE-DECLARE-FORM FORM ))))))))

(DEFUN MAKE-DECLARE-FORM (FORM)
; !!!
  NIL
  #+AKCL
  (WHEN
   (AND *NQTHM-MAKE-PROCLAMATIONS*
        (LISTP FORM))
   (COND ((MEMBER (CAR FORM) '(EVAL-WHEN ))
          (DOLIST (V (CDDR FORM)) (MAKE-DECLARE-FORM V)))
         ((MEMBER (CAR FORM) '(PROGN ))
          (DOLIST (V (CDR FORM)) (MAKE-DECLARE-FORM V)))
         ((MEMBER (CAR FORM) '(IN-PACKAGE DEFCONSTANT))
          (EVAL FORM))
         ((MEMBER (CAR FORM) '(DEFUN))
          (COND
           ((AND
             (NOT (MEMBER '&REST (CADDR FORM)))
             (NOT (MEMBER '&BODY (CADDR FORM)))
             (NOT (MEMBER '&KEY (CADDR FORM)))
             (NOT (MEMBER '&OPTIONAL (CADDR FORM))))
            (FUNCALL 'PROCLAIM
                     (LIST  'FUNCTION
                            (CADR FORM)
                            (MAKE-LIST (- (LENGTH (THIRD FORM))
                                          (LENGTH (MEMBER '&AUX (THIRD FORM))))
                                       :INITIAL-ELEMENT T)
                            T))))))))

(DEFUN EXTEND-FILE-NAME (FILE EXTENSION)
;  !!!
  ;;If extension = nil, don't adjoin anything
  (LET ((*PRINT-PRETTY* NIL)
        (*PRINT-BASE* 10)
        (*PRINT-RADIX* NIL)
        (*PRINT-LEVEL* NIL)
        (*PRINT-LENGTH* NIL)
        (*PRINT-CASE* :UPCASE))
    (LET ((STRING (FORMAT NIL "~A~@[.~A~]" FILE EXTENSION)))
      (IF *DEFAULT-NQTHM-PATH* (MERGE-PATHNAMES STRING *DEFAULT-NQTHM-PATH*)
          STRING))))

;                              ITERATE and SLOOP

;   We use Bill Schelter's SLOOP package to provide the iterative
;   primitive FOR in Lisp.  It has been renamed ITERATE for historical
;   reasons.  Upon converting to Common Lisp we adopted the
;   "officially sanctioned" Common Lisp version of LOOP by Glenn Burke
;   of Palladian Software, in Cambridge MA, April 1986.  We changed
;   the name LOOP to ITERATE and included the sources in our sources
;   to make us immune to the eventual adoption of a modified LOOP by
;   Common Lisp.  When Schelter improved the efficiency of this code,
;   he used his loop package because the arithmetic was more efficient.
;   We do not (USE-PACKAGE "SLOOP") in order to avoid importing all that
;   SLOOP exports: loop-finish collides with a Symbolics symbol in
;   USER.

(DEFMACRO ITERATE
;   !!!
  (&REST L)
  `(SLOOP::SLOOP ,@ L))


;                       A DIATRIBE ON PACKAGES

;  N. B. Although we find mode lines such as:

;;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 -*- ;;;;

;  rather ugly, we include them in the sources out of pity for anyone
;  trying to use the system on a Lisp Machine.  Omitting these lines
;  causes endless grief: complaints from ZMACS, mistakes about
;  packages, mistakes about base.  Of course, because mode lines look
;  like comments, no Common Lisp implementation has any right to do
;  anything one way or the other because of the presence or absence of
;  a mode line.  But on a Lisp machine, the presence of such a mode
;  line can cause an unreasonable error, e.g., when an unknown package
;  is mentioned.  This unreasonable behavior is part of the reason
;  that we use the USER package -- it already exists in all Common
;  Lisp implemenations.

;  Boyer and Moore, January 1988

;  Even the existence of the package USER cannot be relied upon!  It went
;  away in CLTL2.

;  Boyer and Moore, April 1992.



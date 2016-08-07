;;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 -*- ;;;;

;  Copyright (C) 1989-1994 by Robert S. Boyer, J Strother Moore, and
;  Computational Logic, Inc. All Rights Reserved.

;  Copying of this file is authorized to those who have read and
;  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
;  LICENSE" at the beginning of the Nqthm file "basis.lisp".

;  NQTHM Version 1992

(IN-PACKAGE "USER")

(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))

(DEFMACRO DEFEVENT (&REST X)

;   An apology for our user-level functions being macros.

;   We find it desireable to permit the theorem-prover to be invoked from a
;   Lisp read-eval-print loop rather than from some interface of our own
;   design.  One reason for this attitude is that it allows the user of the
;   system to enjoy the benefits of his customary Lisp environment.

;   If the top level functions for events, such as DEFN and PROVE-LEMMA were
;   defined as EXPRS, then it would be necessary to quote the arguments, which
;   we find burdensome.  Common Lisp leaves us no alternative to EXPRS except
;   macros.  We therefore define each user-level function, say DOIT, as a macro
;   which, after checking for the right number of arguments calls another
;   function, DOIT-FN, which is an EXPR.

;   So that DEFN and PROVE-LEMMA can have optional "hint" arguments, we permit
;   &OPTIONAL to occur in the arg list, though in fact it does not occur in the
;   arg list of either the MACRO or the EXPR we define.

;   Historical note:  In Interlisp we defined our user-level functions as
;   EXPRS, yet we were able to write:

;   DEFN(FOO (X) (BAR X))

;   which not only solved the quote problem but also permitted the optional
;   arguments to default to NIL.

;   Not all of the Lisps in which we run check macro arguments as carefully as
;   we would like, so we do it here for the user-level functions ourselves.

  (LET (NAME ARGS BODY REQUIRED-ARGS OPTIONAL-ARGS FN)
    (OR (MATCH X (CONS NAME (CONS ARGS BODY)))
        (ERROR "DEFEVENT takes three or more arguments."))
    (OR (NULL (CDR (OUR-LAST X)))
        (ERROR "DEFEVENT argument lists must end in NIL."))


;   In the spirit of Common Lisp, we permit ourselves optional arguments in the
;   user interface.

    (COND ((MEMBER-EQ (QUOTE &OPTIONAL) ARGS)
           (SETQ REQUIRED-ARGS
                 (ITERATE FOR ARG IN ARGS UNTIL (EQ ARG (QUOTE &OPTIONAL))
                          COLLECT ARG))
           (SETQ OPTIONAL-ARGS (CDR (MEMBER-EQ (QUOTE &OPTIONAL) ARGS))))
          (T (SETQ REQUIRED-ARGS ARGS)
             (SETQ OPTIONAL-ARGS NIL)))
    (SETQ FN (PACK (LIST NAME (QUOTE -FN))))
    `(PROGN (QUOTE COMPILE)
            (DEFMACRO ,NAME (&REST X)
              (DEFEVENT-APPLY X (QUOTE ,NAME) (QUOTE ,FN)
                ,(LENGTH REQUIRED-ARGS)
                ,(+ (LENGTH OPTIONAL-ARGS) (LENGTH REQUIRED-ARGS))))
            (DEFUN ,FN ,(APPEND REQUIRED-ARGS OPTIONAL-ARGS) ,@BODY))))

(DEFEVENT ADD-AXIOM (NAME TYPES TERM)
  (EVENT-COMMAND
   (LIST (QUOTE ADD-AXIOM) NAME TYPES TERM)
   (LET ((IN-ADD-AXIOM-FLG T))
     (MATCH! (CHK-ACCEPTABLE-LEMMA NAME TYPES TERM)
             (LIST NAME TYPES TERM))
     (MAKE-EVENT NAME (LIST (QUOTE ADD-AXIOM) NAME TYPES TERM))
     (ADD-FACT NIL (QUOTE NONCONSTRUCTIVE-AXIOM-NAMES) NAME)
     (ADD-LEMMA0 NAME TYPES TERM)
     (DEPEND NAME (ALL-FNNAMES TERM))
     NAME)))

(DEFEVENT ADD-SHELL
  (SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)
  (EVENT-COMMAND
   (LIST (QUOTE ADD-SHELL)
         SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)
   (MATCH! (CHK-ACCEPTABLE-SHELL SHELL-NAME BTM-FN-SYMB RECOGNIZER
                                 DESTRUCTOR-TUPLES)
           (LIST SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES))
   (MAKE-EVENT SHELL-NAME
               (LIST (QUOTE ADD-SHELL)
                     SHELL-NAME BTM-FN-SYMB RECOGNIZER
                     DESTRUCTOR-TUPLES))
   (ADD-SHELL0 SHELL-NAME BTM-FN-SYMB RECOGNIZER
               DESTRUCTOR-TUPLES)
   (DEPEND SHELL-NAME
           (SET-DIFF (UNION-EQ (ITERATE FOR X IN DESTRUCTOR-TUPLES
                                        WITH ITERATE-ANS
                                        DO (SETQ ITERATE-ANS
                                                 (UNION-EQ
                                                  (CDR (CADR X))
                                                  ITERATE-ANS))
                                        FINALLY (RETURN ITERATE-ANS))
                               (ITERATE FOR X IN DESTRUCTOR-TUPLES
                                        WITH ITERATE-ANS
                                        DO
                                        (SETQ ITERATE-ANS
                                              (ADD-TO-SET (CADDR X)
                                                          ITERATE-ANS))
                                        FINALLY (RETURN ITERATE-ANS)))
                     (COND (BTM-FN-SYMB (LIST BTM-FN-SYMB
                                              RECOGNIZER))
                           (T (LIST RECOGNIZER)))))
    
;   Make the shell depend on every fn used in the type restrictions and
;   defaults except the BTM-FN-SYMB and RECOGNIZER of this type.
    
   SHELL-NAME))

(DEFEVENT AXIOM (NAME TYPES TERM &OPTIONAL IGNORE)
  (DECLARE (IGNORE IGNORE))
  (APPLY (FUNCTION ADD-AXIOM-FN)
         (LIST NAME TYPES TERM)))

(DEFEVENT BOOT-STRAP (&OPTIONAL MODE)
  (EVENT-COMMAND
   (LIST (QUOTE BOOT-STRAP) MODE)
   (LET ((IN-BOOT-STRAP-FLG T)
         (ARITY-ALIST
          (QUOTE ((NOT . 1) (AND . 2) (OR . 2) (IMPLIES . 2)
                  (LESSP . 2) (PLUS . 2)))))
     (PRINT-NQTHM-DISCLAIMER)
     (OR MODE (SETQ MODE (QUOTE THM)))
     (BOOT-STRAP0 MODE)
     (MAKE-EVENT (QUOTE GROUND-ZERO) (LIST (QUOTE BOOT-STRAP) MODE))
     (ADD-FACT (QUOTE IF) (QUOTE LISP-CODE)
               (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE IF-ERROR))))
     (GUARANTEE-CITIZENSHIP
      (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE IF-ERROR))))
     (ADD-FACT (QUOTE EQUAL) (QUOTE LISP-CODE)
               (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE EQUAL))))
     (GUARANTEE-CITIZENSHIP
      (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE EQUAL))))
     (ADD-FACT (QUOTE IF)
               (QUOTE TYPE-PRESCRIPTION-LST)
               (CONS (QUOTE GROUND-ZERO)
                     (QUOTE (0 NIL T T))))
     (ADD-FACT (QUOTE IF)
               (QUOTE SUBRP)
               *1*T)
     (ADD-FACT (QUOTE IF)
               (QUOTE TOTALP-LST)
               (CONS (QUOTE GROUND-ZERO)
                     T))
     (ADD-FACT (QUOTE EQUAL)
               (QUOTE TYPE-PRESCRIPTION-LST)
               (CONS (QUOTE GROUND-ZERO)
                     (CONS TYPE-SET-BOOLEAN (QUOTE (NIL NIL)))))
     (ADD-FACT (QUOTE EQUAL)
               (QUOTE SUBRP)
               *1*T)
     (ADD-FACT (QUOTE EQUAL)
               (QUOTE TOTALP-LST)
               (CONS (QUOTE GROUND-ZERO)
                     T))
     (ADD-FACT (QUOTE QUOTE) (QUOTE SUBRP) *1*F)
     (ADD-FACT (QUOTE COUNT) (QUOTE LISP-CODE)
               (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE COUNT))))
     (GUARANTEE-CITIZENSHIP
      (PACK (LIST PREFIX-FOR-FUNCTIONS (QUOTE COUNT))))
     (ADD-FACT (QUOTE COUNT)
               (QUOTE SUBRP)
               *1*T)
     (ADD-FACT (QUOTE COUNT)
               (QUOTE TOTALP-LST)
               (CONS (QUOTE GROUND-ZERO)
                     T))
     (ADD-FACT (QUOTE COUNT)
               (QUOTE TYPE-PRESCRIPTION-LST)
               (CONS (QUOTE GROUND-ZERO)
                     (CONS TYPE-SET-NUMBERS (QUOTE (NIL)))))

;   We now set the ERRATICP property to NIL for each of the BOOT-STRAP
;   functions not introduced by DCL0, ADD-SHELL0, and DEFN0.  That list
;   of functions is IF, EQUAL, and COUNT (obtained by looking at every
;   place in the source code where we set TYPE-PRESCRIPTION-LST and
;   thereby declare the arity of a new symbol).  Since NIL properties
;   are not stored, we don't actually do anything.

     (ITERATE FOR INSTR IN BOOT-STRAP-INSTRS
              DO (APPLY (CAR INSTR) (CDR INSTR)))
     (QUOTE GROUND-ZERO))))

(DEFEVENT CONSTRAIN (NAME TYPES TERM WITNESS-ALIST &OPTIONAL HINTS)

; The CONSTRAIN and FUNCTIONALLY-INSTANTIATE events were designed and 
; implemented in collaboration with Matt Kaufmann, David Goldschlag, and
; Bill Bevier.

  (EVENT-COMMAND
   (LIST 'CONSTRAIN NAME TYPES TERM WITNESS-ALIST HINTS)
   (LET ((IN-PROVE-LEMMA-FLG T) THM PROVE-ANS)
        (MATCH! (CHK-ACCEPTABLE-CONSTRAIN NAME TYPES TERM WITNESS-ALIST)
                (LIST NAME TYPES TERM WITNESS-ALIST))
        (MATCH! (CHK-ACCEPTABLE-HINTS HINTS)
                (LIST HINTS))
        (SETQ THM
              (SUBLIS-FN (ITERATE FOR DOUBLET IN WITNESS-ALIST
                                  COLLECT
                                  (CONS (CAR DOUBLET)
                                        (CADR DOUBLET)))
                         TERM))
        (OR PETITIO-PRINCIPII
            (PRINEVAL (PQUOTE (PROGN CR CR
                                     |We| |will| |verify| |the|
                                     |consistency| |and| |the| |conservative|
                                     |nature| |of| |this| |constraint|
                                     |by| |attempting| |to| |prove|
                                     (!TERM THM '|.|) CR))
                      (LIST (CONS 'THM THM))
                      0 PROVE-FILE))
        (UNWIND-PROTECT
         (PROGN
          (SETQ PROVE-ANS
                (PROVE-FN (APPLY-HINTS HINTS THM)))
          (COND (PROVE-ANS
                 (MAKE-EVENT NAME
                             (LIST 'CONSTRAIN NAME TYPES TERM
                                   WITNESS-ALIST
                                   HINTS))
                 (ITERATE FOR DOUBLET IN WITNESS-ALIST
                          DO
                          (DCL0 (CAR DOUBLET)
                                (COND ((SYMBOLP (CADR DOUBLET))
                                       (ITERATE FOR I FROM 1
                                                TO (ARITY (CADR DOUBLET))
                                                COLLECT
                                                (PACK (LIST 'X I))))
                                      (T (CADR (CADR DOUBLET))))
                                NIL))
                 (ADD-LEMMA0 NAME TYPES TERM)
                 (DEPEND
                  NAME
                  (UNION-EQ
                   ALL-LEMMAS-USED
                   (UNION-EQ
                    (EXTRACT-DEPENDENCIES-FROM-HINTS HINTS)
                    (UNION-EQ
                     (SET-DIFF (ALL-FNNAMES TERM)
                               (ITERATE FOR DOUBLET IN WITNESS-ALIST
                                        COLLECT (CAR DOUBLET)))
                     (ITERATE
                      FOR DOUBLET IN WITNESS-ALIST
                      WITH ANS
                      DO
                      (SETQ ANS
                            (UNION
                             (COND ((SYMBOLP (CADR DOUBLET))
                                    (LIST (CADR DOUBLET)))
                                   (T (ALL-FNNAMES (CADDR (CADR DOUBLET)))))
                             ANS))
                      FINALLY (RETURN ANS))))))
                 NAME)
                (T (ER SOFT NIL |We| |are| |unable| |to| |prove|
                       |that| |the| |constraint| |is| |witnessed|
                       |as| |specified| |.|))))
         (PROGN (ITERATE FOR X IN HINT-VARIABLE-ALIST
                         DO (SET (CADR X) (CADDDR X)))
                (SETQ LOCAL-DISABLEDP-HASH-FLAG NIL))))))

(DEFEVENT DCL (NAME ARGS)
  (EVENT-COMMAND
   (LIST (QUOTE DCL) NAME ARGS)
   (MATCH! (CHK-ACCEPTABLE-DCL NAME ARGS)
           (LIST NAME ARGS))
   (MAKE-EVENT NAME (LIST (QUOTE DCL) NAME ARGS))
   (DCL0 NAME ARGS NIL)
   NAME))

(DEFEVENT DEFN (NAME ARGS BODY &OPTIONAL RELATION-MEASURE-LST)
  (EVENT-COMMAND
   (LIST (QUOTE DEFN) NAME ARGS BODY RELATION-MEASURE-LST)
   (MATCH! (CHK-ACCEPTABLE-DEFN NAME ARGS BODY RELATION-MEASURE-LST)
           (LIST NAME ARGS BODY RELATION-MEASURE-LST))
   (MAKE-EVENT NAME (COND (RELATION-MEASURE-LST
                           (LIST (QUOTE DEFN) NAME ARGS BODY
                                 RELATION-MEASURE-LST))
                          (T (LIST (QUOTE DEFN) NAME ARGS BODY))))
   (DEFN0 NAME ARGS BODY RELATION-MEASURE-LST NIL NIL)
   (DEPEND
    NAME
    (REMOVE
     NAME
     (UNION-EQ
      (ALL-FNNAMES BODY)
      (UNION-EQ
       ALL-LEMMAS-USED
       (ITERATE FOR TEMP IN (GET NAME (QUOTE JUSTIFICATIONS))
                WITH ITERATE-ANS
                DO (SETQ
                    ITERATE-ANS
                    (UNION-EQ (COND
                               ((NULL (ACCESS JUSTIFICATION
                                              RELATION TEMP))
                                NIL)
                               (T (UNION-EQ
                                   (ALL-FNNAMES (ACCESS
                                                 JUSTIFICATION
                                                 MEASURE-TERM
                                                 TEMP))
                                   (ADD-TO-SET (ACCESS JUSTIFICATION
                                                       RELATION TEMP)
                                               (ACCESS JUSTIFICATION
                                                       LEMMAS TEMP)))))
                              ITERATE-ANS))
                FINALLY (RETURN ITERATE-ANS))))))
    
   (COND ((NOT (ADMITTED-FUNCTIONP NAME))
          (UNDO-BACK-THROUGH-FN NAME)
          (DEFN-WRAPUP NIL)
          NIL)
         (T (PRINT-DEFN-MSG NAME ARGS)
            (DEFN-WRAPUP (ADMITTED-FUNCTIONP NAME))
            NAME))))

(DEFEVENT DEFTHEORY (NAME EVENTNAMES)

; The prototype of the DEFTHEORY event was invented and coded by Bill
; Bevier.  Matt Kaufmann subsequently collaborated with Bevier to
; bring the code into the style of Nqthm and to handle various loose
; ends.  Closely associated with DEFTHEORY are the PROVE-LEMMA hints
; ENABLE-THEORY and DISABLE-THEORY.

  (EVENT-COMMAND
    (LIST (QUOTE DEFTHEORY) NAME EVENTNAMES)
    (MATCH! (CHK-ACCEPTABLE-DEFTHEORY NAME EVENTNAMES)
            (LIST NAME EVENTNAMES)) 
    (MAKE-EVENT NAME (LIST (QUOTE DEFTHEORY) NAME EVENTNAMES))
    (DEPEND NAME EVENTNAMES)
    NAME))

(DEFEVENT DISABLE (OLDNAME)
  (CHK-DISABLEABLE OLDNAME)
  (APPLY (FUNCTION TOGGLE-FN)
         (LIST (MAKE-NEW-NAME (PACK (LIST OLDNAME (QUOTE -OFF))))
               OLDNAME T)))

(DEFEVENT DISABLE-THEORY (THEORY)
  (APPLY (FUNCTION SET-STATUS-FN)
         (LIST (GUESS-NEW-EVENT-NAME
                (PACK (LIST 'DISABLE-THEORY-AFTER-
                            (MOST-RECENT-NON-STATUS)
                            '-)))
               THEORY
               '((OTHERWISE DISABLE)))))

(DEFEVENT ENABLE (OLDNAME)
  (CHK-DISABLEABLE OLDNAME)
  (APPLY (FUNCTION TOGGLE-FN)
         (LIST (MAKE-NEW-NAME (PACK (LIST OLDNAME (QUOTE -ON))))
               OLDNAME NIL)))

(DEFEVENT ENABLE-THEORY (THEORY)
  (APPLY (FUNCTION SET-STATUS-FN)
         (LIST (GUESS-NEW-EVENT-NAME
                (PACK (LIST 'ENABLE-THEORY-AFTER-
                            (MOST-RECENT-NON-STATUS)
                            '-)))
               THEORY
               '((OTHERWISE ENABLE)))))

(DEFEVENT FUNCTIONALLY-INSTANTIATE (NAME TYPES TERM OLD-NAME-OR-LIST FS
                                         &OPTIONAL HINTS)

; The CONSTRAIN and FUNCTIONALLY-INSTANTIATE events were designed and 
; implemented in collaboration with Matt Kaufmann, David Goldschlag, and
; Bill Bevier.

; See definition of AVAILABLE-EVENT-FS-PAIRS-ALIST for the form of 
; old-name-or-list.

  (LET ((IN-PROVE-LEMMA-FLG T) PROVE-ANS CONSTRAINT
        EVENT-FS-ALIST PRECEDING-FI-EVENTS OLD-NAME)
       (EVENT-COMMAND
         (LIST 'FUNCTIONALLY-INSTANTIATE NAME TYPES
               TERM OLD-NAME-OR-LIST FS HINTS)
         (MATCH (CHK-ACCEPTABLE-FUNCTIONALLY-INSTANTIATE NAME TYPES TERM
                                                         OLD-NAME-OR-LIST FS) 
                (LIST NAME TYPES TERM OLD-NAME FS
                      CONSTRAINT
                      ;; The following is an alist with entries of the form
                      ;; (name . fs), where fs is a functional substitution
                      ;; that has already been sorted as in the definition of
                      ;; MAKE-LOCAL-FS.  The idea is that this alist records
                      ;; which instances of which events are being proved by
                      ;; the current FUNCTIONALLY-INSTANTIATE event.  This 
                      ;; alist will be stored on the JUSTIFICATIONS property
                      ;; of that new event.
                      EVENT-FS-ALIST
                      ;; The final component records the previous
                      ;; FUNCTIONALLY-INSTANTIATE events whose JUSTIFICATIONS
                      ;; are being used in the current event.
                      PRECEDING-FI-EVENTS))
         (MATCH! (CHK-ACCEPTABLE-HINTS HINTS)
                 (LIST HINTS))
         (OR PETITIO-PRINCIPII
             (PRINEVAL
              (PQUOTE (PROGN CR CR |The| |functional| |instantiation|
                             |of| (!PPR OLD-NAME NIL) |under| (!PPR FS NIL)
                             (COND
                              (TRUE-FLG |generates| |no| |new| |proof|
                                        |obligation| |.|)
                              (T |requires| |us| |to| |prove|
                                 (!TERM CONSTRAINT '|.|)))
                             (COND (PRECEDING-FI-EVENTS
                                    CR |#| |Note| |that| |we| |are| |using|
                                    |the| |following|
                                    |earlier| FUNCTIONALLY-INSTANTIATE
                                    (plural? PRECEDING-FI-EVENTS |events|
                                             |event|)
                                    |in| |order| |to| |satisfy| |part| |of|
                                    |the| |proof| |obligation| |:|
                                    (!PPR-LIST PRECEDING-FI-EVENTS '|.|) CR)
                                   (T CR))
                             CR))
              (LIST (CONS 'TRUE-FLG (EQUAL CONSTRAINT TRUE))
                    (CONS 'PRECEDING-FI-EVENTS PRECEDING-FI-EVENTS)
                    (CONS 'OLD-NAME OLD-NAME)
                    (CONS 'FS FS)
                    (CONS 'CONSTRAINT CONSTRAINT))
              0 PROVE-FILE))
        (UNWIND-PROTECT
           (PROGN
             (SETQ PROVE-ANS
                   (OR (EQUAL CONSTRAINT TRUE)
                       (PROVE-FN (APPLY-HINTS HINTS CONSTRAINT))))
             (COND (PROVE-ANS
                     (MAKE-EVENT NAME (LIST (QUOTE FUNCTIONALLY-INSTANTIATE)
                                            NAME TYPES TERM
                                            OLD-NAME FS HINTS))
                     (AND EVENT-FS-ALIST
                          (ADD-FACT NAME 'JUSTIFICATIONS EVENT-FS-ALIST))
                     (ADD-LEMMA0 NAME TYPES TERM)
                     (DEPEND NAME
                             (SCRUNCH
                              (APPEND
                               ;; Here we note the dependency on previous
                               ;; FUNCTIONALLY-INSTANTIATE events that
                               ;; were used for relieving constraints.
                               (IF (CONSP OLD-NAME-OR-LIST)
                                   ;; Then store explicitly what was provided
                                   ;; -- no less than that, so that 
                                   ;; error-checking doesn't catch us upon
                                   ;; replay.
                                   (CDR OLD-NAME-OR-LIST)
                                   PRECEDING-FI-EVENTS)
                               ;; Here we store the names of all constraints
                               ;; that were proved under FS.
                               (ITERATE FOR PAIR IN EVENT-FS-ALIST
                                        COLLECT (CAR PAIR))
                               ALL-LEMMAS-USED
                               (EXTRACT-DEPENDENCIES-FROM-HINTS HINTS)
                               (ALL-FNNAMES TERM)
                               (ITERATE FOR DOUBLET IN FS
                                        APPEND
                                        (CONS (CAR DOUBLET)
                                              (COND
                                               ((SYMBOLP (CADR DOUBLET))
                                                (LIST (CADR DOUBLET)))
                                               (T (ALL-FNNAMES
                                                   (CADDR (CADR DOUBLET)))))))
                               (LIST OLD-NAME))))))
             (COND (PROVE-ANS NAME)
                   (T NIL)))
           (PROGN (ITERATE FOR X IN HINT-VARIABLE-ALIST
                           DO (SET (CADR X) (CADDDR X)))
                  (SETQ LOCAL-DISABLEDP-HASH-FLAG NIL))))))

(DEFEVENT LEMMA (NAME TYPES TERM &OPTIONAL HINTS)

; The event LEMMA is like PROVE-LEMMA except that hints are handled as
; though in "Bevier-mode."  In this mode, the global state is viewed
; as though only the GROUND-ZERO theory is enabled, though of course
; one can give ENABLE and DISABLE hints to LEMMA, as well as
; ENABLE-THEORY and DISABLE-THEORY hints.  This event is due to
; Bill Bevier.

  (APPLY (FUNCTION PROVE-LEMMA-FN)
         (LIST NAME TYPES TERM (BEVIER-MODE HINTS))))

(DEFEVENT PROVE-LEMMA (NAME TYPES TERM &OPTIONAL HINTS)
  (EVENT-COMMAND
   (LIST (QUOTE PROVE-LEMMA) NAME TYPES TERM HINTS)
   (LET ((IN-PROVE-LEMMA-FLG T) PROVE-ANS)
     (MATCH! (CHK-ACCEPTABLE-LEMMA NAME TYPES TERM)
             (LIST NAME TYPES TERM))
     (MATCH! (CHK-ACCEPTABLE-HINTS HINTS)
             (LIST HINTS))
     (UNWIND-PROTECT
         (PROGN
            
;   Before calling PROVE we call APPLY-HINTS.  APPLY-HINTS sets some global
;   variables that affect the theorem-prover.  We enter an UNWIND-PROTECT here
;   so that we can set those variables to their standard default values no
;   matter how we exit PROVE.
            
           (SETQ PROVE-ANS
                 (PROVE-FN (APPLY-HINTS HINTS TERM)))
           (COND (PROVE-ANS
                  (MAKE-EVENT NAME (COND (HINTS
                                          (LIST (QUOTE PROVE-LEMMA)
                                                NAME TYPES TERM HINTS))
                                         (T (LIST (QUOTE PROVE-LEMMA)
                                                  NAME TYPES TERM))))
                  (ADD-LEMMA0 NAME TYPES TERM)
                  (DEPEND NAME
                          (UNION-EQ ALL-LEMMAS-USED
                                    (UNION-EQ
                                     (EXTRACT-DEPENDENCIES-FROM-HINTS
                                      HINTS)
                                     (ALL-FNNAMES TERM))))))
           (COND (PROVE-ANS NAME)
                 (T NIL)))
       (PROGN (ITERATE FOR X IN HINT-VARIABLE-ALIST
                       DO (SET (CADR X) (CADDDR X)))
              (SETQ LOCAL-DISABLEDP-HASH-FLAG NIL))))))

(DEFEVENT SET-STATUS (NAME NAMES ALIST)
  (EVENT-COMMAND
   (LIST 'SET-STATUS NAME NAMES ALIST)
   (LET ((SET-STATUS-DEPENDENTS NIL)
         (SET-STATUS-DISABLE-NAMES NIL)
         (SET-STATUS-ENABLE-NAMES NIL)
         NAMES-CASE
         LST
         BOOT-STRAP-STATUS
         DEFN-STATUS
         *1*DEFN-STATUS
         ADD-AXIOM-STATUS
         ADD-SHELL-STATUS
         PROVE-LEMMA-STATUS
         CONSTRAIN-STATUS
         FUNCTIONALLY-INSTANTIATE-STATUS)
        (MATCH! (CHK-ACCEPTABLE-SET-STATUS NAME NAMES ALIST)
                (LIST NAME NAMES ALIST))
        (MAKE-EVENT NAME (LIST 'SET-STATUS NAME NAMES ALIST))
        (SETQ LST
              (COND ((EQ NAMES T)
                     (SETQ NAMES-CASE 'TEE)
                     (ITERATE FOR X IN CHRONOLOGY
                              APPEND (CONS X (GET X 'SATELLITES))))
                    ((THEORYP NAMES)
                     (SETQ NAMES-CASE 'THEORY)
                     (COND ((EQ NAMES 'GROUND-ZERO)
                            (GET 'GROUND-ZERO 'SATELLITES))
                           (T (CADDR (GET NAMES 'EVENT)))))
                    ((NULL NAMES)
                     (SETQ NAMES-CASE 'LIST)
                     NIL)
                    ((AND (CONSP NAMES)
                          (SYMBOLP (CDR NAMES))
                          (GET (CDR NAMES) 'EVENT))
                     (LET ((NAME1 (CAR NAMES))
                           (NAME2 (CDR NAMES)))
                          (SETQ NAMES-CASE 'INTERVAL)
                          (COND
                           ((MEMBER-EQ NAME1 (MEMBER-EQ NAME2 CHRONOLOGY))
                            (OUR-SWAP NAME1 NAME2)))
                          (ITERATE FOR X IN (MEMBER-EQ NAME1 CHRONOLOGY)
                                   APPEND
                                   (CONS X (GET X 'SATELLITES))
                                   UNTIL (EQ X NAME2))))
                    (T (SETQ NAMES-CASE 'LIST)
                       NAMES)))
        (SETQ BOOT-STRAP-STATUS (GET-STATUS 'BOOT-STRAP ALIST))
        (SETQ DEFN-STATUS (GET-STATUS 'DEFN ALIST))
        (SETQ *1*DEFN-STATUS (GET-STATUS '*1*DEFN ALIST))
        (SETQ ADD-AXIOM-STATUS (GET-STATUS 'ADD-AXIOM ALIST))
        (SETQ ADD-SHELL-STATUS (GET-STATUS 'ADD-SHELL ALIST))
        (SETQ PROVE-LEMMA-STATUS (GET-STATUS 'PROVE-LEMMA ALIST))
        (SETQ CONSTRAIN-STATUS (GET-STATUS 'CONSTRAIN ALIST))
        (SETQ FUNCTIONALLY-INSTANTIATE-STATUS
              (GET-STATUS 'FUNCTIONALLY-INSTANTIATE ALIST))

; A complete list of the event names is shown below.  An x appearing
; beside an event command means that SET-STATUS may set the status of
; such an event.  We claim that those events not marked have the
; property that the status setting (of the event name and all of its
; satellites) has no effect on the behavior of the system.

; add-axiom                    x
; add-shell                    x
; boot-strap                   x
; constrain                    x
; dcl
; defn                         x
; deftheory
; functionally-instantiate     x
; prove-lemma                  x
; set-status
; toggle
; toggle-defined-functions

        (ITERATE FOR X IN LST
                 DO
                 (LET ((EV (OR (GET X 'EVENT)
                               (GET (MAIN-EVENT-OF X) 'EVENT))))
                      (CASE (CAR EV)
                            (ADD-AXIOM
                             (SET-STATUS1 X ADD-AXIOM-STATUS))
                            (ADD-SHELL
                             (SET-STATUS1 X ADD-SHELL-STATUS))
                            (BOOT-STRAP
                             (SET-STATUS1 X BOOT-STRAP-STATUS))
                            (CONSTRAIN
                             (SET-STATUS1 X CONSTRAIN-STATUS))
                            (DEFN
                             (SET-STATUS1 X (IF (EQ X (CADR EV))
                                                DEFN-STATUS
                                                *1*DEFN-STATUS)))
                            (FUNCTIONALLY-INSTANTIATE
                             (SET-STATUS1 X FUNCTIONALLY-INSTANTIATE-STATUS))
                            (PROVE-LEMMA
                             (SET-STATUS1 X PROVE-LEMMA-STATUS))
                            (OTHERWISE NIL))))
        
        (ITERATE FOR NAME IN SET-STATUS-ENABLE-NAMES
                 DO
                 (ADD-FACT NIL 'DISABLED-LEMMAS
                           (CONS NAME (CONS MAIN-EVENT-NAME NIL))))
        (ITERATE FOR NAME IN SET-STATUS-DISABLE-NAMES
                 DO
                 (ADD-FACT NIL 'DISABLED-LEMMAS
                           (CONS NAME (CONS MAIN-EVENT-NAME T))))
        (DEPEND NAME
                (CASE
                 NAMES-CASE
                 (TEE SET-STATUS-DEPENDENTS)
                 (THEORY (LIST NAMES))
                 (LIST NAMES)
                 (OTHERWISE (ADD-TO-SET (CAR NAMES)
                                        (ADD-TO-SET (CDR NAMES)
                                                    SET-STATUS-DEPENDENTS)))))
        NAME)))

(DEFEVENT TOGGLE (NAME OLDNAME FLG)
  (EVENT-COMMAND
   (LIST (QUOTE TOGGLE) NAME OLDNAME FLG)
   (MATCH! (CHK-ACCEPTABLE-TOGGLE NAME OLDNAME FLG)
           (LIST NAME OLDNAME FLG))
   (MAKE-EVENT NAME (LIST (QUOTE TOGGLE) NAME OLDNAME FLG))
   (ADD-FACT NIL (QUOTE DISABLED-LEMMAS)
             (CONS OLDNAME (CONS NAME FLG)))
   (DEPEND NAME (LIST (MAIN-EVENT-OF OLDNAME)))
   NAME))

(DEFEVENT TOGGLE-DEFINED-FUNCTIONS (NAME FLG)
  (EVENT-COMMAND
   (LIST (QUOTE TOGGLE-DEFINED-FUNCTIONS) NAME FLG)
   (MATCH! (CHK-ACCEPTABLE-TOGGLE-DEFINED-FUNCTIONS NAME FLG)
           (LIST NAME FLG))
   (MAKE-EVENT NAME (LIST (QUOTE TOGGLE-DEFINED-FUNCTIONS) NAME FLG))
   (ADD-FACT NIL (QUOTE DEFINED-FUNCTIONS-TOGGLED)
             (CONS NAME FLG))
   NAME))

(DEFEVENT UBT (&OPTIONAL N)
  (PROGN
   (CHK-COMMAND-STATUS NIL)
   (LET (UNDONE-EVENTS
         (COMMAND-STATUS-FLG T))
        (COND ((NOT (BOUNDP 'CHRONOLOGY))
               (ER SOFT NIL |You| |should| |do| |a| BOOT-STRAP |or|
                   NOTE-LIB |before| |attempting| |to| |undo| |events| EXCL))
              ((NULL N) (SETQ N (CAR CHRONOLOGY)))
              ((NUMBERP N)
               (IF (AND (>= N 0)
                        (< N (LENGTH CHRONOLOGY)))
                   (SETQ N (NTH N CHRONOLOGY))
                   (ER SOFT (N (LEN (LENGTH CHRONOLOGY))) |An| |integer|
                       |argument| |to| UBT |,| |such| |as| (!ppr n nil) |,|
                       |must| |be| |at| |least| |0| |but| |less| |than| |the|
                       |number| |of| |events| |,| |which| |is| |currently|
                       (!PPR LEN (QUOTE |.|))))))
        (SETQ UNDONE-EVENTS (UNDO-BACK-THROUGH-FN N))
        (PUSHU)
        N)))

(DEFMACRO COMMENT (&REST REST)
  (DECLARE (IGNORE REST))
  T)

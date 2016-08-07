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

(DEFMACRO ADD-SUB-FACT-BODY (&REST X) (GENERATE-ADD-SUB-FACT1 X))

(DEFUN GENERATE-ADD-FACT-PART (ALIST)
  (LET (!SINGLE-PROPS! !ADDITIVE-PROPS! !ADDITIVE-VARS! !SINGLE-VARS!)
    (SETQ !SINGLE-PROPS! (ITERATE FOR X IN ALIST
                                  WHEN (AND (EQ (CADR X) (QUOTE SINGLE))
                                            (EQ (CADDR X) (QUOTE PROPERTY)))
                                  COLLECT (CAR X)))
    (SETQ !ADDITIVE-PROPS!
          (ITERATE FOR X IN ALIST WHEN (AND (EQ (CADR X) (QUOTE ADDITIVE))
                                            (EQ (CADDR X) (QUOTE PROPERTY)))
                   COLLECT (CAR X)))
    (SETQ !ADDITIVE-VARS!
          (ITERATE FOR X IN ALIST WHEN (AND (EQ (CADR X) (QUOTE ADDITIVE))
                                            (EQ (CADDR X) (QUOTE VARIABLE)))
                   COLLECT (CAR X)))
    (SETQ !SINGLE-VARS!
          (ITERATE FOR X IN ALIST WHEN (AND (EQ (CADR X) (QUOTE SINGLE))
                                            (EQ (CADDR X) (QUOTE VARIABLE)))
                   COLLECT (CAR X)))
    `(PROGN (COND
             ((NULL VAL)
              (ERROR1 (PQUOTE (PROGN |Attempt| |to| |do| |an| ADD-FACT
                                     |with| |value| (!PPR NIL NIL)
                                     |on| (!PPR PROP NIL) |and|
                                     (!PPR ATM (QUOTE |.|))))
                      `((PROP . ,PROP) (ATM . ,ATM))
                      (QUOTE HARD))))
            (CASE PROP
                  (,!SINGLE-PROPS!
                   (COND
                    ((GET ATM PROP)
                     (ERROR1 (PQUOTE (PROGN |Attempt| |to| |smash| |existing|
                                            SINGLE PROPERTY |fact| |hung|
                                            |under| (!PPR PROP NIL) |of|
                                            (!PPR ATM (QUOTE |.|))))
                             `((PROP . ,PROP) (ATM . ,ATM))
                             (QUOTE HARD))))
                   (PUT1 ATM VAL PROP))
                  (,!ADDITIVE-PROPS! (PUT1 ATM (CONS VAL (GET ATM PROP))
                                           PROP))
                  (DCELL (COND
                          ((FBOUNDP ATM)
                           (ERROR1 (PQUOTE (PROGN |Attempt| |to|
                                                  |smash|
                                                  |existing|
                                                  LISP
                                                  |definition|
                                                  |cell| |of| |the|
                                                  |function|
                                                  (!PPR ATM (QUOTE |.|))))
                                   `((ATM . ,ATM))
                                   (QUOTE HARD)))
                          (T (PUTD1 ATM VAL))))
                  (,!ADDITIVE-VARS!
                   (OR (NULL ATM)
                       (ERROR1 (PQUOTE (PROGN ADD-SUB-FACT |must|
                                              |not| |be| |called| |with|
                                              PROP |set| |to| |a|
                                              |variable| |name|
                                              |while| ATM |is|
                                              |non-NIL| |because| |it|
                                              |confuses| |the| |undo|
                                              |information| |.|))
                               NIL
                               (QUOTE HARD)))
                   (SET PROP (CONS VAL (SYMBOL-VALUE PROP))))
                  (,!SINGLE-VARS!
                   (OR (NULL ATM)
                       (ERROR1 (PQUOTE (PROGN ADD-SUB-FACT |must|
                                              |not| |be| |called| |with|
                                              PROP |set| |to| |a|
                                              |variable| |name|
                                              |while| ATM |is|
                                              |non-NIL| |because| |it|
                                              |confuses| |the| |undo|
                                              |information| |.|))
                               NIL
                               (QUOTE HARD)))
                   (COND
                    ((SYMBOL-VALUE PROP)

;   This used to be a BOUNDP check but when I added a SINGLE VARIABLE
;   I discovered that INIT-LIB initializes all variables, SINGLE or
;   ADDITIVE, to NIL.  So now I merely check that the current value is
;   NIL and if so permit it to be smashed.

                     (ERROR1 (PQUOTE (PROGN |Attempt| |to| |smash|
                                            |existing| SINGLE
                                            VARIABLE |,|
                                            (!PPR PROP (QUOTE |.|))))
                             `((PROP . ,PROP))
                             (QUOTE HARD))))
                   (SET PROP VAL))
                  (OTHERWISE
                   (ERROR1 (PQUOTE (PROGN ADD-SUB-FACT |has| |been| |called|
                                          |on|
                                          |a| |property| |or| |variable| |name|
                                          |,| |namely| (!PPR PROP (QUOTE |,|))
                                          |that| |was| |not| |declared| EXCL))
                           `((PROP . ,PROP))
                           (QUOTE HARD)))))))

(DEFUN GENERATE-ADD-SUB-FACT1 (ALIST)
  (COND
   ((AND (ITERATE FOR X IN (QUOTE (IDATE SATELLITES MAIN-EVENT EVENT SEXPR
                                         LOCAL-UNDO-TUPLES))
                  ALWAYS (AND (SETQ TEMP-TEMP (ASSOC-EQ X ALIST))
                              (MATCH (CDR TEMP-TEMP)
                                     (LIST (QUOTE HIDDEN)
                                           (QUOTE PROPERTY)))))
         (MATCH (ASSOC-EQ (QUOTE CHRONOLOGY) ALIST)
                (LIST (QUOTE CHRONOLOGY) (QUOTE HIDDEN) (QUOTE VARIABLE)))
         (ITERATE
          FOR X IN ALIST
          NEVER (AND (EQ (CADR X) (QUOTE HIDDEN))
                     (NOT (MEMBER-EQ (CAR X)
                                     (QUOTE (IDATE SATELLITES
                                                   MAIN-EVENT EVENT SEXPR
                                                   LOCAL-UNDO-TUPLES
                                                   CHRONOLOGY)))))))
    (SUB-PAIR
     (QUOTE (!LIB-PROPS! !LIBVARS! !SUBTRACT-FACT! !UNDO-TUPLE!
                         !ADD-FACT!))
     (LIST (ITERATE FOR X IN ALIST
                    WHEN (AND (EQ (CADDR X) (QUOTE PROPERTY))
                              (NOT (EQ (CAR X) (QUOTE SEXPR))))
                    COLLECT (CAR X))
           (ITERATE FOR X IN ALIST WHEN (EQ (CADDR X) (QUOTE VARIABLE))
                    COLLECT (CAR X))
           (GENERATE-SUB-FACT-PART ALIST)
           (GENERATE-UNDO-TUPLE-PART ALIST)
           (GENERATE-ADD-FACT-PART ALIST))
     (QUOTE
      (COND
       (INIT
        (INIT-LIB (QUOTE !LIB-PROPS!) (QUOTE !LIBVARS!)))
       (TUPLE !SUBTRACT-FACT!)
       (T
        (COND
         ((OR
           (EQ MAIN-EVENT-NAME (QUOTE GROUND-ZERO))
           (AND
            (OR (EQ MAIN-EVENT-NAME ATM)
                (AND ATM
                     (EQ MAIN-EVENT-NAME
                         (GET ATM
                              (QUOTE MAIN-EVENT)))))
            (NOT (EQ PROP (QUOTE DCELL)))))
          NIL)
         (T (PUT1 MAIN-EVENT-NAME
                  (CONS !UNDO-TUPLE!
                        (GET MAIN-EVENT-NAME
                             (QUOTE LOCAL-UNDO-TUPLES)))
                  (QUOTE LOCAL-UNDO-TUPLES))))
        !ADD-FACT!)))))
   (T (ERROR "~%The user must declare all the built-in ~
             event level properties and variables as ~
             HIDDEN and must not declare any other HIDDEN data."))))

(DEFUN GENERATE-SUB-FACT-PART (ALIST)
  (SUBST
   (CONS (QUOTE CASE)
         (CONS (QUOTE PROP)
               (NCONC1 (ITERATE FOR X IN ALIST
                                WHEN (EQ (CADR X) (QUOTE ADDITIVE))
                                COLLECT (LIST (CAR X) (CADDDR X)))
                       (QUOTE (OTHERWISE NIL)))))
   (QUOTE !VAL-NAME!)
   (QUOTE (LET (ATM PROP VAL-NAME VAL TEMP)
            (COND
             ((ATOM TUPLE)
              (SETQ PROP TUPLE)
              (SET PROP NIL))
             ((ATOM (CDR TUPLE))
              (SETQ PROP (CAR TUPLE))
              (SETQ ATM (CDR TUPLE))
              (COND
               ((EQ PROP (QUOTE DCELL))
                (PUTD1 ATM NIL))
               (T (PUT1 ATM NIL PROP))))
             (T (SETQ PROP (CAR TUPLE))
                (SETQ ATM (CADR TUPLE))
                (SETQ VAL-NAME (CDDR TUPLE))

;   In the following (and in the LET above) TEMP was introduced to skirt a
;   bug in the Release 5.0 compiler.

                (SETQ TEMP (ITERATE FOR VAL IN (COND
                                                ((NULL ATM)
                                                 (SYMBOL-VALUE PROP))
                                                (T (GET ATM PROP)))
                                    WHEN (EQUAL !VAL-NAME! VAL-NAME)
                                    DO (RETURN VAL)))
                (COND
                 ((NULL TEMP)
                  (ERROR1 (PQUOTE (PROGN |In| |undoing| |an| ADDITIVE
                                         ADD-FACT |on| (!PPR ATM NIL)
                                         |and| (!PPR PROP NIL) |the| |value|
                                         |to| |be| |removed| |was| |not|
                                         |found| |.|))
                          `((PROP . ,PROP) (ATM . ,ATM))
                          (QUOTE WARNING))))
                (COND
                 ((NULL ATM)
                  (SET PROP (REMOVE1 TEMP (SYMBOL-VALUE PROP))))
                 (T (PUT1 ATM (REMOVE1 TEMP
                                       (GET ATM PROP)) PROP)))))
            NIL))))

(DEFUN GENERATE-UNDO-TUPLE-PART (ALIST)
  (LET (!ADDITIVE! !---ADDITIVE-LST---! !SINGLE-VARS!)
    (SETQ !ADDITIVE! (QUOTE (!ADDITIVE-TYPE! (CONS PROP
                                                   (CONS ATM
                                                         !VAL-NAME!)))))
    (SETQ !---ADDITIVE-LST---!
          (ITERATE FOR X IN ALIST WHEN (EQ (CADR X) (QUOTE ADDITIVE))
                   COLLECT (SUB-PAIR (QUOTE (!ADDITIVE-TYPE! !VAL-NAME!))
                                     (LIST (CAR X) (CADDDR X))
                                     !ADDITIVE!)))
    (SETQ !SINGLE-VARS! (ITERATE FOR X IN ALIST
                                 WHEN (AND (EQ (CADR X) (QUOTE SINGLE))
                                           (EQ (CADDR X) (QUOTE VARIABLE)))
                                 COLLECT (CAR X)))
    `(CASE PROP ,@!---ADDITIVE-LST---!
           (,!SINGLE-VARS! PROP)
           (DCELL (CONS (QUOTE DCELL) ATM))
           (OTHERWISE (CONS PROP ATM)))))


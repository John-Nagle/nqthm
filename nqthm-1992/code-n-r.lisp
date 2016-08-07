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

(DEFUN NEGATE (TERM)
  (COND ((FALSE-NONFALSEP TERM)
         (COND (DEFINITELY-FALSE TRUE) (T FALSE)))
        ((VARIABLEP TERM)
         (LIST (QUOTE NOT) TERM))
        (T (CASE (FFN-SYMB TERM)
                 (NOT (COND ((OUR-BOOLEAN (FARGN TERM 1))
                             (FARGN TERM 1))
                            (T (FCONS-TERM* (QUOTE IF) (FARGN TERM 1)
                                            TRUE FALSE))))
                 (AND (DISJOIN2 (NEGATE (FARGN TERM 1))
                                (NEGATE (FARGN TERM 2))
                                NIL))
                 (OR (CONJOIN2 (NEGATE (FARGN TERM 1))
                               (NEGATE (FARGN TERM 2)) NIL))
                 (OTHERWISE
                  (FCONS-TERM* (QUOTE NOT) TERM))))))

(DEFUN NEGATE-LIT (TERM)
  (COND ((FALSE-NONFALSEP TERM)
         (COND (DEFINITELY-FALSE TRUE) (T FALSE)))
        ((VARIABLEP TERM)
         (FCONS-TERM* (QUOTE NOT) TERM))
        ((EQ (FFN-SYMB TERM) (QUOTE NOT))
         (FARGN TERM 1))
        (T (FCONS-TERM* (QUOTE NOT) TERM))))

(DEFUN NEW-TAMEP-SUBST-VAR (ORIG-TERM)
  (ITERATE FOR I FROM NEW-VAR-INDEX
           WITH NEW-VAR
           WHEN (NOT (DUMB-OCCUR (SETQ NEW-VAR (VVV- I))
                                 ORIG-TERM))
           DO (PROGN (SETQ NEW-VAR-INDEX (1+ I))
                     (RETURN NEW-VAR))))

(DEFUN NEXT-AVAILABLE-TYPE-NO NIL
  (LET (TYPE-NO)
    (SETQ TYPE-NO
          (ITERATE FOR I FROM 0
                   WHEN (NOT (ITERATE FOR PAIR IN SHELL-ALIST
                                      THEREIS (EQUAL (CDR PAIR) I)))
                   DO (RETURN I)))
    (COND ((> TYPE-NO 30)
           (ER HARD NIL |Too| |many| |shells| EXCL |Because| |of| |our| |use|
               |of| |32-bit| |words| |to| |represent| |sets| |of| |shell|
               |types| |,| |the| |need| |to| |reserve| |one| |bit| |for|
               |internal| |use| |,| |and| |the| |existence| |of| 31
               |previously| |defined| |shells| |,| |we| |cannot| |accept|
               |further| ADD-SHELL |commands| |.|)))
    TYPE-NO))

(DEFUN NO-DUPLICATESP (L)
  (ITERATE FOR TAIL ON L NEVER (MEMBER-EQ (CAR TAIL) (CDR TAIL))))

(DEFUN NON-RECURSIVE-DEFNP (FNNAME)

;   We use the fact that this AND returns the SDEFN!

  (AND (NOT (DISABLEDP FNNAME))
       (NOT (GET FNNAME (QUOTE INDUCTION-MACHINE)))
       (GET FNNAME (QUOTE SDEFN))))

(DEFUN NORMALIZE-IFS (TERM TRUE-TERMS FALSE-TERMS IFF-FLG)
  (LET (T1 T2 T3 T11 T12 T13 BAD-ARG)
    (COND ((VARIABLEP TERM)
           (COND ((MEMBER-EQ TERM FALSE-TERMS) FALSE)
                 ((AND IFF-FLG (MEMBER-EQ TERM TRUE-TERMS)) TRUE)
                 (T TERM)))
          ((FQUOTEP TERM)
           (COND ((AND IFF-FLG (NOT (EQ (CADR TERM) *1*F))) TRUE)
                 (T TERM)))
          ((MATCH TERM (IF T1 T2 T3))
           (SETQ T1 (NORMALIZE-IFS T1 TRUE-TERMS FALSE-TERMS T))
           (COND ((EQUAL T1 TRUE)
                  (NORMALIZE-IFS T2 TRUE-TERMS FALSE-TERMS IFF-FLG))
                 ((OR (EQUAL T1 FALSE) (MEMBER-EQUAL T1 FALSE-TERMS))
                  (NORMALIZE-IFS T3 TRUE-TERMS FALSE-TERMS IFF-FLG))
                 ((MATCH T1 (IF T11 T12 T13))
                  (NORMALIZE-IFS
                   (FCONS-TERM* (QUOTE IF)
                                T11
                                (FCONS-TERM* (QUOTE IF) T12 T2 T3)
                                (FCONS-TERM* (QUOTE IF) T13 T2 T3))
                   TRUE-TERMS FALSE-TERMS IFF-FLG))
                 (T (SETQ T2 (NORMALIZE-IFS T2
                                            (CONS T1 TRUE-TERMS)
                                            FALSE-TERMS IFF-FLG))
                    (SETQ T3 (NORMALIZE-IFS T3 TRUE-TERMS
                                            (CONS T1 FALSE-TERMS) IFF-FLG))
                    (COND ((EQUAL T2 T3) T2)
                          ((AND (OUR-BOOLEAN T1)
                                (EQUAL T2 TRUE)
                                (AND (FALSE-NONFALSEP T3)
                                     DEFINITELY-FALSE))
                           T1)
                          (T (FCONS-TERM* (QUOTE IF) T1 T2 T3))))))
          (T (SETQ TERM
                   (CONS-TERM (CAR TERM)
                              (ITERATE FOR ARG IN (FARGS TERM)
                                       COLLECT (NORMALIZE-IFS ARG
                                                              TRUE-TERMS
                                                              FALSE-TERMS
                                                              NIL))))
             (COND ((MATCH TERM (EQUAL T1 T2))
                    (COND ((EQUAL T1 T2) (SETQ TERM TRUE))
                          ((NOT-IDENT T1 T2) (SETQ TERM FALSE)))))
             (COND ((FQUOTEP TERM) TERM)
                   ((SETQ BAD-ARG (ITERATE FOR ARG IN (FARGS TERM)
                                           WHEN (MATCH ARG
                                                       (IF T1 T2 T3))
                                           DO (RETURN ARG)))
                    (FCONS-TERM* (QUOTE IF)
                                 T1
                                 (NORMALIZE-IFS
                                  (SUBST-EXPR T2 BAD-ARG TERM)
                                  (CONS T1 TRUE-TERMS)
                                  FALSE-TERMS
                                  IFF-FLG)
                                 (NORMALIZE-IFS
                                  (SUBST-EXPR T3 BAD-ARG TERM)
                                  TRUE-TERMS
                                  (CONS T1 FALSE-TERMS)
                                  IFF-FLG)))
                   ((MEMBER-EQUAL TERM FALSE-TERMS) FALSE)
                   ((MEMBER-EQUAL TERM TRUE-TERMS)
                    (COND (IFF-FLG TRUE)
                          ((OUR-BOOLEAN TERM) TRUE)
                          (T TERM)))
                   (T TERM))))))

(DEFUN NOT-IDENT (TERM1 TERM2)
  (COND ((AND (QUOTEP TERM1) (QUOTEP TERM2) (NOT (EQUAL TERM1 TERM2)))
         T)
        ((OR (AND (BTM-OBJECTP TERM1) (SHELL-CONSTRUCTORP TERM2))
             (AND (BTM-OBJECTP TERM2) (SHELL-CONSTRUCTORP TERM1)))

;   Note, we do not even bother to check that they are of the same type, since
;   if they weren't they'd be unequal on type considerations alone.

         T)
        ((TS= 0 (TSLOGAND (TYPE-SET TERM1) (TYPE-SET TERM2))) T)
        ((SHELL-OCCUR TERM1 TERM2) T)
        ((SHELL-OCCUR TERM2 TERM1) T)
        (T NIL)))

(DEFUN NOT-TO-BE-REWRITTENP (TERM ALIST)

;   We assume TERM is a nonvariable nonQUOTEP and that
;   TERMS-TO-BE-IGNORED-BY-REWRITE contains no vars or QUOTEPs.  Let term' be
;   (SUBLIS-VAR ALIST TERM).  If term' is a member of
;   TERMS-TO-BE-IGNORED-BY-REWRITE we return term' else NIL.  We would like to
;   do the membership test without doing the substitution, but the maintenance
;   of QUOTE-normal form by SUBLIS-VAR complicates matters.  We first ask
;   whether the FFN-SYMB of TERM is the FFN-SYMB of any term to be ignored.  If
;   not, we return NIL.  Else we do the substitution and member check.

;   The correctness of this function is obvious in the case that we do the
;   substitution.  So suppose we return NIL without doing the substitution.
;   Suppose, contrary to correctness that term' is a member of the to be
;   ignored list.  Then term' is not a QUOTEP.  But in that case the FFN-SYMB
;   of term' is that of TERM and must have passed our initial test.

  (COND ((AND (ITERATE FOR X IN TERMS-TO-BE-IGNORED-BY-REWRITE
                       THEREIS (EQ (FFN-SYMB TERM) (FFN-SYMB X)))
              (MEMBER-EQUAL (SETQ TEMP-TEMP (SUBLIS-VAR ALIST TERM))
                            TERMS-TO-BE-IGNORED-BY-REWRITE))
         TEMP-TEMP)
        (T NIL)))

(DEFUN NOTE-LIB (FILE &OPTIONAL LOAD-COMPILED-CODE-FLG)
  (LET ((*READ-BASE* 10)
        (*READTABLE* (COPY-READTABLE NIL))
        FILE1 FILE2)
    (CHK-COMMAND-STATUS T)
    (PRINT-NQTHM-DISCLAIMER)
    (SETQ FILE1 (EXTEND-FILE-NAME FILE FILE-EXTENSION-LIB))
    (COND ((PROBE-FILE FILE1) NIL)
          (PETITIO-PRINCIPII
           (PRINEVAL (PQUOTE (PROGN CR CR |file| |not| |found| |:|
                                    (!PPR FILE '|.|)
                                    |skipping| |this| NOTE-LIB |.|))
                     (LIST (CONS 'FILE FILE1))
                     0 PROVE-FILE)
           (RETURN-FROM NOTE-LIB T))
          (T (ER SOFT (FILE1) |file| |not| |found:| (!PPR FILE1 '|.|))))
    (KILL-LIB)
    (LOAD FILE1)
    
    (SETQ LIB-FILE FILE1)
    (SETQ FILE2
          (EXTEND-FILE-NAME FILE
                            (COND (LOAD-COMPILED-CODE-FLG FILE-EXTENSION-BIN)
                                  (T FILE-EXTENSION-LISP))))
    (PROCLAIM-NQTHM-FILE FILE)
    (IF LOAD-COMPILED-CODE-FLG
        (OR (LOAD FILE2 :IF-DOES-NOT-EXIST NIL)
            (ER SOFT (FILE2) |You| |have| |supplied| |a| |non-NIL| |second|
                |argument| |to| NOTE-LIB |,| |indicating| |a| |desire| |to|
                |load| |a| |compiled| |file| |.| |However| |,| |an| |attempt|
                |to| |load| |the| |file| (!PPR FILE2 NIL) |has| |failed| |.|))
        (LOAD FILE2))
    (COND ((OR (NOT (BOUNDP (QUOTE LIB-VERSION)))
               (NOT (EQUAL LIB-VERSION THEOREM-PROVER-LIBRARY-VERSION)))
           (SETQ LIB-VERSION-TROUBLE T)
           (ERROR1 (QUOTE (PROGN |The| |library| |being| |loaded| |was|
                                 |created| |with| |a| |format| |different|
                                 |from| |the| |one| |appropriate| |for| |this|
                                 |version| |of| |the| |theorem-prover| |.|
                                 |you| |are| |advised| |to| |remake| |all| |of|
                                 |your| |libraries| |from| |scratch| |.|
                                 |it| |is| |possible| |that| |you| |will|
                                 |meet| |with| |nonsensical| |results| |by|
                                 |using| |the| |results| |of| |this| |call|
                                 |to| NOTE-LIB |.|))
                   NIL
                   (QUOTE WARNING))))
    (LIST FILE1 FILE2)))

(DEFUN NQTHM-READTABLE NIL

; NQTHM-READTABLE is the readtable that we use within PROVE-FILE to
; avoid the possibility of side effects during reading and to
; implement the Nqthm version of backquote.  For example, an obvious
; thing that would make Nqthm unsound is to read #.(setq true false).
; But we also need to worry about #,, user defined read macros, etc.
; We prohibit the use of #s syntax because constructors may have side
; effects.  In general, we prohibit reading characters that are not
; printing Ascii characters, excepting whitespace.  We even prohibit
; reading things that would do no harm in themselves (e.g., reading a
; character such as #\A or reading a complex) but for which we can
; imagine no sensible use in an Nqthm events file.

  (COND
   ((EQ NQTHM-READTABLE 'UNINITIALIZED)
    (LET ((*READTABLE* (COPY-READTABLE NIL)))
      (ITERATE FOR I BELOW CHAR-CODE-LIMIT 
               FOR CHAR = (CODE-CHAR I)
               DO
               (COND
                ((NULL (CHARACTERP CHAR)) NIL)
                (T
                 (COND
                  ((OR (MEMBER CHAR '(#\SPACE #\NEWLINE #\LINEFEED
                                      #\RETURN #\PAGE #\TAB))
                       (AND (MEMBER CHAR PRINTING-COMMON-LISP-CHARACTERS)
                            (NOT (MEMBER
                                  CHAR
                                  '(#\, ; The meanings of backquote and comma
                                    #\` ; vary from Lisp to Lisp.
                                    #\: ; Packages just mean trouble.
                                    #\| ; There is no need to slashify
                                    #\\ ; anything that would be legal.
                                    #\/ ; useful only for rationals.
                                    )))))
                   NIL)
                  (T

;  This leaves with their usual special meanings:
;  1.  Parentheses.
;  2.  String quotation (for file names).
;  3.  # syntax, but as severely restricted below.
;  4.  Semicolon for comments.
;  5.  Stuff for building numbers, including floating point.
;  6.  ' for quote, but no backquote.

                   (SET-MACRO-CHARACTER
                    CHAR
                    (FUNCTION (LAMBDA (STREAM CHAR)
                                      (DECLARE (IGNORE STREAM))
                                      (ER SOFT (CHAR)
                                          PROVE-FILE |does| |not| |handle| 
                                          |the| |character| (!PPR CHAR NIL)
                                          |.|))))))
                 (COND ((MEMBER CHAR
                                '(#\| ; comment
                                  #\o #\O ; octal
                                  #\b #\B ; binary
                                  #\x #\X ; hexadecimal
                                  #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                                  ; cannot touch these
                                  ))
                        NIL)
                       (T 
                        (SET-DISPATCH-MACRO-CHARACTER
                         #\#
                         CHAR
                         (FUNCTION
                          (LAMBDA (STREAM CHAR N) (DECLARE (IGNORE STREAM N))
                                  (ER SOFT ((X (PACK (LIST "#" CHAR))))
                                      |Nqthm's| |readtable| |does| |not| 
                                      |support| (!PPR X NIL)
                                      |syntax| |.|)))))))))
      (BACKQUOTE-SETTING 'NQTHM)
      (SETQ NQTHM-READTABLE *READTABLE*))))
  NQTHM-READTABLE)


(DEFUN NUMBERP? (TERM)
  (LET (TEMP)
    (SETQ TEMP (TYPE-SET TERM))
    (COND ((TS= TEMP TYPE-SET-NUMBERS)
           TRUE)
          ((NOT (TSLOGSUBSETP TYPE-SET-NUMBERS TEMP))
           FALSE)
          (T (FCONS-TERM*(QUOTE NUMBERP)
                         TERM)))))

(DEFUN OBJ-TABLE (TYPE-SET OBJ ID-IFF-LOC)
  (CASE OBJ
        (TRUE (COND ((TS= TYPE-SET TYPE-SET-TRUE) TRUE)
                    ((EQ ID-IFF-LOC (QUOTE ID)) NIL)
                    ((TSLOGSUBSETP TYPE-SET-FALSE TYPE-SET) NIL)
                    (T TRUE)))
        (FALSE (COND ((TS= TYPE-SET TYPE-SET-FALSE) FALSE)
                     (T NIL)))
        (? (COND ((TS= TYPE-SET TYPE-SET-FALSE) FALSE)
                 ((TS= TYPE-SET TYPE-SET-TRUE) TRUE)
                 ((EQ ID-IFF-LOC (QUOTE ID)) NIL)
                 ((TSLOGSUBSETP TYPE-SET-FALSE TYPE-SET) NIL)
                 (T TRUE)))
        (OTHERWISE
         (ER HARD (OBJ) |Unrecognized| REWRITE OBJ |,|
             (!PPR OBJ (QUOTE |.|))))))

(DEFUN OCCUR (TERM1 TERM2)
  (COND ((VARIABLEP TERM2)
         (EQ TERM1 TERM2))
        ((FQUOTEP TERM2)
         (COND ((QUOTEP TERM1)
                (COND ((INTEGERP (CADR TERM1))
                       (EVG-OCCUR-NUMBER (CADR TERM1) (CADR TERM2)))
                      ((AND (LEGAL-CHAR-CODE-SEQ (CADR TERM1))
                            (EQUAL (CDR (OUR-LAST (CADR TERM1))) 0))
                       (EVG-OCCUR-LEGAL-CHAR-CODE-SEQ (CADR TERM1)
                                                      (CADR TERM2)))
                      (T (EVG-OCCUR-OTHER (CADR TERM1)
                                          (CADR TERM2)))))
               (T NIL)))
        ((EQUAL TERM1 TERM2) T)
        (T (ITERATE FOR ARG IN (FARGS TERM2) THEREIS (OCCUR TERM1 ARG)))))

(DEFUN OCCUR-CNT (TERM1 TERM2)

;   Return a lower bound on the number of times TERM1 occurs in TERM2.  We do
;   not go inside of QUOTEs in TERM2.

  (COND ((EQUAL TERM1 TERM2) 1)
        ((VARIABLEP TERM2) 0)
        ((FQUOTEP TERM2) 0)
        (T (ITERATE FOR ARG IN (FARGS TERM2) SUM (OCCUR-CNT TERM1 ARG)))))

(DEFUN OCCUR-LST (X LST) (ITERATE FOR Y IN LST THEREIS (OCCUR X Y)))

(DEFUN ODDS (L)
  (COND ((OR (ATOM L)
             (ATOM (CDR L)))
         L)
        (T (CONS (CAR L)
                 (ODDS (CDDR L))))))

(DEFUN OK-SYMBOLP (X)

;   From 1974 till 1983 our theorem-prover was implemented in Interlisp-10, in
;   which it is the case that, to use Zetalisp terminology, there is only one
;   package, every symbolp is interned in it, and symbolp's with the same pname
;   are EQ.  In the theory in which our system proves theorems, two LITATOMS
;   are EQUAL if and only if they have the same UNPACKs.  If our theorem-prover
;   admitted, say, CHAOS:FOO and USER:FOO as LITATOMS, then it would have to
;   conclude that they are EQUAL because their UNPACKs are the same given our
;   representation of evgs.  However, our theorem-prover also is based upon the
;   assumption that two evg's are not EQUAL in the theory if they are not EQUAL
;   LISP objects.  Therefore, we have to reject some litatoms, such as
;   CHAOS:FOO.  The rejection occurs in TRANSLATE, where we check that every
;   SYMBOLP is OK-SYMBOLP.

;   The following definition of OK-SYMBOLP is not sufficient to avoid the
;   problems mentioned above if, in MACLISP, OBARRAY does not have its initial
;   value, or if someone has mangled the contents of the OBARRAY, or if someone
;   has engaged in REMOB's.  The following definition is not sufficient to
;   avoid the problems in Zetalisp if someone has set PACKAGE to something
;   other than USER, has engaged in malicious INTERNing, has smashed strings
;   of SYMBOLPs, etc., etc., etc.

  (MULTIPLE-VALUE-BIND
   (SYMBOL INTERNEDP)
   (FIND-SYMBOL (SYMBOL-NAME X) 'USER)
   (AND INTERNEDP (EQ X SYMBOL))))

(DEFUN ONE-WAY-UNIFY (TERM1 TERM2)
  (SETQ UNIFY-SUBST NIL)
  (ONE-WAY-UNIFY1 TERM1 TERM2))

(DEFUN ONE-WAY-UNIFY1 (TERM1 TERM2)
  (LET (OLD-ALIST)
    (SETQ COMMUTED-EQUALITY-FLG NIL)
    (SETQ OLD-ALIST UNIFY-SUBST)
    (COND ((ONE-WAY-UNIFY11 TERM1 TERM2) T)
          (T (SETQ UNIFY-SUBST OLD-ALIST) NIL))))

(DEFUN ONE-WAY-UNIFY11 (TERM1 TERM2)
  (COND ((VARIABLEP TERM1)
         (LET ((TMP1  (ASSOC-EQ TERM1 UNIFY-SUBST)))
           (COND (TMP1 (EQUAL (CDR TMP1) TERM2))
                 (T (SETQ UNIFY-SUBST (CONS (CONS TERM1 TERM2)
                                            UNIFY-SUBST))))))
        ((FQUOTEP TERM1)

;   Since TERM1 is the only one whose variables we instantiate, and is
;   constant, and all terms are in the QUOTE-normal form discussed in
;   CONS-TERM, these two terms unify iff they are EQUAL.

         (EQUAL TERM1 TERM2))
        ((VARIABLEP TERM2) NIL)
        ((EQ (FFN-SYMB TERM1) (FN-SYMB TERM2))
         (COND ((EQ (FFN-SYMB TERM1) (QUOTE EQUAL))
                (LET ((SAVED-UNIFY-SUBST UNIFY-SUBST))
                  (COND ((AND (ONE-WAY-UNIFY11 (FARGN TERM1 1) (FARGN TERM2 1))
                              (ONE-WAY-UNIFY11 (FARGN TERM1 2)
                                               (FARGN TERM2 2)))
                         T)
                        (T (SETQ UNIFY-SUBST SAVED-UNIFY-SUBST)
                           (AND (ONE-WAY-UNIFY11 (FARGN TERM1 2)
                                                 (FARGN TERM2 1))
                                (ONE-WAY-UNIFY11 (FARGN TERM1 1)
                                                 (FARGN TERM2 2))
                                (SETQ COMMUTED-EQUALITY-FLG T))))))
               (T (ITERATE FOR ARG1 IN (FARGS TERM1) AS ARG2 IN (SARGS TERM2)
                           ALWAYS (ONE-WAY-UNIFY11 ARG1 ARG2)))))
        (T NIL)))

(DEFUN ONEIFY (TERM TESTS)
  (COND ((VARIABLEP TERM) TERM)
        ((FQUOTEP TERM) TERM)
        (T (CASE (FFN-SYMB TERM)
                 (IF (LIST (QUOTE *2*IF)
                           (ONEIFY-TEST (FARGN TERM 1) TESTS)
                           (ONEIFY (FARGN TERM 2)
                                   (ONEIFY-ASSUME-TRUE (FARGN TERM 1) TESTS))
                           (ONEIFY (FARGN TERM 3)
                                   (ONEIFY-ASSUME-FALSE (FARGN TERM 1)
                                                        TESTS))))
                 (CONS (LIST (QUOTE CONS)
                             (ONEIFY (FARGN TERM 1) TESTS)
                             (ONEIFY (FARGN TERM 2) TESTS)))
                 (CAR (COND ((IMPLIES? TESTS (FCONS-TERM* (QUOTE LISTP)
                                                          (FARGN TERM 1)))
                             (LIST (QUOTE CAR)
                                   (ONEIFY (FARGN TERM 1) TESTS)))
                            (T (LIST (QUOTE *1*CAR)
                                     (ONEIFY (FARGN TERM 1) TESTS)))))
                 (CDR (COND ((IMPLIES? TESTS (FCONS-TERM*(QUOTE LISTP)
                                                         (FARGN TERM 1)))
                             (LIST (QUOTE CDR)
                                   (ONEIFY (FARGN TERM 1) TESTS)))
                            (T (LIST (QUOTE *1*CDR)
                                     (ONEIFY (FARGN TERM 1) TESTS)))))
                 ((LISTP EQUAL)
                  (LIST (QUOTE *2*IF)
                        (ONEIFY-TEST TERM TESTS)
                        (KWOTE *1*T)
                        (KWOTE *1*F)))
                 (OTHERWISE
                  (CONS (PACK (LIST PREFIX-FOR-FUNCTIONS (FFN-SYMB TERM)))
                        (ITERATE FOR ARG IN (FARGS TERM)
                                 COLLECT (ONEIFY ARG TESTS))))))))

(DEFUN ONEIFY-ASSUME-FALSE (TEST TESTS)
  (CONS (NEGATE-LIT TEST)
        TESTS))

(DEFUN ONEIFY-ASSUME-TRUE (TEST TESTS)
  (COND ((ATOM TEST)
         (CONS TEST TESTS))
        ((FQUOTEP TEST)
         (CONS TEST TESTS))
        ((AND (EQ (FFN-SYMB TEST)
                  (QUOTE IF))
              (EQUAL (FARGN TEST 3)
                     FALSE))
         (ONEIFY-ASSUME-TRUE (FARGN TEST 1)
                             (ONEIFY-ASSUME-TRUE (FARGN TEST 2)
                                                 TESTS)))
        (T (CONS TEST TESTS))))

(DEFUN ONEIFY-TEST (TERM TESTS)
  (COND ((VARIABLEP TERM)
         (LIST (QUOTE NOT)
               (LIST (QUOTE EQ)
                     TERM
                     (QUOTE *1*F))))
        ((FQUOTEP TERM)
         (NOT (EQ (CADR TERM) *1*F)))
        (T (CASE (FFN-SYMB TERM)
                 (IF (LIST (QUOTE *2*IF)
                           (ONEIFY-TEST (FARGN TERM 1)
                                        TESTS)
                           (ONEIFY-TEST (FARGN TERM 2)
                                        (ONEIFY-ASSUME-TRUE
                                         (FARGN TERM 1)
                                         TESTS))
                           (ONEIFY-TEST (FARGN TERM 3)
                                        (ONEIFY-ASSUME-FALSE
                                         (FARGN TERM 1)
                                         TESTS))))
                 (LISTP

;   We have to COPY-TREE the result of this SUB-PAIR so we do not have two EQ
;   occurrences of the arg in the X positions.

                  (COPY-TREE (SUB-PAIR
                              (QUOTE (X *1*SHELL-QUOTE-MARK))
                              (LIST (ONEIFY (FARGN TERM 1) TESTS)
                                    (KWOTE *1*SHELL-QUOTE-MARK))
                              (QUOTE (*2*IF (CONSP X)
                                            (NOT (EQ (CAR X)
                                                     *1*SHELL-QUOTE-MARK))
                                            NIL)))))
                 (EQUAL (COND ((AND (QUOTEP (FARGN TERM 1))
                                    (SYMBOLP (CADR (FARGN TERM 1))))
                               (LIST (QUOTE EQ)
                                     (ONEIFY (FARGN TERM 2)
                                             TESTS)
                                     (FARGN TERM 1)))
                              ((AND (QUOTEP (FARGN TERM 2))
                                    (SYMBOLP (CADR (FARGN TERM 2))))
                               (LIST (QUOTE EQ)
                                     (ONEIFY (FARGN TERM 1)
                                             TESTS)
                                     (FARGN TERM 2)))
                              (T (LIST (QUOTE EQUAL)
                                       (ONEIFY (FARGN TERM 1)
                                               TESTS)
                                       (ONEIFY (FARGN TERM 2)
                                               TESTS)))))
                 (OTHERWISE
                  (LIST (QUOTE NOT)
                        (LIST (QUOTE EQ)
                              (ONEIFY TERM TESTS)
                              (QUOTE *1*F))))))))

(DEFUN OPTIMIZE-COMMON-SUBTERMS (FORM)
  (PROG (SUBTERMS COMMONSUBTERMS PATHS DECISIONS OCC OCC1 OCC2
                  VAR-ALIST PARTI DOUBLE-TERMS NEW-FORM
                  ISOLATED-CNT FIRST-CNT SECOND-CNT)

;   We are interested in evaluating certain LISP FORMs that are constructed out
;   of variables (i.e., SYMBOLPS (none of which begin with 2)), objects of the
;   form (QUOTE x) and FORMs which are proper lists beginning with SYMBOLPs
;   which are either *2*IF or which have LAMBDA spread definitions.  *2*IF
;   behaves as though it had the MACRO ((X Y Z) (COND (X Y) (T Z))).  We assume
;   that no function associated with any function symbol has any effect on the
;   LISP state.  We assume that no variable is bound to the SYMBOLP *1*X.  We
;   assume that there is no structure sharing among the non-QUOTE
;   subexpressions of FORM.

;   Under these hypotheses, we generate and return a LISP form which when
;   evaluated returns the the same value as would be returned by evaluating
;   FORM.  We intentionally ignore the fact that in LISP, if a variable is
;   bound to NOBIND, the evaluation of that variable causes an error.  This
;   does not happened in compiled code.

        (SETQ SUBTERMS (INTERESTING-SUBTERMS FORM))
        (SETQ COMMONSUBTERMS
              (ITERATE FOR TERM IN SUBTERMS
                       WHEN (ITERATE FOR TERM2 IN SUBTERMS
                                     THEREIS (AND (NOT (EQ TERM2 TERM))
                                                  (EQUAL TERM2 TERM)))
                       COLLECT TERM))
        (COND ((NULL COMMONSUBTERMS)
               (RETURN FORM)))
        (SETQ PARTI (PARTITION COMMONSUBTERMS))
        (SETQ COMMONSUBTERMS
              (ITERATE FOR PART IN PARTI
                       UNLESS (ITERATE FOR PART2 IN PARTI
                                       THEREIS (PATH-POT-SUBSUMES PART2 PART))
                       APPEND PART))
        (SETQ PATHS (ITERATE FOR P IN (ALL-PATHS FORM)
                             COLLECT (REVERSE (CDR P))))

;   For each term that occurs more than once in FORM, we calculate just how
;   that occurrence occurs on the paths through the FORM.  Given a path, we say
;   the term occurs ISOLATED if no other EQUAL term occurs on the path.  We say
;   the term appears FIRST on the path if some EQUAL term follows it but no
;   EQUAL term precedes it.  We say the term appears SECOND on the path if it
;   occurs on the path but the occurrence is not ISOLATED and is not FIRST,
;   i.e., there is some EQUAL term that has a preceding occurrence on the path.

        (ITERATE FOR TERM IN COMMONSUBTERMS DO
                 (PROGN
                   (SETQ ISOLATED-CNT 0)
                   (SETQ FIRST-CNT 0)
                   (SETQ SECOND-CNT 0)
                   (ITERATE FOR PATH IN PATHS
                            WHEN (SETQ OCC (MEMBER-EQ TERM PATH)) DO
                            (PROGN
                              (SETQ OCC1 (MEMBER-EQUAL TERM PATH))
                              (SETQ OCC2 (MEMBER-EQUAL TERM (CDR OCC)))
                              (COND ((AND (EQ OCC OCC1) (NULL OCC2))
                                     (SETQ ISOLATED-CNT (1+ ISOLATED-CNT)))
                                    ((EQ OCC OCC1) (SETQ FIRST-CNT
                                                         (1+ FIRST-CNT)))
                                    (T (SETQ SECOND-CNT (1+ SECOND-CNT))))))

;   For each common subterm, we now decide what to replace the term with.
;   There are 5 alternatives.

;   1.  (SET) Replace the term with (SETQ (v term) term) where (v term) is a
;   SYMBOLP beginning with 2 and such that for all non-EQUAL common subterms s
;   and t of FORM, (v t) is not (v s).

;   2.  (VAR) Replace term with (v term).

;   3.  (TEST) Replace term with (*2*IF (EQ (v term) *1*X) term (v term)).

;   4.  (TEST-AND-SET) Replace term with
;        (*2*IF (EQ (v term) *1*X) (SETQ (v term) term) (v term)).

;   5.  Do nothing.

                   (COND ((> FIRST-CNT 0)
                          (COND ((> SECOND-CNT 0)
                                 (SETQ DECISIONS
                                       (CONS (CONS TERM
                                                   (QUOTE TEST-AND-SET))
                                             DECISIONS)))
                                (T (SETQ DECISIONS
                                         (CONS (CONS TERM (QUOTE SET))
                                               DECISIONS)))))
                         ((> SECOND-CNT 0)
                          (COND ((> ISOLATED-CNT 0)
                                 (SETQ DECISIONS (CONS (CONS TERM (QUOTE TEST))
                                                       DECISIONS)))
                                (T

;   This is the only decision that deserves serious consideration.  All of the
;   other decisions obviously result in correct behavior.  Here, we know that
;   the term always occurs second.  Thus we are guaranteed that on every path
;   to term, an equal term will have previously been evaluated.  For each such
;   path, some EQUAL term will have a FIRST occurrence and every term that is
;   ever first is always SET or TEST-AND-SET.

                                 (SETQ DECISIONS (CONS (CONS TERM (QUOTE VAR))
                                                       DECISIONS)))))
                         (T NIL))))

;   We now construct a list of the common subterms, omitting EQUAL
;   duplications.  We wish to associate a unique variable *2*TEMPi, for some i,
;   with all EQUAL common subterms.

        (SETQ DOUBLE-TERMS (ITERATE FOR D IN DECISIONS WITH ITERATE-ANS DO
                                    (SETQ ITERATE-ANS
                                          (ADD-TO-SET (CAR D) ITERATE-ANS))
                                    FINALLY (RETURN ITERATE-ANS)))
        (SETQ VAR-ALIST
              (ITERATE FOR D IN DOUBLE-TERMS AS I FROM 1
                       COLLECT (CONS D (PACK (LIST PREFIX-FOR-PROG-VARS
                                                   (QUOTE TEMP)
                                                   I)))))

;   Using DOUBLE-TERMS and VAR-ALIST, COMMON-SWEEP now carries out the
;   DECISIONS.

        (SETQ NEW-FORM (COMMON-SWEEP FORM))
        (RETURN (LIST (QUOTE LET)
                      (ITERATE FOR PAIR IN VAR-ALIST
                               COLLECT (LIST (CDR PAIR) (QUOTE (QUOTE *1*X))))
                      NEW-FORM))))


(DEFUN OUR-EXPLODEN (SYM)
  (LET ((S (SYMBOL-NAME SYM)))
    (ITERATE FOR I FROM 0 TO (1- (LENGTH S))
             COLLECT (CHAR-CODE (CHAR S I)))))

(DEFUN OUR-FLATC (X)
  (COND ((STRINGP X) (+ 2 (LENGTH X)))
        ((SYMBOLP X) (LENGTH (SYMBOL-NAME X)))
        ((INTEGERP X) (OUR-FLATC-NUMBER X))
        (T (LET ((*PRINT-BASE* 10)
                 (*PRINT-PRETTY* NIL)
                 (*PRINT-RADIX* NIL)
                 (*PRINT-LEVEL* NIL)
                 (*PRINT-LENGTH* NIL)
                 (*PRINT-CASE* :UPCASE))
             (LENGTH (FORMAT NIL "~A" X))))))

(DEFUN OUR-FLATC-NUMBER (N)
  (COND ((< N 0) (1+ (OUR-FLATC-NUMBER (- N))))
        ((< N 10) 1)
        (T (1+ (OUR-FLATC-NUMBER (FLOOR (/ N 10)))))))

(DEFUN OUR-GETCHARN (X N)
  (CHAR-CODE (CHAR (SYMBOL-NAME X) (1- N))))

(DEFUN OUR-LINEL (FILE N) FILE
  (COND ((INTEGERP N) (PROG1 LINEL-VALUE (SETQ LINEL-VALUE N)))
        (T LINEL-VALUE)))

(DEFUN OUR-MERGE (L M FN)
  (COND ((ATOM L) M)
        ((ATOM M) L)
        ((OR (FUNCALL FN (CAR L) (CAR M))
             (NOT (FUNCALL FN (CAR M) (CAR L))))
         (CONS (CAR L) (OUR-MERGE (CDR L) M FN)))
        (T (CONS (CAR M) (OUR-MERGE L (CDR M) FN)))))

(DEFUN OUR-STABLE-SORT (L FN)

;   The different Lisps we use have failed to agree on whether SORT
;   is stable.  Therefore we define our own, not very efficient,
;   but at least stable, version of a sorter.  This function has the
;   property discovered by Matt Kaufmann that regardless of what
;   the sorting predicate, FN, is, provided it returns T or F on all
;   input, then the output is "ordered" in the following sense:
;   x immediately precedes y in the output then either (FN x y) = T
;   or, at least, (FN y x) = F.

;   INTERLISP's SORT is apparently nonstable and frequently (perhaps always)
;   reverses elements of equal weight.  Zetalisp sort is stable.  We found
;   three occasions in the rsa and wilson proofs when this difference bit us
;   and caused a different elimination to be chosen first.  The first two times
;   we fixed it by letting it do the new elim and just seeing that the
;   appropriate lemmas were available to handle the new goals.  But on the
;   third time we decided simply to REVERSE the input list to mimic INTERLISP's
;   sort, just so we could get on with reproducing the old proofs on the new
;   machine.  Franz' sort is unstable, so to guarantee the same sorting
;   on all machines we have adopted our own sort, but use the maximally
;   unstable version.

  (COND ((OR (ATOM L)
             (ATOM (CDR L)))
         L)
        (T (OUR-MERGE (OUR-STABLE-SORT (ODDS L) FN)
                      (OUR-STABLE-SORT (ODDS (CDR L)) FN)
                      FN))))

(DEFUN PARTITION (L)

;   Returns a list of lists.  Each member of L is a MEMBer of exactly one the
;   of list of lists.  Each MEMBer of each list is a MEMBer of L.

  (LET (POT TEMP)
    (ITERATE FOR L1 IN L DO
             (PROGN
               (SETQ TEMP (ASSOC-EQUAL L1 POT))
               (COND ((NULL TEMP)
                      (SETQ POT (CONS (LIST L1)
                                      POT)))
                     (T (NCONC1 TEMP L1)))))
    POT))

(DEFUN PARTITION-CLAUSES (LST)
  (LET (ALIST FLG POCKETS N)
    (SETQ LST (ITERATE FOR CL IN LST COLLECT (CONS NIL CL)))
    (ITERATE FOR PAIR IN LST DO
             (ITERATE FOR LIT IN (CDR PAIR) DO
                      (PROGN
                        (SETQ FLG (MATCH LIT (NOT LIT)))
                        (SETQ TEMP-TEMP (ASSOC-EQUAL LIT ALIST))
                        (COND ((NULL TEMP-TEMP)
                               (SETQ TEMP-TEMP (LIST LIT FLG PAIR))
                               (SETQ ALIST (CONS TEMP-TEMP ALIST)))
                              ((EQUAL 0 (CADR TEMP-TEMP)) NIL)
                              ((NOT (EQ FLG (CADR TEMP-TEMP)))
                               (RPLACA (CDR TEMP-TEMP) 0))
                              (T (RPLACD (CDR TEMP-TEMP)
                                         (CONS PAIR (CDDR TEMP-TEMP))))))))
    (SETQ N (LENGTH LST))
    (ITERATE FOR PAIR IN ALIST WHEN (AND (NOT (EQUAL 0 (CADR PAIR)))
                                         (NOT (INT= N (LENGTH (CDDR PAIR)))))
             DO (SETQ POCKETS (CONS (ITERATE FOR PAIR IN (CDDR PAIR)
                                             UNLESS (CAR PAIR)
                                             COLLECT (PROGN (RPLACA PAIR T)
                                                            (CDR PAIR)))
                                    POCKETS)))
    (COND ((SETQ TEMP-TEMP (ITERATE FOR PAIR IN LST
                                    UNLESS (CAR PAIR)
                                    COLLECT (CDR PAIR)))
           (SETQ POCKETS (CONS TEMP-TEMP POCKETS))))
    POCKETS))

(DEFUN PATH-ADD-TO-SET (X Y)
  (COND ((ITERATE FOR Y1 IN Y THEREIS (PATH-EQ X Y1))
         Y)
        (T (CONS X Y))))

(DEFUN PATH-EQ (X Y)
  (AND (INT= (LENGTH X) (LENGTH Y))
       (ITERATE FOR X1 IN X AS Y1 IN Y ALWAYS (EQ X1 Y1))))

(DEFUN PATH-POT-SUBSUMES (LARGER SMALLER)
  (ITERATE FOR I FROM 1 TO (1- (LENGTH (CAR LARGER)))
           THEREIS (ITERATE FOR S IN SMALLER ALWAYS
                            (ITERATE FOR L IN LARGER
                                     THEREIS (EQ S (FARGN L I))))))

(DEFUN PATH-UNION (X Y)
  (NCONC (ITERATE FOR X1 IN X
                  UNLESS (ITERATE FOR Y1 IN Y THEREIS (PATH-EQ X1 Y1))
                  COLLECT X1)
         Y))

(DEFUN PEGATE-LIT (TERM)
  (COND ((FALSE-NONFALSEP TERM)
         (COND (DEFINITELY-FALSE FALSE)
               (T TRUE)))
        (T TERM)))

(DEFUN PICK-HIGH-SCORES (CANDLST)

;   Returns the list of elements of CAND-LIST tied for the highest CAR.

  (MAXIMAL-ELEMENTS CANDLST (FUNCTION (LAMBDA (CAND)
                                        (ACCESS CANDIDATE SCORE CAND)))))

(DEFUN PIGEON-HOLE (PIGEONS HOLES FN DO-NOT-CROWD-FLG DO-NOT-SMASH-FLG)
  (LET (PAIRLST)
    (SETQ PAIRLST (ITERATE FOR X IN HOLES COLLECT (CONS NIL X)))
    (COND ((PIGEON-HOLE1 PIGEONS PAIRLST FN DO-NOT-CROWD-FLG
                         DO-NOT-SMASH-FLG)
           (COND (DO-NOT-SMASH-FLG HOLES)
                 (T (ITERATE FOR PAIR IN PAIRLST COLLECT (CDR PAIR)))))
          (T NIL))))

(DEFUN PIGEON-HOLE1 (PIGEONS PAIRLST FN DO-NOT-CROWD-FLG DO-NOT-SMASH-FLG)
  (LET (TEMP OLD-FLG OLD-HOLE)
    (COND ((NULL PIGEONS)
           T)
          ((ITERATE FOR PAIR IN PAIRLST
                    UNLESS (AND DO-NOT-CROWD-FLG (CAR PAIR))
                    THEREIS (COND ((SETQ TEMP (FUNCALL FN (CAR PIGEONS)
                                                       (CDR PAIR)))
                                   (SETQ OLD-FLG (CAR PAIR))
                                   (SETQ OLD-HOLE (CDR PAIR))
                                   (OR DO-NOT-SMASH-FLG
                                       (RPLACD PAIR TEMP))
                                   (RPLACA PAIR T)
                                   (COND ((PIGEON-HOLE1 (CDR PIGEONS)
                                                        PAIRLST FN
                                                        DO-NOT-CROWD-FLG
                                                        DO-NOT-SMASH-FLG)
                                          T)
                                         (T (RPLACD PAIR OLD-HOLE)
                                            (RPLACA PAIR OLD-FLG)
                                            NIL)))
                                  (T NIL)))
           T)
          (T NIL))))

(DEFUN PLUSJOIN (LST)
  (COND ((NULL LST)
         (QUOTE (ZERO)))
        ((NULL (CDR LST))
         (CAR LST))
        (T (FCONS-TERM* (QUOTE PLUS)
                        (CAR LST)
                        (PLUSJOIN (CDR LST))))))

(DEFUN POLY-MEMBER (POLY LST)
  (ITERATE FOR POLY2 IN LST THEREIS (AND (EQUAL (ACCESS POLY CONSTANT POLY)
                                                (ACCESS POLY CONSTANT POLY2))
                                         (EQUAL (ACCESS POLY ALIST POLY)
                                                (ACCESS POLY ALIST POLY2)))))

(DEFUN POP-CLAUSE-SET NIL
  (PROG (CL-SET TEMP)
        TOP (COND ((NULL STACK)
                   (WRAPUP T))
                  ((EQ (CAAR STACK)
                       (QUOTE BEING-PROVED))
                   (SETQ TEMP (CADR (CAR STACK)))
                   (SETQ STACK (CDR STACK))
                   (IO (QUOTE POP)
                       TEMP NIL NIL (LIST (GET-STACK-NAME STACK)))
                   (GO TOP))
                  (T (SETQ CL-SET (CADR (CAR STACK)))
                     (SETQ STACK (CDR STACK))))
        (COND
         ((CATCH (QUOTE SUBSUMED-BELOW)
            (ITERATE FOR STACK-TAIL ON STACK
                     DO (COND ((ITERATE
                                FOR CL2 IN CL-SET
                                ALWAYS (ITERATE FOR CL1
                                                IN (CADR (CAR STACK-TAIL))
                                                THEREIS (SUBSUMES CL1 CL2)))
                               (COND ((EQ (CAR (CAR STACK-TAIL))
                                          (QUOTE BEING-PROVED))
                                      (IO (QUOTE SUBSUMED-BY-PARENT)
                                          CL-SET NIL NIL
                                          (LIST (GET-STACK-NAME STACK)
                                                (GET-STACK-NAME
                                                 (CDR STACK-TAIL))
                                                (CADR (CAR STACK-TAIL))))
                                      (WRAPUP NIL))
                                     (T (IO (QUOTE SUBSUMED-BELOW)
                                            CL-SET NIL NIL
                                            (LIST (GET-STACK-NAME STACK)
                                                  (GET-STACK-NAME
                                                   (CDR STACK-TAIL))
                                                  (CADR (CAR STACK-TAIL))))
                                        (THROW (QUOTE SUBSUMED-BELOW) T)))))))
          (GO TOP)))
        (SETQ STACK (CONS (LIST (QUOTE BEING-PROVED)
                                CL-SET)
                          STACK))
        (RETURN CL-SET)))

(DEFUN POP-LEMMA-FRAME NIL
  (PROG1 (CAR LEMMA-STACK)
    (RPLACA (PROG1 LEMMA-STACK
              (OR (SETQ LEMMA-STACK (CADR LEMMA-STACK))
                  (ER HARD NIL LEMMA-STACK |is| |too| |pooped|
                      |to| |pop| EXCL)))
            NIL)))

(DEFUN POP-LINEARIZE-ASSUMPTIONS-FRAME NIL
  (PROG1 (CAR LINEARIZE-ASSUMPTIONS-STACK)
    (RPLACA (PROG1 LINEARIZE-ASSUMPTIONS-STACK
              (OR (SETQ LINEARIZE-ASSUMPTIONS-STACK
                        (CADR LINEARIZE-ASSUMPTIONS-STACK))
                  (ER HARD NIL LINEARIZE-ASSUMPTIONS-STACK |is| |too|
                      |pooped| |to| |pop| EXCL)))
            NIL)))

(DEFUN POP-REWRITE-PATH-FRAME NIL
  (COND (REWRITE-PATH-STK-PTR
         (LET ((X (AREF REWRITE-PATH-STK REWRITE-PATH-STK-PTR)))
           (CASE (ACCESS REWRITE-PATH-FRAME PROG X)
                 (REWRITE
                  (COND ((AND (ACCESS REWRITE-PATH-FRAME LOC X)
                              (NVARIABLEP (ACCESS REWRITE-PATH-FRAME TERM X))
                              (NOT (FQUOTEP (ACCESS REWRITE-PATH-FRAME
                                                    TERM X))))
                         (UPDATE-PERSISTENCE-ALIST
                          (FFN-SYMB (ACCESS REWRITE-PATH-FRAME TERM X))
                          (- REWRITE-PATH-FRAME-CNT
                             (ACCESS REWRITE-PATH-FRAME CNT X))))))
                 (REWRITE-WITH-LEMMAS
                  (UPDATE-PERSISTENCE-ALIST
                   (ACCESS REWRITE-RULE NAME
                           (ACCESS REWRITE-PATH-FRAME TERM X))
                   (- REWRITE-PATH-FRAME-CNT
                      (ACCESS REWRITE-PATH-FRAME CNT X))))
                 (ADD-EQUATIONS-TO-POT-LST
                  (UPDATE-PERSISTENCE-ALIST
                   (ACCESS LINEAR-LEMMA NAME
                           (ACCESS REWRITE-PATH-FRAME TERM X))
                   (- REWRITE-PATH-FRAME-CNT
                      (ACCESS REWRITE-PATH-FRAME CNT X))))
                 (OTHERWISE NIL))
           (SETQ REWRITE-PATH-STK-PTR
                 (1- REWRITE-PATH-STK-PTR))))))

(DEFUN POSSIBLE-IND-PRINCIPLES (TERM)

;   TERM is a non-QUOTE fn call and this fn returns all the induction
;   principles suggested by it.  See FLESH-OUT-IND-PRIN for the form of an
;   induction prin.

  (LET (MACHINE FORMALS QUICK-BLOCK-INFO MASK)
    (SETQ FORMALS (CADR (GET (FFN-SYMB TERM)
                             (QUOTE SDEFN))))
    (SETQ QUICK-BLOCK-INFO (GET (FFN-SYMB TERM)
                                (QUOTE QUICK-BLOCK-INFO)))
    (SETQ MACHINE (GET (FFN-SYMB TERM)
                       (QUOTE INDUCTION-MACHINE)))
    (COND ((DISABLEDP (FFN-SYMB TERM))
           NIL)
          (T (ITERATE FOR J IN (GET (FFN-SYMB TERM)
                                    (QUOTE JUSTIFICATIONS))
                      WHEN (SETQ MASK
                                 (SOUND-IND-PRIN-MASK TERM J FORMALS
                                                      QUICK-BLOCK-INFO))
                      COLLECT (FLESH-OUT-IND-PRIN TERM FORMALS
                                                  MACHINE J MASK
                                                  QUICK-BLOCK-INFO))))))

(DEFUN POSSIBLY-NUMERIC (TERM)
  (LET ((TYPE-ALIST (OR HEURISTIC-TYPE-ALIST TYPE-ALIST)))
    (TS= (TYPE-SET TERM)
         TYPE-SET-NUMBERS)))

(DEFUN POWER-EVAL (L B)
  (IF (ATOM L)
      0
      (+ (CAR L) (* B (POWER-EVAL (CDR L) B)))))

(DEFUN POWER-REP (N B)
  (IF (< N B)
      (LIST N)
      (CONS (OUR-REMAINDER N B)
            (POWER-REP (OUR-QUOTIENT N B) B))))

;  The following three functions are user interface functions only

(DEFUN PPC (CL)
  (ITERPRI NIL)
  (PPR (PRETTYIFY-CLAUSE CL) NIL)
  NIL)

(DEFUN PPE (NAME)
  (ITERPRI NIL)
  (COND ((OR (NOT (SYMBOLP NAME))
             (AND (NOT (GET NAME 'EVENT))
                  (NOT (GET NAME 'MAIN-EVENT))))
         (PPR (CONS (QUOTE *****)
                    (CONS NAME
                          (QUOTE (|is| |neither| |an|
                                  |event| |nor|
                                  |satellite|))))
              NIL))
        ((GET NAME 'EVENT)
         (PPR (UNTRANSLATE-EVENT (GET NAME 'EVENT))
              NIL))
        (T
         (COND ((GET NAME 'SDEFN)

; The only symbols with SDEFNs that are not DEFNs are the DEFN0s of BOOT-STRAP.
; We recover the original DEFN0 form and represent it as an event, because it
; is prettier than the SDEFN.  (Compare the SDEFN of 'PLUS with what we print.)

                (PPR (ITERATE
                      FOR X IN BOOT-STRAP-INSTRS
                      WHEN
                      (OR (AND (EQ (CAR X) 'DEFN0)
                               (EQ (CADR X) NAME))
                          (AND (MEMBER-EQ (CAR X)
                                          '(IF-NQTHM-MODE IF-NOT-NQTHM-MODE))
                               (EQ (CAR (CADR X)) 'DEFN0)
                               (EQ (CADR (CADR X)) NAME)))
                      DO

; All uses of DEFN0 in BOOT-STRAP-INSTRS have the TRANSLATE-FLG set to T,
; meaning that the body provided in the DEFN0 is in untranslated form.  Thus,
; we do not translate these forms.

                      (RETURN
                       (COND ((EQ (CAR X) 'DEFN0)
                              (LIST 'DEFN (CADR X) (CADDR X) (CADDDR X)))
                             (T (LIST 'DEFN (CADR (CADR X))
                                      (CADDR (CADR X))
                                      (CADDDR (CADR X))))))
                      FINALLY
                      (ER HARD (NAME)
                          |It| |was| |thought| |that| |the| |only|
                          |satellites| |that| |had| |SDEFNs| |were|
                          |defined| |on| BOOT-STRAP-INSTRS |with|
                          |a| DEFN0 |but| (!PPR NAME NIL) |is| |an|
                          |example| |to| |the| |contrary| |.|))
                     NIL)
                (ITERPRI NIL)
                (ITERPRI NIL)))
         (PPR (LIST (QUOTE *****) NAME (QUOTE |is|)
                    (QUOTE |a|) (QUOTE |satellite|) (QUOTE |of|)
                    (UNTRANSLATE-EVENT
                     (GET (GET NAME (QUOTE MAIN-EVENT))
                          (QUOTE EVENT))))
              NIL)))
  (ITERPRI NIL))

;   A word about the "PPR" prefix...  The basic prettyprinter is PPRIND,
;   which is defined in the file PPR.  It takes a LEFTMARGIN and assumes
;   you are at that point when you invoke the function.  PPRINDENT below
;   puts you at the indicated LEFTMARGIN and then PPRINDs.  PPR is provided
;   primarily for the user:  it pretty prints with LEFTMARGIN 0.  We use it
;   only to implement user-level print functions like PPC and PPSD.  PPR-TERM
;   is like PPR but is only applied to terms and introduces the abbreviations
;   with UNTRANSLATE.  No function with the "PPR" prefix except PPR-TERM
;   introduces abbreviations;  that is, with the exception of PPR-TERM, all
;   the PPR functions print what you give them.

(DEFUN PPR (FMLA PPRFILE)
  (LET (LEFTMARGINCHAR)
    (PPRIND FMLA 0 0 PPRFILE)
    NIL))

(DEFUN PPR-TERM (TERM PPRFILE)
  (LET (LEFTMARGINCHAR)
    (PPRIND (UNTRANSLATE TERM) 0 0 PPRFILE)
    NIL))

(DEFUN PPRINDENT (TERM LEFTMARGIN RPARCNT FILE)
  (COND ((> (IPOSITION FILE NIL NIL)
            LEFTMARGIN)
         (ITERPRISPACES LEFTMARGIN FILE))
        (T (TABULATE LEFTMARGIN FILE)))
  (PPRIND TERM LEFTMARGIN (OR RPARCNT 0) FILE))

(DEFUN PPSD (X) (PPSD-LST (LIST X)))

(DEFUN PPSD-LST (X)
  (ITERATE FOR FNNAME IN X DO
           (PROGN
             (ITERPRI NIL)
             (PPR (COND ((GET FNNAME (QUOTE SDEFN))
                         (UNTRANSLATE
                          (FCONS-TERM* (QUOTE EQUAL)
                                       (FCONS-TERM
                                        FNNAME
                                        (CADR (GET FNNAME (QUOTE SDEFN))))
                                       (CADDR (GET FNNAME (QUOTE SDEFN))))))
                        (T (LIST FNNAME (QUOTE |is|) (QUOTE |undefined.|))))
                  NIL)
             (ITERPRI NIL))))

(DEFUN PREPROCESS (TERM)

;   Returns a set of clauses whose conjunction is equivalent to TERM and sets
;   ABBREVIATIONS-USED to the list of fn symbols and rewrite rules applied.

  (LET (TYPE-ALIST)
    (SETQ ABBREVIATIONS-USED NIL)
    (CLAUSIFY-INPUT (EXPAND-ABBREVIATIONS TERM NIL))))

(DEFUN PREPROCESS-HYPS (HYPS)

;   Expand NLISTP and NOT ZEROP hyps.

  (ITERATE FOR HYP IN HYPS WITH X
           NCONC (COND ((MATCH HYP (NOT (ZEROP X)))
                        (LIST (FCONS-TERM* (QUOTE NUMBERP)
                                           X)
                              (FCONS-TERM* (QUOTE NOT)
                                           (FCONS-TERM* (QUOTE EQUAL)
                                                        X ZERO))))
                       ((MATCH HYP (NLISTP X))
                        (LIST (FCONS-TERM* (QUOTE NOT)
                                           (FCONS-TERM* (QUOTE LISTP)
                                                        X))))
                       (T (LIST HYP)))))

(DEFUN PRETTYIFY-CLAUSE (CL)
  (COND ((NULL CL)
         (UNTRANSLATE FALSE))
        ((NULL (CDR CL))
         (UNTRANSLATE (CAR CL)))
        ((NULL (CDDR CL))
         (LIST (QUOTE IMPLIES)
               (DUMB-NEGATE-LIT (UNTRANSLATE (CAR CL)))
               (UNTRANSLATE (CADR CL))))
        (T (LIST (QUOTE IMPLIES)
                 (CONS (QUOTE AND)
                       (ITERATE FOR TAIL ON CL
                                UNLESS (NULL (CDR TAIL))
                                COLLECT
                                (DUMB-NEGATE-LIT (UNTRANSLATE (CAR TAIL)))))
                 (UNTRANSLATE (CAR (OUR-LAST CL)))))))

(DEFUN PRETTYIFY-LISP (X)
  (REMOVE-*2*IFS (INTRODUCE-ANDS (INTRODUCE-LISTS X))))

(DEFUN PRETTYIFY-RULE (HYPS CONCL)
  (COND ((NULL HYPS)
         CONCL)
        ((NULL (CDR HYPS))
         (LIST 'IMPLIES (CAR HYPS) CONCL))
        (T (LIST 'IMPLIES (CONS 'AND HYPS)
                 CONCL))))

(DEFUN PRETTYIFY-TYPE-ALIST (ALIST)
  (LET ((NOT-FALSE (TSLOGNOT TYPE-SET-FALSE)))
    (ITERATE FOR PAIR IN TYPE-ALIST
             COLLECT
             (COND ((TS= (CDR PAIR) TYPE-SET-FALSE)
                    (LIST 'NOT (UNTRANSLATE (CAR PAIR))))
                   ((EQ (CDR PAIR) NOT-FALSE)
                    (UNTRANSLATE (CAR PAIR)))
                   ((AND (TS= (CDR PAIR) TYPE-SET-TRUE)
                         (TS= (LET ((TYPE-ALIST NIL))
                                (TYPE-SET  (CAR PAIR)))
                              TYPE-SET-BOOLEAN))
                    (UNTRANSLATE (CAR PAIR)))
                   (T (DUMB-CONVERT-TYPE-SET-TO-TYPE-RESTRICTION-TERM
                       (CDR PAIR)
                       (UNTRANSLATE (CAR PAIR))))))))

(DEFUN PRIMITIVE-RECURSIVEP (FNNAME)
  (LET (FORMALS)
    (SETQ FORMALS (CADR (GET FNNAME (QUOTE SDEFN))))
    (COND ((DISABLEDP FNNAME) T)
          ((AND (GET FNNAME (QUOTE INDUCTION-MACHINE))
                (NOT (GET FNNAME (QUOTE JUSTIFICATIONS))))
           NIL)
          (T (ITERATE FOR X IN (GET FNNAME (QUOTE INDUCTION-MACHINE))
                      ALWAYS (ITERATE FOR CASE
                                      IN (ACCESS TESTS-AND-CASES CASES X)
                                      ALWAYS
                                      (ITERATE FOR VAR IN FORMALS
                                               AS TERM IN CASE
                                               ALWAYS (SHELL-DESTRUCTOR-NESTP
                                                       VAR
                                                       TERM))))))))

(DEFUN PRIMITIVEP (TERM)
  (OR (VARIABLEP TERM)
      (FQUOTEP TERM)
      (AND (OR (NULL (GET (FFN-SYMB TERM)
                          (QUOTE SDEFN)))
               (DISABLEDP (FFN-SYMB TERM))
               (EQ (FFN-SYMB TERM)
                   (QUOTE NOT)))
           (ITERATE FOR ARG IN (FARGS TERM) ALWAYS (PRIMITIVEP ARG)))))

(DEFUN PRINT-DATE-LINE NIL
  (PRINT-IDATE (IDATE) PROVE-FILE))

(DEFUN PRINT-IDATE (N FILE)
  (LET (SEC MIN HRS DAY MO YR
            (*PRINT-PRETTY* NIL)
            (*PRINT-BASE* 10)
            (*PRINT-RADIX* NIL)
            (*PRINT-LEVEL* NIL)
            (*PRINT-LENGTH* NIL)
            (*PRINT-CASE* :UPCASE)
            (*READ-BASE* 10))

;   This function may not be changed to put out any TERPRIs -- see NOTE-LIB.

    (MATCH (DECODE-IDATE N) (LIST SEC MIN HRS DAY MO YR))
    (IPRINC (NTH (1- MO)
                 (QUOTE (|January| |February| |March| |April| |May|
                                   |June| |July| |August| |September|
                                   |October| |November| |December|)))
            FILE)
    (ISPACES 1 FILE)
    (IPRINC DAY FILE)
    (IPRINC (QUOTE |,|) FILE)
    (ISPACES 1 FILE)
    (IPRINC (+ 1900 YR) FILE)
    (ISPACES 2 FILE)
    (FORMAT FILE "~2,'0D" HRS)
    (IPRINC (QUOTE |:|) FILE)
    (FORMAT FILE "~2,'0D" MIN)
    (IPRINC (QUOTE |:|) FILE)
    (FORMAT FILE "~2,'0D" SEC)
    N))

(DEFUN PRINT-STACK (Y)
  (ITERATE FOR X ON Y BY (QUOTE CADR) DO (PRINT (CAR X) T)))

(DEFUN PRINT-STATS (M-TIME P-TIME I-TIME FILE)
  (FORMAT (OR FILE *STANDARD-OUTPUT*)
          "~%[~{ ~,1F~} ]"
          (LIST M-TIME P-TIME I-TIME))
  (ITERPRI FILE))

(DEFUN PRINC-LOC (LOC PREV-FRAME PREV-FRAME-PTR FILE)

;   This function prints a description of the LOC component of a
;   REWRITE-PATH-FRAME given the LOC and the previous frame.

  (COND ((INTEGERP LOC)
         (CASE (ACCESS REWRITE-PATH-FRAME PROG PREV-FRAME)
               (REWRITE
                (FORMAT FILE "the ~:R argument of the term in frame ~D"
                        LOC PREV-FRAME-PTR))
               ((REWRITE-WITH-LEMMAS ADD-EQUATIONS-TO-POT-LST)
                (FORMAT FILE "the ~:R hypothesis of ~A"
                        LOC
                        (COND
                         ((EQ (ACCESS REWRITE-PATH-FRAME PROG PREV-FRAME)
                              'REWRITE-WITH-LEMMAS)
                          (ACCESS REWRITE-RULE NAME
                                  (ACCESS REWRITE-PATH-FRAME TERM
                                          PREV-FRAME)))
                         (T
                          (ACCESS LINEAR-LEMMA NAME
                                  (ACCESS REWRITE-PATH-FRAME TERM
                                          PREV-FRAME))))))
               ((SIMPLIFY-CLAUSE SET-SIMPLIFY-CLAUSE-POT-LST)
                (COND ((INT= 1 (LENGTH (ACCESS REWRITE-PATH-FRAME TERM
                                               PREV-FRAME)))
                       (FORMAT FILE "the top-level goal"))
                      ((INT= LOC (LENGTH (ACCESS REWRITE-PATH-FRAME TERM
                                                 PREV-FRAME)))
                       (FORMAT FILE "the conclusion of the top-level goal"))
                      (T (FORMAT FILE
                                 "the atom of the ~:R hypothesis of the ~
                              top-level goal"
                                 LOC))))
               (REWRITE-WITH-LINEAR
                (ER HARD NIL |It| |was| |thought| |impossible| |for| |a|
                    REWRITE-PATH |frame| |with| |a| |numeric| LOC |to| |be|
                    |preceded| |by| |a| REWRITE-WITH-LINEAR |frame| |.|))
               (OTHERWISE
                (ER HARD NIL |An| |unrecognized| REWRITE-PATH |frame| |type|
                    |has| |been| |encountered| |by| PRINC-LOC |.|))))
        ((CONSP LOC)
         (FORMAT FILE "a term manufactured by ~A" (CADR LOC)))
        (T (CASE LOC
                 (BODY
                  (FORMAT FILE "the body of ~A"
                          (FFN-SYMB
                           (ACCESS REWRITE-PATH-FRAME TERM PREV-FRAME))))
                 (REWRITTEN-BODY
                  (FORMAT FILE "the result of rewriting the body of ~A"
                          (FFN-SYMB
                           (ACCESS REWRITE-PATH-FRAME TERM PREV-FRAME))))
                 (RHS
                  (FORMAT FILE
                          "the right hand side of the conclusion of ~A"
                          (COND
                           ((EQ (ACCESS REWRITE-PATH-FRAME PROG PREV-FRAME)
                                'REWRITE-WITH-LEMMAS)
                            (ACCESS REWRITE-RULE NAME
                                    (ACCESS REWRITE-PATH-FRAME TERM
                                            PREV-FRAME)))
                           (T
                            (ACCESS LINEAR-LEMMA NAME
                                    (ACCESS REWRITE-PATH-FRAME TERM
                                            PREV-FRAME))))))
                 (META-RHS
                  (FORMAT FILE
                          "the result produced by the metafunction ~
                        in frame ~D"
                          PREV-FRAME-PTR))
                 ((NIL)
                  (FORMAT FILE "the term in frame ~D" PREV-FRAME-PTR))
                 (OTHERWISE
                  (ER HARD NIL |An| |unrecognized| LOC |has| |been|
                      |encountered|
                      |by| PRINC-LOC |.|))))))

(DEFUN PRINT-NQTHM-MODS (STREAM)
  (SETQ STREAM (OR STREAM *STANDARD-OUTPUT*))
  (COND
   ((NULL *MODS-ALIST*)
    NIL)
   (*THM-SUPPRESS-DISCLAIMER-FLG*
    (FORMAT STREAM
            "~%Nqthm-1992 mods:  ~s~%"
            (ITERATE FOR MOD IN *MODS-ALIST*
                     COLLECT (CAR MOD)))
    (ITERPRI STREAM))
   (T
    (ITERATE FOR MOD IN *MODS-ALIST* DO
             (FORMAT STREAM
                     "~%Nqthm-1992 modification ~s:~%~a~%"
                     (CAR MOD)
                     (CDR MOD)))
    (ITERPRI STREAM))))

(DEFUN PRINT-REWRITE-PATH-FRAME (I SKETCH-FLG FILE)
  
;   If the SKETCH-FLG is on we print sketched forms
;   and omit printing events and rules.
  
  (COND 
   (REWRITE-PATH-STK-PTR
    (LET ((X (AREF REWRITE-PATH-STK I)))
      (TERPRI FILE)
      (COND ((HIGH-PERSISTENCEP I)
             (FORMAT
              FILE
              "---- Frame ~D -----           (persistence ~D)  <-***"
              I
              (- REWRITE-PATH-FRAME-CNT
                 (ACCESS REWRITE-PATH-FRAME CNT X))))
            (T (FORMAT FILE "---- Frame ~D -----           (persistence ~D)"
                       I
                       (- REWRITE-PATH-FRAME-CNT
                          (ACCESS REWRITE-PATH-FRAME CNT X)))))
      (TERPRI FILE)
      (CASE (ACCESS REWRITE-PATH-FRAME PROG X)
            (SIMPLIFY-CLAUSE
             (PRINC "Goal:" FILE)
             (TERPRI FILE)
             (COND (SKETCH-FLG
                    (PPR (SKETCH 3
                                 (PRETTYIFY-CLAUSE
                                  (ACCESS REWRITE-PATH-FRAME TERM X)))
                         FILE))
                   (T (PPR (PRETTYIFY-CLAUSE
                            (ACCESS REWRITE-PATH-FRAME TERM X))
                           FILE)))
             (TERPRI FILE))
            (SET-SIMPLIFY-CLAUSE-POT-LST
             (PRINC "Initializing the linear database.")
             (TERPRI FILE))
            (REWRITE
             (PRINC "Rewriting " FILE)
             (PRINC-LOC (ACCESS REWRITE-PATH-FRAME LOC X)
                        (AREF REWRITE-PATH-STK (1- I))
                        (1- I)
                        FILE)
             (PRINC ":" FILE)
             (TERPRI FILE)
             (COND (SKETCH-FLG
                    (PPR (SKETCH 3
                                 (UNTRANSLATE
                                  (ACCESS REWRITE-PATH-FRAME TERM X)))
                         FILE))
                   (T
                    (PPR-TERM (ACCESS REWRITE-PATH-FRAME TERM X) FILE)))
             (TERPRI FILE)
             (PRINC "under the substitution:" FILE)
             (TERPRI FILE)
             (PRINT-SUBSTITUTION SKETCH-FLG
                                 (ACCESS REWRITE-PATH-FRAME ALIST X)
                                 FILE))
            (REWRITE-WITH-LEMMAS
             (PRINC "Attempting to apply the replacement rule " FILE)
             (PRINC (ACCESS REWRITE-RULE NAME
                            (ACCESS REWRITE-PATH-FRAME TERM X))
                    FILE)
             (COND ((NOT SKETCH-FLG)
                    (PRINC ":" FILE)
                    (TERPRI FILE)
                    (PPR (PRETTYIFY-RULE
                          (ACCESS REWRITE-RULE HYPS
                                  (ACCESS REWRITE-PATH-FRAME TERM X))
                          (ACCESS REWRITE-RULE CONCL
                                  (ACCESS REWRITE-PATH-FRAME TERM X)))
                         FILE)
                    (TERPRI FILE)
                    (PRINC "to the target term:" FILE)
                    (TERPRI FILE)
                    (PPR (ACCESS REWRITE-PATH-FRAME LOC X) FILE)))
             (TERPRI FILE)
             (PRINC "using the substitution:" FILE)
             (TERPRI FILE)
             (PRINT-SUBSTITUTION SKETCH-FLG
                                 (ACCESS REWRITE-PATH-FRAME ALIST X)
                                 FILE))
            (ADD-EQUATIONS-TO-POT-LST
             (PRINC "Attempting to apply the linear rule " FILE)
             (PRINC (ACCESS LINEAR-LEMMA NAME
                            (ACCESS REWRITE-PATH-FRAME TERM X))
                    FILE)
             (COND ((NOT SKETCH-FLG)
                    (PRINC ":" FILE)
                    (TERPRI FILE)
                    (PPR (PRETTYIFY-RULE
                          (ACCESS LINEAR-LEMMA HYPS
                                  (ACCESS REWRITE-PATH-FRAME TERM X))
                          (ACCESS LINEAR-LEMMA CONCL
                                  (ACCESS REWRITE-PATH-FRAME TERM X)))
                         FILE)
                    (TERPRI FILE)
                    (PRINC "to the target term:" FILE)
                    (TERPRI FILE)
                    (PPR (ACCESS REWRITE-PATH-FRAME LOC X) FILE)))
             (TERPRI FILE)
             (PRINC "using the substitution:" FILE)
             (TERPRI FILE)
             (PRINT-SUBSTITUTION SKETCH-FLG
                                 (ACCESS REWRITE-PATH-FRAME ALIST X)
                                 FILE))
            (REWRITE-WITH-LINEAR
             (COND (SKETCH-FLG
                    (PRINC "Attempting to use linear arithmetic." FILE))
                   (T
                    (PRINC
                     "Attempting to use linear arithmetic on the target term:"
                       FILE)
                      (TERPRI FILE)
                      (PPR (ACCESS REWRITE-PATH-FRAME TERM X) FILE)))
             (TERPRI FILE))
            (OTHERWISE
             (ER HARD ((NAME (ACCESS REWRITE-PATH-FRAME PROG X)))
                 |Unrecognized| REWRITE-PATH |frame|
                 (!PPR NAME '|.|))))))
   (T (PRINC "The REWRITE-PATH is not being maintained." FILE))))

(DEFUN PRINT-REWRITE-PATH (FLG FILE)

;  If FLG is HIGHLIGHT we highlight the path.  Otherwise
;  we print each frame with the sketch-flg set to flg.

  (TERPRI FILE)
  (COND (REWRITE-PATH-STK-PTR
         (COND ((EQ FLG 'HIGHLIGHT)
                (HIGHLIGHT-REWRITE-PATH FILE))
               (T
                (ITERATE FOR I FROM 0 TO REWRITE-PATH-STK-PTR
                         DO
                         (PRINT-REWRITE-PATH-FRAME I FLG FILE)))))
        (T (PRINC "The REWRITE-PATH is not being maintained." FILE)))
  (TERPRI FILE))

(DEFUN PRINT-SUBSTITUTION (SKETCH-FLG ALIST FILE)
  (COND ((NULL ALIST) (PRINC NIL FILE) (TERPRI FILE))
        (T (ITERATE FOR PAIR IN ALIST
                    DO
                    (PRINC (CAR PAIR) FILE)
                    (PRINC " <- " FILE)
                    (PPRIND (COND (SKETCH-FLG
                                   (SKETCH 3
                                           (UNTRANSLATE (CDR PAIR))))
                                  (T (UNTRANSLATE (CDR PAIR))))
                            (+ 4 (OUR-FLATC (CAR PAIR)))
                            0
                            FILE)
                    (TERPRI FILE)))))
        
(DEFUN PRINT-NQTHM-DISCLAIMER NIL
  (COND ((NOT *THM-SUPPRESS-DISCLAIMER-FLG*)
         (IPRINC *THM-DISCLAIMER* T)
         (FORCE-OUTPUT T)))
  (PRINT-NQTHM-MODS NIL)
  (IF (NOT (EQ PROVE-FILE NIL))
      (PRINT-NQTHM-MODS PROVE-FILE)))

(DEFUN PRINT-TWO-COLUMN-TABLE (HEADER COL1 COL2 ALIST FILE)
  (TERPRI FILE)
  (PRINC HEADER FILE)
  (TERPRI)
  (ITERATE FOR PAIR IN ALIST
           DO
           (ITERATE FOR I FROM 1 TO COL1
                    DO (WRITE-CHAR #\Space FILE))
           (PRINC (CAR PAIR) FILE)
           (COND ((>= (+ COL1 (OUR-FLATC (CAR PAIR))) COL2)
                  (TERPRI FILE)
                  (ITERATE FOR I FROM 1 TO COL2
                           DO (WRITE-CHAR #\Space FILE)))
                 (T (ITERATE FOR I FROM
                             (+ 1 COL1 (OUR-FLATC (CAR PAIR))) TO COL2
                             DO (WRITE-CHAR #\Space FILE))))
           (PRINC (CDR PAIR) FILE)
           (TERPRI FILE)))

(DEFUN PROCESS-EQUATIONAL-POLYS (CL HIST POT-LST)

;   Deduce from POT-LST all the interesting equations in it and add them to CL
;   unless they have already been generated and recorded in HIST.  This
;   function has no effect on the lemma and assumptions stacks but sets the
;   globals LEMMAS-USED-BY-LINEAR and LINEAR-ASSUMPTIONS if it changes CL.
;   When it adds an equation to CL it adds an entry to LEMMAS-USED-BY-LINEAR
;   that will ultimately be copied into the new hist for the clause.  The entry
;   is of the form ((FIND-EQUATIONAL-POLYS lhs . rhs)) -- the apparently
;   redundant level of parens is there to insure that the element cannot be
;   confused with a term.  Thus, when it is thrown into the list PROCESS-HIST
;   with lemma names and literals used, we can filter out the literals.
;   SIMPLIFY-CLAUSE handles this filtering above us.  FIND-EQUATIONAL-POLY is
;   the function that adds such entries to LEMMAS-USED-BY-LINEAR and that looks
;   for them in the HIST.

  (SETQ LEMMAS-USED-BY-LINEAR NIL)
  (SETQ LINEAR-ASSUMPTIONS NIL)
  (ITERATE FOR POT IN POT-LST WITH PAIR
           WHEN (SETQ PAIR (FIND-EQUATIONAL-POLY HIST POT)) DO

;   When FIND-EQUATIONAL-POLY returns nonNIL it side-effects the two global
;   collection sites above.

           (SETQ CL (COND ((AND (VARIABLEP (CAR PAIR))
                                (NOT (OCCUR (CAR PAIR) (CDR PAIR))))
                           (SUBST-VAR-LST (CDR PAIR) (CAR PAIR) CL))
                          ((AND (VARIABLEP (CDR PAIR))
                                (NOT (OCCUR (CDR PAIR) (CAR PAIR))))
                           (SUBST-VAR-LST (CAR PAIR) (CDR PAIR) CL))
                          (T (CONS (FCONS-TERM* (QUOTE NOT)
                                                (FCONS-TERM* (QUOTE EQUAL)
                                                             (CAR PAIR)
                                                             (CDR PAIR)))
                                   (SUBST-EXPR-LST (CDR PAIR)
                                                   (CAR PAIR) CL))))))
  CL)

#|
Beware:  this function is defined in nqthm.lisp.

(DEFUN PROCLAIM-NQTHM-FILE (NAME)
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

|#

(DEFUN PROPERTYLESS-SYMBOLP (X)
  (OR (CAR-CDRP X)
      (MEMBER-EQ X (QUOTE (NIL QUOTE LIST LET CASE COND T F
                               LIST*)))
      (ASSOC-EQ X *EXTRA-PROPERTYLESS-SYMBOLS-ALIST*)))

(DEFUN PROVE (FORM)
  (CHK-COMMAND-STATUS NIL)
  (LET ((COMMAND-STATUS-FLG T))
       (PROVE-FN FORM)))

(DEFUN PROVE-FN (FORM)
  (COND (PETITIO-PRINCIPII
         (SETQ ALL-LEMMAS-USED NIL)
         (RETURN-FROM PROVE-FN T)))
  (LET ((PROOF-START-TIME-IN-60THS (TIME-IN-60THS)))
    (PROG1
        (CATCH (QUOTE PROVE)
          (PROG (THM CLAUSES VARS)
                (CHK-INIT)
                (SETQ THM (TRANSLATE FORM))
                (SETQ CLAUSES (PREPROCESS THM))
                (SETUP FORM CLAUSES ABBREVIATIONS-USED)
                LOOP(SETQ VARS (ITERATE FOR CL IN CLAUSES WITH ITERATE-ANS
                                        DO (SETQ ITERATE-ANS
                                                 (UNION-EQ (ALL-VARS-LST CL)
                                                           ITERATE-ANS))
                                        FINALLY (RETURN ITERATE-ANS)))
                (SETQ ELIM-VARIABLE-NAMES1 (SET-DIFF ELIM-VARIABLE-NAMES VARS))
                (SETQ GEN-VARIABLE-NAMES1 (SET-DIFF GEN-VARIABLE-NAMES VARS))
                (SIMPLIFY-LOOP CLAUSES)
                (SETQ CLAUSES (INDUCT (POP-CLAUSE-SET)))
                (GO LOOP)))
      (SETQ PROVE-TIME (- (- (TIME-IN-60THS) PROOF-START-TIME-IN-60THS)
                          IO-TIME)))))

(DEFUN PROVE-FILE (INFILE-ROOT &KEY
                               (CHECK-SYNTAX T)
                               (WRITE-FLAG-FILES T)
                               (PETITIO-PRINCIPII NIL))

; PROVE-FILE READs the forms in the file INFILE-ROOT.events and evaluates them
; in order.  PROVE-FILE requires the file to begin with a BOOT-STRAP or a
; NOTE-LIB command.  MAKE-LIB is called at the end if a MAKE-LIB form is the
; last form.  MAKE-LIB may not occur except at the end.  See the documentation
; for the variable LEGAL-PROVE-FILE-FNS for a list of the forms that PROVE-FILE
; will evaluate.  If the file INFILE-ROOT.proved is created, then all the forms
; evaluated were legal Nqthm forms and all the forms were processed
; successfully.  See also PROVE-FILE-OUT.

; We recommend against the casual use of PROVE-FILE in the development phase of
; a project.  We recommend that the use of PROVE-FILE only towards the very
; end, when you believe your events all work; use PROVE-FILE then to learn that
; there are no illegal forms in your file.  One reason we recommend against the
; casual use of PROVE-FILE is that it binds *READTABLE* to a rather restrictive
; value, as discussed below, and consequently, recovering from certain errors
; is tedious.

; INFILE-ROOT should be a string. QUIRK: PROVE-FILE will cause an error if
; INFILE-ROOT ends in "tmp".  This is because of a possible unsound collision
; between a lib file named tmp.lisp and the file tmp.lisp created by evaluating
; (compile-uncompiled-defns "tmp"), which is a form that is permitted in a file
; processed by PROVE-FILE.

; If CHECK-SYNTAX is non-NIL, as it is by default, then we READ using a
; readtable that forbids surreptitious side effects via #., #,, or user-defined
; read macros, and we insist that the file begin with a NOTE-LIB or BOOT-STRAP
; and subsequently consists entirely of events forms.

; If the WRITE-FLAG-FILES parameter is non-NIL, as it is by default, then
; PROVE-FILE starts by creating the empty file INFILE-ROOT.STARTED and deleting
; the files INFILE-ROOT.proved INFILE.fail, if either exists.  If successful
; termination occurs, the file INFILE-ROOT.proved is created, listing total
; stats, all nondefinitional axioms used (including those used in any lib
; noted), and the files INFILE-ROOT.STARTED is deleted.  Thus a sure way to
; check for successful termination of a batch or background execution of a
; PROVE-FILE is to look for a file named INFILE-ROOT.proved and check that it
; has a later date than the start of the PROVE-FILE, just in case someone has
; made it impossible to delete such a file and you missed the error message
; saying it could not be deleted; or just make sure there were no *.proved
; files in the directory when you started.  The existence of a *.STARTED file
; at the end is another sign of failure.  If PROVE-FILE does terminates without
; successfully processing all forms, it creates the file INFILE-ROOT.fail.  In
; certain circumstances, e.g., a power failure or a stack overlow, such a
; failure file may not be created.

; PROVE-FILE causes an error on any MAKE-LIB form in the file being processed,
; unless it is the last form in the file, in which case it is evaluated.

; If the PETITIO-PRINCIPII parameter is non-NIL, then PROVE-FILE
; arranges for PROVE and PROVE-TERMINATION to act as though they
; succeeded without really doing any work.  THIS RENDERS THE WHOLE
; THING UNSOUND.  In this case, a *.proved file is not created.

; In spirit, PROVE-FILE is like the LISP function LOAD in that its job is to
; evaluate the forms in the file, in order.  The remainer of this paragraph is
; a philosophical motivation for why we are not content just to use LOAD.  By
; default, PROVE-FILE makes several syntactic checks on forms before evaluating
; them, e.g., that all the forms to be evaluated are legal for an Nqthm user,
; as opposed to an arbitrary Common Lisp hacker, to evaluate.  It should be
; clear to the Nqthm user that because he or she is `speaking directly to Lisp'
; in the normal course of using Nqthm, it is easy to evaluate a Lisp form,
; e.g., (SETQ TRUE FALSE), that will render Nqthm unsound.  We prefer the
; flexibility and sense of freedom one gets from dealing directly with Lisp
; when developing and checking proofs with Nqthm, rather than dealing with some
; pea-brained and constraining `user interface'.  (For example, we often find
; ourselves executing raw Common Lisp forms to `compute' the Nqthm forms we
; wish to evaluate.)  But when a proving project is entirely complete, we
; prefer to know that no idiotic or surreptitious Lisp forms are present that
; would render Nqthm unsound.  Thus it makes sense to have, as we do in
; PROVE-FILE, a loader that prohibits intermingling possibly dangerous Lisp
; forms with legal Nqthm forms.

; Like LOAD, PROVE-FILE is a file oriented read-eval-print-loop: the forms are
; read with the Common Lisp READ function, evaluated with the Common Lisp EVAL
; function (provided we do not first cause an error because the form is not a
; suitable PROVE-FILE form), and the value is printed, with PRINC.  The READing
; is done with the readtable NQTHM-READTABLE, which is a copy of the initial
; Common Lisp readtable within which some ordinarily legal constructs have been
; made to cause errors, including backquote and most of the sharpsign syntax.
; See the function NQTHM-READTABLE for full details.  Unlike EVAL, PROVE-FILE
; returns as soon as any form evaluates to NIL, with the exception of the form
; (SETQ *COMPILE-FUNCTIONS-FLG* NIL).  PROVE-FILE returns on a NIL value
; because a NIL return value by any of the top-level Nqthm functions is a sign
; of failure.

; Warning: Because PROVE-FILE binds *READTABLE* to a special value, it may
; occasionally be tricky to get out of an error break under PROVE-FILE.  In
; almost every case that we can imagine an error arising, Nqthm will reset the
; readtable to a normal value before asking for user input, but in certain
; situations the readtable may still be bound, when an error arises, to a value
; that causes an error upon reading a colon.  This can cause trouble.  For
; example, many Common Lisps expect you to type keywords such as :q, :a, or
; :reset to exit from an error break.  But if reading a colon causes an error,
; typing a keyword will merely cause another error.  One way to get out of such
; a situation is to type

;    (setq *readtable* (copy-readtable nil))

; and then type the keyword.  We admit that this is a considerable
; inconvenience and imposition!  If we knew how to `tell ERROR to switch to the
; default readtable in *every* case' we would do it, but we do not.  There is
; compensation for this imposition.  We would be sad to see PROVE-FILE pass a
; file that contained, say, the `theorem' (equal car lucid::car).  But if we
; did not forbid colons, this might get proven if, for example, we happend to
; be running Nqthm under Lucid Common Lisp, simply because the package Lucid
; might `use' Lisp.  But even reading this `theorem' would cause an error in,
; say, AKCL.

; Before invoking (PROVE-FILE "foo"), we check beforehand that there is no file
; named foo.proved and we check at the end that there exists a file named
; foo.proved.  If there is such a file, we conclude that the processing of the
; events in the file foo.events was entirely successful, with all definitions
; accepted and all theorems proved.  If we are not familiar with a particular
; events file, we also check the contents of the foo.proved file that was
; created to see if any axioms were added or any undoing was requested.  Adding
; axioms, of course, is an easy way to cheat your way through to getting any
; theorem proved.  And if any undoing, i.e., UBT, is done, then there is some
; possibility of confusion, e.g., the same concept might be defined several
; times in the same file.  If we find no foo.proved file, or if there is a file
; foo.STARTED we concluded that either the run has not yet completed or that an
; error arose during the execution of PROVE-FILE, and we inspect the output
; produced during the execution of PROVE-FILE to see what the problem was.

; Because projects that use Nqthm can be very large, taking years to complete,
; and can be worked on by many people, there is often the practical necessity
; to divide the events into a collection of several files.  To `certify root
; and branch' a collection of files with Nqthm, using PROVE-FILE, one should
; start by making sure that there are no *.lib, *.lisp, *.proved, or *.STARTED
; files on the directory containing the files to be ``done''.  One should
; further make the same check for all the directories that are referred to in
; the NOTE-LIB forms that occur at the beginnings of the files to be certified.
; Thus, if one of the files begins with (NOTE-LIB "foo/bar"), make sure that
; directory foo is also free of the files with extensions mentioned above.
; (This check will prevent the use of older libraries and thus avoid the risk
; of using libraries that are uncertified or otherwise out of date with respect
; to their source files.)  Then, to ``certify'', execute a sequence of
; PROVE-FILE commands on the events files in question in an order consistent
; with the inner dependencies (calling PROVE-FILE on each file exactly once).
; If at the end there is a .proved file for each of the source files, the
; certification is complete.  Obviously, there should be no changes permitted
; to any of the files in sight (except, of course, the creation of new files by
; PROVE-FILE) during the execution of the PROVE-FILEs.

; PROVE-FILE executes each of the event commands in the file
; INFILE-ROOT.events.  The events are top level forms in the file.  PROVE-FILE
; prints each event form and then executes it, accumulating the total event
; times and printing the event names to the terminal if the output is going
; elsewhere.  PROVE-FILE aborts if some event causes an error or fails.  It
; returns T if all events succeeded and NIL if some failed.

; Inadequacies.  We currently know of three senses in which PROVE-FILE fails to
; fully do the job that we intend.  (1) Common Lisp syntax for integers is not
; entirely fixed by the Common Lisp standards.  For example, 1.7J is given as
; an explicit example, on p. 341 of CLTL1, of a character sequence that is a
; `potential number', that is, a sequence that some Common Lisp might read as a
; number.  If a Common Lisp were to read 1.7J as an integer, e.g., as the
; integer 17, then by running Nqthm in that Common Lisp one could `prove' the
; theorem (equal 1.7J 17).  But (equal 1.7J 17) might be false, or might even
; cause an error in Nqthm in another Common Lisp.  The solution to this problem
; is to check with your Lisp provider that no character strings that are
; `potential numbers' read as integers, except those satisfying the normal
; syntax for integers shared by all Common Lisp implementations.  (2) It is
; certainly not clear from the Common Lisp standard what files can be created
; by the compilation process.  Typically, if you compile foo.lisp, then foo.x
; is created, for some extension x.  However, AKCL takes this freedom to a
; rather liberal extent: when the compiler::*split-files* option is non-NIL, as
; we have been forced to set it when doing the fm9001-piton proofs, files with
; names 0foo.o, 1foo.o, 2foo.o, ..., may be created.  Such names create a
; potential for collision with the compiled lib of another events file, say one
; named 0foo.events.  Thus the user of PROVE-FILE should check that the name of
; no events file begins with a digit.  We do not make this check mechanically,
; as we do the check for names that end in "tmp", because it is possible that
; some prefix of a name supplied to PROVE-FILE is a mere directory name, e.g.,
; "bar/0foo".  (3) Unbalanced close parentheses at the top level are treated by
; READ in an undefined, implementation dependent way.  Most Lisps we use ignore
; these; some even comment on this act of ignoring.  But some cause an error.
; CLTL1 says such parentheses are `invalid'; a perfect implementation of
; PROVE-FILE would check for these and cause an error.

  (LET*
      ((*READ-BASE* 10)
       (*PACKAGE* (FIND-PACKAGE "USER"))
       (PROVED-FILE-NAME (EXTEND-FILE-NAME INFILE-ROOT FILE-EXTENSION-PROVED))
       (EVENT-FILE-NAME (EXTEND-FILE-NAME INFILE-ROOT FILE-EXTENSION-EVENTS))
       (STARTED-FILE-NAME (EXTEND-FILE-NAME INFILE-ROOT
                                            FILE-EXTENSION-STARTED))
       (A-VERY-RARE-CONS (CONS NIL NIL))
       (START-DATE (IDATE))
       (M-TIME TOTAL-MISC-TIME)
       (P-TIME TOTAL-PROVE-TIME)
       (I-TIME TOTAL-IO-TIME)
       (AXIOMS NIL)
       (UBTS NIL)
       (SUCCESS NIL)
       (FIRST-FORM (MAKE-SYMBOL "the first form in the file."))
       (FORM FIRST-FORM))
    (CHK-COMMAND-STATUS T)
    (UNWIND-PROTECT
     (PROGN
      (COND ((NOT (STRINGP INFILE-ROOT))
             (ERROR1-SET
              (ER SOFT (INFILE-ROOT)
                  |The| |first| |argument| |to| PROVE-FILE |must| |be|
                  |a| |string| |,| |but| (!PPR INFILE-ROOT NIL) |is|
                  |not| |.|))
             (RETURN-FROM PROVE-FILE NIL))
            ((AND (> (LENGTH INFILE-ROOT) 2)
                  (STRING-EQUAL "tmp" (SUBSEQ INFILE-ROOT
                                              (- (LENGTH INFILE-ROOT) 3)
                                              (LENGTH INFILE-ROOT))))
             (ERROR1-SET
              (ER SOFT ((X '|"tmp"|) (Y '(compile-uncompiled-defns |"tmp"|)))
                  PROVE-FILE |prohibits| |the| |use| |of| |a| |file| |name|
                  |that| |ends| |with| (!PPR X NIL) |on| |the| |off| |chance|
                  |that| |there| |will| |be| |some| |collision| |with| |the|
                  |results| |of| |evaluating| (!PPR Y '|.|)))
             (RETURN-FROM PROVE-FILE NIL)))
      (COND (WRITE-FLAG-FILES
             (WITH-OPEN-FILE
              (OUTSTREAM STARTED-FILE-NAME :DIRECTION :OUTPUT
                         :IF-EXISTS :RENAME-AND-DELETE)
              NIL)))
      (COND ((AND WRITE-FLAG-FILES
                  (PROBE-FILE (EXTEND-FILE-NAME INFILE-ROOT
                                                FILE-EXTENSION-FAIL)))
             (DELETE-FILE (EXTEND-FILE-NAME INFILE-ROOT FILE-EXTENSION-FAIL))))
      (COND ((NULL WRITE-FLAG-FILES) NIL)
            ((PROBE-FILE PROVED-FILE-NAME)
             (DELETE-FILE PROVED-FILE-NAME)
             (COND ((PROBE-FILE PROVED-FILE-NAME)
                    (ERROR1-SET
                     (ER SOFT (PROVED-FILE-NAME)
                         |Unable| |to| |delete| |the| |file|
                         (!PPR PROVED-FILE-NAME '|.|)))
                    (RETURN-FROM PROVE-FILE NIL)))))
      (LET ((READTABLE (COND (CHECK-SYNTAX (NQTHM-READTABLE))
                               (T *READTABLE*))))
        (COND ((NOT (PROBE-FILE EVENT-FILE-NAME))
               (ERROR1-SET
                (ER SOFT (EVENT-FILE-NAME)
                    PROVE-FILE |cannot| |open| (!PPR EVENT-FILE-NAME '|.|)))
               (RETURN-FROM PROVE-FILE NIL)))
        (WITH-OPEN-FILE
         (INSTREAM EVENT-FILE-NAME
                   :DIRECTION :INPUT
                   :IF-DOES-NOT-EXIST :ERROR)
         (UNWIND-PROTECT
          (PROGN
           (SETQ FIRST-FORM
                 (LET ((R (ERROR1-SET
                           (LET ((*READTABLE* READTABLE))
                             (READ INSTREAM NIL A-VERY-RARE-CONS)))))
                   (COND (R (CAR R))
                         (T (RETURN-FROM PROVE-FILE NIL)))))
           (COND ((EQ FIRST-FORM A-VERY-RARE-CONS)
                  (ERROR1-SET
                   (ER SOFT (EVENT-FILE-NAME)
                       PROVE-FILE |was| |called| |on| |an| |empty| |file|
                       |,| (!PPR EVENT-FILE-NAME '|.|)))
                  (RETURN-FROM PROVE-FILE NIL)))
           (COND ((NULL CHECK-SYNTAX) NIL)
                 ((MEMBER-EQUAL FIRST-FORM
                                (QUOTE ((BOOT-STRAP)
                                        (BOOT-STRAP THM)
                                        (BOOT-STRAP NQTHM))))
                  NIL)
                 ((AND (CONSP FIRST-FORM)
                       (EQ (CAR FIRST-FORM) (QUOTE NOTE-LIB))
                       (NULL (CDR (OUR-LAST FIRST-FORM)))
                       (< (LENGTH FIRST-FORM) 4)
                       (STRINGP (CADR FIRST-FORM))
                       (MEMBER (CADDR FIRST-FORM)
                               (QUOTE (T NIL))))
                  NIL)
                 (T (ERROR1-SET
                     (ER SOFT (FIRST-FORM EVENT-FILE-NAME)
                         |A| |file| |that| PROVE-FILE |evaluates| |must|
                         |begin| |with| |one| |of| |the| |forms|
                         (!PPR '(BOOT-STRAP NQTHM) '|,|)
                         (!PPR '(BOOT-STRAP THM) '|,|)
                         (!PPR '(BOOT-STRAP) '|,|)
                         (!PPR '(NOTE-LIB |string| T) '|,|)
                         (!PPR '(NOTE-LIB |string| NIL) '|,|)
                         |or|
                         (!PPR '(NOTE-LIB |string|) '|.|)
                         |so| |the| |first| |form| |,| (!PPR FIRST-FORM '|,|)
                         |of| |the| |file| (!PPR EVENT-FILE-NAME NIL) |is|
                         |illegal| |.|))
                    (RETURN-FROM PROVE-FILE NIL)))
           (LET (ANS)
             (PROG NIL
                   LOOP 

;   READ a form.

; The first time through, we use FIRST-FORM, but we set FIRST-FORM to NIL
; below, after bypassing the interior legality check.

                   (COND (FIRST-FORM (SETQ FORM FIRST-FORM))
                         (T (SETQ
                             FORM
                             (LET ((R (ERROR1-SET
                                       (LET ((*READTABLE* READTABLE))
                                         (READ INSTREAM NIL
                                               A-VERY-RARE-CONS)))))
                               (COND (R (CAR R))
                                     (T (RETURN-FROM PROVE-FILE NIL)))))))

;   Check if at end of file, and if so, wrap up.

                   (COND ((EQ FORM A-VERY-RARE-CONS)
                          (COND
                           ((AND WRITE-FLAG-FILES (NOT PETITIO-PRINCIPII))
                            (SETQ SUCCESS T)
                            (WITH-OPEN-FILE
                             (OUTSTREAM PROVED-FILE-NAME
                                        :DIRECTION :OUTPUT
                                        :IF-EXISTS :RENAME-AND-DELETE)
                             (FORMAT OUTSTREAM
                                     "The evaluation of PROVE-FILE on the ~
                                      file:~%~%  ~a~%~%was completed ~
                                      successfully.~%~%"
                                     EVENT-FILE-NAME)
                             (PRINT-NQTHM-MODS OUTSTREAM)
                             (COND (LIB-VERSION-TROUBLE
                                    (FORMAT OUTSTREAM
                                            "~%~%Warning:  Use of ~
                                             incompatible libraries ~
                                             encountered during this ~
                                             session.~%~%")))
                             (COND (AXIOMS
                                    (FORMAT
                                     OUTSTREAM
                                     "Here is the list of names of the ~
                                       nondefinitional axioms assumed:~%~%")
                                    (PPR AXIOMS OUTSTREAM))
                                   (T (FORMAT OUTSTREAM
                                              "No nondefinitional axioms were ~
                                                assumed.")))
                             (COND (UBTS
                                    (FORMAT OUTSTREAM
                                            "~%~%Here is the list of names of ~
                                             the UBT targets:~%~%")
                                    (PPR UBTS OUTSTREAM))
                                   (T (FORMAT OUTSTREAM
                                              "~%~%No actions involving ~
                                               undoing, i.e., uses of UBT, ~
                                               were encountered.")))
                             (ITERPRIN 2 OUTSTREAM)
                             (IPRINC (QUOTE |Total Statistics:|) OUTSTREAM)
                             (PRINT-STATS (- TOTAL-MISC-TIME M-TIME)
                                          (- TOTAL-PROVE-TIME P-TIME)
                                          (- TOTAL-IO-TIME I-TIME)
                                          OUTSTREAM)
                             (ITERPRI OUTSTREAM)
                             (IPRINC (QUOTE |Start of run: |) OUTSTREAM)
                             (PRINT-IDATE START-DATE OUTSTREAM)
                             (ITERPRI OUTSTREAM)
                             (IPRINC (QUOTE |End of run:   |) OUTSTREAM)
                             (PRINT-IDATE (IDATE) OUTSTREAM)
                             (ITERPRI OUTSTREAM)
                             (DELETE-FILE STARTED-FILE-NAME)))
                           (PETITIO-PRINCIPII
                            (SETQ SUCCESS T)))
                          (RETURN T)))

; Check that the form is one we know about.  For the first form, ignore this
; check.

                   (COND (FIRST-FORM NIL)
                         ((NULL CHECK-SYNTAX) NIL)
                         ((AND (CONSP FORM)
                               (EQ (CAR FORM) 'MAKE-LIB))
                          (COND ((AND (NULL (CDR (OUR-LAST FORM)))
                                      (<= (LENGTH FORM) 3)
                                      (EQUAL (CADR FORM) INFILE-ROOT)
                                      (MEMBER (CADDR FORM) '(T NIL)))
                                 NIL)
                                (T (ERROR1-SET
                                    (ER SOFT (FORM
                                              (EXAMPLE '(MAKE-LIB |string|
                                                                  T/NIL)))
                                        |a| MAKE-LIB |form| |may| |only|
                                        |occur| |in| |a| |file| |to| |be|
                                        |processed| |by| PROVE-FILE |if|
                                        |it| |is| |of| |the| |form|
                                        (!PPR EXAMPLE NIL) |,| |where|
                                        |string| |is| |the| |root| |name|
                                        |of| |the| |file| |being| |processed|
                                        |.|))
                                   (RETURN-FROM PROVE-FILE NIL)))
                          (COND ((EQ A-VERY-RARE-CONS
                                     (READ INSTREAM NIL A-VERY-RARE-CONS))
                                 NIL)
                                (T (ERROR1-SET
                                    (ER SOFT (FORM)
                                        |a| MAKE-LIB |form| |may| |occur|
                                        |in| |a| |file| |to| |be| |processed|
                                        |by| PROVE-FILE |only| |as| |the|
                                        |last| |form| |in| |the| |file| |.|))
                                   (RETURN-FROM PROVE-FILE NIL))))
                         ((AND (CONSP FORM)
                               (MEMBER-EQ (CAR FORM) LEGAL-PROVE-FILE-FNS))
                          NIL)
                         ((EQUAL FORM (QUOTE (COMPILE-UNCOMPILED-DEFNS "tmp")))
                          NIL)
                         ((AND (CONSP FORM)
                               (EQ (CAR FORM) (QUOTE SETQ))
                               (NULL (CDR (OUR-LAST FORM)))
                               (EQUAL (LENGTH FORM) 3)
                               (OR
                                (AND (EQ (QUOTE REDUCE-TERM-CLOCK) (CADR FORM))
                                     (INTEGERP (CADDR FORM)))
                                (AND (EQ (QUOTE *COMPILE-FUNCTIONS-FLG*)
                                         (CADR FORM))
                                     (MEMBER-EQ (CADDR FORM) '(T NIL)))))
                          NIL)
                         (T (ERROR1-SET
                             (ER SOFT
                                 (LEGAL-PROVE-FILE-FNS
                                  FORM
                                  (X '(COMPILE-UNCOMPILED-DEFNS |"tmp"|))
                                  (Y '(SETQ REDUCE-TERM-CLOCK |integer|))
                                  (Z '(SETQ *COMPILE-FUNCTIONS-FLG* |x|)))
                                 |The| |form| (!PPR FORM NIL) |is|
                                 |illegal| |here| |.| |Below| |we| |specify|
                                 |what| |kind| |of| |file| |is|
                                 |expected| |by| PROVE-FILE |.| CR |#|
                                 |The| |first| |form| |in| |the| |file|
                                 |must| |be| |a| BOOT-STRAP |or| NOTE-LIB
                                 |form| |.| |A| MAKE-LIB
                                 |form| |may| |appear| |at| |the|
                                 |end| |of| |the| |file| |.|
                                 |Otherwise| |,|
                                 |the| |permitted| |commands| |are|
                                 (!LIST LEGAL-PROVE-FILE-FNS) |,|
                                 |as| |well| |as| |the| |forms| CR
                                 (!PPR X '|,|) CR (!PPR Y '|,|) |and| CR
                                 (!PPR Z '|,|) |where| |x| |is| T
                                 |or| (!PPR NIL '|.|)))
                            (RETURN-FROM PROVE-FILE NIL)))

; Print out the event form to PROVE-FILE and, if PROVE-FILE is not the
; terminal, print the name to the terminal.

                   (COND ((NULL PETITIO-PRINCIPII)
                          (ITERPRIN 1 PROVE-FILE)
                          (IPRINC EVENT-SEPARATOR-STRING PROVE-FILE)
                          (ITERPRIN 2 PROVE-FILE)
                          (PPRIND FORM 0 0 PROVE-FILE)
                          (ITERPRI PROVE-FILE)
                          (COND ((NOT (EQ PROVE-FILE NIL))
                                 (IPRINC (CADR FORM) NIL)))))

; Evaluate the event form.

                   (SETQ ANS (ERROR1-SET (EVAL FORM)))

                   (COND ((NULL ANS)

; A SOFT ERROR1 occurred during the evaluation, so quit.
                           
                          (ITERPRI PROVE-FILE)
                          (IPRINC FAILURE-MSG PROVE-FILE)
                          (ITERPRI PROVE-FILE)
                          (RETURN NIL)))

; Recover the actual value from the CONS produced by the ERROR1-SET
; protection.

                   (SETQ ANS (CAR ANS))

; Print the answer to PROVE-FILE and, if PROVE-FILE is not the terminal, print
; a comma or the failure message, as appropriate, to the terminal to indicate
; completion of the event.


                   (COND ((NULL PETITIO-PRINCIPII)
                          (ITERPRI PROVE-FILE)
                          (IPRINC ANS PROVE-FILE)
                          (COND ((NOT (EQ PROVE-FILE NIL))
                                 (COND ((AND (EQ ANS NIL)
                                             (NOT (EQ (CAR FORM)
                                                      (QUOTE SETQ))))
                                        (ITERPRI NIL)
                                        (IPRINC FAILURE-MSG NIL)
                                        (ITERPRI NIL))
                                       (T (IPRINC (QUOTE |,|) NIL)
                                          (COND ((< (OUR-LINEL NIL NIL)
                                                    (IPOSITION NIL NIL NIL))
                                                 (ITERPRI NIL)))))))))

; Exit if the command failed but was not a SETQ.

                   (COND ((AND (EQ ANS NIL)
                               (NOT (EQ (CAR FORM) (QUOTE SETQ))))
                          (ITERPRI PROVE-FILE)
                          (IPRINC FAILURE-MSG PROVE-FILE)
                          (ITERPRI PROVE-FILE)
                          (RETURN NIL)))

; If it is the first form, and a lib was noted, then pick up the axioms
; from it.

                   (COND (FIRST-FORM
                          (SETQ AXIOMS NONCONSTRUCTIVE-AXIOM-NAMES)
                          (SETQ FIRST-FORM NIL)))

; Note if it was an UBT.

                   (COND ((EQ (CAR FORM) 'UBT)
                          (PUSH (CADR FORM) UBTS))
                         ((MEMBER-EQ (CAR FORM) '(ADD-AXIOM AXIOM))
                          (PUSH (CADR FORM) AXIOMS)))

; Otherwise, continue looping.

                   (GO LOOP))))

; When exiting from the UNWIND-PROTECT, make an uncompiled lib
; if we failed but got past the first form.  

          (COND ((AND (NULL SUCCESS)
                      (NOT FIRST-FORM))
                 (MAKE-LIB INFILE-ROOT)))))))
     (COND ((AND (NULL SUCCESS) WRITE-FLAG-FILES)
            (WITH-OPEN-FILE
             (STR (EXTEND-FILE-NAME INFILE-ROOT FILE-EXTENSION-FAIL)
                  :DIRECTION :OUTPUT
                  :IF-EXISTS :RENAME-AND-DELETE)
             (FORMAT STR "Failure occurred when attempting to process ~
                          the file ~%~%  ~a~%~%The failure occurred ~
                          approximately when attempting to ~
                          evaluate~%~%"
                     EVENT-FILE-NAME)
             (PPR FORM STR)))))))

#|  These silly definitions make it easier for us to test the driver.
    (defmacro add-axiom (&rest x) t)
    (defmacro  add-shell (&rest x) t)
    (defmacro  dcl (&rest x) t)
    (defmacro  defn (&rest x) t)
    (defmacro  disable (&rest x) t)
    (defmacro  enable (&rest x) t)
    (defmacro  prove-lemma (&rest x) t)
    (defmacro toggle (&rest x) t)
    (defmacro  toggle-defined-functions (&rest x) t)
    (defmacro  ubt (&rest x) t)
    (defmacro constrain (&rest x) t)
    (defmacro deftheory (&rest x) t)
    (defmacro lemma (&rest x) t)
    (defmacro compile-uncompiled-defns (&rest x) t)
    (defmacro functionally-instantiate (&rest x) t)
    (defun pprind (fm l r p) nil)
|#

(DEFUN PROVE-TERMINATION (FORMALS RM MACHINE)
  (LET ((PROOF-START-TIME-IN-60THS (TIME-IN-60THS))
        ALL-PROCESS-CLAUSES)
    (SETQ PROVE-TERMINATION-LEMMAS-USED NIL)
    (PROG1
        (AND (COND ((AND (EQ *1*THM-MODE$ (QUOTE NQTHM))
                         (EQ (CAR RM) (QUOTE ORD-LESSP)))
                    (COND
                     ((AND (SIMPLIFY-CLAUSE-MAXIMALLY
                            (LIST (CONS-TERM (QUOTE ORDINALP)
                                             (LIST (CADR RM)))))
                           (NULL PROCESS-CLAUSES))
                      (SETQ PROVE-TERMINATION-LEMMAS-USED
                            (UNION-EQUAL PROCESS-HIST
                                         PROVE-TERMINATION-LEMMAS-USED))
                      T)
                     (T (SETQ ALL-PROCESS-CLAUSES
                              (UNION-EQUAL PROCESS-CLAUSES
                                           ALL-PROCESS-CLAUSES))
                        (ER WARNING ((X (CONS-TERM (QUOTE ORDINALP)
                                                   (LIST (CADR RM))))
                                     (Y (COND ((AND (NVARIABLEP (CADR RM))
                                                    (NOT (FQUOTEP (CADR RM)))
                                                    (EQ (FFN-SYMB (CADR RM))
                                                        'CONS))
                                               (FARGN (CADR RM) 1))
                                              (T NIL))))
                            |The| |formula| (!TERM X NIL) |has| |not| |been|
                            |proved| |.|
                            (COND (Y |This| |often| |happens| |because| |the|
                                     |first| |component| |,| (!TERM Y '|,|)
                                     |of| |the| |alleged| |ordinal| |is| |not|
                                     |strictly| |positive| |.|)))
                        NIL)))
                   (T T))
             (ITERATE FOR X IN MACHINE
                      ALWAYS
                      (COND
                       ((AND (SIMPLIFY-CLAUSE-MAXIMALLY
                              (NCONC1 (ITERATE
                                       FOR H IN (ACCESS TESTS-AND-CASE TESTS X)
                                       COLLECT (NEGATE-LIT H))
                                      (CONS-TERM (CAR RM)
                                                 (LIST (SUB-PAIR-VAR
                                                        FORMALS
                                                        (ACCESS
                                                         TESTS-AND-CASE
                                                         CASE X)
                                                        (CADR RM))
                                                       (CADR RM)))))
                             (NULL PROCESS-CLAUSES))
                        (SETQ PROVE-TERMINATION-LEMMAS-USED
                              (UNION-EQUAL PROCESS-HIST
                                           PROVE-TERMINATION-LEMMAS-USED))
                        T)
                       (T (SETQ ALL-PROCESS-CLAUSES
                                (UNION-EQUAL PROCESS-CLAUSES
                                             ALL-PROCESS-CLAUSES))
                          NIL))))
      (SETQ PROVE-TERMINATION-CASES-TRIED
            (CONS (CONS RM ALL-PROCESS-CLAUSES)
                  PROVE-TERMINATION-CASES-TRIED))
      (SETQ PROVE-TIME (+ PROVE-TIME
                          (- (TIME-IN-60THS) PROOF-START-TIME-IN-60THS))))))

(DEFUN PROVEALL (FILENAME EVENT-LST &OPTIONAL COMPILE-FLG)
  (LET (ANS M-TIME P-TIME I-TIME
            (PROVEALL-FLG T)
            (PROVEALL-FILENAME FILENAME))
    (CHK-COMMAND-STATUS T)
    (SETQ PROVE-FILE (OPEN (EXTEND-FILE-NAME FILENAME
                                             FILE-EXTENSION-PROOFS)
                           :DIRECTION :OUTPUT
                           :IF-EXISTS :RENAME-AND-DELETE))
    (OUR-LINEL PROVE-FILE 79)
    (SETQ ERR-FILE
          (OPEN (EXTEND-FILE-NAME FILENAME
                                  FILE-EXTENSION-ERR)
                :DIRECTION :OUTPUT
                :IF-EXISTS :RENAME-AND-DELETE))
    (OUR-LINEL ERR-FILE 79)
    (SETQ M-TIME TOTAL-MISC-TIME)
    (SETQ P-TIME TOTAL-PROVE-TIME)
    (SETQ I-TIME TOTAL-IO-TIME)
    (ITERPRIN 1 PROVE-FILE)
    (PRINT-DATE-LINE)
    (ITERPRI NIL)
    (SETQ ANS (DO-EVENTS EVENT-LST))
    (ITERPRI NIL)
    (COND ((NULL ANS)
           (PRINEVAL
            (PQUOTE (PROGN CR CR
                           |The| PROVEALL |named| (!PPR FILENAME NIL)
                           |failed| |when| |executing| |the| |command|
                           (!PPR EVENT (QUOTE |.|)) CR CR))
            (LIST (CONS (QUOTE FILENAME) FILENAME)
                  (CONS (QUOTE EVENT) (CAR UNDONE-EVENTS)))
            0 ERR-FILE)
           (IPRINC FAILURE-MSG ERR-FILE)
           (ITERPRI ERR-FILE)
           (WITH-OPEN-FILE
            (STREAM (EXTEND-FILE-NAME FILENAME FILE-EXTENSION-FAIL)
                    :DIRECTION :OUTPUT
                    :IF-EXISTS :RENAME-AND-DELETE)
            (PRINEVAL
             (PQUOTE (PROGN CR CR
                            |The| PROVEALL |named| (!PPR FILENAME NIL)
                            |failed| |when| |executing| |the| |command|
                            (!PPR EVENT (QUOTE |.|)) CR CR))
             (LIST (CONS (QUOTE FILENAME) FILENAME)
                   (CONS (QUOTE EVENT) (CAR UNDONE-EVENTS)))
             0 STREAM)
            (IPRINC FAILURE-MSG STREAM)
            (ITERPRI STREAM))))
    (ITERPRIN 1 PROVE-FILE)
    (IPRINC EVENT-SEPARATOR-STRING PROVE-FILE)
    (ITERPRIN 2 PROVE-FILE)
    (LET ((*STANDARD-OUTPUT* PROVE-FILE))
      (ROOM T))
    (ITERPRIN 2 PROVE-FILE)
    (IPRINC (QUOTE |Total Statistics:|) PROVE-FILE)
    (PRINT-STATS (- TOTAL-MISC-TIME M-TIME)
                 (- TOTAL-PROVE-TIME P-TIME)
                 (- TOTAL-IO-TIME I-TIME)
                 PROVE-FILE)
    (ITERPRI PROVE-FILE)
    (COND ((NULL ANS)
           (IPRINC FAILURE-MSG PROVE-FILE)
           (ITERPRI PROVE-FILE)))
    (CLOSE PROVE-FILE)
    (SETQ PROVE-FILE NIL)
    (CLOSE ERR-FILE)
    (SETQ ERR-FILE NIL)
    (IPRINC (QUOTE |Total Statistics:|) NIL)
    (PRINT-STATS (- TOTAL-MISC-TIME M-TIME)
                 (- TOTAL-PROVE-TIME P-TIME)
                 (- TOTAL-IO-TIME I-TIME)
                 NIL)
    (ITERPRI NIL)
    (COND ((NULL ANS)
           (IPRINC FAILURE-MSG NIL)
           (ITERPRI NIL)))
    (IPRINC (LIST (QUOTE MAKE-LIB) FILENAME) NIL)
    (MAKE-LIB FILENAME COMPILE-FLG)
    (ITERPRI NIL)
    (COND ((NULL ANS)
           (ERROR "PROVEALL failed!")))
    ANS))

(DEFUN PSEUDO-TERMP (X)

;   X must be an evg.  This function returns T or F according to whether
;   X is has all the properties of a term except, possibly, that of being
;   in QUOTE normal form.  A related, stronger concept is TERMP.  It should
;   be the case that if (PSEUDO-TERMP X) then (TERMP (SUBLIS-VAR NIL X)).

  (COND ((ATOM X)

;   The only atoms that are terms are SYMBOLPs.  The only evgs that are
;   SYMBOLPs are *1*T, *1*F, and LEGAL-NAMES.  TRANSLATE can return any
;   LEGAL-NAME except T, F, and NIL.

         (AND (SYMBOLP X)
              (NOT (EQ X *1*T))
              (NOT (EQ X *1*F))
              (NOT (EQ X T))
              (NOT (EQ X (QUOTE F)))
              (NOT (EQ X NIL))))
        ((EQ (CAR X) (QUOTE QUOTE))

;   Any evg of the form (QUOTE x) is acceptable because x must itself be
;   an evg.

         (AND (CONSP (CDR X))
              (EQ (CDDR X) NIL)))
        (T 
           
;   Otherwise we check merely that X is of the form (fn a1 ... an) where
;   fn is a fn symbol of arity n and each ai is a PSEUDO-TERMP.
           
         (AND (SYMBOLP (CAR X))
              (EQ (CDR (OUR-LAST X)) NIL)
              (NOT (MEMBER-EQ *1*SHELL-QUOTE-MARK X))
              (EQUAL (ARITY (CAR X)) (LENGTH (CDR X)))
              (ITERATE FOR ARG IN (CDR X) ALWAYS (PSEUDO-TERMP ARG))))))

(DEFUN PUSH-CLAUSE-SET (CL-SET)
  (SETQ STACK (CONS (LIST (QUOTE TO-BE-PROVED) CL-SET) STACK)))

(DEFUN PUSH-LEMMA (ELE)
  (COND ((MEMBER-EQ ELE (CAR LEMMA-STACK)) NIL)
        (T (RPLACA LEMMA-STACK (CONS ELE (CAR LEMMA-STACK)))
           NIL)))

(DEFUN PUSH-LEMMA-FRAME NIL
  (COND ((ATOM (CDDR LEMMA-STACK))
         (RPLACD (CDR LEMMA-STACK) (CREATE-STACK1 10))
         (RPLACA (CDDDR LEMMA-STACK) LEMMA-STACK)))
  (SETQ LEMMA-STACK (CDDR LEMMA-STACK))
  (RPLACA LEMMA-STACK NIL)
  NIL)

(DEFUN PUSH-LINEARIZE-ASSUMPTION (ELE)
  (RPLACA LINEARIZE-ASSUMPTIONS-STACK
          (ADD-TO-SET ELE (CAR LINEARIZE-ASSUMPTIONS-STACK)))
  NIL)

(DEFUN PUSH-LINEARIZE-ASSUMPTIONS-FRAME NIL
  (COND ((ATOM (CDDR LINEARIZE-ASSUMPTIONS-STACK))
         (RPLACD (CDR LINEARIZE-ASSUMPTIONS-STACK) (CREATE-STACK1 10))
         (RPLACA (CDDDR LINEARIZE-ASSUMPTIONS-STACK)
                 LINEARIZE-ASSUMPTIONS-STACK)))
  (SETQ LINEARIZE-ASSUMPTIONS-STACK
        (CDDR LINEARIZE-ASSUMPTIONS-STACK))
  (RPLACA LINEARIZE-ASSUMPTIONS-STACK NIL)
  NIL)

(DEFUN PUSH-REWRITE-PATH-FRAME (PROG TERM ALIST LOC)
  (COND (REWRITE-PATH-STK-PTR
         (SETQ REWRITE-PATH-FRAME-CNT (1+ REWRITE-PATH-FRAME-CNT))
         (COND ((INT= REWRITE-PATH-STK-LENGTH
                      (SETQ REWRITE-PATH-STK-PTR
                            (1+ REWRITE-PATH-STK-PTR)))
                (PROG1
                 (LET ((REWRITE-PATH-STK-LENGTH
                        (+ REWRITE-PATH-STK-LENGTH 100)))
                   (SETQ REWRITE-PATH-STK
                         (MAKE-ARRAY
                          REWRITE-PATH-STK-LENGTH
                          :INITIAL-CONTENTS
                          (NCONC
                           (ITERATE FOR I FROM 0 TO
                                    (1- REWRITE-PATH-STK-PTR)
                                    COLLECT (AREF REWRITE-PATH-STK I))
                           (ITERATE FOR I FROM 1 TO 100
                                    COLLECT
                                    (MAKE REWRITE-PATH-FRAME
                                          0 ;prog
                                          0 ;cnt
                                          0 ;loc
                                          0 ;term
                                          0 ;alist
                                          ))))))
                 (SETQ REWRITE-PATH-STK-LENGTH
                       (+ REWRITE-PATH-STK-LENGTH 100)))))
         (LET ((X (AREF REWRITE-PATH-STK REWRITE-PATH-STK-PTR)))
           (CHANGE REWRITE-PATH-FRAME PROG X PROG)
           (CHANGE REWRITE-PATH-FRAME CNT X REWRITE-PATH-FRAME-CNT)
           (CHANGE REWRITE-PATH-FRAME LOC X LOC)
           (CHANGE REWRITE-PATH-FRAME TERM X TERM)
           (CHANGE REWRITE-PATH-FRAME ALIST X ALIST)))))

(DEFUN PUSHU NIL
  (SETQ UNDONE-EVENTS-STACK (CONS UNDONE-EVENTS UNDONE-EVENTS-STACK))
  (SETQ UNDONE-EVENTS NIL))

(DEFUN PUT-INDUCTION-INFO (FNNAME FORMALS BODY RELATION-MEASURE-LST)

;   If FNNAME is recursive we store JUSTIFICATIONS, INDUCTION-MACHINE, and
;   QUICK-BLOCK-INFO properties.  If only one JUSTIFICATION is stored and in it
;   the RELATION is NIL then we did not establish termination.  ALL-LEMMAS-USED
;   is side-effected to contain lemma names used to clean up the
;   INDUCTION-MACHINE.

  (PROG (T-MACHINE I-MACHINE JUSTIFICATIONS)
        (SETQ PROVE-TERMINATION-CASES-TRIED NIL)
        (SETQ T-MACHINE (TERMINATION-MACHINE FNNAME BODY NIL))
        (COND ((NULL T-MACHINE)
               (SETQ ALL-LEMMAS-USED NIL)
               (RETURN NIL)))
        (OR RELATION-MEASURE-LST
            (SETQ RELATION-MEASURE-LST
                  (GUESS-RELATION-MEASURE-LST FORMALS T-MACHINE)))
        (SETQ JUSTIFICATIONS
              (COND ((AND PETITIO-PRINCIPII
                          (EQUAL (LENGTH RELATION-MEASURE-LST) 1))
                     (LET ((RM (CAR RELATION-MEASURE-LST))
                           (PROVE-TERMINATION-LEMMAS-USED NIL))
                       (LIST (MAKE JUSTIFICATION
                                   (ALL-VARS (CADR RM))
                                   (CADR RM)
                                   (CAR RM)
                                   PROVE-TERMINATION-LEMMAS-USED))))
                    (T
                     (ITERATE FOR RM IN RELATION-MEASURE-LST
                              WHEN (PROVE-TERMINATION FORMALS RM
                                                      T-MACHINE)
                              COLLECT (MAKE JUSTIFICATION
                                            (ALL-VARS (CADR RM))
                                            (CADR RM)
                                            (CAR RM)
                                            PROVE-TERMINATION-LEMMAS-USED)))))
        (COND (JUSTIFICATIONS
               (ADD-FACT FNNAME (QUOTE JUSTIFICATIONS)
                         JUSTIFICATIONS)))
        (SETQ ALL-LEMMAS-USED NIL)

;   We set ALL-LEMMAS-USED to NIL to forget the lemmas put there by PROVE so we
;   can now accumulate the lemmas used by REMOVE-REDUNDANT-TESTS in
;   INDUCTION-MACHINE.

        (SETQ I-MACHINE
              (INDUCTION-MACHINE FNNAME BODY NIL))

;   We store the INDUCTION-MACHINE even for inadmissible BOOT-STRAP
;   fns like V&C$.  Otherwise, we would be fooled into thinking such
;   functions were non-recursive.  It is illegitimate to make use of
;   the INDUCTION-MACHINE as an induction schema unless the
;   JUSTIFICATIONS property is non-NIL.

        (ADD-FACT FNNAME (QUOTE INDUCTION-MACHINE) I-MACHINE)
        (COND (FORMALS
               (ADD-FACT FNNAME (QUOTE QUICK-BLOCK-INFO)
                         (QUICK-BLOCK-INFO FORMALS I-MACHINE))))
        (RETURN NIL)))

(DEFUN PUT-LEVEL-NO (FNNAME)
  (LET (BODY MAX)
    (SETQ BODY (CADDR (GET FNNAME (QUOTE SDEFN))))
    (SETQ MAX (COND (BODY (OR (ITERATE FOR FN IN (ALL-FNNAMES BODY)
                                       WHEN (NOT (EQ FN FNNAME))
                                       MAXIMIZE (GET-LEVEL-NO FN))
                              0))
                    (T 0)))
    (ADD-FACT FNNAME (QUOTE LEVEL-NO)
              (COND ((FNNAMEP FNNAME BODY)
                     (1+ MAX))
                    (T MAX)))))

(DEFUN PUT-REWRITE-PATH-ALIST (ALIST)
  (COND (REWRITE-PATH-STK-PTR
         (CHANGE REWRITE-PATH-FRAME ALIST
                 (AREF REWRITE-PATH-STK REWRITE-PATH-STK-PTR)
                 ALIST))))

(DEFUN PUT-TOTALP (NAME)
  (COND ((EQ *1*THM-MODE$ (QUOTE THM))
         (ADD-FACT NAME (QUOTE TOTALP-LST)
                   (CONS NAME
                         (NOT (MEMBER-EQ NAME (QUOTE (APPLY$ EVAL$)))))))
        ((OR (NON-RECURSIVE-DEFNP NAME)
             (GET NAME (QUOTE JUSTIFICATIONS)))
         (ADD-FACT NAME (QUOTE TOTALP-LST)
                   (CONS NAME
                         (SUPER-TAMEP
                          NAME (CADDR (GET NAME (QUOTE SDEFN)))))))
        (T (ADD-FACT NAME (QUOTE TOTALP-LST)
                     (CONS NAME NIL)))))

(DEFUN PUT-TYPE-PRESCRIPTION (NAME)

;   *************************************************************
;   THIS FUNCTION WILL BE COMPLETELY UNSOUND IF TYPE-SET
;   IS EVER REACHABLE FROM WITHIN IT.
;   IN PARTICULAR, BOTH THE TYPE-ALIST AND THE
;   TYPE-PRESCRIPTION FOR THE FN BEING PROCESSED ARE SET
;   TO ONLY PARTIALLY ACCURATE VALUES AS THIS FN
;   COMPUTES THE REAL TYPE-SET.
;   *************************************************************

  (PROG (OLD-TYPE-PRESCRIPTION NEW-TYPE-PRESCRIPTION BODY FORMALS
                               TYPE-ALIST ANS TEMP)
        (SETQ BODY (GET NAME (QUOTE SDEFN)))
        (SETQ FORMALS (CADR BODY))
        (SETQ BODY (CADDR BODY))
        (SETQ TYPE-ALIST (ITERATE FOR ARG IN FORMALS
                                  COLLECT (CONS ARG (CONS 0 (LIST ARG)))))
        (SETQ OLD-TYPE-PRESCRIPTION
              (CONS 0 (MAKE-LIST (LENGTH FORMALS))))
        (ADD-FACT NAME (QUOTE TYPE-PRESCRIPTION-LST)
                  (CONS NAME OLD-TYPE-PRESCRIPTION))
        LOOP
        (RPLACD (CAR (SETQ TEMP (GET NAME (QUOTE TYPE-PRESCRIPTION-LST))))
                OLD-TYPE-PRESCRIPTION)

;   It is very unusual to be mucking about with RPLACDs on data that is part
;   of the event level abstraction.  But by virtue of the fact that we know
;   what the abstraction is and how it works -- i.e., by violating the
;   abstraction! -- we know what we're doing here.  The TYPE-PRESCRIPTION-LST
;   at this moment is a singleton list containing just the CONS added above.
;   The CAR of that CONS is the name of the event that gave rise to the
;   type prescription and the CDR is the type prescription.  The
;   RPLACD above smashes the type prescription in the CDR to a new "guess"
;   that includes all the information contained in the current guess.  The
;   fundamental difficulty with destructively changing event level data
;   arises because the ADD-SUB-FACT mechanism stores certain undo information
;   about each added fact, and if you change the data without being aware of
;   that, you might make the data inconsistent with the undoing information
;   about it.  But we know that all ADD-SUB-FACT stores in this case is the
;   name of the lemma, that is, the CAR of the TYPE-PRESCRIPTION-NAME-AND-PAIR,
;   and so by smashing the CDR we're consistently fooling it.

        (SETF (GET NAME (QUOTE TYPE-PRESCRIPTION-LST)) TEMP)

;   Why do we both RPLACD the structure on the property list AND do the
;   SETF?  The answer is that a SWAPOUT can occur anytime.  Note that if
;   that happened after we did the GET but before the RPLACD happened we would
;   otherwise lose.

        (SETQ ANS (DEFN-TYPE-SET BODY))
        (SETQ NEW-TYPE-PRESCRIPTION
              (CONS (CAR ANS)
                    (ITERATE FOR ARG IN FORMALS
                             COLLECT (COND ((MEMBER-EQ ARG (CDR ANS))
                                            T)
                                           (T NIL)))))
        (COND ((EQUAL OLD-TYPE-PRESCRIPTION NEW-TYPE-PRESCRIPTION)
               (RETURN NIL))
              ((AND (TSLOGSUBSETP (CAR NEW-TYPE-PRESCRIPTION)
                                  (CAR OLD-TYPE-PRESCRIPTION))
                    (ITERATE FOR FLG1 IN (CDR NEW-TYPE-PRESCRIPTION) AS FLG2
                             IN (CDR OLD-TYPE-PRESCRIPTION)
                             ALWAYS (OR (NOT FLG1)
                                        FLG2)))
               (ER WARNING NIL |An| |unexpected| |situation| |has| |arisen|
                   EXCL |The| DEFN-TYPE-SET |iteration| |stopped| |because|
                   |of| |a|
                   |proper| |subset| |check| |rather| |than| |the| |equality|
                   |of| |the| |old| |and| |new| |type| |sets| |.|)
               (RETURN NIL)))
        (SETQ OLD-TYPE-PRESCRIPTION
              (CONS (TSLOGIOR (CAR OLD-TYPE-PRESCRIPTION)
                              (CAR NEW-TYPE-PRESCRIPTION))
                    (ITERATE FOR FLG1 IN (CDR OLD-TYPE-PRESCRIPTION)
                             AS FLG2 IN (CDR NEW-TYPE-PRESCRIPTION)
                             COLLECT (OR FLG1 FLG2))))
        (GO LOOP)))

(DEFUN PUT1 (ATM VAL PROP)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (COND ((NOT (SYMBOLP ATM))
         (ER HARD (ATM) |Attempt| |to| |use| PUT1 |on| |the|
             |non| |symbolp| (!PPR ATM (QUOTE |.|))))
        ((NOT (MEMBER-EQ PROP LIB-PROPS))
         (ER HARD (PROP) |Attempt| |to| |use| PUT1 |to| |store| |the|
             |non-LIB-PROPS| |property| (!PPR PROP (QUOTE |.|))))
        ((NOT (MEMBER-EQ ATM LIB-ATOMS-WITH-PROPS))
         (SETQ LIB-ATOMS-WITH-PROPS (CONS ATM LIB-ATOMS-WITH-PROPS))))
  (SETF (GET ATM PROP) VAL))

(DEFUN PUT1-LST (ATM PROPS)

;   PROPS is a list of the form (prop1 val1 prop2 val2 ...).

  (ITERATE FOR TAIL ON (REVERSE PROPS) BY (QUOTE CDDR)
           DO (SETF (GET ATM (CADR TAIL)) (CAR TAIL))))

(DEFUN PUTD1 (ATM EXPR)

;   If EXPR is NIL, remove ATM from LIB-ATOMS-WITH-DEFS and erase its function
;   definition and EXPR property.  If EXPR is non-NIL, add ATM to
;   LIB-ATOMS-WITH-DEFS, make the compiled version of EXPR be the definition of
;   ATM, and store EXPR under the EXPR prop.

  (COND ((NULL EXPR)
         (SETQ LIB-ATOMS-WITH-DEFS (DELETE ATM LIB-ATOMS-WITH-DEFS))
         (KILL-DEFINITION ATM))
        (T (SETQ LIB-ATOMS-WITH-DEFS (CONS ATM LIB-ATOMS-WITH-DEFS))
           (STORE-DEFINITION ATM EXPR))))

(DEFUN QUICK-BLOCK-INFO (FORMALS TESTS-AND-CASES-LST)

;   Return a list of "block-types," each being one of the words UNCHANGING,
;   SELF-REFLEXIVE, or QUESTIONABLE, indicating how the corresponding arg
;   position is changed in the calls enumerated.  This is used to help quickly
;   decide if a blocked formal can be tolerated in induction.

  (LET (BLOCK-TYPES)
    (SETQ BLOCK-TYPES (MAKE-LIST (LENGTH FORMALS)
                                 :INITIAL-ELEMENT
                                 (QUOTE UN-INITIALIZED)))
    (ITERATE FOR TESTS-AND-CASES IN TESTS-AND-CASES-LST DO
             (ITERATE FOR CASE IN
                      (ACCESS TESTS-AND-CASES CASES TESTS-AND-CASES) DO
                      (ITERATE FOR VAR IN FORMALS AS ARG IN CASE AS TAIL
                               ON BLOCK-TYPES DO
                               (CASE
                                (CAR TAIL)
                                (QUESTIONABLE NIL)
                                (UN-INITIALIZED
                                 (RPLACA TAIL (QUICK-BLOCK-INFO1 VAR ARG)))
                                (OTHERWISE
                                 (OR (EQ (CAR TAIL)
                                         (QUICK-BLOCK-INFO1 VAR ARG))
                                     (RPLACA TAIL (QUOTE QUESTIONABLE))))))))
    BLOCK-TYPES))

(DEFUN QUICK-BLOCK-INFO1 (VAR TERM)
  (COND ((EQ VAR TERM)
         (QUOTE UNCHANGING))
        ((OCCUR VAR TERM)
         (QUOTE SELF-REFLEXIVE))
        (T (QUOTE QUESTIONABLE))))

(DEFUN QUICK-WORSE-THAN (TERM1 TERM2)
  (COND ((VARIABLEP TERM2)
         (COND ((EQ TERM1 TERM2) NIL)
               (T (OCCUR TERM2 TERM1))))
        ((FQUOTEP TERM2)
         (COND ((VARIABLEP TERM1) T)
               ((FQUOTEP TERM1)
                (> (FORM-COUNT-EVG (CADR TERM1))
                   (FORM-COUNT-EVG (CADR TERM2))))
               (T T)))
        ((VARIABLEP TERM1) NIL)
        ((FQUOTEP TERM1) NIL)
        ((EQ (FFN-SYMB TERM1) (FFN-SYMB TERM2))
         (COND ((EQUAL TERM1 TERM2) NIL)
               ((ITERATE FOR ARG1 IN (FARGS TERM1) AS ARG2 IN (FARGS TERM2)
                         THEREIS (OR (AND (OR (VARIABLEP ARG1) (QUOTEP ARG1))
                                          (NOT (OR (VARIABLEP ARG2)
                                                   (QUOTEP ARG2))))
                                     (WORSE-THAN ARG2 ARG1)))
                NIL)
               (T (ITERATE FOR ARG1 IN (FARGS TERM1) AS ARG2 IN (FARGS TERM2)
                           THEREIS (WORSE-THAN ARG1 ARG2)))))
        (T NIL)))

(DEFUN QUOTATIONS-CHK (TERM)
  
;   This function explores TERM and prints WARNING messages whenever it
;   finds FOR, EVAL$, or V&C$ applied to QUOTEd objects that are not
;   PSEUDO-TERMPs.  The idea is that users write '(PLUS 1 X) when they ought
;   to write '(PLUS '1 X).
  
  (LET (FLG FORM TEST BODY)
    (COND ((EQ *1*THM-MODE$ (QUOTE THM)) T)
          ((VARIABLEP TERM) T)
          ((FQUOTEP TERM) T)
          (T
           (ITERATE FOR ARG IN (FARGS TERM)
                    DO (QUOTATIONS-CHK ARG))
           (COND ((OR (MATCH TERM (V&C$ (LIST (QUOTE QUOTE) FLG)
                                        (LIST (QUOTE QUOTE) FORM)
                                        &))
                      (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                         (LIST (QUOTE QUOTE) FORM)
                                         &)))
                  (COND ((EQ FLG (QUOTE LIST))
                         (OR (ITERATE FOR ARG IN FORM
                                      ALWAYS (PSEUDO-TERMP ARG))
                             (QUOTATIONS-CHK-ER (FFN-SYMB TERM)
                                                (QUOTE LIST) FORM)))
                        (T (OR (PSEUDO-TERMP FORM)
                               (QUOTATIONS-CHK-ER (FFN-SYMB TERM) T FORM)))))
                 ((MATCH TERM (FOR & & (LIST (QUOTE QUOTE) TEST)
                                   & (LIST (QUOTE QUOTE) BODY) &))
                  (AND (OR (PSEUDO-TERMP TEST)
                           (QUOTATIONS-CHK-ER (QUOTE FOR) T TEST))
                       (OR (PSEUDO-TERMP BODY)
                           (QUOTATIONS-CHK-ER (QUOTE FOR) T BODY))))
                 (T NIL))))))

(DEFUN QUOTATIONS-CHK-ER (FN FLG EVG)
  (ER WARNING (FN FLG (TERM (LIST (QUOTE QUOTE) EVG)))
      |It| |is| |unusual| |to| |see| |an| |application| |of| (!PPR FN NIL)
      (COND ((EQ FLG (QUOTE LIST))
             |,| |with|  FLG |=| (!PPR (QUOTE (QUOTE LIST)) (QUOTE |,|))))
      |to| |a| |QUOTEd| |constant| |,| |e.g.,|
      (!TERM TERM (QUOTE |,|))
      |that| |is| |not| |the| |quotation| |of| |a|
      (COND ((EQ FLG (QUOTE LIST)) |list| |of| |terms|)
            (T |term|))
      |.|))

(DEFUN OUR-QUOTIENT (X Y)
  (COND ((OR (NOT (INTEGERP X))
             (NOT (INTEGERP Y))
             (INT= Y 0))
         (ERROR "In appropriate args to OUR-QUOTIENT: ~A ~A." X Y))
        (T (VALUES (TRUNCATE X Y)))))

(DEFUN R (FORM)
  (CHK-INIT)
  (COND ((NOT (ERROR1-SET (SETQ FORM (TRANSLATE-AND-CHK FORM)))) NIL)
        ((EQ (SETQ TEMP-TEMP (REDUCE-TERM FORM R-ALIST)) (QUOTE *1*FAILED))
         (QUOTE (NOT REDUCIBLE)))
        (T (SETQ TEMP-TEMP (UNTRANSLATE TEMP-TEMP)))))

(DEFUN R-LOOP ()
  (PROG (FORM)
        (CHK-INIT)
        (TERPRI NIL)
        (COND ((EQ R-LOOP-TRACE-MODE (QUOTE PARTIAL))
               (PRINC "Trace Mode:  Partial   " NIL))
              ((EQ R-LOOP-TRACE-MODE (QUOTE FULL))
               (PRINC "Trace Mode:  Full   " NIL))
              (T (PRINC "Trace Mode: Off   " NIL)))
        (COND (R-LOOP-UNTRANSLATE-MODE
               (PRINC "Abbreviated Output Mode:  On" NIL))
              (T (PRINC "Abbreviated Output Mode: Off" NIL)))
        (TERPRI NIL)
        (PRINC "Type ? for help." NIL)
        (TERPRI NIL)
        LOOP
        (PRINC (QUOTE *) NIL)
        (SETQ FORM (READ *STANDARD-INPUT*))
        (FORMAT *STANDARD-OUTPUT* "~&")
        (COND ((R-LOOP1 FORM) (GO LOOP))
              (T (RETURN NIL)))))

(DEFUN R-LOOP1 (FORM)

;   This is the body of the iteration in R-LOOP.  FORM has been
;   read.  We process it and print the answer.  Returning T
;   means continue iterating.  Returning NIL means quit.

  (LET (ANS VAR)
    (CASE FORM
          (? (PRINC "Permitted R-LOOP commands:
    term              evaluate term and prettyprint result
    (SETQ var term)   evaluate term and let var be result
    TRACE             trace mode:  partial
    FULL-TRACE        trace mode:  full
    UNTRACE           trace mode:  off
    ABBREV            enter abbreviated output mode
    UNABBREV          exit abbreviated output mode
    ?                 print this message
    OK                exit R-LOOP" NIL)
             (TERPRI NIL)
             T)
          (OK (PRINC "Exiting R-LOOP." NIL)
              NIL)
          (TRACE (SETQ R-LOOP-TRACE-MODE (QUOTE PARTIAL))
                 (PRINC "Trace Mode:  Partial" NIL)
                 (TERPRI NIL)
                 T)
          (FULL-TRACE (SETQ R-LOOP-TRACE-MODE (QUOTE FULL))
                      (PRINC "Trace Mode:  Full" NIL)
                      (TERPRI NIL)
                      T)
          (UNTRACE (SETQ R-LOOP-TRACE-MODE NIL)
                   (PRINC "Trace Mode: Off" NIL)
                   (TERPRI NIL)
                   T)
          (ABBREV (SETQ R-LOOP-UNTRANSLATE-MODE T)
                  (PRINC "Abbreviated Output Mode:  On" NIL)
                  (TERPRI NIL)
                  T)
          (UNABBREV (SETQ R-LOOP-UNTRANSLATE-MODE NIL)
                    (PRINC "Abbreviated Output Mode: Off" NIL)
                    (TERPRI NIL)
                    T)
          (OTHERWISE
           (SETQ VAR NIL)
           (MATCH FORM (SETQ VAR FORM))
           (COND ((ERROR1-SET (SETQ FORM (TRANSLATE-AND-CHK FORM)))
                  (SETQ ANS (COND (R-LOOP-TRACE-MODE
                                   (REDUCE-TERM-TRACE FORM R-ALIST))
                                  (T (PROG1 (REDUCE-TERM FORM R-ALIST)
                                       (ISPACES 1 NIL)))))
                  (COND ((AND VAR (NOT (EQ ANS (QUOTE *1*FAILED))))
                         (COND ((SETQ TEMP-TEMP (ASSOC-EQ VAR R-ALIST))
                                (RPLACD TEMP-TEMP (CADR ANS)))
                               (T (SETQ R-ALIST
                                        (CONS (CONS VAR (CADR ANS))
                                              R-ALIST))))))
                  (PPRIND (COND
                           ((EQ ANS (QUOTE *1*FAILED))
                            (QUOTE (NOT REDUCIBLE)))
                           (R-LOOP-UNTRANSLATE-MODE (UNTRANSLATE ANS))
                           (T ANS))
                          1 0 NIL)
                  (TERPRI NIL)
                  T)
                 (T T))))))

(DEFUN RANDOM-INITIALIZATION (EVENT)
  (SETQ *RANDOM-SEED* (CONS-COUNT EVENT)))

(DEFUN RANDOM-NUMBER (N)

;  We only use random numbers to vary the English phrases in the
;  output.  We define our own random number generator to maintain
;  uniformity across all the Lisps we use.

  (LET ((LINEAR 267) (MULTIPLIER 317) (MODULUS 4096))
    (OUR-REMAINDER (SETQ *RANDOM-SEED*
                         (OUR-REMAINDER (+ LINEAR (* MULTIPLIER
                                                     *RANDOM-SEED*))
                                        MODULUS))
                   N)))

(DEFUN READ-FILE (FILE-NAME)
  (WITH-OPEN-FILE (FILE FILE-NAME :DIRECTION :INPUT)
    (ITERATE WITH TEMP
             WHILE (PROGN (SETQ TEMP (READ FILE NIL A-VERY-RARE-CONS))
                          (NOT (EQ A-VERY-RARE-CONS TEMP)))
             COLLECT TEMP)))

(DEFUN RECOGNIZER-TERMP (X)
  (COND ((VARIABLEP X) NIL)
        ((FQUOTEP X) NIL)
        ((SETQ TEMP-TEMP (ASSOC-EQ (FFN-SYMB X) RECOGNIZER-ALIST))
         (CDR TEMP-TEMP))
        (T NIL)))

(DEFUN REDUCE-TERM (TERM ALIST)

;   TERM is a term.  ALIST is an alist dotting variable names to EVGs.
;   Reduce TERM under the assumptions that each var is equal to the
;   corresponding constant.  Return the resulting term or *1*FAILED if
;   TERM is not reducible.  REDUCE-TERM is just serving as a name from
;   which REDUCE-TERM1 sometimes THROWs.
  
  (LET ((REDUCE-TERM-CLOCK REDUCE-TERM-CLOCK))
    (CATCH (QUOTE REDUCE-TERM)
      (LIST (QUOTE QUOTE) (REDUCE-TERM1 TERM ALIST)))))

(DEFUN REDUCE-TERM1 (TERM ALIST)
  (COND ((VARIABLEP TERM)
         (COND ((SETQ TEMP-TEMP (ASSOC-EQ TERM ALIST))
                (CDR TEMP-TEMP))
               (T (THROW (QUOTE REDUCE-TERM)
                         (QUOTE *1*FAILED)))))
        ((FQUOTEP TERM)
         (CADR TERM))
        ((EQ (FFN-SYMB TERM) (QUOTE IF))
         (COND ((EQ *1*F (REDUCE-TERM1 (FARGN TERM 1) ALIST))
                (REDUCE-TERM1 (FARGN TERM 3) ALIST))
               (T (REDUCE-TERM1 (FARGN TERM 2) ALIST))))
        (T

;   We special case the fns of arity 0, 1, 2, and 3 to avoid consing up the arg
;   list.

         (SETQ TEMP-TEMP (GET (FFN-SYMB TERM) (QUOTE LISP-CODE)))
         (LET ((TEMP (LENGTH TERM)))
           (COND ((INT= TEMP 1) (FUNCALL TEMP-TEMP))
                 ((INT= TEMP 2) (FUNCALL TEMP-TEMP
                                         (REDUCE-TERM1 (FARGN TERM 1) ALIST)))
                 ((INT= TEMP 3) (FUNCALL TEMP-TEMP
                                         (REDUCE-TERM1 (FARGN TERM 1) ALIST)
                                         (REDUCE-TERM1 (FARGN TERM 2) ALIST)))
                 ((INT= TEMP 4) (FUNCALL TEMP-TEMP
                                         (REDUCE-TERM1 (FARGN TERM 1) ALIST)
                                         (REDUCE-TERM1 (FARGN TERM 2) ALIST)
                                         (REDUCE-TERM1 (FARGN TERM 3) ALIST)))
                 (T (APPLY TEMP-TEMP (ITERATE FOR ARG IN (FARGS TERM)
                                              COLLECT
                                              (REDUCE-TERM1 ARG ALIST)))))))))

;   The following three functions provide a traced single stepper for
;   the logic.  The REDUCE-TERM-TRACE just repeatedly applies
;   REDUCE-TERM-TRACE1, which is the single stepper.

(DEFUN REDUCE-TERM-TRACE (TERM ALIST)
  (LET ((REDUCE-TERM-CLOCK REDUCE-TERM-CLOCK))

;   We protect REDUCE-TERM-CLOCK but don't use it here.
;   REDUCE-TERM-TRACE, since it is printing every step, runs forever
;   -- until the user aborts it.

    (COND ((QUOTEP TERM)
           (PRINC "=" NIL))
          ((EQ (QUOTE *1*FAILED)
               (CATCH (QUOTE REDUCE-TERM)
                 (ITERATE
                  UNTIL (QUOTEP TERM) WITH ANS
                  DO (PROGN (SETQ ANS (REDUCE-TERM-TRACE1 TERM ALIST))
                            (COND ((EQ R-LOOP-TRACE-MODE (QUOTE PARTIAL))
                                   (SETQ ANS (REDUCE-TERM-SUBRS ANS))))
                            (PRINC "=" NIL)
                            (COND ((NOT (QUOTEP ANS))
                                   (PPRIND (COND (R-LOOP-UNTRANSLATE-MODE
                                                  (UNTRANSLATE ANS))
                                                 (T ANS))
                                           1 0 NIL)
                                   (TERPRI NIL)))
                            (SETQ TERM ANS)))))
           (SETQ TERM (QUOTE *1*FAILED))))
    TERM))

(DEFUN REDUCE-TERM-TRACE1 (TERM ALIST)
  (COND ((VARIABLEP TERM)
         (COND ((SETQ TEMP-TEMP (ASSOC-EQ TERM ALIST))
                (LIST (QUOTE QUOTE) (CDR TEMP-TEMP)))
               (T (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))))
        ((FQUOTEP TERM) TERM)
        ((EQ (FFN-SYMB TERM) (QUOTE IF))
         (COND ((QUOTEP (FARGN TERM 1))
                (COND ((EQ (CADR (FARGN TERM 1)) *1*F)
                       (FARGN TERM 3))
                      (T (FARGN TERM 2))))
               (T (FCONS-TERM* (QUOTE IF)
                               (REDUCE-TERM-TRACE1 (FARGN TERM 1) ALIST)
                               (FARGN TERM 2)
                               (FARGN TERM 3)))))
        ((ITERATE FOR ARG IN (FARGS TERM) ALWAYS (QUOTEP ARG))

;   If fn symb is a primitive, eval it.  Otherwise, subst actuals into body.
;   By "primitive" we mean, in THM mode, "having no SDEFN" and, in NQTHM mode,
;   "is a SUBRP."

         (COND ((EQ *1*THM-MODE$ (QUOTE THM))
                (COND ((SETQ TEMP-TEMP (GET (FFN-SYMB TERM) (QUOTE SDEFN)))
                       (SUB-PAIR-VAR (CADR TEMP-TEMP)
                                     (FARGS TERM)
                                     (CADDR TEMP-TEMP)))
                      (T (LIST (QUOTE QUOTE)
                               (APPLY (GET (FFN-SYMB TERM) (QUOTE LISP-CODE))
                                      (ITERATE FOR ARG IN (FARGS TERM)
                                               COLLECT (CADR ARG)))))))
               ((EQ (GET (FFN-SYMB TERM) (QUOTE SUBRP)) *1*T)
                (LIST (QUOTE QUOTE)
                      (APPLY (GET (FFN-SYMB TERM) (QUOTE LISP-CODE))
                             (ITERATE FOR ARG IN (FARGS TERM)
                                      COLLECT (CADR ARG)))))
               ((SETQ TEMP-TEMP (GET (FFN-SYMB TERM) (QUOTE SDEFN)))

;   We can't use (CADDR TEMP-TEMP) for the body here because V&C$ has
;   its "long form" body.  So we use *1**BODY to get the body.

                (SUB-PAIR-VAR (CADR TEMP-TEMP)
                              (FARGS TERM)
                              (*1**BODY (FFN-SYMB TERM))))
               (T (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))))
        (T (CONS-TERM (FFN-SYMB TERM)
                      (REDUCE-TERM-TRACE1-LIST (FARGS TERM) ALIST)))))

(DEFUN REDUCE-TERM-TRACE1-LIST (LST ALIST)
  (COND ((NULL LST) NIL)
        ((QUOTEP (CAR LST))
         (CONS (CAR LST)
               (REDUCE-TERM-TRACE1-LIST (CDR LST) ALIST)))
        (T (CONS (REDUCE-TERM-TRACE1 (CAR LST) ALIST) (CDR LST)))))

(DEFUN REDUCE-TERM-SUBRS (TERM)
  (LET (TEST ARGS)
    (COND ((VARIABLEP TERM)
           TERM)
          ((FQUOTEP TERM) TERM)
          ((EQ (FFN-SYMB TERM) (QUOTE IF))
           (SETQ TEST (REDUCE-TERM-SUBRS (FARGN TERM 1)))
           (COND ((QUOTEP TEST)
                  (COND ((EQ (CADR TEST) *1*F)
                         (REDUCE-TERM-SUBRS (FARGN TERM 3)))
                        (T (REDUCE-TERM-SUBRS (FARGN TERM 2)))))
                 (T (FCONS-TERM* (QUOTE IF)
                                 TEST
                                 (FARGN TERM 2)
                                 (FARGN TERM 3)))))
          (T (SETQ ARGS (ITERATE FOR ARG IN (FARGS TERM)
                                 COLLECT (REDUCE-TERM-SUBRS ARG)))
             (COND ((AND (ITERATE FOR ARG IN ARGS ALWAYS (QUOTEP ARG))
                         (EQ (GET (FFN-SYMB TERM) (QUOTE SUBRP)) *1*T))
                    (LIST (QUOTE QUOTE)
                          (APPLY (GET (FFN-SYMB TERM) (QUOTE LISP-CODE))
                                 (ITERATE FOR ARG IN ARGS
                                          COLLECT (CADR ARG)))))
                   (T (FCONS-TERM (FFN-SYMB TERM) ARGS)))))))

(DEFUN RELEVANT-EVENTS (THM FS)

;  RELEVANT-EVENTS for thm and fs is the set of event names, ev, such
;  that (a) ev mentions some function symbol in the domain of fs
;  (otherwise there would be nothing to instantiate) and that (b)
;  either (i) ev is a DEFN or CONSTRAIN that introduces a function
;  symbol ancestral in thm or some add-axiom or (ii) ev is an
;  add-axiom.

  (ITERATE FOR EVENT-NAME IN
           (UNION-EQ NONCONSTRUCTIVE-AXIOM-NAMES
                     (ANCESTORS
                      (APPEND (ALL-FNNAMES THM)
                              (ITERATE FOR AX IN NONCONSTRUCTIVE-AXIOM-NAMES
                                       APPEND
                                       (ALL-FNNAMES
                                        (CADDDR
                                         (GET AX 'EVENT)))))))
           WHEN (HITP (HITABLE-AXIOM-INTRODUCED-BY EVENT-NAME) FS)
           COLLECT EVENT-NAME))

(DEFUN RELIEVE-HYPS (HYPS)
  (PUSH-LEMMA-FRAME)
  (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
  (COND ((RELIEVE-HYPS1 HYPS)
         (ITERATE FOR X IN (POP-LEMMA-FRAME) DO (PUSH-LEMMA X))
         (ITERATE FOR X IN (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                  DO (PUSH-LINEARIZE-ASSUMPTION X))
         T)
        (T (POP-LEMMA-FRAME)
           (POP-LINEARIZE-ASSUMPTIONS-FRAME)
           NIL)))

(DEFUN RELIEVE-HYPS-NOT-OK (LIT)
  (LET (LIT-ATOM ANS-ATOM)
    (SETQ LIT-ATOM LIT)
    (MATCH LIT (NOT LIT-ATOM))
    (ITERATE FOR ANS IN ANCESTORS THEREIS
             (PROGN
               (SETQ ANS-ATOM ANS)
               (MATCH ANS (NOT ANS-ATOM))
               (COND ((EQUAL LIT ANS)
                      (SETQ RELIEVE-HYPS-NOT-OK-ANS T)
                      T)
                     ((AND (>= (FORM-COUNT LIT-ATOM) (FORM-COUNT ANS-ATOM))
                           (WORSE-THAN-OR-EQUAL LIT-ATOM ANS-ATOM))
                      (SETQ RELIEVE-HYPS-NOT-OK-ANS NIL)
                      T)
                     (T NIL))))))

(DEFUN RELIEVE-HYPS1 (HYPS)
  (COND ((ITERATE FOR HYP IN HYPS AS I FROM 1 WITH (LHS RHS ATOM-HYP)
                  ALWAYS
                  (COND ((LOOKUP-HYP HYP)
                         (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                         T)
                        ((FREE-VARSP HYP UNIFY-SUBST)
                         (COND ((AND (MATCH HYP (EQUAL LHS RHS))
                                     (VARIABLEP LHS)
                                     (NOT (ASSOC-EQ LHS UNIFY-SUBST))
                                     (NOT (FREE-VARSP RHS UNIFY-SUBST)))
                                (SETQ UNIFY-SUBST
                                      (CONS (CONS LHS (REWRITE
                                                       RHS UNIFY-SUBST
                                                       TYPE-ALIST
                                                       (QUOTE ?)
                                                       (QUOTE ID)
                                                       NIL
                                                       I))
                                            UNIFY-SUBST))
                                (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                T)
                               ((SEARCH-GROUND-UNITS HYP)
                                (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                T)
                               (T (SETQ LAST-HYP HYP)
                                  (SETQ LAST-EXIT (QUOTE FREE-VARSP))
                                  NIL)))
                        ((RELIEVE-HYPS-NOT-OK
                          (SETQ INST-HYP (SUBLIS-VAR UNIFY-SUBST HYP)))
                         (SETQ LAST-HYP HYP)
                         (SETQ LAST-EXIT (QUOTE RELIEVE-HYPS-NOT-OK))
                         RELIEVE-HYPS-NOT-OK-ANS)
                        ((FALSE-NONFALSEP INST-HYP)
                         (SETQ LAST-HYP HYP)
                         (SETQ LAST-EXIT (QUOTE FALSE-NONFALSEP))
                         (NOT DEFINITELY-FALSE))
                        ((MEMBER-EQUAL INST-HYP
                                       LITS-THAT-MAY-BE-ASSUMED-FALSE)
                         (SETQ LAST-HYP HYP)
                         (SETQ LAST-EXIT
                               (QUOTE LITS-THAT-MAY-BE-ASSUMED-FALSE))
                         NIL)
                        ((MATCH HYP (NOT ATOM-HYP))
                         (LET ((ANCESTORS (CONS (DUMB-NEGATE-LIT INST-HYP)
                                                ANCESTORS)))
                           (SETQ LAST-EXIT
                                 (REWRITE ATOM-HYP UNIFY-SUBST TYPE-ALIST
                                          (QUOTE FALSE)
                                          (QUOTE IFF)
                                          NIL
                                          I))
                           (SETQ LAST-HYP HYP)
                           (EQUAL LAST-EXIT FALSE)))
                        (T (LET ((ANCESTORS (CONS (DUMB-NEGATE-LIT INST-HYP)
                                                  ANCESTORS)))
                             (SETQ LAST-EXIT
                                   (NORMALIZE-IFS
                                    (REWRITE HYP UNIFY-SUBST TYPE-ALIST
                                             (QUOTE TRUE)
                                             (QUOTE IFF)
                                             NIL
                                             I)
                                    NIL
                                    NIL
                                    T))
                             (SETQ LAST-HYP HYP)
                             
;   Could be NOT-IDENT FALSE but LAST-EXIT was just rewritten with IFF.
                             
                             (EQUAL LAST-EXIT TRUE)))))
         T)
        (T NIL)))

(DEFUN OUR-REMAINDER (X Y)
  (COND ((OR (NOT (INTEGERP X))
             (NOT (INTEGERP Y))
             (INT= Y 0))
         (ERROR "Inappropriate args to OUR-REMAINDER: ~A ~A." X Y))
        (T (REM X Y))))

(DEFUN REMOVE-*2*IFS (X)
  (LET (REST)
    (COND ((ATOM X) X)
          ((EQ (CAR X) (QUOTE QUOTE)) X)
          ((EQ (CAR X) (QUOTE *2*IF))
           (SETQ REST (REMOVE-*2*IFS (CADDDR X)))
           (CONS (QUOTE COND)
                 (CONS (LIST (REMOVE-*2*IFS (CADR X))
                             (REMOVE-*2*IFS (CADDR X)))
                       (COND ((AND (CONSP REST) (EQ (CAR REST) (QUOTE COND)))
                              (CDR REST))
                             (T (LIST (LIST T REST)))))))
          (T (CONS (CAR X)
                   (ITERATE FOR ARG IN (CDR X)
                            COLLECT (REMOVE-*2*IFS ARG)))))))

(DEFUN REMOVE-IDENTITY (TERM WARN-FLG)

; This function returns the result of replacing zero or more calls of IDENTITY
; from TERM by provably equivalent subterms.

; This feature was designed and originally implemented by Matt Kaufmann in
; response to complaints from several users that Nqthm did not provide a
; mechanism by which large constants could be usefully abbreviated.

  (COND
   ((OR (VARIABLEP TERM)
        (FQUOTEP TERM))
    TERM)
   ((AND (EQ (FFN-SYMB TERM) 'IDENTITY)
         (NULL (ALL-VARS (FARGN TERM 1))))
    (LET* ((ARG (FARGN TERM 1))
           (VAL (REDUCE-TERM ARG NIL)))
          (COND
           ((EQ VAL (QUOTE *1*FAILED))
            (IF WARN-FLG
                (ER WARNING (TERM) |Unable|
                    |to| |evaluate| |the| |term| (!TERM TERM (QUOTE |.|))))
            TERM)
           (T
            VAL))))
   ((FNNAMEP 'IDENTITY TERM)
    (CONS-TERM (FFN-SYMB TERM)
               (ITERATE FOR ARG IN (FARGS TERM)
                        COLLECT (REMOVE-IDENTITY ARG WARN-FLG))))
   (T TERM)))

(DEFUN REMOVE-NEGATIVE (LIT CL)
  (COND ((ATOM CL) NIL)
        ((COMPLEMENTARYP LIT (CAR CL)) (CDR CL))
        (T (CONS (CAR CL) (REMOVE-NEGATIVE LIT (CDR CL))))))

(DEFUN REMOVE-REDUNDANT-TESTS (TO-DO DONE)

;   When this function was conceived, we used to run the following code.
;   However, we have trivialized the effect because we found that it sometimes
;   hurt.  In particular, if the tests were (LISTP X) and (EQUAL (CAAR X)
;   (QUOTE FOO)), the LISTP could get removed.  But then the LISTP has to be
;   rederived when it comes up during a proof.  It is speculated that the
;   original motivation for this function was messy base cases, which was
;   altered if not fixed by carrying around the base cases in the
;   INDUCTION-MACHINE.  The following code is left in case a real removal of
;   tests is deemed necessary.

;       ( COND ((NULL TO-DO) DONE)
;             ((AND (SIMPLIFY-CLAUSE-MAXIMALLY
;                     (CONS (CAR TO-DO)
;                           (APPEND (ITERATE FOR X IN (CDR TO-DO)
;                                         COLLECT (NEGATE-LIT X))
;                                   (ITERATE FOR X IN DONE
;                                         COLLECT (NEGATE-LIT X)))))
;                   (NULL PROCESS-CLAUSES))

;   The lemmas on PROCESS-HIST will have been added to ALL-LEMMAS-USED by
;   SIMPLIFY-CLAUSE under SIMPLIFY-CLAUSE-MAXIMALLY and ALL-LEMMAS-USED is
;   correctly initialized and processed by DEFN-SETUP and the post processing
;   in DEFN.

;              (REMOVE-REDUNDANT-TESTS (CDR TO-DO) DONE))
;             (T (REMOVE-REDUNDANT-TESTS
;                  (CDR TO-DO)
;                  (CONS (CAR TO-DO) DONE)))).

  (APPEND TO-DO DONE))

(DEFUN REMOVE1 (X LST)
  (COND ((ATOM LST) NIL)
        ((EQ X (CAR LST)) (CDR LST))
        (T (CONS (CAR LST) (REMOVE1 X (CDR LST))))))

(DEFUN REMOVE-TRIVIAL-EQUATIONS (CL)
  (ITERATE WITH (LHS RHS) WHILE
           (ITERATE FOR LIT IN CL THEREIS
                    (AND (OR (AND (MATCH LIT (NOT (EQUAL LHS RHS)))
                                  (OR (AND (VARIABLEP LHS)
                                           (NOT (OCCUR LHS RHS)))
                                      (AND (PROG2 (OUR-SWAP LHS RHS) T)
                                           (VARIABLEP LHS)
                                           (NOT (OCCUR LHS RHS)))))
                             (AND (VARIABLEP LIT)
                                  (PROGN (SETQ LHS LIT) (SETQ RHS FALSE) T)))
                         (PROGN (SETQ CL (ITERATE FOR LIT2 IN CL
                                                  UNLESS (EQ LIT LIT2)
                                                  COLLECT
                                                  (SUBST-VAR RHS LHS LIT2)))
                                T))))
  (ITERATE WITH (LHS RHS) WHILE
           (ITERATE FOR LIT IN CL
                    THEREIS (AND (MATCH LIT (NOT (EQUAL LHS RHS)))
                                 (OR (AND (NOT (QUOTEP LHS)) (QUOTEP RHS))
                                     (AND (PROG2 (OUR-SWAP LHS RHS) T)
                                          (NOT (QUOTEP LHS))
                                          (QUOTEP RHS)))
                                 (ITERATE
                                  FOR LIT2 IN CL WHEN (NOT (EQ LIT LIT2))
                                  THEREIS (OCCUR LHS LIT2))
                                 (SETQ CL
                                       (ITERATE
                                        FOR LIT2 IN CL
                                        COLLECT
                                        (COND
                                         ((OR (EQ LIT LIT2)
                                              (NOT (OCCUR LHS LIT2)))
                                          LIT2)
                                         (T (SUBST-EXPR RHS LHS LIT2))))))))
  CL)

(DEFUN REMOVE-UNCHANGING-VARS (CAND-LST CL-SET)
  (LET (NOT-CHANGING-VARS)
    (SETQ NOT-CHANGING-VARS
          (ITERATE FOR CL IN CL-SET WITH ITERATE-ANS DO
                   (SETQ ITERATE-ANS
                         (UNION-EQ (ITERATE
                                    FOR LIT IN CL WITH ITERATE-ANS DO
                                    (SETQ ITERATE-ANS
                                          (UNION-EQ (UNCHANGING-VARS LIT)
                                                    ITERATE-ANS))
                                    FINALLY (RETURN ITERATE-ANS))
                                   ITERATE-ANS))
                   FINALLY (RETURN ITERATE-ANS)))
    (OR (ITERATE FOR CAND IN CAND-LST
                 UNLESS (INTERSECTP (ACCESS CANDIDATE CHANGED-VARS CAND)
                                    NOT-CHANGING-VARS)
                 COLLECT CAND)
        CAND-LST)))

(DEFUN REWRITE (TERM ALIST TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG LOC)

;   Returns a term that is equal (modulo ID-IFF) to the result of
;   substituting ALIST into TERM under the hypotheses of (a)
;   TYPE-ALIST, (b) the conjunction of the top frame of
;   LINEARIZE-ASSUMPTIONS-STACK, and (c) some subset S of
;   SIMPLIFY-CLAUSE-POT-LST such that if x = (LIST 'MARK) is MEMBER-EQ
;   the LEMMAS field of some poly in S, then x is a member of the top
;   frame of the LEMMA-STACK.

;   LOC is an arbitrary object that describes the "location" of the current
;   TERM in the parent term that caused this call of rewrite.  If the
;   REWRITE-PATH is being maintained, LOC is used as the location entry
;   for the frame built for this rewrite.

  (COND ((VARIABLEP TERM)
         (REWRITE-SOLIDIFY (COND ((SETQ TEMP-TEMP (ASSOC-EQ TERM ALIST))
                                  (CDR TEMP-TEMP))
                                 (T TERM))))
        ((FQUOTEP TERM) TERM)
        ((EQ (FFN-SYMB TERM) (QUOTE IF))
         (PUSH-REWRITE-PATH-FRAME 'REWRITE TERM ALIST LOC)
         (PROG1 (REWRITE-IF (REWRITE (FARGN TERM 1)
                                     ALIST TYPE-ALIST (QUOTE ?)
                                     (QUOTE IFF)
                                     NIL
                                     1)
                            (FARGN TERM 2)
                            (FARGN TERM 3)
                            TYPE-ALIST)
           (POP-REWRITE-PATH-FRAME)))
        ((SETQ TEMP-TEMP (NOT-TO-BE-REWRITTENP TERM ALIST))
         (REWRITE-SOLIDIFY TEMP-TEMP))
        (T
         (PUSH-REWRITE-PATH-FRAME 'REWRITE TERM ALIST LOC)
         (PROG1
             (LET ((ARGS (ITERATE FOR ARG IN (FARGS TERM)
                                  AS I FROM 1
                                  COLLECT (REWRITE ARG ALIST TYPE-ALIST
                                                   (QUOTE ?)
                                                   (QUOTE ID)
                                                   NIL
                                                   I)))
                   TEMP
                   (FN (GET (FFN-SYMB TERM) (QUOTE LISP-CODE)))
                   (REDUCE-TERM-CLOCK REDUCE-TERM-CLOCK))
               (COND ((AND FN
                           (ITERATE FOR ARG IN ARGS ALWAYS (QUOTEP ARG))
                           (NOT (DISABLEDP FN))
                           (OR (NULL (GET (FFN-SYMB TERM) (QUOTE EVENT)))
                               (NULL (CDAR DEFINED-FUNCTIONS-TOGGLED)))
                           (NOT (EQ (QUOTE *1*FAILED)
                                    (SETQ TEMP
                                          (CATCH (QUOTE REDUCE-TERM)
                                            (APPLY FN
                                                   (ITERATE
                                                    FOR ARG IN ARGS
                                                    COLLECT (CADR ARG))))))))
                      (PUSH-LEMMA (FFN-SYMB TERM))
                      (LIST (QUOTE QUOTE) TEMP))
                     (T
                    
;   The use of FCONS-TERM below is justified by the immediately preceding
;   computation given that shell constructors cannot be disabled.
                    
                      (SETQ TEMP (REWRITE-TYPE-PRED
                                  (FCONS-TERM (FFN-SYMB TERM) ARGS)))
                      (SETQ TEMP (REWRITE-EVAL$ TEMP OBJECTIVE
                                                ID-IFF DEFN-FLG))
                      (SETQ TEMP (REWRITE-APPLY$ TEMP OBJECTIVE
                                                 ID-IFF DEFN-FLG))
                      (COND ((EQ *1*THM-MODE$ (QUOTE NQTHM))
                             (SETQ TEMP (REWRITE-V&C$-AND-EVAL$-FLG TEMP))
                             (SETQ TEMP (REWRITE-FOR TEMP TYPE-ALIST))
                             (SETQ TEMP (REWRITE-APPLY-SUBR TEMP OBJECTIVE
                                                            ID-IFF
                                                            DEFN-FLG))
                             (SETQ TEMP (REWRITE-CAR-V&C$
                                         TEMP OBJECTIVE ID-IFF DEFN-FLG))
                             (SETQ TEMP (REWRITE-CAR-V&C-APPLY$
                                         TEMP OBJECTIVE ID-IFF DEFN-FLG))
                             (SETQ TEMP (REWRITE-V&C$
                                         TEMP OBJECTIVE ID-IFF DEFN-FLG))
                             (SETQ TEMP (REWRITE-V&C-APPLY$
                                         TEMP OBJECTIVE ID-IFF DEFN-FLG))))
                      (REWRITE-WITH-LEMMAS TEMP))))
           (POP-REWRITE-PATH-FRAME)))))

(DEFUN REWRITE-CAR-V&C-APPLY$ (TERM OBJECTIVE ID-IFF DEFN-FLG)
  (LET (FN ACTUALS)

;   This code relies upon the following theorems.
;
;   (CAR (V&C-APPLY$ (QUOTE IF) args))
;      =
;   (IF (CAR args)
;       (IF (CAAR args)
;           (CAADR args)
;           (CAADDR args))
;       0)
;
;   And, for all TOTALP fn other than IF:
;
;   (CAR (V&C-APPLY$ (QUOTE fn) args))
;      =
;   (IF (MEMBER F args)
;       0
;       (fn (CAAR args) ... (CAAD...DR args)))
;
;   The first follows immediately from the axiom introducing V&C-APPLY$, with
;   the observation that (CAR (FIX-COST a)) = (CAR a).  The second is the
;   fundamental theorem about TOTALP.

;   We also use the theorem that:
;   (CAR (V&C-APPLY$ (QUOTE x) args))
;      =
;   (IF (MEMBER F args)
;       0
;       F)
;   when (QUOTE x) is not a LITATOM.  The follows from the definition of
;   V&C-APPLY$, the fact that SUBRP (QUOTE x) is F, and (BODY (QUOTE x))
;   is F.

    (CHK-NQTHM-MODE$ (QUOTE REWRITE-CAR-V&C-APPLY$))
    (COND ((MATCH TERM (CAR (V&C-APPLY$
                             (LIST (QUOTE QUOTE) FN) ACTUALS)))
           (COND ((OR (DISABLEDP 'REWRITE-CAR-V&C-APPLY$)
                      (AND (CONSP FN)
                           (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
                           (EQ (CADR FN) 'PACK)))
                  TERM)           
                 ((OR (NOT (SYMBOLP FN))
                           (EQ FN *1*T)
                           (EQ FN *1*F))
                  (PUSH-LEMMA (QUOTE REWRITE-CAR-V&C-APPLY$))
                  (NORMALIZE-IFS
                   (REWRITE
                    (FCONS-TERM* (QUOTE IF)
                                 (FCONS-TERM* (QUOTE MEMBER)
                                              FALSE (QUOTE ACTUALS))
                                 ZERO
                                 FALSE)
                    (LIST (CONS (QUOTE ACTUALS) ACTUALS))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    '(BUILTIN-RULE REWRITE-CAR-V&C-APPLY$))
                   NIL NIL
                   (EQ ID-IFF (QUOTE IFF))))
                 ((TOTALP FN)
                  (PUSH-LEMMA (QUOTE REWRITE-CAR-V&C-APPLY$))
                  (NORMALIZE-IFS
                   (REWRITE
                    (COND ((EQ FN (QUOTE IF))
                           (QUOTE (IF (CAR ACTUALS)
                                      (IF (CAR (CAR ACTUALS))
                                          (CAR (CAR (CDR ACTUALS)))
                                          (CAR (CAR (CDR (CDR ACTUALS)))))
                                      (QUOTE 0))))
                          (T
                           (FCONS-TERM*
                            (QUOTE IF)
                            (FCONS-TERM* (QUOTE MEMBER) FALSE (QUOTE ACTUALS))
                            ZERO
                            (CONS-TERM
                             FN
                             (ITERATE FOR I FROM 1 TO (ARITY FN)
                                      COLLECT
                                      (FCONS-TERM*
                                       (QUOTE CAR)
                                       (FCONS-TERM-NTH I (QUOTE ACTUALS))))))))
                    (LIST (CONS (QUOTE ACTUALS) ACTUALS))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    '(BUILTIN-RULE REWRITE-CAR-V&C-APPLY$))
                   NIL NIL
                   (EQ ID-IFF (QUOTE IFF))))
                 (T TERM)))
          (T TERM))))

(DEFUN REWRITE-APPLY$ (TERM OBJECTIVE ID-IFF DEFN-FLG)
  (LET (FN ACTUALS)

;   Rewrite (APPLY$ (QUOTE fn) actuals), where fn is TOTALP, to
;   (fn (CAR actuals) (CADR actuals) ... (CAD...DR actuals)).

    (COND ((MATCH TERM (APPLY$ (LIST (QUOTE QUOTE) FN) ACTUALS))
           (COND ((OR (DISABLEDP 'REWRITE-APPLY$)
                      (AND (CONSP FN)
                           (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
                           (EQ (CADR FN) 'PACK)))
                  TERM)
                 ((OR (NOT (SYMBOLP FN))
                      (EQ FN *1*T)
                      (EQ FN *1*F))

;   (APPLY$ (QUOTE x) actuals), where (QUOTE x) is not a LITATOM
;   is F.  See the argument above in REWRITE-CAR-V&C-APPLY$.
                  
                  (PUSH-LEMMA (QUOTE REWRITE-APPLY$))
                  FALSE)
                 ((TOTALP FN)
                  (PUSH-LEMMA (QUOTE REWRITE-APPLY$))
                  (NORMALIZE-IFS
                   (REWRITE
                    (CONS-TERM FN
                               (ITERATE FOR I FROM 1 TO (ARITY FN)
                                        COLLECT
                                        (FCONS-TERM-NTH I (QUOTE ACTUALS))))
                    (LIST (CONS (QUOTE ACTUALS) ACTUALS))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    '(BUILTIN-RULE REWRITE-APPLY$))
                   NIL NIL
                   (EQ ID-IFF (QUOTE IFF))))
                 (T TERM)))
          (T TERM))))

(DEFUN REWRITE-APPLY-SUBR (TERM OBJECTIVE ID-IFF DEFN-FLG)
  (LET (FN ACTUALS)

;   The theorems we rely upon here are:
;     (APPLY-SUBR (QUOTE fn) args) = (fn (CAR args) ... (CAD...DR args))
;   where fn is a SUBRP.  And
;     (APPLY-SUBRP (QUOTE fn) args) = F.
;   where fn is not the evg of a LITATOM or is not a SUBRP.

    (CHK-NQTHM-MODE$ (QUOTE REWRITE-APPLY-SUBR))
    (COND ((AND (MATCH TERM (APPLY-SUBR (LIST (QUOTE QUOTE) FN) ACTUALS))
                (NOT (DISABLEDP 'REWRITE-APPLY-SUBR)))
           (COND ((AND (CONSP FN)
                       (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
                       (EQ (CADR FN) 'PACK))
                  TERM)
                 ((OR (NOT (SYMBOLP FN))
                      (EQ FN *1*T)
                      (EQ FN *1*F)
                      (EQ (GET FN (QUOTE SUBRP)) *1*F))
                  (PUSH-LEMMA (QUOTE REWRITE-APPLY-SUBR))
                  FALSE)
                 ((AND (EQ (GET FN (QUOTE SUBRP)) *1*T)
                       (NOT (GET FN (QUOTE ERRATICP))))

;   Note that this code implicitly exploits the fact that
;   (APPLY-SUBR (QUOTE IF) args) = (IF (CAR args) ...).

                  (PUSH-LEMMA (QUOTE REWRITE-APPLY-SUBR))
                  (NORMALIZE-IFS
                   (REWRITE
                    (CONS-TERM
                     FN
                     (ITERATE FOR I FROM 1 TO (ARITY FN) COLLECT
                              (FCONS-TERM-NTH I (QUOTE ACTUALS))))
                    (LIST (CONS (QUOTE ACTUALS) ACTUALS))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    '(BUILTIN-RULE REWRITE-APPLY-SUBR))
                   NIL NIL
                   (EQ ID-IFF (QUOTE IFF))))
                 (T TERM)))
          (T TERM))))

(DEFUN REWRITE-V&C$ (TERM OBJECTIVE ID-IFF DEFN-FLG)

;   Apply the theorem that (V&C$ flg form a) is non-F if either

;   (1) flg is 'LIST, or
;   (2) form is (QUOTE term) where term is a TAMEP TERMP.

;   The first follows immediately from the definition of V&C$.  The second is
;   the Fundamental Theorem about TAMEP with one twist, we don't care if flg is
;   T.  See the discussion below.

  (LET (FLG FORM)
    (CHK-NQTHM-MODE$ (QUOTE REWRITE-V&C$))
    (COND ((AND (EQ ID-IFF (QUOTE IFF))
                (MATCH TERM (V&C$ FLG FORM &))
                (NOT (DISABLEDP 'REWRITE-V&C$)))
           (COND ((AND (QUOTEP FLG)
                       (EQUAL (CADR FLG) (QUOTE LIST)))
                  (PUSH-LEMMA (QUOTE REWRITE-V&C$))
                  TRUE)
                 ((AND (QUOTEP FORM)
                       (TERMP (CADR FORM))
                       (TAMEP (CADR FORM)))

;   The code above would be obviously correct if we checked also that (QUOTEP
;   FLG) and (CADR FLG) is not 'LIST.  But it is correct as it stands because
;   TERM is equal to (IF (EQUAL FLG 'LIST) TERM TERM), in the true branch the
;   case above obtains and we get T; in the false branch we rely on the fact
;   that (V&C$ FLG x a) = (V&C$ T x a) if FLG isn't 'LIST.  We then apply the
;   Fundamental Theorem about TAMEP.

;   However, this code isn't as useful as it may seem since we still require
;   FORM to be a QUOTEd TERMP. 
                  
                  (PUSH-LEMMA (QUOTE REWRITE-V&C$))
                  TRUE)
                 (T TERM)))
          (T TERM))))

(DEFUN REWRITE-V&C$-AND-EVAL$-FLG (TERM)

;   Apply the theorem:
;   flg /= 'LIST -> (V&C$ flg form a) = (V&C$ T form a)
;   and the analogous theorem about EVAL$.  We search the
;   TYPE-ALIST for the hypothesis (EQUAL flg (QUOTE LIST))
;   assumed false.

  (LET (FLG FORM ALIST)
    (CHK-NQTHM-MODE$ (QUOTE REWRITE-V&C$-AND-EVAL$-FLG))
    (COND ((AND (OR (MATCH TERM (V&C$ FLG FORM ALIST))
                    (MATCH TERM (EVAL$ FLG FORM ALIST)))
                (NOT (EQUAL FLG (QUOTE (QUOTE LIST))))
                (NOT (EQUAL FLG TRUE))
                (SETQ TEMP-TEMP (ASSOC-EQUAL (FCONS-TERM* (QUOTE EQUAL)
                                                          FLG
                                                          (QUOTE (QUOTE LIST)))
                                             TYPE-ALIST))
                (EQUAL (CDR TEMP-TEMP) TYPE-SET-FALSE))
           (PUSH-LEMMA (FFN-SYMB TERM))
           (FCONS-TERM* (FFN-SYMB TERM) TRUE FORM ALIST))
          (T TERM))))

(DEFUN REWRITE-V&C-APPLY$ (TERM OBJECTIVE ID-IFF DEFN-FLG)

;   Apply the theorems:

;   (V&C-APPLY$ (QUOTE IF) args)
;     <->
;   (IF (CAR ARGS)
;       (IF (CAR (CAR ARGS))
;           (CAR (CDR ARGS))
;           (CAR (CDR (CDR ARGS))))
;       F)

;   and

;   If (TOTALP fn) or (QUOTE fn) is not a LITATOM
;      then (V&C-APPLY$ (QUOTE fn) args) <-> (NOT (MEMBER F args))

;   The former follows immediately from the defn of V&C-APPLY$ since
;   (FIX-COST x a) <-> x.  The latter is the Fundamental Theorem about TOTALP
;   along with the observation that the BODY of a non-LITATOM is F.

  (LET (FN ARGS)
    (CHK-NQTHM-MODE$ (QUOTE REWRITE-V&C-APPLY$))
    (COND ((AND (EQ ID-IFF (QUOTE IFF))
                (MATCH TERM (V&C-APPLY$ (LIST (QUOTE QUOTE) FN)
                                        ARGS))
                (OR (EQ (*1*LITATOM FN) *1*F)
                    (AND (SYMBOLP FN)
                         (TOTALP FN)))
                (NOT (DISABLEDP 'REWRITE-V&C-APPLY$)))
           (PUSH-LEMMA (QUOTE REWRITE-V&C-APPLY$))
           (REWRITE (COND ((EQ FN (QUOTE IF))
                           (QUOTE (IF (CAR ARGS)
                                      (IF (CAR (CAR ARGS))
                                          (CAR (CDR ARGS))
                                          (CAR (CDR (CDR ARGS))))
                                      FF)))
                          (T (QUOTE (NOT (MEMBER FF ARGS)))))
                    (LIST (CONS (QUOTE ARGS) ARGS)
                          (CONS (QUOTE FF) FALSE))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    '(BUILTIN-RULE REWRITE-V&C-APPLY$)))
          (T TERM))))

(DEFUN REWRITE-CAR-V&C$ (TERM OBJECTIVE ID-IFF DEFN-FLG)

;   We apply the theorem that 
;   (CAR (V&C$ T (QUOTE term) a))
;     =
;   (IF (V&C$ T (QUOTE term) a)
;       term/c(a)
;       0)

;   if term is a non-erratic TERMP and a is a semi-concrete alist.

  (LET (FLG B FORM ALIST REWRITE-ALIST)
    (CHK-NQTHM-MODE$ (QUOTE REWRITE-CAR-V&C$))
    (COND ((AND (MATCH TERM (CAR (V&C$ (LIST (QUOTE QUOTE) FLG)
                                       (LIST (QUOTE QUOTE) FORM)
                                       ALIST)))
                (NOT (EQ FLG (QUOTE LIST)))
                (TERMP FORM)
                (NOT (ERRATICP FORM))
                (SEMI-CONCRETE-ALISTP ALIST)
                (NOT (DISABLEDP 'REWRITE-CAR-V&C$)))
           (SETQ REWRITE-ALIST
                 (COMPLETE-ALIST (ALL-VARS FORM)
                                 (MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST
                                  ALIST)))
           (PUSH-LEMMA (QUOTE REWRITE-CAR-V&C$))
           (SETQ B (NORMALIZE-IFS
                    (REWRITE FORM REWRITE-ALIST TYPE-ALIST
                             OBJECTIVE ID-IFF DEFN-FLG
                             '(BUILTIN-RULE REWRITE-CAR-V&C$))
                    NIL NIL
                    (EQ ID-IFF (QUOTE IFF))))
           (FCONS-TERM* (QUOTE IF) (FARGN TERM 1) B ZERO))
          (T TERM))))

(DEFUN REWRITE-EVAL$ (TERM OBJECTIVE ID-IFF DEFN-FLG)

;   We apply the theorem:

;   (EVAL$ T (QUOTE term) a) = term/c(a)
;   where term is a TAMEP TERMP and a is semi-concrete

;   and
;   (EVAL$ T (CONS (QUOTE fn) args) a)
;      =
;   (fn (EVAL$ T (CAR args) a)
;       ...
;       (EVAL$ T (CAD...DR args) a))
;   where (TOTALP fn).

  (LET (FLG FORM FN ACTUALS ALIST REWRITE-ALIST)
    (COND ((AND (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                   (LIST (QUOTE QUOTE) FORM)
                                   ALIST))
                (NOT (EQ FLG (QUOTE LIST)))
                (TERMP FORM)
                (TAMEP FORM)
                (SEMI-CONCRETE-ALISTP ALIST)
                (NOT (DISABLEDP 'REWRITE-EVAL$)))
           (SETQ REWRITE-ALIST
                 (COMPLETE-ALIST (ALL-VARS FORM)
                                 (MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST
                                  ALIST)))
           (PUSH-LEMMA (QUOTE REWRITE-EVAL$))
           (NORMALIZE-IFS
            (REWRITE FORM REWRITE-ALIST TYPE-ALIST
                     OBJECTIVE ID-IFF DEFN-FLG
                     '(BUILTIN-RULE REWRITE-EVAL$))
            NIL NIL
            (EQ ID-IFF (QUOTE IFF))))
          ((AND (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                   FORM
                                   ALIST))
                (NOT (EQ FLG (QUOTE LIST)))
                (NVARIABLEP FORM)
                ; FORM=(CONS (QUOTE fn) actuals)
                (EQ (FN-SYMB FORM) (QUOTE CONS))
                (QUOTEP (ARGN FORM 1))
                (SYMBOLP (SETQ FN (CADR (ARGN FORM 1))))
                (NOT (EQ FN *1*T))
                (NOT (EQ FN *1*F))
                (TOTALP FN)
                (NOT (DISABLEDP 'REWRITE-EVAL$)))
           (PUSH-LEMMA (QUOTE REWRITE-EVAL$))
           (SETQ ACTUALS (ARGN FORM 2))
           (NORMALIZE-IFS
            (REWRITE
             (CONS-TERM
              FN
              (ITERATE FOR I FROM 1 TO (ARITY FN) COLLECT
                       (FCONS-TERM* (QUOTE EVAL$)
                                    TRUE
                                    (FCONS-TERM-NTH I (QUOTE ACTUALS))
                                    (QUOTE ALIST))))
             (LIST (CONS (QUOTE ACTUALS) ACTUALS)
                   (CONS (QUOTE ALIST) ALIST))
             TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
             '(BUILTIN-RULE REWRITE-EVAL$))
            NIL NIL
            (EQ ID-IFF (QUOTE IFF))))
          (T TERM))))
     
(DEFUN REWRITE-FNCALL (*FNNAME* *ARGLIST*)
  (CATCH
      (QUOTE REWRITE-FNCALL)
    (LET (VALUE SDEFN (FNSTACK FNSTACK)
                *CONTROLLER-COMPLEXITIES*
                (LEMMA-STACK LEMMA-STACK)
                (REWRITE-PATH-STK-PTR0 REWRITE-PATH-STK-PTR) 
                (LINEARIZE-ASSUMPTIONS-STACK
                 LINEARIZE-ASSUMPTIONS-STACK)
                (*TYPE-ALIST* TYPE-ALIST))
      (SETQ SDEFN (GET *FNNAME* (QUOTE SDEFN)))
      (COND ((NULL SDEFN)
             (REWRITE-SOLIDIFY (CONS-TERM *FNNAME* *ARGLIST*)))
            ((OR (MEMBER-EQ *FNNAME* FNSTACK)
                 (DISABLEDP *FNNAME*))
             (REWRITE-SOLIDIFY (CONS-TERM *FNNAME* *ARGLIST*)))
            (T (SETQ *CONTROLLER-COMPLEXITIES*
                     (ITERATE FOR MASK IN (GET *FNNAME*
                                               (QUOTE CONTROLLER-POCKETS))
                              COLLECT (ITERATE
                                       FOR ARG IN *ARGLIST*
                                       WHEN (PROG1 (NOT (CT= (CTLOGAND MASK 1)
                                                             0))
                                              (SETQ MASK (CTASH MASK -1)))
                                       SUM
                                       (PROGN
                                         (OR (QUOTEP ARG)
                                             (SETQ VALUE NIL))
                                         (MAX-FORM-COUNT ARG)))))
               (SETQ FNSTACK (CONS *FNNAME* FNSTACK))

;   Add the name of the current fn to the FNSTACK so that when we see recursive
;   calls in the body we won't be tempted to go into them.  There is an odd
;   aspect to the use of FNSTACK by this function.  Suppose that in the
;   rewriting of the body of fn we apply a lemma and backwards chain to some
;   hyp.  Suppose the hyp contains a call of fn.  Then when we try to rewrite
;   fn in the hyp we will think it is a recursive call and quit due to the
;   (MEMBER-EQ *FNNAME* FNSTACK) above.  Once upon a time, when we did not
;   preprocess the hyps of lemmas at all and did not
;   EXPAND-BOOT-STRAP-NON-REC-FNS in defns this problem burned us on (ZEROP
;   expr) because inside the defn of ZEROP we saw (EQUAL expr 0) and we
;   backward chained to something with a ZEROP hyp and shied away from it.
;   This occurred while trying to use LITTLE-STEP under PRIME-KEY under
;   QUOTIENT-DIVIDES in the proof of PRIME-LIST-TIMES-LIST -- the ZEROP we were
;   expanding was that in the DIVIDES hyp of PRIME-KEY and the ZEROP we shied
;   away from was that in PRIME in LITTLE-STEP.  We implemented makeshift fix
;   to that by not putting nonrec fns onto FNSTACK here.  But that does not
;   prevent us from shying away from calls to recursive fns encountered in
;   lemmas while somehow under the body of the fn.  Worse, it turns out to be
;   very expensive.  Suppose we eliminate ZEROP by expanding it in
;   preprocessing.  Then PRIME-LIST-TIMES-LIST is proved whether we put nonrec
;   fns onto the stack or not.  But if we do not, it takes 248K conses while if
;   we do it takes 140K.  So we have gone back to putting everything on the
;   stack and await the day that shying away from a spurious "recursive call"
;   gets us.

               (PUSH-LEMMA-FRAME)
               (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
               (SETQ VALUE (REWRITE (CADDR SDEFN)
                                    (ITERATE FOR VAR IN (CADR SDEFN)
                                             AS VAL IN *ARGLIST*
                                             COLLECT (CONS VAR VAL))
                                    TYPE-ALIST OBJECTIVE ID-IFF T
                                    'BODY))
               (COND ((NULL (GET *FNNAME* (QUOTE INDUCTION-MACHINE)))

;   We are dealing with a nonrec fn.  If we are at the top level of the clause
;   but the expanded body has too many IFs in it compared to the number of IFs
;   in the args, we do not use the expanded body.  Because we know the IFs in
;   the args will be classified out soon and we do not want to swamp CLAUSIFY
;   by giving it too many at once.  Otherwise we use the expanded body.

                      (COND ((AND (ITERATE FOR X IN (CDR FNSTACK) NEVER
                                           (GET X (QUOTE INDUCTION-MACHINE)))
                                  (TOO-MANY-IFS *ARGLIST* VALUE))
                             (POP-LEMMA-FRAME)
                             (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                             (REWRITE-SOLIDIFY (FCONS-TERM *FNNAME*
                                                           *ARGLIST*)))
                            (T (ITERATE FOR X
                                        IN (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                                        DO (PUSH-LINEARIZE-ASSUMPTION X))
                               (ITERATE FOR X IN (POP-LEMMA-FRAME)
                                        DO (PUSH-LEMMA X))
                               (PUSH-LEMMA *FNNAME*)
                               VALUE)))
                     ((REWRITE-FNCALLP *FNNAME* VALUE)
                      (ITERATE FOR X IN (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                               DO (PUSH-LINEARIZE-ASSUMPTION X))
                      (ITERATE FOR X IN (POP-LEMMA-FRAME) DO (PUSH-LEMMA X))
                      (PUSH-LEMMA *FNNAME*)
                      VALUE)
                     (T (POP-LEMMA-FRAME)
                        (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                        (REWRITE-SOLIDIFY
                         (CONS-TERM *FNNAME* *ARGLIST*)))))))))

(DEFUN REWRITE-FNCALLP (FNNAME VALUE)
  (COND ((VARIABLEP VALUE)
         T)
        ((FQUOTEP VALUE)
         T)
        ((EQ (FFN-SYMB VALUE)
             FNNAME)
         (AND
          (OR (ITERATE FOR ARG IN (FARGS VALUE)
                       ALWAYS (ITERATE FOR LIT IN CURRENT-CL
                                       THEREIS (DUMB-OCCUR ARG LIT)))
              (ITERATE FOR LIT IN CURRENT-SIMPLIFY-CL
                       THEREIS (DUMB-OCCUR VALUE LIT))
              (ITERATE FOR N IN *CONTROLLER-COMPLEXITIES*
                       AS MASK IN (GET FNNAME (QUOTE CONTROLLER-POCKETS))
                       THEREIS (< (ITERATE FOR ARG IN (FARGS VALUE)
                                           WHEN (PROG1
                                                    (NOT (CT= 0
                                                              (CTLOGAND
                                                               MASK 1)))
                                                  (SETQ MASK (CTASH MASK
                                                                    -1)))
                                           SUM (MAX-FORM-COUNT ARG))
                                  N))
              (ITERATE FOR MASK IN (GET FNNAME (QUOTE CONTROLLER-POCKETS))
                       WITH TEMP THEREIS
                       (PROGN
                         (SETQ TEMP MASK)

;   Is there a controller pocket such that all the controllers are constant and
;   some non controller is symbolically simpler now than before?

                         (AND (ITERATE FOR ARG IN (FARGS VALUE)
                                       WHEN (PROG1 (NOT (CT= 0 (CTLOGAND
                                                                TEMP 1)))
                                              (SETQ TEMP (CTASH TEMP -1)))
                                       ALWAYS (QUOTEP ARG))
                              (ITERATE FOR ARG1 IN *ARGLIST*
                                       AS ARG2 IN (FARGS VALUE)
                                       THEREIS
                                       (AND (PROG1 (CT= 0 (CTLOGAND MASK 1))
                                              (SETQ MASK (CTASH MASK -1)))
                                            (< (MAX-FORM-COUNT ARG2)
                                               (MAX-FORM-COUNT ARG1))))))))
          (ITERATE FOR ARG IN (FARGS VALUE)
                   ALWAYS (REWRITE-FNCALLP FNNAME ARG))))
        (T (ITERATE FOR ARG IN (FARGS VALUE)
                    ALWAYS (REWRITE-FNCALLP FNNAME ARG)))))

(DEFUN REWRITE-FOR (TERM TYPE-ALIST)

;   The basic idea is to rewrite:
;   
;      (FOR (QUOTE v) RANGE (QUOTE t1) OP (QUOTE b1) a1)
;   
;   to
;   
;      (FOR (QUOTE v) RANGE (QUOTE t2) OP (QUOTE b2) a2)
;   
;   where t2 is obtained by rewriting t1 and b2 is obtained by
;   rewriting b1.  However, there are many subtle issues here:
;   
;   0.  the usual issues of tameness and semi-concreteness;
;   1.  whether v occurs free in the hypotheses governing the 
;       rewriting;
;   2.  the assumptions we can make about v while rewriting;
;   3.  what we do with the linear assumptions that arise;
;   
;   We discuss all these issues in detail in this elaborate
;   comment.
;   
;   The initial constraints on this rewrite are:
;   
;      v is a variable symbol,
;      t1 and b1 are tame, and
;      a1 is a semi-concrete alist.
;   
;   
;   The Fundamental Theorem about FOR is:
;   
;       [for all 0 <= N < (LENGTH R) always 
;            (EVAL$ T T1 (CONS (CONS V (NTH R N)) A1))
;               <->
;            (EVAL$ T T2 (CONS (CONS V (NTH R N)) A2))]
;          &
;   
;            (EVAL$ T T2 (CONS (CONS V (NTH R N)) A2))
;            ->
;            (EVAL$ T B1 (CONS (CONS V (NTH R N)) A1))
;               =*
;            (EVAL$ T B2 (CONS (CONS V (NTH R N)) A2))]
;   
;     ->
;   
;      (FOR V RANGE T1 OP B1 A1) = (FOR V RANGE T2 OP B2 A2)
;   
;   *Note:  If OP is one of ALWAYS, COUNT, or EXISTS, the starred
;   equality can be replaced by an iff.  We don't further consider
;   this, but the code uses it.
;   
;   The theorem can be written in the logic if one uses a
;   recursively defined predicate to express the hypothesis.  The
;   theorem can be proved in the logic I'm sure.
;   
;   The instantiations we are using here are:
;   
;      V = (QUOTE v)
;      RANGE = range
;      T1 = (QUOTE t1)
;      OP = op
;      B1 = (QUOTE b1)
;      A1 = a1
;      T2 = (QUOTE t2) (see below)
;      B2 = (QUOTE b2) (see below)
;      A2 = a2 (see below)
;   
;   where
;   
;   t2 is the result of REWRITEing t1, with substitution {<v,v>} +
;   c(a1), type-alist (MEMBER v range) & TYPE-ALIST, and
;   ID/IFF='IFF.  c(a1) is the completion of the substitution
;   derived from the semi-concrete alist a1 by extending it with
;   pairs of the form <x,(QUOTE 0)> for all x not bound in a1.  We
;   can eliminate the unbounded "for all" by limiting ourselves to
;   the variables in the terms into which we are substituting.  The
;   + ("substitution concatentation") operator used here is odd: if
;   v is bound in s1 and v is bound in s2 then v is bound in s1+s2
;   and its binding is that in s1.
;   
;   b2 is the result of REWRITEing b1, with the same substitution
;   above, the type-alist used above conjoined with t2, and ID/IFF
;   set according to OP.
;   
;   a2 is the standard alist on all the variables occurring in t2
;   or b2.
;   
;   Note that from the specification of REWRITE we can conclude:
;   
;        ta & potlist & lin-assumpts             [hyps]
;        & (MEMBER v range)                      [MEM-hyp]
;       ->
;        t1/{<v,v>}+c(a1) = t2                [lhs=rhs]
;   
;   where ta is the term representing the current TYPE-ALIST,
;   potlist is the term representing the SIMPLIFY-CLAUSE-POT-LST,
;   and lin-assumpts is the term representing the linearization
;   assumptions produced by the rewriting.
;   
;   The specification of REWRITE requires that we prove:
;   
;         ta & potlist & lin-assumpts
;        ->
;         (FOR (QUOTE v) range (QUOTE t1) op (QUOTE b1) a1)
;           =
;         (FOR (QUOTE v) range (QUOTE t2) op (QUOTE b2) a2).
;   
;   in order for us to return the desired result.
;   
;   Assume v does not occur in any of these three hypotheses.  Call
;   this the "free-v assumption".
;   
;   To justify our rewrite we backchain through the Fundamental
;   Theorem about FOR.  Thus, we wish to establish
;   
;       goal:
;   
;       ta & potlist & lin-assumpts
;      ->
;       [for all 0 <= N < (LENGTH range) always 
;            (EVAL$ T (QUOTE t1) 
;                     (CONS (CONS (QUOTE v) (NTH range N)) a1))
;               <->
;            (EVAL$ T (QUOTE t2)
;                     (CONS (CONS (QUOTE v) (NTH range N)) a2))]
;          &
;   
;            (EVAL$ T (QUOTE t2)
;                     (CONS (CONS (QUOTE v) (NTH range N)) a2))
;            ->
;            (EVAL$ T (QUOTE b1)
;                     (CONS (CONS (QUOTE v) (NTH range N)) a1))
;               =*
;            (eval$ T (QUOTE b2)
;                     (CONS (CONS (QUOTE v) (NTH range N)) a2))]
;   
;   We will focus entirely on the proof of the first conjunct.  The
;   second conjunct has a similar proof.
;   
;   Proof of the first conjunct in the conclusion of goal:
;   Assume the hypothesis ta & potlist & lin-assumpts.
;   
;   Observe that
;        t1/c((CONS (CONS (QUOTE v) v) a1)) = t1/{<v,v>}+c(a1)
;   Observe that
;        t2/c((CONS (CONS (QUOTE v) v) a2)) = t2
;   since a2 has all the vars in t2 bound and if 'v is bound it is
;   bound to v.
;   
;   From the free-v assumption we can conclude from the
;   specification of REWRITE:
;       for all v
;          (MEMBER v range)
;       ->
;          t1/{<v,v>}+c(a1)
;         <->
;          t2
;   which, by our observations about c above is equivalent to:
;       for all v
;          (MEMBER v range)
;       ->
;          t1/c((CONS (CONS (QUOTE v) v) a1))
;         <->
;          t2/c((CONS (CONS (QUOTE v) v) a2))
;   Thus, if t1 and t2 are tame, by the fundamental theorem about 
;   EVAL$, we get:
;       for all v
;          (MEMBER v range)
;        ->
;          (EVAL$ T (QUOTE t1) (CONS (CONS (QUOTE v) v) a1))
;         <->
;          (EVAL$ T (QUOTE t2) (CONS (CONS (QUOTE v) v) a2))
;   Now we wish to prove
;       goal1:
;       [for all 0 <= N < (LENGTH range) always 
;            (EVAL$ T (QUOTE t1) (CONS (CONS (QUOTE v) (NTH range N)) a1))
;               <->
;            (EVAL$ T (QUOTE t2) (CONS (CONS (QUOTE v) (NTH range N)) a2))]
;   
;   Fix upon an N satisfying the hypothesis.  Consider (NTH range
;   N).  Because 0<=N<(LENGTH range) we know (MEMBER (NTH range N)
;   range).  Hence, we can appeal to the just derived theorem,
;   letting the variable v be (NTH range N), and get:
;          (EVAL$ T (QUOTE t1)
;                   (CONS (CONS (QUOTE v) (NTH range N)) a1))
;         <->
;          (EVAL$ T (QUOTE t2)
;               (CONS (CONS (QUOTE v) (NTH range N)) a2))
;   
;   Q.E.D.
;   
;   Now, we patch the theorem to consider several special cases.
;   If the free-v assumption is invalid, we can rename the indicial
;   variable of the FOR.  However, while this gives us a v free in
;   ta and potlist it does not guarantee a v free in lin-assumpts.
;   The code was once incorrect because of this oversight.  By
;   proving a lemma (x-1 < x) -> hyp(x)=T and then attacking (for x
;   in r when hyp(x) collect x) you could get the theorem prover to
;   reduce the theorem to x<1 -> (for x in r when hyp(x) collect
;   x).  I can't off-hand see an inconsistency through here, but it
;   is certainly nonsense.
;   
;   We can't generate a new v that is guaranteed free in
;   lin-assumpts since lin-assumpts is generated by rewriting t1.
;   However, we can split off those lin-assumpts that involve v,
;   let them be lin-assumpts-v and act as though the rewrite
;   returned (IF lin-assumpts-v t2 t1).

  (LET (VAR RANGE TEST OP BODY ALIST NEW-VAR REWRITE-ALIST
            (FREE-VARS-IN-SIGHT FREE-VARS-IN-SIGHT))
    (CHK-NQTHM-MODE$ (QUOTE REWRITE-FOR))
    (COND ((AND (MATCH TERM (FOR (LIST (QUOTE QUOTE) VAR)
                                 RANGE
                                 (LIST (QUOTE QUOTE) TEST) OP
                                 (LIST (QUOTE QUOTE) BODY) ALIST))
                (SYMBOLP VAR)
                (TERMP VAR)
                (TERMP TEST)
                (TAMEP TEST)
                (TERMP BODY)
                (TAMEP BODY)
                (SEMI-CONCRETE-ALISTP ALIST))
           (COND ((MEMBER-EQ VAR FREE-VARS-IN-SIGHT)

;   If VAR occurs in sight, we rename it and substitute the new one in
;   for the old in TEST and BODY.  The new variable might be bound in
;   ALIST, but if so it is unimportant because it doesn't occur in the
;   terms we'll rewrite and in any case we'll cover up its binding
;   with <VAR,VAR>.

                  (SETQ NEW-VAR (CAR (GEN-VARS (APPEND FREE-VARS-IN-SIGHT
                                                       (APPEND (ALL-VARS TEST)
                                                               (ALL-VARS
                                                                BODY)))
                                               1 INDICIAL-VARIABLE-NAMES)))
                  (SETQ TEST (SUBST-VAR NEW-VAR VAR TEST))
                  (SETQ BODY (SUBST-VAR NEW-VAR VAR BODY))
                  (SETQ VAR NEW-VAR)))

;   When we rewrite the test and body we do so under an alist that binds
;   VAR to VAR.  There used to be a bug in the system here.  Once upon a
;   time we did not complete the alist with 0's for unbound vars that
;   occurred in test.  (Instead we forced the alist to be on the vars in
;   test.)  And we did not bind VAR to VAR but relied on the fact that
;   REWRITE leaves unbound vars untouched.  But VAR might be bound in
;   ALIST!  If so, REWRITE would see the binding while EVAL$ would see the
;   one provided by FOR and we'd lose.

           (SETQ REWRITE-ALIST
                 (CONS (CONS VAR VAR)
                       (COMPLETE-ALIST
                        (DELETE VAR
                                (UNION-EQ (ALL-VARS TEST)
                                          (ALL-VARS BODY)))
                        (MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST ALIST))))
           (SETQ FREE-VARS-IN-SIGHT (CONS VAR FREE-VARS-IN-SIGHT))
           (PUSH-LEMMA-FRAME)
           (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
           (ASSUME-TRUE-LST
            (EXTRACT-CONJUNCTS
             (NORMALIZE-IFS
              (INSURE-FREE-V-ASSUMPTION
               VAR
               (FCONS-TERM* (QUOTE MEMBER) VAR RANGE)
               (REWRITE (FCONS-TERM* (QUOTE MEMBER) VAR RANGE)
                        NIL TYPE-ALIST (QUOTE ?) (QUOTE IFF) NIL
                        '(BUILTIN-RULE REWRITE-FOR)))
              NIL NIL T))
            TYPE-ALIST)
           (COND (MUST-BE-TRUE

;   If we can prove that (MEMBER v range) for a free v, then we can prove
;   anything in the current context.  It is not clear what is the best way to
;   use this fact.  But things simplify dramatically if we simply "prove" that
;   the range is empty.  That is effectively done by:

                  (SETQ TEST FALSE))
                 (MUST-BE-FALSE
                  (SETQ TEST FALSE)))
           (SETQ TYPE-ALIST TRUE-TYPE-ALIST)
           (SETQ TEST (NORMALIZE-IFS
                       (INSURE-FREE-V-ASSUMPTION
                        VAR TEST
                        (REWRITE TEST REWRITE-ALIST TYPE-ALIST
                                 (QUOTE ?) (QUOTE IFF) NIL
                                 '(BUILTIN-RULE REWRITE-FOR)))
                       NIL NIL T))
           (COND ((NOT (TAMEP TEST))
                  (POP-LEMMA-FRAME)
                  (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                  TERM)
                 (T
                  (ASSUME-TRUE-LST (EXTRACT-CONJUNCTS TEST) TYPE-ALIST)
                  (COND (MUST-BE-FALSE
                         (ITERATE FOR X IN (POP-LEMMA-FRAME) DO (PUSH-LEMMA X))
                         (ITERATE FOR X IN (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                                  DO (PUSH-LINEARIZE-ASSUMPTION X))
                         (PUSH-LEMMA (QUOTE FOR))
                         (FCONS-TERM* (QUOTE QUANTIFIER-INITIAL-VALUE)
                                      OP))
                        (T (COND (MUST-BE-TRUE (SETQ TEST TRUE)))
                           (SETQ
                            BODY (NORMALIZE-IFS
                                  (INSURE-FREE-V-ASSUMPTION
                                   VAR BODY
                                   (REWRITE
                                    BODY REWRITE-ALIST
                                    TRUE-TYPE-ALIST
                                    (QUOTE ?)
                                    (COND
                                     ((MEMBER-EQUAL
                                       OP
                                       (QUOTE ((QUOTE ALWAYS)
                                               (QUOTE EXISTS)
                                               (QUOTE COUNT))))
                                      (QUOTE IFF))
                                     (T (QUOTE ID)))
                                    NIL
                                    '(BUILTIN-RULE REWRITE-FOR)))
                                  NIL NIL
                                  (MEMBER-EQUAL OP
                                                (QUOTE ((QUOTE ALWAYS)
                                                        (QUOTE EXISTS)
                                                        (QUOTE COUNT))))))
                           (COND ((TAMEP BODY)
                                  (ITERATE FOR X IN (POP-LEMMA-FRAME) DO
                                           (PUSH-LEMMA X))
                                  (ITERATE FOR X IN
                                           (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                                           DO (PUSH-LINEARIZE-ASSUMPTION X))
                                  (PUSH-LEMMA (QUOTE EVAL$))
                                  (CONS-TERM
                                   (QUOTE FOR)
                                   (LIST
                                    (KWOTE VAR)
                                    RANGE
                                    (KWOTE TEST)
                                    OP
                                    (KWOTE BODY)
                                    (STANDARD-ALIST
                                     (UNSTABLE-SORT (DELETE VAR
                                                            (ALL-VARS-LST
                                                             (LIST TEST BODY)))
                                                    (FUNCTION ALPHORDER))))))
                                 (T (POP-LEMMA-FRAME)
                                    (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                                    TERM)))))))
          (T TERM))))

(DEFUN REWRITE-IF (TEST LEFT RIGHT TYPE-ALIST)
  (COND ((AND (NVARIABLEP TEST)
              (NOT (FQUOTEP TEST))
              (EQ (FFN-SYMB TEST)
                  (QUOTE IF))
              (EQUAL (FARGN TEST 2)
                     FALSE)
              (FALSE-NONFALSEP (FARGN TEST 3))
              (NOT DEFINITELY-FALSE))
         (OUR-SWAP LEFT RIGHT)
         (SETQ TEST (FARGN TEST 1))))
  (SMART-ASSUME-TRUE-FALSE TEST)
  (COND (MUST-BE-TRUE (JUMPOUTP LEFT
                                (REWRITE LEFT ALIST TYPE-ALIST OBJECTIVE
                                         ID-IFF DEFN-FLG
                                         2)))
        (MUST-BE-FALSE (JUMPOUTP RIGHT
                                 (REWRITE RIGHT ALIST TYPE-ALIST
                                          OBJECTIVE ID-IFF DEFN-FLG
                                          3)))
        (T (REWRITE-IF1 TEST
                        (JUMPOUTP LEFT
                                  (LET (FALSE-TYPE-ALIST)
                                    (REWRITE LEFT ALIST
                                             TRUE-TYPE-ALIST
                                             OBJECTIVE ID-IFF
                                             DEFN-FLG
                                             2)))
                        (JUMPOUTP RIGHT
                                  (REWRITE RIGHT ALIST FALSE-TYPE-ALIST
                                           OBJECTIVE ID-IFF DEFN-FLG
                                           3))))))

(DEFUN REWRITE-IF1 (TEST LEFT RIGHT)
  (COND ((EQUAL LEFT RIGHT)
         LEFT)
        ((AND (EQUAL TEST LEFT) (FALSE-NONFALSEP RIGHT) DEFINITELY-FALSE)
         TEST)
        ((AND (EQUAL TRUE LEFT)
              (FALSE-NONFALSEP RIGHT)
              DEFINITELY-FALSE
              (OUR-BOOLEAN TEST))
         TEST)
        (T (FCONS-TERM* (QUOTE IF)
                        TEST LEFT RIGHT))))

(DEFUN REWRITE-LINEAR-CONCL (CONCL)

;   We desire to rewrite the instantiated conclusion of linear lemmas before
;   adding them to the linear pot.  However, because all of the literals of the
;   clause being proved are on the TYPE-ALIST as false, it is possible -- say
;   when proving an instance of an already proved linear lemma -- to rewrite
;   the conclusion to F!  We could avoid this by either not putting the
;   linear-like literals on the type alist in the first place, or by not
;   rewriting the entire conclusion, just the args.  We took the latter
;   approach because it was simplest.  It does suffer from the possibility that
;   the whole (LESSP lhs rhs) of the conclusion might rewrite to something
;   else, possibly a better LESSP.

  (LET (LHS RHS)
    (COND ((MATCH CONCL (LESSP LHS RHS))
           (FCONS-TERM* (QUOTE LESSP)
                        (REWRITE LHS UNIFY-SUBST TYPE-ALIST
                                 (QUOTE ?)
                                 (QUOTE ID)
                                 NIL
                                 'RHS)
                        (REWRITE RHS UNIFY-SUBST TYPE-ALIST
                                 (QUOTE ?)
                                 (QUOTE ID)
                                 NIL
                                 'RHS)))
          ((MATCH CONCL (NOT (LESSP LHS RHS)))
           (FCONS-TERM* (QUOTE NOT)
                        (FCONS-TERM* (QUOTE LESSP)
                                     (REWRITE LHS
                                              UNIFY-SUBST
                                              TYPE-ALIST
                                              (QUOTE ?)
                                              (QUOTE ID)
                                              NIL
                                              'RHS)
                                     (REWRITE RHS
                                              UNIFY-SUBST
                                              TYPE-ALIST
                                              (QUOTE ?)
                                              (QUOTE ID)
                                              NIL
                                              'RHS))))
          (T (ER HARD NIL REWRITE-LINEAR-CONCL |thought| |that| |all| |linear|
                 |lemmas| |had| |conclusions| |with| |atom| LESSP EXCL)))))

(DEFUN REWRITE-SOLIDIFY (TERM)
  (COND ((QUOTEP TERM) TERM)
        ((AND (NVARIABLEP TERM)
              (EQ (FFN-SYMB TERM) (QUOTE IF)))

;   See the proof in JUMPOUTP.

         TERM)
         
        ((ITERATE FOR PAIR IN TYPE-ALIST WITH RHS WITH LHS
                  WHEN (AND (TS= TYPE-SET-TRUE (CDR PAIR))
                            (MATCH (CAR PAIR) (EQUAL LHS RHS))
                            (EQUAL LHS TERM))
                  DO (RETURN-FROM REWRITE-SOLIDIFY RHS)))
        (T
         (LET (LIT TEMP)
           (COND
            ((AND (SETQ TEMP (ASSOC-EQUAL TERM TYPE-ALIST))
                  (OBJ-TABLE (CDR TEMP) OBJECTIVE ID-IFF)))
            ((SETQ LIT
                   (ITERATE FOR LIT IN LITS-THAT-MAY-BE-ASSUMED-FALSE
                            WHEN (COND ((EQUAL LIT TERM) (SETQ TEMP FALSE))
                                       ((COMPLEMENTARYP LIT TERM)
                                        (SETQ TEMP TRUE))
                                       (T NIL))
                            DO (RETURN LIT)))
             (COND ((OR (EQ ID-IFF (QUOTE IFF))
                        (EQ TEMP FALSE)
                        (OUR-BOOLEAN TERM))
                    (PUSH-LEMMA LIT)
                    TEMP)
                   (T TERM)))
            (T TERM))))))

(DEFUN REWRITE-TYPE-PRED (TERM)
  (LET (LHS RHS PAIR TYPE-SET)
    (COND ((OR (VARIABLEP TERM) (FQUOTEP TERM))
           TERM)
          ((MATCH TERM (EQUAL LHS RHS))
           (COND ((EQUAL LHS RHS) TRUE)
                 ((NOT-IDENT LHS RHS) FALSE)
                 ((AND (OUR-BOOLEAN LHS) (EQUAL TRUE RHS))
                  LHS)
                 ((AND (OUR-BOOLEAN RHS) (EQUAL TRUE LHS))
                  RHS)
                 ((MATCH RHS (EQUAL & &))
                  (FCONS-TERM* (QUOTE IF)
                               RHS
                               (FCONS-TERM* (QUOTE EQUAL) LHS TRUE)
                               (FCONS-TERM* (QUOTE IF) LHS FALSE TRUE)))
                 ((EQUAL LHS FALSE)
                  (FCONS-TERM* (QUOTE IF) RHS FALSE TRUE))
                 ((EQUAL RHS FALSE)
                  (FCONS-TERM* (QUOTE IF) LHS FALSE TRUE))
                 ((MATCH LHS (EQUAL & &))
                  (FCONS-TERM* (QUOTE IF)
                               LHS
                               (FCONS-TERM* (QUOTE EQUAL)
                                            RHS TRUE)
                               (FCONS-TERM* (QUOTE IF)
                                            RHS FALSE TRUE)))
                 ((AND (SETQ TYPE-SET (TYPE-SET LHS))
                       (ITERATE FOR X IN RECOGNIZER-ALIST
                                THEREIS (TS= TYPE-SET (CDR X)))
                       (TS= TYPE-SET (TYPE-SET RHS))
                       (NOT (BTM-OBJECT-OF-TYPE-SET TYPE-SET)))

;   This piece of code was hacked together to test the idea that if you have an
;   (EQUAL lhs rhs) in which lhs and rhs have the same type -- and that type
;   does not contain a btm object -- that you should rewrite it to T or F
;   provided you can appropriately decide the equalities of the components.
;   Before attempting to add complete equality we did not do anything like this
;   and relied solely on elim to do it for us.  In the first attempt to add it
;   to rewrite we just rewrote all such (EQUAL lhs rhs) to the conjunction of
;   the equalities of the components.  That was unsatisfactory because it
;   caused such equalities as (EQUAL (ADDTOLIST X L) B) to be torn up all the
;   time.  That caused us to fail to prove thms like
;   SORT  -OF-ORDERED-NUMBER-LIST because weak subgoals are pushed -- subgoals
;   about (CAR (ADDTOLIST X L)) and (CDR (ADDTOLIST X L)) instead about
;   (ADDTOLIST X L) itself.

;   If this piece of code survives it should be cleaned up.  Two problems.  We
;   repeatedly cons up the constant (EQUAL (CAR LHS) (CAR RHS)) and we (RETURN
;   TERM) which works only because we know this clause is the second to last
;   one in the parent COND.

                  (ITERATE FOR DEST IN
                           (CDR
                            (ASSOC-EQ (CAR (ITERATE
                                            FOR X IN SHELL-ALIST
                                            WHEN (TS= TYPE-SET (TSLOGBIT
                                                                (CDR X)))
                                            DO (RETURN X)))
                                      SHELL-POCKETS))
                           DO
                           (PROGN
                             (SETQ TEMP-TEMP
                                   (REWRITE (FCONS-TERM*
                                             (QUOTE EQUAL)
                                             (FCONS-TERM* DEST (QUOTE LHS))
                                             (FCONS-TERM* DEST (QUOTE RHS)))
                                            (LIST (CONS (QUOTE LHS)
                                                        LHS)
                                                  (CONS (QUOTE RHS)
                                                        RHS))
                                            TYPE-ALIST
                                            (QUOTE ?)
                                            (QUOTE ID)
                                            NIL
                                            '(BUILTIN-RULE REWRITE-TYPE-PRED)))
                             (COND ((EQUAL TEMP-TEMP FALSE)
                                    (RETURN FALSE))
                                   ((NOT (EQUAL TEMP-TEMP TRUE))
                                    (RETURN TERM))))
                           FINALLY (RETURN TRUE)))
                 (T TERM)))
          ((SETQ PAIR (ASSOC-EQ (FFN-SYMB TERM)
                                RECOGNIZER-ALIST))
           (SETQ TYPE-SET (TYPE-SET (FARGN TERM 1)))
           (COND ((TSLOGSUBSETP TYPE-SET (CDR PAIR))
                  TRUE)
                 ((TS= 0 (TSLOGAND TYPE-SET (CDR PAIR)))
                  FALSE)
                 (T TERM)))
          (T TERM))))

(DEFUN REWRITE-WITH-LEMMAS (TERM)
  (LET (REWRITTEN-TERM UNIFY-SUBST TEMP INST-HYP
                       BREAK-REWRITE-COMMAND-HANDLER-STATE)
    (COND ((VARIABLEP TERM) (REWRITE-SOLIDIFY TERM))
          ((FQUOTEP TERM) TERM)
          ((MEMBER-EQ  (FFN-SYMB TERM) FNS-TO-BE-IGNORED-BY-REWRITE) TERM)
          ((AND (OR (NOT (EQ (FFN-SYMB TERM) (QUOTE LESSP)))
                    (NOT (MEMBER-EQ (QUOTE LESSP) FNSTACK)))
                (REWRITE-WITH-LINEAR TERM)))
          ((ITERATE FOR LEMMA IN (GET (FFN-SYMB TERM) (QUOTE LEMMAS))
                    UNLESS (DISABLEDP (ACCESS REWRITE-RULE NAME LEMMA))
                    THEREIS
                    (PROG2
                     (PUSH-REWRITE-PATH-FRAME 'REWRITE-WITH-LEMMAS
                                              LEMMA
                                              NIL
                                              TERM)
                     (COND
                      ((META-LEMMAP LEMMA)

; Matt Kaufmann suggested (and first implemented) a modification to our
; original handling of metalemmas.  The modification allows their application
; to non-tame terms by the generalization via MAKE-TAMEP-SUBST and its later
; inversion.

                       (LET* ((TAMEP-SUBST (MAKE-TAMEP-SUBST TERM))
                              (TERM (IF TAMEP-SUBST
                                        (SUBLIS-EXPR1 TAMEP-SUBST TERM)
                                        TERM)))

;   The conclusion is the name of a LISP fn to apply to the term being
;   rewritten.  To add such lemma it must be the case that the LISP function
;   return a term val such that in the current history (EQUAL TERM val)
;   can be proved.
                       
                         (SETQ REWRITTEN-TERM
                               (CATCH (QUOTE REDUCE-TERM)
                                 (FUNCALL (ACCESS REWRITE-RULE CONCL LEMMA)
                                          TERM)))
                         (COND ((OR (EQ REWRITTEN-TERM (QUOTE *1*FAILED))
                                    (EQUAL REWRITTEN-TERM TERM))
                                NIL)
                               ((NOT (PSEUDO-TERMP REWRITTEN-TERM))

;   In the following error message we print with !PPR rather than !TERM so the
;   user can see exactly what the input term and output non-term are.

                                (ER SOFT
                                    ((NAME (ACCESS REWRITE-RULE NAME LEMMA))
                                     TERM
                                     REWRITTEN-TERM)
                                    |the| |metalemma| |named|
                                    (!PPR NAME NIL) |has|
                                    |simplified| |the| |term|
                                    (!PPR TERM NIL) |to|
                                    |the| |non-term|
                                    (!PPR REWRITTEN-TERM (QUOTE |.|))))
                               ((NOT (TAMEP (SETQ REWRITTEN-TERM
                                                  (SUBLIS-VAR
                                                   NIL
                                                   REWRITTEN-TERM))))
                                (ER SOFT
                                    ((NAME (ACCESS REWRITE-RULE NAME LEMMA))
                                     TERM
                                     REWRITTEN-TERM)
                                    |the| |metalemma| |named| (!PPR NAME NIL)
                                    |has|
                                    |simplified| |the| |tame| |term|
                                    (!TERM TERM NIL) |to|
                                    |the| |non-tame| |term|
                                    (!TERM REWRITTEN-TERM (QUOTE |.|))))
                               ((NOT (SUBSETP-EQ (ALL-VARS REWRITTEN-TERM)
                                                 (ALL-VARS TERM)))
                                (ER SOFT
                                    ((NAME (ACCESS REWRITE-RULE NAME LEMMA))
                                     TERM
                                     REWRITTEN-TERM)
                                    |the| |metalemma| |named| (!PPR NAME NIL)
                                    |has|
                                    |simplified| |the| |tame| |term|
                                    (!TERM TERM NIL) |to|
                                    |the| |term|
                                    (!TERM REWRITTEN-TERM (QUOTE |,|))
                                    |which| |contains| |variables| |not|
                                    |in| |the| |original| |term| |.|))
                               (T

;   We now know that REWRITTEN-TERM is a tame term and introduce no new 
;   variables.  The SUBLIS-VAR above has put it into QUOTE normal form.

;   Historical Note about QUOTE normal form:  When we wrote the metapaper we
;   were uncertain whether the soundness of the theorem-prover depended on
;   terms being in QUOTE normal form -- however the theorem-prover could
;   certainly be implemented so that it was not crucial so we left this issue
;   out of the paper.  We attempted to verify that the soundness of the current
;   implementation did not depend upon terms being in quote normal form, but we
;   got very weary, particularly because one of us could never remember what it
;   was that we were trying to prove.  We did learn that some parts of the
;   theorem prover that used functions such as OCCUR would be heuristically
;   inaccurate if terms were not in normal form.  We never discovered any
;   situation in which terms not being in normal form would cause unsoundness
;   but we did not get past the C's in an alphabetical scan.  Instead, we gave
;   up the search and decided to require that terms be in normal form
;   throughout the theorem-prover.

                                (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                                (SETQ REWRITTEN-TERM

;   Note that it's OK to avoid SUBLIS-VAR when TAMEP-SUBST is NIL, since we
;   have already put REWRITTEN-TERM into QUOTE normal form.

                                      (REWRITE (IF TAMEP-SUBST
                                                   (SUBLIS-VAR
                                                    (INVERT TAMEP-SUBST)
                                                    REWRITTEN-TERM)
                                                   REWRITTEN-TERM)
                                               NIL
                                               TYPE-ALIST OBJECTIVE ID-IFF
                                               DEFN-FLG
                                               'META-RHS))
                                T))))
                      ((EQ (FFN-SYMB (ACCESS REWRITE-RULE CONCL LEMMA))
                           (QUOTE NOT))
                       (COND ((AND (OR (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                       (NOT (EQ OBJECTIVE (QUOTE TRUE))))
                                   (ONE-WAY-UNIFY
                                    (FARGN (ACCESS REWRITE-RULE
                                                   CONCL LEMMA)
                                           1)
                                    TERM)
                                   (LET (RELIEVE-HYPS-ANS)
                                     (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                     (AND BROKEN-LEMMAS
                                          (BREAK-BEFORE-RELIEVE-HYPS
                                           (ACCESS REWRITE-RULE NAME LEMMA)
                                           LEMMA
                                           TERM))
                                     (SETQ RELIEVE-HYPS-ANS
                                           (RELIEVE-HYPS
                                            (ACCESS REWRITE-RULE HYPS LEMMA)))
                                     (AND BROKEN-LEMMAS
                                          (BREAK-AFTER-RELIEVE-HYPS
                                           (ACCESS REWRITE-RULE NAME LEMMA)
                                           LEMMA
                                           TERM
                                           RELIEVE-HYPS-ANS))
                                     RELIEVE-HYPS-ANS))
                              (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                              (SETQ REWRITTEN-TERM FALSE)
                              (AND BROKEN-LEMMAS
                                   (BREAK-AFTER-REWRITE-RHS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM
                                    REWRITTEN-TERM))
                              T)
                             (T NIL)))
                      ((EQ (FFN-SYMB (ACCESS REWRITE-RULE CONCL LEMMA))
                           (QUOTE EQUAL))
                       (COND ((AND
                               (OR (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                   (NOT (EQ OBJECTIVE (QUOTE TRUE)))
                                   (NOT (EQUAL (FARGN (ACCESS REWRITE-RULE
                                                              CONCL LEMMA)
                                                      2)
                                               FALSE)))
                               (OR (NOT (MEMBER-EQ (FFN-SYMB TERM) FNSTACK))
                                   (NOT (FNNAMEP (FFN-SYMB TERM)
                                                 (FARGN (ACCESS REWRITE-RULE
                                                                CONCL LEMMA)
                                                        2))))
                               (ONE-WAY-UNIFY
                                (FARGN (ACCESS
                                        REWRITE-RULE CONCL LEMMA)
                                       1)
                                TERM)
                               (PROGN
                                 (SETQ TEMP COMMUTED-EQUALITY-FLG)
                                 T)
                               (ITERATE FOR PAIR
                                        IN (ACCESS REWRITE-RULE
                                                   LOOP-STOPPER LEMMA)
                                        NEVER (TERM-ORDER
                                               (CDR (ASSOC-EQ (CAR PAIR)
                                                              UNIFY-SUBST))
                                               (CDR (ASSOC-EQ (CDR PAIR)
                                                              UNIFY-SUBST))))
                               (LET (RELIEVE-HYPS-ANS)
                                 (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                 (AND BROKEN-LEMMAS
                                      (BREAK-BEFORE-RELIEVE-HYPS
                                       (ACCESS REWRITE-RULE NAME LEMMA)
                                       LEMMA
                                       TERM))
                                 (SETQ RELIEVE-HYPS-ANS
                                       (RELIEVE-HYPS
                                        (ACCESS REWRITE-RULE HYPS LEMMA)))
                                 (AND BROKEN-LEMMAS
                                      (BREAK-AFTER-RELIEVE-HYPS
                                       (ACCESS REWRITE-RULE NAME LEMMA)
                                       LEMMA
                                       TERM
                                       RELIEVE-HYPS-ANS))
                                 RELIEVE-HYPS-ANS))

                              (SETQ REWRITTEN-TERM
                                    (REWRITE
                                     (COND (TEMP (COMMUTE-EQUALITIES
                                                  (FARGN
                                                   (ACCESS REWRITE-RULE
                                                           CONCL
                                                           LEMMA)
                                                   2)))
                                           (T (FARGN (ACCESS REWRITE-RULE
                                                             CONCL LEMMA)
                                                     2)))
                                     UNIFY-SUBST TYPE-ALIST OBJECTIVE ID-IFF
                                     DEFN-FLG
                                     'RHS))
                              (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                              (AND BROKEN-LEMMAS
                                   (BREAK-AFTER-REWRITE-RHS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM
                                    REWRITTEN-TERM))
                              T)
                             ((AND (OR (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                       (NOT (EQ OBJECTIVE (QUOTE FALSE))))
                                   (EQ (FFN-SYMB TERM)
                                       (QUOTE EQUAL))
                                   (ONE-WAY-UNIFY (ACCESS REWRITE-RULE CONCL
                                                          LEMMA)
                                                  TERM)
                                   (LET (RELIEVE-HYPS-ANS)
                                     (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                     (AND BROKEN-LEMMAS
                                          (BREAK-BEFORE-RELIEVE-HYPS
                                           (ACCESS REWRITE-RULE NAME LEMMA)
                                           LEMMA
                                           TERM))
                                     (SETQ RELIEVE-HYPS-ANS
                                           (RELIEVE-HYPS
                                            (ACCESS REWRITE-RULE HYPS LEMMA)))
                                     (AND BROKEN-LEMMAS
                                          (BREAK-AFTER-RELIEVE-HYPS
                                           (ACCESS REWRITE-RULE NAME LEMMA)
                                           LEMMA
                                           TERM
                                           RELIEVE-HYPS-ANS))
                                     RELIEVE-HYPS-ANS))

                              (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                              (SETQ REWRITTEN-TERM TRUE)
                              (AND BROKEN-LEMMAS
                                   (BREAK-AFTER-REWRITE-RHS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM
                                    REWRITTEN-TERM))
                              T)
                             (T NIL)))
                      ((AND (EQ (FFN-SYMB (ACCESS REWRITE-RULE CONCL LEMMA))
                                (QUOTE IFF))
                            (EQ ID-IFF (QUOTE IFF)))
                       (COND ((AND
                               (OR (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                   (NOT (EQ OBJECTIVE (QUOTE TRUE)))
                                   (NOT (EQUAL (FARGN (ACCESS REWRITE-RULE
                                                              CONCL LEMMA)
                                                      2)
                                               FALSE)))
                               (OR (NOT (MEMBER-EQ (FFN-SYMB TERM) FNSTACK))
                                   (NOT (FNNAMEP (FFN-SYMB TERM)
                                                 (FARGN (ACCESS REWRITE-RULE
                                                                CONCL LEMMA)
                                                        2))))
                               (ONE-WAY-UNIFY
                                (FARGN (ACCESS
                                        REWRITE-RULE CONCL LEMMA)
                                       1)
                                TERM)
                               (ITERATE FOR PAIR
                                        IN (ACCESS REWRITE-RULE
                                                   LOOP-STOPPER LEMMA)
                                        NEVER (TERM-ORDER
                                               (CDR (ASSOC-EQ (CAR PAIR)
                                                              UNIFY-SUBST))
                                               (CDR (ASSOC-EQ (CDR PAIR)
                                                              UNIFY-SUBST))))
                               (LET (RELIEVE-HYPS-ANS)
                                 (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                                 (AND BROKEN-LEMMAS
                                      (BREAK-BEFORE-RELIEVE-HYPS
                                       (ACCESS REWRITE-RULE NAME LEMMA)
                                       LEMMA
                                       TERM))
                                 (SETQ RELIEVE-HYPS-ANS
                                       (RELIEVE-HYPS
                                        (ACCESS REWRITE-RULE HYPS LEMMA)))
                                 (AND BROKEN-LEMMAS
                                      (BREAK-AFTER-RELIEVE-HYPS
                                       (ACCESS REWRITE-RULE NAME LEMMA)
                                       LEMMA
                                       TERM
                                       RELIEVE-HYPS-ANS))
                                 RELIEVE-HYPS-ANS))

                              (SETQ REWRITTEN-TERM
                                    (REWRITE
                                     (FARGN (ACCESS REWRITE-RULE CONCL LEMMA)
                                            2)
                                     UNIFY-SUBST TYPE-ALIST OBJECTIVE ID-IFF
                                     DEFN-FLG
                                     'RHS))
                              (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                              (AND BROKEN-LEMMAS
                                   (BREAK-AFTER-REWRITE-RHS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM
                                    REWRITTEN-TERM))
                              T)
                             (T NIL)))
                      ((AND (OR (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                (NOT (EQ OBJECTIVE (QUOTE FALSE))))
                            (OR (EQ ID-IFF (QUOTE IFF))
                                (OUR-BOOLEAN TERM))
                            (ONE-WAY-UNIFY (ACCESS REWRITE-RULE CONCL LEMMA)
                                           TERM)
                            (LET (RELIEVE-HYPS-ANS)
                              (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                              (AND BROKEN-LEMMAS
                                   (BREAK-BEFORE-RELIEVE-HYPS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM))
                              (SETQ RELIEVE-HYPS-ANS
                                    (RELIEVE-HYPS
                                     (ACCESS REWRITE-RULE HYPS LEMMA)))
                              (AND BROKEN-LEMMAS
                                   (BREAK-AFTER-RELIEVE-HYPS
                                    (ACCESS REWRITE-RULE NAME LEMMA)
                                    LEMMA
                                    TERM
                                    RELIEVE-HYPS-ANS))
                              RELIEVE-HYPS-ANS))

                       (PUSH-LEMMA (ACCESS REWRITE-RULE NAME LEMMA))
                       (SETQ REWRITTEN-TERM TRUE)
                       (AND BROKEN-LEMMAS
                            (BREAK-AFTER-REWRITE-RHS
                             (ACCESS REWRITE-RULE NAME LEMMA)
                             LEMMA
                             TERM
                             REWRITTEN-TERM))
                       T)
                      (T NIL))
                     (POP-REWRITE-PATH-FRAME)))
           REWRITTEN-TERM)
          ((MEMBER-EQUAL TERM EXPAND-LST)

;   If we have been told to expand this term, do it.  We used to do this inside
;   of REWRITE-FNCALL, but there to avoid jumping out when we hit unapproved
;   recursive calls we just substituted the actuals into the body and returned
;   that.  This seems neater.

           (SETQ TEMP (GET (FFN-SYMB TERM) (QUOTE SDEFN)))
           (PUSH-LEMMA (FFN-SYMB TERM))
           (REWRITE (CADDR TEMP)
                    (ITERATE FOR V IN (CADR TEMP) AS X IN (FARGS TERM)
                             COLLECT (CONS V X))
                    TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                    'BODY))
          (T (SETQ TEMP (REWRITE-FNCALL (FFN-SYMB TERM)
                                        (FARGS TERM)))
             (COND ((EQUAL TEMP TERM) TERM)
                   ((CONTAINS-REWRITEABLE-CALLP (FFN-SYMB TERM) TEMP)
                    (REWRITE TEMP NIL TYPE-ALIST OBJECTIVE ID-IFF DEFN-FLG
                             'REWRITTEN-BODY))
                   (T TEMP))))))

(DEFUN REWRITE-WITH-LINEAR (TERM)
  (PROG2
   (PUSH-REWRITE-PATH-FRAME 'REWRITE-WITH-LINEAR
                            TERM
                            NIL
                            NIL)
   (PROG (ANS TEMP)
         (SETQ TEMP TERM)
         (MATCH TEMP (NOT TEMP))

;   TEMP is the atom of TERM.

         (COND ((AND (NOT (MATCH TEMP (LESSP & &)))
                     (NOT (MATCH TEMP (EQUAL & &))))
                NIL)
               ((EQ OBJECTIVE (QUOTE ?))

;   We tried rewriting with linear under the objective ?, and it cost us 4
;   million conses over a proveall, so we stopped rewriting with linear under
;   the objective ?.  We found that too restrictive, and experimented with the
;   idea of only rewriting with linear under ? when ANCESTORS is nonNIL, i.e.,
;   when we are working on a term that may appear as part of the simplification
;   of the theorem as opposed to a term that appears while rewriting the
;   hypothesis of a rewrite rule.  That cost us 5 times more conses on the
;   theorem it was designed to prove!  So we have abandoned linear under ?
;   altogether, again.  Here, however is the most recent experimental code:

;   ( COND ((AND (NULL ANCESTORS)
;               (EQ (ADD-TERM-TO-POT-LST TERM
;                                        SIMPLIFY-CLAUSE-POT-LST NIL NIL)
;                   (QUOTE CONTRADICTION)))
;          (SETQ ANS TRUE)
;          (GO WIN)))

;   ( COND ((AND (NULL ANCESTORS)
;               (EQ (ADD-TERM-TO-POT-LST TERM SIMPLIFY-CLAUSE-POT-LST T NIL)
;                   (QUOTE CONTRADICTION)))
;          (SETQ ANS FALSE)
;          (GO WIN)))

                NIL)
               ((EQ OBJECTIVE (QUOTE TRUE))
                (COND ((EQ (ADD-TERM-TO-POT-LST TERM SIMPLIFY-CLAUSE-POT-LST
                                                NIL NIL)
                           (QUOTE CONTRADICTION))
                       (SETQ ANS TRUE)
                       (GO WIN))))
               (T (COND ((EQ (ADD-TERM-TO-POT-LST TERM SIMPLIFY-CLAUSE-POT-LST
                                                  T NIL)
                             (QUOTE CONTRADICTION))
                         (SETQ ANS FALSE)
                         (GO WIN)))))
         (RETURN NIL)
         WIN
         (ITERATE FOR X IN LEMMAS-USED-BY-LINEAR DO (PUSH-LEMMA X))
         (PUSH-LEMMA (QUOTE ZERO))
         (ITERATE FOR X IN LINEAR-ASSUMPTIONS DO (PUSH-LINEARIZE-ASSUMPTION X))
         (RETURN ANS))
   (POP-REWRITE-PATH-FRAME)))


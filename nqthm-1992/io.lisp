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

(DEFUN !CLAUSE-SET (CL-SET INDENT)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET ((*INDENT* (OR INDENT *INDENT*)))
    (SETQ LAST-CLAUSE CL-SET)
    (PPRINDENT (COND ((NULL CL-SET) (UNTRANSLATE TRUE))
                     ((NULL (CDR CL-SET)) (PRETTYIFY-CLAUSE (CAR CL-SET)))
                     (T (CONS (QUOTE AND)
                              (ITERATE FOR CL IN CL-SET
                                       COLLECT (PRETTYIFY-CLAUSE CL)))))
               (COND ((INT= 0 *INDENT*) 0)
                     (T (1+ *INDENT*)))
               1 *FILE*)
    (SETQ LAST-PRINEVAL-CHAR NIL)
    NIL))

(DEFUN !CLAUSE (CL INDENT)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET ((*INDENT* (OR INDENT *INDENT*)))
    (SETQ LAST-CLAUSE CL)
    (PPRINDENT (PRETTYIFY-CLAUSE CL)
               (COND ((INT= 0 *INDENT*) 0)
                     (T (1+ *INDENT*)))
               1 *FILE*)
    (SETQ LAST-PRINEVAL-CHAR NIL)
    NIL))

(DEFUN EQUALITY-HYP-NO (TERM CL)
  (LET (HYPS)
    (SETQ HYPS (ITERATE FOR LIT IN CL
                        COUNT (MATCH LIT (NOT (EQUAL & &)))))
    (COND ((INT= HYPS 1) NIL)
          (T  (1+ (ITERATE FOR LIT IN CL UNTIL (EQUAL LIT TERM)
                           COUNT (MATCH LIT (NOT (EQUAL & &)))))))))

(DEFUN GET-SCHEMA-MEASURE-RELATION (CANDIDATE CL-SET)

;   Returns a list of three things.  A schematic formula, using p applied to
;   all the vars in CL-SET, showing the induction in CANDIDATE; a measure
;   term, indicating what decreases; and the well-founded relation.  The
;   schematic formula is not a well-formed term!  It has been UNTRANSLATEd.

  (LET (TERM MEASURE-ARGS FORMALS SCHEMA MEASURE RELATION P-ARITY)
    (SETQ TERM (ACCESS CANDIDATE INDUCTION-TERM CANDIDATE))
    (SETQ FORMALS (CADR (GET (FFN-SYMB TERM) (QUOTE SDEFN))))
    (SETQ MEASURE (ACCESS JUSTIFICATION MEASURE-TERM
                          (ACCESS CANDIDATE JUSTIFICATION CANDIDATE)))

;   We must instantiate the measure term with the actuals.

    (SETQ MEASURE-ARGS (ALL-VARS MEASURE))
    (SETQ MEASURE
          (COND (MEASURE
                 (SUB-PAIR-VAR-LST MEASURE-ARGS
                                   (FILTER-ARGS MEASURE-ARGS
                                                FORMALS
                                                (FARGS TERM))
                                   MEASURE))
                (T NIL)))
    (SETQ RELATION (ACCESS JUSTIFICATION RELATION
                           (ACCESS CANDIDATE JUSTIFICATION CANDIDATE)))
    (SETQ SCHEMA
          (CONS (QUOTE AND)
                (ITERATE FOR CL IN
                         (IND-FORMULA
                          (ACCESS CANDIDATE TESTS-AND-ALISTS-LST CANDIDATE)
                          NIL
                          (LIST
                           (LIST
                            (CONS
                             (QUOTE |p|)
                             (REVERSE
                              (ALL-VARS-LST
                               (REVERSE (ITERATE FOR C IN CL-SET
                                                 APPEND C))))))))
                         COLLECT (PRETTYIFY-CLAUSE CL))))
    (SETQ P-ARITY (LENGTH (ALL-VARS-LST
                           (REVERSE (ITERATE FOR C IN CL-SET APPEND C)))))
    (LIST SCHEMA MEASURE RELATION P-ARITY)))


(DEFUN IO (PROCESS PARENT PARENT-HIST DESCENDANTS HIST-ENTRY)
  (LET (TIME)
    (SETQ TIME (TIME-IN-60THS))
    (APPLY IO-FN NIL)
    (SETQ IO-TIME (+ IO-TIME
                     (- (TIME-IN-60THS) TIME)))
    NIL))


(DEFUN IO1 NIL

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (PROG
   (SO-NEXT-CONSIDER ACCUMS CROSS DEFNS DIR ELIM-LEMMAS GEN-LEMMAS HIGH-CNT
                     INDENT KEEP LEMMAS LST MASS MERGED-CAND-CNT N NAME NAMES
                     OBVIOUS RAW-CAND-CNT SKOS TERM1 TERM2 TERMS WINNING-CAND
                     WON-FLG VETO-CNT BROTHER-NO MAX MEASURE RELATION SCHEMA
                     FAVORED-CNT HYP-NO FLG P-ARITY)
   (SETQ SO-NEXT-CONSIDER
         (PQUOTE
          (PROGN
            (COND ((EQ LAST-PROCESS (QUOTE POP))
                   |.|)) CR CR CR |#|
            (COND ((NOT (EQ LAST-PROCESS (QUOTE STORE-SENT)))
                   (? (|so| |next| |consider|)
                      (|so| |let| |us| |turn| |our| |attention|
                            |to|)
                      (|so| |we| |now| |return| |to|))
                   |:| CR CR (!CLAUSE-SET CL-SET INDENT)
                   (? (|,| CR CR |named|)
                      (|,| CR CR |which| |we| |named|)
                      (|,| CR CR |which| |is| |formula|))
                   (!PPR (CAR HIST-ENTRY) NIL)
                   |above| |.|)
                  ((AND (= (LENGTH CL-SET) 1)
                        (EQ LAST-CLAUSE (CAR CL-SET))))
                  (T |so| |now| |let| |us| (? (|consider|)
                                              (|return| |to|))
                     |:| CR CR (!CLAUSE-SET CL-SET NIL)
                     (? (|,| CR CR |named|)
                        (|,| CR CR |which| |we| |named|)
                        (|.| CR CR |we| |named| |this|)
                        (|.| CR CR |we| |gave| |this| |the| |name|))
                     (!PPR (CAR HIST-ENTRY) NIL)
                     (? (|above|)
                        NIL)
                     |.|)))))
   (COND ((EQ PROCESS (QUOTE SETUP))
          (SETQ CLAUSE-ALIST NIL)
          (SETQ LAST-PROCESS (QUOTE SETUP))
          (SETQ LAST-PRINEVAL-CHAR (QUOTE |.|))
          (NOTICE-CLAUSE PARENT 0 (LIST NIL)))
         ((EQ PROCESS (QUOTE SETTLED-DOWN-CLAUSE))
          (RETURN NIL))
         ((EQ PROCESS (QUOTE INDUCT))
          (COND ((AND (NOT LEFTMARGINCHAR) (EQ PARENT LAST-CLAUSE))
                 (SETQ TEMP-TEMP (UN-NOTICE-CLAUSE LAST-CLAUSE))
                 (SETQ CLAUSE-ALIST NIL)
                 (COND ((AND (INTEGERP (CADR TEMP-TEMP))
                             (< (CADR TEMP-TEMP) 16))
                        (NOTICE-CLAUSE LAST-CLAUSE (CADR TEMP-TEMP)
                                       (LIST NIL)))
                       (T (NOTICE-CLAUSE (CAR TEMP-TEMP)
                                         0
                                         (LIST NIL)))))
                (T (SETQ CLAUSE-ALIST NIL)
                   (NOTICE-CLAUSE PARENT 0 (LIST NIL))))))
   (SETQ TEMP-TEMP
         (COND ((AND PARENT
                     (NOT (MEMBER-EQ PROCESS
                                     (QUOTE (POP SUBSUMED-ABOVE
                                                 SUBSUMED-BY-PARENT
                                                 SUBSUMED-BELOW)))))
                (UN-NOTICE-CLAUSE PARENT))
               (T (QUOTE (NIL 0 (NIL))))))

;   The BROTHER-NO of a clause is the case number for it.  It is a list of
;   numbers, to be printed in reverse order, separated by dots.  If the CAR of
;   the BROTHER-NO is NIL it means do not print it.

   (SETQ BROTHER-NO (OR (CADDR TEMP-TEMP) (LIST NIL)))
   (SETQ INDENT (CADR TEMP-TEMP))
   (SETQ MAX (LENGTH DESCENDANTS))
   (ITERATE FOR CL IN DESCENDANTS AS I FROM MAX BY -1
            DO (NOTICE-CLAUSE CL (COND ((INT= MAX 1) INDENT)
                                       (T (+ TREE-INDENT INDENT)))
                              (COND ((INT= MAX 1)
                                     (COND ((CAR BROTHER-NO)
                                            (CONS NIL BROTHER-NO))
                                           (T BROTHER-NO)))
                                    ((CAR BROTHER-NO) (CONS I BROTHER-NO))
                                    (T (CONS I (CDR BROTHER-NO))))))
   (COND ((MEMBER-EQ PROCESS EXECUTE-PROCESSES)
          (COND ((EQ LAST-PROCESS (QUOTE SETUP))
                 (SETQ LAST-CLAUSE PARENT))
                (T (ITERPRIN TREE-LINES PROVE-FILE)
                   (ISPACES (- INDENT TREE-INDENT) PROVE-FILE)
                   (COND ((AND (NOT (EQUAL INDENT 0)) (CAR BROTHER-NO))
                          (IPRINC (QUOTE |Case |) PROVE-FILE)
                          (ITERATE FOR I IN (REVERSE BROTHER-NO) DO
                                   (PROGN (IPRINC I PROVE-FILE)
                                          (IPRINC (QUOTE |.|) PROVE-FILE)))))
                   (PRINEVAL (PQUOTE (!CLAUSE PARENT NIL))
                             `((PARENT . ,PARENT))
                             (+ 5 INDENT)
                             PROVE-FILE)))))
   (CASE
    PROCESS
    (SIMPLIFY-CLAUSE
     (SETQ FLG NIL)
     (SETQ LEMMAS NIL)
     (SETQ DEFNS NIL)
     (ITERATE FOR X IN HIST-ENTRY
              DO (COND ((CONSP X)

;   A CONSP entry here means that PROCESS-EQUATIONAL-POLYS added an equality to
;   this clause.  The form of X in this case is ((FIND-EQUATIONAL-POLY lhs .
;   rhs)), where lhs and rhs are the sides of the equation added.  In this
;   case, ZERO is also a member of HIST-ENTRY and at the moment we will just
;   ignore this opportunity to make the IO fancier.

                        NIL)
                       ((EQ X (QUOTE ZERO)) (SETQ FLG T))
                       ((GET X (QUOTE TYPE-PRESCRIPTION-LST))
                        (SETQ DEFNS (CONS X DEFNS)))
                       (T (SETQ LEMMAS (CONS X LEMMAS)))))
     (COND ((AND (EQ LAST-PROCESS (QUOTE SETUP))
                 (INT= (LENGTH DESCENDANTS) 1)
                 (NOT LEMMAS)
                 (ITERATE FOR X IN DEFNS
                          ALWAYS (MEMBER-EQ X (QUOTE (AND OR NOT IMPLIES))))
                 (NOT FLG))

;   pretend nothing happened in this case.

            (RPLACA (CDR (ASSOC-EQ (CAR DESCENDANTS) CLAUSE-ALIST)) 0)
            (RETURN NIL))
           (T
            (PRINEVAL
             (PQUOTE
              (PROGN
                (COND ((EQ LAST-PROCESS (QUOTE SETUP))
                       |this| (? (|formula|) (|conjecture|) NIL)
                       |simplifies|)
                      (T (? (|,| CR CR |which|
                                 (? (|we| (@ FURTHER?) |simplify|)
                                    ((@ FURTHER?) |simplifies|)))
                            (|.| CR CR (COND ((EQ HIST-ENTRY NIL)
                                              (? NIL (|of| |course| |,|)))
                                             (PARENT-HIST
                                              (? (|but|) NIL (|however|))))
                                 |this|
                                 (? (|simplifies| (@ FURTHER?))
                                    ((@ FURTHER?)
                                     |simplifies|))))))
                (COND (FLG |,| |using| |linear| |arithmetic|
                           (COND ((AND (NOT LEMMAS) (NOT DEFNS)) |,|))))
                (COND (LEMMAS (COND ((AND FLG (NOT DEFNS)) |and|)
                                    (T |,|))
                              (? ((? (|appealing| |to|)
                                     (|applying|)
                                     (|rewriting| |with|))
                                  |the|
                                  (PLURAL? LEMMAS |lemmas| |lemma|))
                                 (|applying|)
                                 (|rewriting| |with|))
                              (!LIST LEMMAS)
                              |,|))
                (COND (DEFNS (COND ((OR FLG LEMMAS) |and|) (T |,|))
                        (? (|opening| |up|)
                           (|expanding|)
                           (|unfolding|))
                        (? (|the| (PLURAL? DEFNS |functions| |function|))
                           (|the| (PLURAL? DEFNS |definitions|
                                           |definition|)
                                  |of|)
                           NIL)
                        (!LIST DEFNS)
                        |,|))
                (COND ((AND (NOT FLG) (EQ LEMMAS NIL) (EQ DEFNS NIL))
                       |,|
                       (? (|trivially|) (|clearly|) (|obviously|))
                       |,|))
                |to|))
             `((DEFNS . ,DEFNS)
               (LEMMAS . ,LEMMAS)
               (PARENT-HIST . ,PARENT-HIST)
               (HIST-ENTRY . ,HIST-ENTRY)
               (FURTHER? . ,(COND ((AND (NOT DESCENDANTS)
                                        (> (LENGTH PARENT-HIST) 5))
                                   (PQUOTE |finally|))
                                  ((EQ (CAAR PARENT-HIST)
                                       (QUOTE SIMPLIFY-CLAUSE))
                                   (PQUOTE |again|))
                                  ((ASSOC-EQ (QUOTE SIMPLIFY-CLAUSE)
                                             PARENT-HIST)
                                   (PQUOTE |further|))
                                  (T NIL)))
               (LAST-PROCESS . ,LAST-PROCESS)
               (FLG . ,FLG))
             INDENT PROVE-FILE))))
    (FERTILIZE-CLAUSE (MATCH HIST-ENTRY
                             (LIST MASS CROSS DIR TERM1 TERM2 KEEP))
                      (SETQ HYP-NO
                            (EQUALITY-HYP-NO
                             (LIST (QUOTE NOT)
                                   (LIST (QUOTE EQUAL) TERM1 TERM2))
                             PARENT))
                      (OR (EQ DIR (QUOTE LEFT-FOR-RIGHT))
                          (OUR-SWAP TERM1 TERM2))
                      (PRINEVAL
                       (PQUOTE (PROGN |.| CR CR |we| (? NIL NIL (|now|))
                                      |use| |the|
                                      (COND (HYP-NO (@ N)) (T |above|))
                                      |equality| |hypothesis|
                                      (COND ((OR MASS (NOT CROSS))
                                             |by| |substituting|)
                                            (T |by| |cross-fertilizing|))
                                      (!TERM TERM1 NIL)
                                      |for|
                                      (!TERM TERM2 NIL)
                                      (COND (KEEP |and| |keeping| |the|
                                                  |equality|
                                                  |hypothesis|)
                                            (T |and| |throwing| |away|
                                               |the| |equality|))
                                      |.|))
                       `((KEEP . ,KEEP)
                         (TERM2 . ,TERM2)
                         (TERM1 . ,TERM1)
                         (CROSS . ,CROSS)
                         (MASS . ,MASS)
                         (N . ,(TH-IFY HYP-NO))
                         (HYP-NO . ,HYP-NO))
                       INDENT PROVE-FILE))
    (ELIMINATE-DESTRUCTORS-CLAUSE
     (SETQ ELIM-LEMMAS NIL)
     (SETQ GEN-LEMMAS NIL)
     (ITERATE FOR X IN HIST-ENTRY DO
              (PROGN
                (SETQ ELIM-LEMMAS (ADD-TO-SET (CAR X) ELIM-LEMMAS))
                (SETQ LST
                      (CONS (LIST (QUOTE PROGN)
                                  (LIST (QUOTE !TERM)
                                        (KWOTE (CAR (CDDDDR X)))
                                        NIL)
                                  (PQUOTE |by|)
                                  (LIST (QUOTE !TERM)
                                        (KWOTE (CADR (CDDDDR X)))
                                        NIL)
                                  (PQUOTE (PROGN |to| |eliminate|))
                                  (LIST (QUOTE !LIST)
                                        (KWOTE (ITERATE FOR D IN (CADR X)
                                                        COLLECT
                                                        (LIST (QUOTE !TERM)
                                                              (KWOTE D)
                                                              NIL)))))
                            LST))
                (COND ((CADDR X)
                       (SETQ
                        GEN-LEMMAS
                        (UNION-EQUAL
                         (ITERATE FOR TERM IN (CADDR X)
                                  WITH ITERATE-ANS DO
                                  (SETQ
                                   ITERATE-ANS
                                   (ADD-TO-SET
                                    (LIST (QUOTE PROGN)
                                          (PQUOTE
                                           (PROGN |the| |type| |restriction|
                                                  |lemma| |noted| |when|))
                                          (FN-SYMB (ARGN TERM 1))
                                          (PQUOTE (PROGN |was| |introduced|)))
                                    ITERATE-ANS))
                                  FINALLY (RETURN ITERATE-ANS))
                         GEN-LEMMAS))))
                (SETQ GEN-LEMMAS (UNION-EQUAL (CADDDR X) GEN-LEMMAS))))
     (PRINEVAL
      (PQUOTE
       (PROGN |.| CR CR (? (|applying|) (|appealing| |to|)) |the|
              (PLURAL? ELIM-LEMMAS |lemmas| |lemma|)
              (!LIST ELIM-LEMMAS)
              |,| (? (|we| |now|) NIL) |replace| (!LIST LST) |.|
              (COND (GEN-LEMMAS
                     |we| (? (|use|) (|rely| |upon|) (|employ|))
                     (!LIST GEN-LEMMAS)
                     |to| (? (|constrain|) (|restrict|))
                     |the| |new|
                     (COND ((OR (CDR ELIM-LEMMAS)
                                (CDR (CAR (CDR (CAR HIST-ENTRY)))))
                            |variables|)
                           (T |variable|))
                     |.|))))
      `((HIST-ENTRY . ,HIST-ENTRY)
        (ELIM-LEMMAS . ,ELIM-LEMMAS)
        (GEN-LEMMAS . ,GEN-LEMMAS)
        (LST . ,LST))
      INDENT PROVE-FILE))
    (GENERALIZE-CLAUSE
     (MATCH HIST-ENTRY (LIST SKOS TERMS OBVIOUS LEMMAS))
     (SETQ LST (ITERATE FOR TERM IN TERMS AS VAR IN SKOS
                        COLLECT (LIST (QUOTE PROGN)
                                      (LIST (QUOTE !TERM) (KWOTE TERM) NIL)
                                      (PQUOTE |by|)
                                      (LIST (QUOTE !TERM) (KWOTE VAR) NIL))))
     (COND (OBVIOUS
            (SETQ
             LEMMAS
             (UNION-EQUAL
              (ITERATE FOR TERM IN OBVIOUS WITH ITERATE-ANS DO
                       (SETQ ITERATE-ANS
                             (ADD-TO-SET
                              (LIST (QUOTE PROGN)
                                    (PQUOTE (PROGN |the| |type| |restriction|
                                                   |lemma| |noted| |when|))
                                    (FN-SYMB (ARGN TERM 1))
                                    (PQUOTE (PROGN |was| |introduced|)))
                              ITERATE-ANS))
                       FINALLY (RETURN ITERATE-ANS))
              LEMMAS))))
     (PRINEVAL (PQUOTE (PROGN (? (|,| CR CR |which| |we| |generalize| |by|)
                                 (|.| CR CR |we| |will| |try| |to| |prove|
                                      |the| |above|
                                      (? (|formula|) (|conjecture|))
                                      |by| |generalizing| |it| |,|))
                              |replacing| (!LIST LST) |.|
                              (COND (LEMMAS |we| |restrict| |the| |new|
                                            (PLURAL? SKOS
                                                     |variables|
                                                     |variable|)
                                            |by|
                                            (? (|appealing| |to|)
                                               (|recalling|))
                                            (!LIST LEMMAS)
                                            |.|))))
               `((LEMMAS . ,LEMMAS)
                 (SKOS . ,SKOS)
                 (LST . ,LST))
               INDENT PROVE-FILE))
    (ELIMINATE-IRRELEVANCE-CLAUSE
     (PRINEVAL (PQUOTE (? (|,| CR CR |which| |has| (PLURAL? N (@ N) |an|)
                               |irrelevant| (PLURAL? N |terms| |term|)
                               |in| |it| |.| |by| |eliminating|
                               (PLURAL? N (PROGN |these| |terms|)
                                        (PROGN |the| |term|))
                               |we| |get|)
                          (|.| CR CR |eliminate|
                               (PLURAL? N NIL |the|) |irrelevant|
                               (PLURAL? N |terms| |term|) |.|)))
               `((N . ,(- (LENGTH PARENT) (LENGTH (CAR DESCENDANTS)))))
               INDENT PROVE-FILE))
    (STORE-SENT (NOTICE-CLAUSE PARENT INDENT BROTHER-NO)
                (COND ((AND PARENT (EQ LAST-PROCESS (QUOTE SETUP))
                            (CADR HIST-ENTRY))
                       (SETQ LAST-CLAUSE (CADR HIST-ENTRY))
                       (NOTICE-CLAUSE LAST-CLAUSE 0 (LIST NIL))))
                (PRINEVAL (PQUOTE
                           (COND ((EQ PARENT NIL)
                                  (? (|,| CR CR |which| |means| |the|
                                          |proof| |attempt| |has|)
                                     (|.| CR CR |why| |say| |more| ?)
                                     (|.| CR CR |need| |we| |go| |on| ?)))
                                 ((EQ LAST-PROCESS (QUOTE SETUP))
                                  CR |#|
                                  (? (|give| |the| |conjecture| |the|
                                             |name|)
                                     (|name| |the| |conjecture|)
                                     (|call| |the| |conjecture|))
                                  (!PPR (CAR HIST-ENTRY) (QUOTE |.|)))
                                 ((EQ (QUOTE QUIT) (CAR (CDR HIST-ENTRY)))
                                  |,| CR CR |which| |we| |would| |normally|
                                  |try| |to| |prove| |by| |induction| |.|
                                  |But| |since| |the|
                                  DO-NOT-INDUCT |hint| |has| |been|
                                  |provided| |by| |the| |user| |,| |the|
                                  |proof| |attempt| |has|)
                                 ((CAR (CDR HIST-ENTRY))
                                  |,| CR CR |which| |we| |would|
                                  (? (|normally|) (|usually|)) |push| |and|
                                  |work| |on| |later| |by| |induction| |.|
                                  |But| |if| |we| |must| |use| |induction|
                                  |to| |prove| |the| |input| |conjecture|
                                  |,| |we| |prefer| |to| |induct| |on| |the|
                                  |original| |formulation| |of| |the|
                                  |problem| |.| |Thus| |we| |will|
                                  |disregard| |all| |that| |we| |have|
                                  |previously| |done| |,| |give| |the|
                                  |name| (!PPR (CAR HIST-ENTRY) NIL) |to|
                                  |the| |original| |input| |,| |and| |work|
                                  |on| |it| |.|)
                                 (T (? (|,| CR CR |which| |we|
                                            |will| (@ FINALLY?) |name|
                                            (!PPR (CAR HIST-ENTRY)
                                                  (QUOTE |.|)))
                                       (|.| CR CR (@ FINALLY?)
                                            (? (|give| |the| |above|
                                                       |formula| |the|
                                                       |name|)
                                               (|name| |the| |above|
                                                       |subgoal|)
                                               (|call| |the| |above|
                                                       |conjecture|))
                                            (!PPR (CAR HIST-ENTRY)
                                                  (QUOTE |.|)))))))
                          `((HIST-ENTRY . ,HIST-ENTRY)
                            (LAST-PROCESS . ,LAST-PROCESS)
                            (PARENT . ,PARENT)
                            (FINALLY? . ,(COND ((> (LENGTH PARENT-HIST) 5)
                                                (PQUOTE |finally|))
                                               (T NIL))))
                          INDENT PROVE-FILE))
    (POP (PRINEVAL (PQUOTE (PROGN (COND ((EQ LAST-PROCESS (QUOTE POP))
                                         |,| |which|
                                         (? (|,| |in| |turn| |,|)
                                            (|,| |consequently| |,|)
                                            NIL)
                                         (? (|also|) NIL))
                                        (T CR CR CR |#| |that|))
                                  |finishes| |the| |proof| |of|
                                  (!PPR (CAR HIST-ENTRY) NIL)))
                   `((HIST-ENTRY . ,HIST-ENTRY)
                     (LAST-PROCESS . ,LAST-PROCESS))
                   0 PROVE-FILE))
    (SUBSUMED-ABOVE
     (PRINEVAL
      (PQUOTE (PROGN (@ SO-NEXT-CONSIDER)
                     (? (|ha| EXCL) (|how| |nice| EXCL) NIL NIL NIL)
                     |this|
                     (? (|conjecture|) (|formula|) (|goal|) NIL)
                     |is| |subsumed| |by| |the|
                     (? ((? (|lemma|) (|theorem|) (|goal|))
                         |we| |named| (!PPR (CAR (CDR HIST-ENTRY)) NIL)
                         |and| |proved| |above|)
                        (|previously| |proved|
                                      (!PPR (CAR (CDR HIST-ENTRY)) NIL))
                        ((!PPR (CAR (CDR HIST-ENTRY)) |,|)
                         |which| |was| |proved| |above|))
                     EXCL))
      `((HIST-ENTRY . ,HIST-ENTRY)
        (SO-NEXT-CONSIDER . ,SO-NEXT-CONSIDER)
        (LAST-PROCESS . ,LAST-PROCESS)
        (CL-SET . ,PARENT)
        (LAST-CLAUSE . ,LAST-CLAUSE)
        (INDENT . ,5))
      0 PROVE-FILE))
    (SUBSUMED-BY-PARENT
     (PRINEVAL (PQUOTE (PROGN (@ SO-NEXT-CONSIDER)
                              (? (|oh| |no| EXCL) (|oops| EXCL) NIL)
                              |this| |formula| |is| |subsumed| |by| |its|
                              |parent| |,|
                              (!PPR (CAR (CDR HIST-ENTRY)) NIL)
                              EXCL (? (|that| |means| |we| |would|
                                              |loop| |if| |we|
                                              |tried| |to| |prove| |it| |by|
                                              |induction| |.|)
                                      NIL NIL)))
               `((HIST-ENTRY . ,HIST-ENTRY)
                 (SO-NEXT-CONSIDER . ,SO-NEXT-CONSIDER)
                 (LAST-PROCESS . ,LAST-PROCESS)
                 (CL-SET . ,PARENT)
                 (LAST-CLAUSE . ,LAST-CLAUSE)
                 (INDENT . ,5))
               0 PROVE-FILE))
    (SUBSUMED-BELOW (PRINEVAL
                     (PQUOTE (PROGN (@ SO-NEXT-CONSIDER)
                                    (? (|ah| |ha| EXCL) (|what| |luck| EXCL)
                                       (|you| |probably| |did| |not|
                                              |notice| |,| |but|)
                                       (|but|)
                                       NIL)
                                    |this| |conjecture| |is|
                                    |subsumed| |by|
                                    (? (|another| |subgoal|
                                                  |awaiting| |our|
                                                  |attention| |,|
                                                  |namely|)
                                       (|the| |subgoal| |we| |named|)
                                       (|formula|))
                                    (!PPR (CAR (CDR HIST-ENTRY)) NIL)
                                    |above| |.|))
                     `((HIST-ENTRY . ,HIST-ENTRY)
                       (SO-NEXT-CONSIDER . ,SO-NEXT-CONSIDER)
                       (LAST-PROCESS . ,LAST-PROCESS)
                       (CL-SET . ,PARENT)
                       (LAST-CLAUSE . ,LAST-CLAUSE)
                       (INDENT . ,5))
                     0 PROVE-FILE))
    (INDUCT
     (MATCH HIST-ENTRY
            (LIST NAME WINNING-CAND RAW-CAND-CNT MERGED-CAND-CNT VETO-CNT
                  HIGH-CNT FAVORED-CNT))
     (COND
      (WINNING-CAND
       (SETQ FLG NIL)
       (SETQ LEMMAS NIL)
       (SETQ DEFNS NIL)
       (ITERATE FOR X
                IN (ACCESS JUSTIFICATION LEMMAS
                           (ACCESS CANDIDATE JUSTIFICATION WINNING-CAND))
                DO (COND ((EQ X (QUOTE ZERO)) (SETQ FLG T))
                         ((GET X (QUOTE TYPE-PRESCRIPTION-LST))
                          (SETQ DEFNS (CONS X DEFNS)))
                         (T (SETQ LEMMAS (CONS X LEMMAS)))))
       (MATCH (GET-SCHEMA-MEASURE-RELATION WINNING-CAND PARENT)
              (LIST SCHEMA MEASURE RELATION P-ARITY))
       (SETQ ACCUMS
             (SET-DIFF (ACCESS CANDIDATE CHANGED-VARS WINNING-CAND)
                       (ALL-VARS MEASURE)))
       (LET ((ARITY-ALIST (CONS (CONS (QUOTE |p|) P-ARITY) ARITY-ALIST)))
         (PRINEVAL
          (PQUOTE
           (PROGN
             (@ SO-NEXT-CONSIDER)
             (? (|we| |will| |try| |to| |prove| |it| |by| |induction| |.|)
                (|perhaps| |we| |can| |prove| |it| |by| |induction| |.|)
                (|let| |us| |appeal| |to| |the| |induction|
                       |principle| |.|)
                (|we| |will| |appeal| |to| |induction| |.|))
             (COND
              ((NOT (= RAW-CAND-CNT 1))
               (? (|there| |are| (@ RAW-CAND-CNT)
                           |plausible| |inductions|)
                  ((@ RAW-CAND-CNT)
                   |inductions| |are|
                   |suggested| |by| |terms|
                   |in| |the| |conjecture|)
                  (|the| |recursive| |terms| |in| |the|
                         |conjecture| |suggest|
                         (@ RAW-CAND-CNT)
                         |inductions|))
               (COND ((= RAW-CAND-CNT MERGED-CAND-CNT))
                     ((= MERGED-CAND-CNT 1)
                      |.| |However| |,| |they|
                      |merge| |into| |one|
                      |likely| |candidate| |induction| |.|)
                     (T |.| |They| |merge| |into| (@ MERGED-CAND-CNT)
                        |likely| |candidate| |inductions|))
               (COND
                ((NOT (= MERGED-CAND-CNT 1))
                 (COND ((= VETO-CNT 0)
                        |,|
                        (COND ((= MERGED-CAND-CNT 2) |both|) (T |all|))
                        |of| |which| |are| |flawed| |.|)
                       ((= VETO-CNT MERGED-CAND-CNT)
                        |,|
                        (COND ((= VETO-CNT 2) |both|) (T |all|))
                        |of| |which| |are| |unflawed| |.|)
                       ((= VETO-CNT 1)
                        |.| |however| |,| |only| |one| |is|
                        |unflawed| |.|)
                       (T |,| (@ VETO-CNT)
                          |of| |which| |are| |unflawed| |.|))
                 (COND
                  ((NOT (= VETO-CNT 1))
                   (COND ((= FAVORED-CNT 1)
                          |so| |we| |will| |choose| |the| |one|
                          |suggested| |by| |the| |largest| |number|
                          |of| |nonprimitive| |recursive| |functions|
                          |.|)
                         (T (COND ((NOT (= FAVORED-CNT VETO-CNT))
                                   |we| |limit| |our|
                                   |consideration| |to| |the|
                                   (@ FAVORED-CNT)
                                   |suggested| |by| |the|
                                   |largest| |number| |of|
                                   |nonprimitive|
                                   |recursive| |functions|
                                   |in| |the| |conjecture| |.|))
                            (COND ((= HIGH-CNT 1)
                                   |however| |,| |one| |of|
                                   |these| |is| |more| |likely|
                                   |than| |the|
                                   (COND ((= FAVORED-CNT 2)
                                          |other|)
                                         (T |others|))
                                   |.|)
                                  (T |since|
                                     (COND ((= HIGH-CNT FAVORED-CNT)
                                            (COND ((= HIGH-CNT
                                                      2)
                                                   |both|)
                                                  (T |all|)))
                                           (T (@ HIGH-CNT)))
                                     |of| |these| |are| |equally|
                                     |likely| |,| |we| |will|
                                     |choose| |arbitrarily|
                                     |.|)))))))))
              (T |there| |is| |only| |one| (? (|plausible|)
                                              (|suggested|))
                 |induction| |.|))
             |we| |will| |induct| |according| |to| |the| |following|
             |scheme| (!PPR SCHEMA (QUOTE |.|))
             (COND (MEASURE (@ JUSTIFICATION-SENTENCE)
                            (PLURAL? TESTS-AND-ALISTS-LST |each| |the|)
                            |induction| |step| |of| |the| |scheme| |.|
                            (COND (ACCUMS |note| |,| |however| |,| |the|
                                          |inductive|
                                          (COND (INSTANCES?
                                                 |instances|)
                                                (T |instance|))
                                          |chosen| |for|
                                          (!TERM-LIST ACCUMS (QUOTE 
                                                              |.|))))
                            |the| |above| |induction| |scheme|
                            (? (|produces|)
                               (|generates|)
                               (|leads| |to|)))
                   (T |this| |scheme| |is| |justified| |by| |the|
                      |assumption| |that| (!PPR (FN-SYMB TERM) NIL)
                      |is| |total| |.|))))
          `((ACCUMS . ,ACCUMS)
            (JUSTIFICATION-SENTENCE . ,(JUSTIFICATION-SENTENCE))
            (RELATION . ,RELATION)
            (MEASURE . ,MEASURE)
            (LEMMAS . ,LEMMAS)
            (DEFNS . ,DEFNS)
            (FLG . ,FLG)
            (NUMBER . ,(LENGTH (ACCESS JUSTIFICATION LEMMAS
                                       (ACCESS CANDIDATE JUSTIFICATION
                                               WINNING-CAND))))
            (SCHEMA . ,SCHEMA)
            (FAVORED-CNT . ,FAVORED-CNT)
            (HIGH-CNT . ,HIGH-CNT)
            (MERGED-CAND-CNT . ,MERGED-CAND-CNT)
            (VETO-CNT . ,VETO-CNT)
            (RAW-CAND-CNT . ,RAW-CAND-CNT)
            (SO-NEXT-CONSIDER . ,SO-NEXT-CONSIDER)
            (TESTS-AND-ALISTS-LST . ,(ACCESS CANDIDATE
                                             TESTS-AND-ALISTS-LST
                                             WINNING-CAND))
            (INSTANCES? . ,(OR (CDR ACCUMS)
                               (NOT (= 1
                                       (ITERATE FOR TA
                                                IN
                                                (ACCESS CANDIDATE
                                                        TESTS-AND-ALISTS-LST
                                                        WINNING-CAND)
                                                SUM (LENGTH (ACCESS
                                                             TESTS-AND-ALISTS
                                                             ALISTS TA)))))))
            (TERM . ,(ACCESS CANDIDATE INDUCTION-TERM WINNING-CAND))
            (LAST-PROCESS . ,LAST-PROCESS)
            (CL-SET . ,PARENT)
            (LAST-CLAUSE . ,LAST-CLAUSE)
            (HIST-ENTRY . ,HIST-ENTRY)
            (INDENT . ,(+ 5 INDENT)))
          INDENT PROVE-FILE)))
      (T (PRINEVAL (PQUOTE (PROGN (@ SO-NEXT-CONSIDER)
                                  |since| |there| |is| |nothing| |to|
                                  |induct| |upon| |,| |the| |proof| |has|))
                   `((SO-NEXT-CONSIDER . ,SO-NEXT-CONSIDER)
                     (LAST-PROCESS . ,LAST-PROCESS)
                     (CL-SET . ,PARENT)
                     (LAST-CLAUSE . ,LAST-CLAUSE)
                     (HIST-ENTRY . ,HIST-ENTRY)
                     (INDENT . ,5))
                   0 PROVE-FILE))))
    (SETUP
     (PRINEVAL (PQUOTE CR) NIL INDENT PROVE-FILE)
     (COND ((AND (INT= (LENGTH DESCENDANTS) 1)
                 (ITERATE FOR X IN HIST-ENTRY
                          ALWAYS (MEMBER-EQ X (QUOTE (AND OR NOT IMPLIES)))))
            NIL)
           (T (PRINEVAL
               (PQUOTE (PROGN |this| (? (|formula|) (|conjecture|))
                              |can| |be|
                              (COND (HIST-ENTRY |simplified| |,| |using|
                                                |the|
                                                (PLURAL? HIST-ENTRY
                                                         |abbreviations|
                                                         |abbreviation|)
                                                (!LIST HIST-ENTRY)
                                                |,|)
                                    (T |propositionally| |simplified|))
                              |to|))
               `((HIST-ENTRY . ,HIST-ENTRY))
               INDENT PROVE-FILE))))
    (FINISHED (MATCH HIST-ENTRY (LIST WON-FLG))
              (PRINEVAL (PQUOTE
                         (PROGN (COND ((EQ LAST-PROCESS (QUOTE POP))
                                       |.|
                                       (COND (WON-FLG |Q.E.D.|)
                                             (T CR CR (@ FAILURE-MSG))))
                                      (T CR CR
                                         (COND ((EQ WON-FLG
                                                    (QUOTE DEFN-OK)))
                                               (WON-FLG |Q.E.D.|)
                                               (T (@ FAILURE-MSG))))) CR
                                               CR))
                        `((FAILURE-MSG . ,FAILURE-MSG)
                          (WON-FLG . ,WON-FLG)
                          (LAST-PROCESS . ,LAST-PROCESS))
                        0 PROVE-FILE))
    (OTHERWISE
     (ER HARD (PROCESS) IO1 |has| |been| |given| |an| |unrecognized|
         |process| |named| (!PPR PROCESS (QUOTE |.|)))))
   (COND ((NOT (OR (MEMBER-EQ PROCESS UN-PRODUCTIVE-PROCESSES)
                   (AND (EQ PROCESS (QUOTE INDUCT))
                        (NOT (CADR HIST-ENTRY)))
                   (AND (EQ PROCESS (QUOTE SETUP))
                        (INT= (LENGTH DESCENDANTS) 1)
                        (ITERATE FOR X IN HIST-ENTRY
                                 ALWAYS (MEMBER-EQ
                                         X
                                         (QUOTE (AND OR NOT IMPLIES)))))))
          (SETQ N (LENGTH DESCENDANTS))
          (COND ((EQ LAST-PRINEVAL-CHAR (QUOTE |.|))
                 (PRINEVAL (PQUOTE (? (|we| |thus| |obtain|)
                                      (|the| |result| |is|)
                                      (|this| |produces|)
                                      (|this| |generates|)
                                      (|we| |would| |thus| |like| |to|
                                            |prove|)
                                      (|we| |must| |thus| |prove|)))
                           NIL
                           INDENT PROVE-FILE)))
          (COND ((NOT (EQ LAST-PRINEVAL-CHAR (QUOTE |:|)))
                 (PRINEVAL (PQUOTE (PROGN (COND ((EQUAL N 0)
                                                 NIL)
                                                ((EQUAL N 1)
                                                 (? (|the| (? (|new|)
                                                              NIL)
                                                           (? (|goal|)
                                                              (|conjecture|)
                                                              (|formula|)))
                                                    NIL NIL))
                                                (T
                                                 (? ((@ N)
                                                     |new|
                                                     (? (|goals|)
                                                        (|conjectures|)
                                                        (|formulas|)))
                                                    (|the|
                                                     |following|
                                                     (@ N)
                                                     |new|
                                                     (? (|goals|)
                                                        (|conjectures|)
                                                        (|formulas|))))))
                                          |:|))
                           `((N . ,N))
                           INDENT PROVE-FILE)))))
   (COND ((AND (NOT (MEMBER-EQ PROCESS UN-PRODUCTIVE-PROCESSES))
               (NOT DESCENDANTS))
          (ITERPRIN TREE-LINES PROVE-FILE)
          (PRINEVAL (PQUOTE (PROGN T |.|))
                    NIL (+ 6 INDENT) PROVE-FILE)))
   (SETQ LAST-PROCESS
         (COND ((AND (EQ PROCESS (QUOTE SETUP))
                     (OR (NOT (INT= (LENGTH DESCENDANTS) 1))
                         (NOT (ITERATE FOR X IN HIST-ENTRY
                                       ALWAYS (MEMBER-EQ
                                               X
                                               (QUOTE (AND OR NOT
                                                           IMPLIES)))))))
                (QUOTE SETUP-AND-CLAUSIFY-INPUT))
               (T PROCESS)))
   (RETURN NIL)))

(DEFUN JUSTIFICATION-SENTENCE NIL

;   This fn returns a sentence to be fed to PRINEVAL.  The BINDINGS must
;   include FLG, LEMMAS, DEFNS, NUMBER, MEASURE, and RELATION.  FLG is T or NIL
;   indicating that linear arithmetic was used.  LEMMAS and DEFNS are the list
;   of lemmas and definitions used.  NUMBER is the length of LEMMAS plus that
;   of DEFNS plus 1 or 0 according to FLG.  MEASURE is a term and RELATION is a
;   fn name.

  (PQUOTE (PROGN (COND (FLG |linear| |arithmetic|
                            (COND ((AND LEMMAS DEFNS) |,|)
                                  ((OR LEMMAS DEFNS) |and|))))
                 (COND (LEMMAS |the| (PLURAL? LEMMAS |lemmas| |lemma|)
                               (!LIST LEMMAS)
                               (COND ((AND FLG DEFNS) |,| |and|)
                                     (DEFNS |and|))))
                 (COND (DEFNS |the| (PLURAL? DEFNS |definitions| |definition|)
                         |of| (!LIST DEFNS)))
                 (COND ((OR FLG LEMMAS DEFNS)
                        (PLURAL? NUMBER (? (|inform| |us|)
                                           (|establish|)
                                           (|can| |be| |used| |to|
                                                  (? (|prove|)
                                                     (|show|)
                                                     (|establish|))))
                                 (? (|establishes|)
                                    (|informs| |us|)
                                    (|can| |be| |used| |to|
                                           (? (|prove|)
                                              (|show|)
                                              (|establish|)))))
                        |that|)
                       (T (? (|it| |is| |obvious| |that|)
                             (|obviously|)
                             (|clearly|))))
                 |the| |measure| (!TERM MEASURE NIL)
                 |decreases| |according| |to| |the| |well-founded| |relation|
                 (!PPR RELATION NIL)
                 |in|)))

(DEFUN !LIST1 (*LST* *SEPR* *FINALSEPR*)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (MAPRINEVAL *LST* *INDENT* *FILE* NIL NIL *SEPR* *FINALSEPR*))

(DEFUN !LIST (*LST*)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (MAPRINEVAL *LST* *INDENT* *FILE* NIL NIL (PQUOTE |,|)
              (COND ((CDDR *LST*)
                     (PQUOTE (PROGN |,| |and|)))
                    (T (PQUOTE |and|)))))

(DEFUN MAPRINEVAL (*LST* *INDENT* *FILE* *LEFT* *RIGHT* *SEPR* *FINALSEPR*)
  (AND *LEFT* (PRINEVAL1 *LEFT*))
  (COND ((CONSP *LST*)
         (COND ((CDR *LST*)
                (ITERATE FOR TAIL ON *LST* DO
                         (PROGN
                           (PRINEVAL1 (CAR TAIL))
                           (COND ((NULL (CDR TAIL)) NIL)
                                 ((NULL (CDDR TAIL))
                                  (AND *FINALSEPR* (PRINEVAL1 *FINALSEPR*)))
                                 (T (AND *FINALSEPR* (PRINEVAL1 *SEPR*)))))))
               (T (PRINEVAL1 (CAR *LST*))))))
  (AND *RIGHT* (PRINEVAL1 *RIGHT*)))

(DEFUN NOTICE-CLAUSE (CL COL BROTHER-NO)
  (CAR (SETQ CLAUSE-ALIST (NCONC1 CLAUSE-ALIST
                                  (LIST CL (OR COL 0) BROTHER-NO)))))

(DEFUN PEVAL (FORM)
  (COND ((ATOM FORM)
         (COND ((SYMBOLP FORM)
                (COND ((OR (EQ FORM NIL) (EQ FORM T)) FORM)
                      (T (PEVALV FORM))))
               ((NUMBERP FORM) FORM)
               (T
                (ER HARD ((TERM FORM)) |Illegal| PEVAL |form| |,|
                    (!PPR TERM (QUOTE |.|))))))
        ((OR (EQ (CAR FORM) (QUOTE PQUOTE))
             (EQ (CAR FORM) (QUOTE QUOTE)))
         (CADR FORM))
        ((MEMBER-EQ (CAR FORM) PRINEVAL-FNS)
         (PEVAL-APPLY (CAR FORM)
                      (ITERATE FOR X IN (CDR FORM) COLLECT (PEVAL X))))
        (T (ER HARD ((TERM FORM)) |Illegal| PEVAL |form| |,|
               (!PPR TERM (QUOTE |.|))))))

(DEFUN PEVAL-APPLY (FN ARGS)
  (CASE FN
        (QUOTE (CAADR ARGS))
        (AND (COND ((NULL ARGS) T)
                   ((MEMBER-EQ NIL ARGS) NIL)
                   (T (CAR (OUR-LAST ARGS)))))
        (OR (ITERATE FOR X IN ARGS THEREIS X))
        (FN-SYMB (FN-SYMB (CAR ARGS)))
        (FFN-SYMB (FFN-SYMB (CAR ARGS)))
        (ARGN (ARGN (CAR ARGS) (CADR ARGS)))
        (FARGN (FARGN (CAR ARGS) (CADR ARGS)))
        (SARGS (SARGS (CAR ARGS)))
        (FARGS (FARGS (CAR ARGS)))
        (QUOTEP (QUOTEP (CAR ARGS)))
        (FQUOTEP (FQUOTEP (CAR ARGS)))
        (OTHERWISE (APPLY FN ARGS))))

(DEFUN PEVALV (X)
  (LET (TEMP)
    (COND ((SETQ TEMP (ASSOC-EQ X *ALIST*)) (CDR TEMP))
          (T (ERROR1 (PQUOTE (PROGN (!PPR X NIL) |is| |an| |unbound| |atom|
                                    |in| PRINEVAL EXCL))
                     (LIST (CONS (QUOTE X) X))
                     (QUOTE HARD))))))

(DEFUN PLURALP (X)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (NOT (OR (EQUAL X 1) (AND (CONSP X) (ATOM (CDR X))))))

(DEFUN !PPR-LIST (*LST* PUNCT)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (MAPRINEVAL (ITERATE FOR X ON *LST* COLLECT
                       (LIST (QUOTE !PPR)
                             (KWOTE (CAR X))
                             (COND ((ATOM (CDR X)) (KWOTE PUNCT))
                                   (T NIL))))
              *INDENT* *FILE* NIL NIL (PQUOTE |,|)
              (COND ((CDDR *LST*) (PQUOTE (PROGN |,| |and|)))
                    (T (PQUOTE |and|)))))

(DEFUN !PPR (X PUNCT)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET (NCHARS (*PRINT-PRETTY* NIL))
    (SETQ NCHARS (OUR-FLATC X))
    (COND ((> (+ 2 (MAX (IPOSITION *FILE* NIL NIL) *INDENT*) NCHARS)
              (OUR-LINEL *FILE* NIL))
           (COND ((AND (<= (+ *INDENT* NCHARS) (OUR-LINEL *FILE* NIL))
                       (< NCHARS 25))
                  (ITERPRI *FILE*)
                  (ISPACES *INDENT* *FILE*)
                  (IPRINC X *FILE*)
                  (SETQ LAST-PRINEVAL-CHAR (COND ((CONSP X) (QUOTE |)|))
                                                 (T (QUOTE X))))
                  (AND PUNCT (PRINEVAL1 PUNCT)))
                 (T (PRINEVAL1 (PQUOTE (PROGN |:| CR)))
                    (PPRINDENT X (+ *INDENT* 6)
                               (COND (PUNCT (LENGTH (SYMBOL-NAME PUNCT)))
                                     (T 0))
                               *FILE*)
                    (SETQ LAST-PRINEVAL-CHAR (COND ((CONSP X) (QUOTE |)|))
                                                   (T (QUOTE X))))
                    (AND PUNCT (PRINEVAL1 PUNCT))
                    (ITERPRI *FILE*))))
          (T (ISPACES (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
             (OR (INT= (IPOSITION *FILE* NIL NIL)
                       *INDENT*)
                 (ISPACES 1 *FILE*))
             (IPRINC X *FILE*)
             (SETQ LAST-PRINEVAL-CHAR (COND ((CONSP X) (QUOTE |)|))
                                            (T (QUOTE X))))
             (AND PUNCT (PRINEVAL1 PUNCT))))
    NIL))

(DEFUN PRIN5* (X)
  (LET (SPACES)
    (SETQ SPACES (COND ((INT= 0 (IPOSITION *FILE* NIL NIL)) 0)
                       ((EQ LAST-PRINEVAL-CHAR (QUOTE |.|)) 2)
                       ((EQ LAST-PRINEVAL-CHAR (QUOTE |:|)) 2)
                       (T 1)))
    (COND ((MEMBER-EQ X (QUOTE (CR |#| |.| EXCL ? |,| |:|)))
           (COND ((EQ X (QUOTE CR)) (ITERPRI *FILE*))
                 ((EQ X (QUOTE |#|))
                  (ISPACES (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
                  (ISPACES (- PARAGRAPH-INDENT 2) *FILE*)
                  (SETQ LAST-PRINEVAL-CHAR (QUOTE |.|)))
                 ((OR (EQ X (QUOTE |,|)) (EQ X (QUOTE |:|)))
                  (COND ((AND (NOT (MEMBER-EQ LAST-PRINEVAL-CHAR
                                              (QUOTE (|.| |,| |:|))))
                              (NOT (INT= 0 (IPOSITION *FILE* NIL NIL))))
                         (ISPACES
                          (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
                         (IPRINC X *FILE*)
                         (SETQ LAST-PRINEVAL-CHAR X))))
                 ((EQ X (QUOTE EXCL))
                  (ISPACES (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
                  (IPRINC "!" *FILE*)
                  (SETQ LAST-PRINEVAL-CHAR (QUOTE |.|)))
                 ((OR (EQ X (QUOTE |.|)) (EQ X (QUOTE ?)))
                  (ISPACES (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
                  (IPRINC X *FILE*)
                  (SETQ LAST-PRINEVAL-CHAR (QUOTE |.|)))
                 (T (ER HARD NIL |The| |code| |for| PRIN5* |is| |inconsistent|
                        |:| |the| MEMBER-EQ |says| |one| |thing|
                        |and| |the| COND
                        |says| |another| |.|))))
          ((EQ X NIL) NIL)
          (T
           (ISPACES (- *INDENT* (IPOSITION *FILE* NIL NIL)) *FILE*)
           (COND ((> (+ (IPOSITION *FILE* NIL NIL)
                        SPACES
                        (OUR-FLATC X) 1)
                     (OUR-LINEL *FILE* NIL))
                  (ITERPRI *FILE*)
                  (ISPACES *INDENT* *FILE*))
                 (T (ISPACES SPACES *FILE*)))
           (COND ((NUMBERP X)(IPRINC X *FILE*))
                 (T (COND ((EQ LAST-PRINEVAL-CHAR (QUOTE |.|))
                           (WRITE-CHAR (CHAR-UPCASE (CHAR (STRING X) 0))
                                       *FILE*)
                           (ITERATE WITH STR = (STRING X)
                                    FOR I FROM 1 TO (1- (LENGTH STR))
                                    DO
                                    (WRITE-CHAR (CHAR STR I) *FILE*))
                           #|(FORMAT (OR *FILE*
                                       *STANDARD-OUTPUT*)
                                   "~@(~A~)" X)|#
;  The foregoing FORMAT capitalizes X.
;  In Common Lisp *print-case* = :capitalize
;  does not capitalize lowercase atoms.
                           (IPOSITION *FILE* (OUR-FLATC X) T))
                          (T (IPRINC X *FILE*)))))
           (SETQ LAST-PRINEVAL-CHAR NIL)))
    NIL))

(DEFUN PRINEVAL (FORM *ALIST* *INDENT* *FILE*) (PRINEVAL1 FORM))

(DEFUN PRINEVAL1 (*FORM*)
  (COND ((ATOM *FORM*)
         (PRIN5* (COND ((INTEGERP *FORM*) (SPELL-NUMBER *FORM*))
                       (T *FORM*))))
        (T (CASE (CAR *FORM*)
                 (@ (PRINEVAL1 (PEVAL (CADR *FORM*))))
                 (? (ITERATE FOR *FORM*
                             IN (NTH (1+ (RANDOM-NUMBER (LENGTH (CDR *FORM*))))
                                     *FORM*)
                             DO (PRINEVAL1 *FORM*)))
                 ( COND (ITERATE FOR *FORM* IN (CDR *FORM*)
                                THEREIS
                                (COND ((PEVAL (CAR *FORM*))
                                       (ITERATE FOR *FORM* IN (CDR *FORM*)
                                                DO (PRINEVAL1 *FORM*))
                                       T))))
                 (PLURAL? (COND ((PLURALP (PEVAL (CADR *FORM*)))
                                 (PRINEVAL1 (CADDR *FORM*)))
                                (T (PRINEVAL1 (CADDDR *FORM*)))))
                 (PROGN (ITERATE FOR *FORM* IN (CDR *FORM*)
                                 DO (PRINEVAL1 *FORM*)))
                 (OTHERWISE (PEVAL *FORM*))))))

(DEFUN PRINT-DEFN-MSG (NAME ARGS)
  (PROG (TEMPS MEASURE RELATION LEMMAS FLG CONCL TIME N DEFNS)
        (COND (PETITIO-PRINCIPII (RETURN-FROM PRINT-DEFN-MSG T)))
        (SETQ LAST-PRIN5-WORD (QUOTE |.|))
        (SETQ TIME (TIME-IN-60THS))
        (COND (IN-BOOT-STRAP-FLG
               (SETQ IO-TIME (- (TIME-IN-60THS)
                                TIME))
               (RETURN NIL)))
        (SETQ TEMPS (GET NAME (QUOTE JUSTIFICATIONS)))
        (SETQ N (1- (LENGTH TEMPS)))
        (PRINEVAL (PQUOTE (PROGN CR |#|)) NIL 0 PROVE-FILE)
        (ITERATE FOR TEMP IN TEMPS AS I FROM 1 DO
                 (PROGN
                   (SETQ MEASURE (ACCESS JUSTIFICATION MEASURE-TERM TEMP))
                   (SETQ RELATION (ACCESS JUSTIFICATION RELATION TEMP))
                   (SETQ FLG NIL)
                   (SETQ LEMMAS NIL)
                   (SETQ DEFNS NIL)
                   (ITERATE FOR X IN (ACCESS JUSTIFICATION LEMMAS TEMP)
                            DO (COND ((EQ X (QUOTE ZERO)) (SETQ FLG T))
                                     ((GET X (QUOTE TYPE-PRESCRIPTION-LST))
                                      (SETQ DEFNS (CONS X DEFNS)))
                                     (T (SETQ LEMMAS (CONS X LEMMAS)))))
                   (PRINEVAL
                    (PQUOTE (PROGN (COND (FINALLY? (COND ((EQUAL N 2)
                                                          |In| |addition|)
                                                         (T |Finally|)) |,|))
                                   (@ JUSTIFICATION-SENTENCE)
                                   |each| |recursive| |call| |.|
                                   (COND ((EQUAL I 1)
                                          |Hence| |,| (!PPR NAME NIL)
                                          |is| |accepted| |under| |the|
                                          (? (|principle| |of| |definition|)
                                             (|definitional| |principle|))
                                          |.|
                                          (COND ((EQUAL N 1)
                                                 |the| |definition| |of|
                                                 (!PPR NAME NIL)
                                                 |can| |be| |justified|
                                                 |in| |another|
                                                 |way| |.|)
                                                (OTHERS
                                                 |there| |are| (@ N)
                                                 |other|
                                                 (? (|explanations| |of|)
                                                    (|measures|
                                                     |and| |well-founded|
                                                     |functions|
                                                     |explaining|))
                                                 |the| |recursion|
                                                 |above| |.|))))))
                    `((N . ,N)
                      (NAME . ,NAME)
                      (I . ,I)
                      (JUSTIFICATION-SENTENCE . ,(JUSTIFICATION-SENTENCE))
                      (RELATION . ,RELATION)
                      (MEASURE . ,MEASURE)
                      (DEFNS . ,DEFNS)
                      (LEMMAS . ,LEMMAS)
                      (FLG . ,FLG)
                      (NUMBER . ,(LENGTH (ACCESS JUSTIFICATION LEMMAS TEMP)))
                      (FINALLY? . ,(AND (NOT (EQUAL I 1))
                                        (NOT (EQUAL N 1))
                                        (EQUAL I (1+ N))))
                      (OTHERS . ,(> N 1)))
                    0 PROVE-FILE)))
        (COND ((NOT (TS= TYPE-SET-UNKNOWN (CAR (TYPE-PRESCRIPTION NAME))))
               (SETQ TEMP-TEMP
                     (CONS (DUMB-CONVERT-TYPE-SET-TO-TYPE-RESTRICTION-TERM
                            (CAR (TYPE-PRESCRIPTION NAME))
                            (CONS NAME ARGS))
                           (ITERATE FOR FLG IN (CDR (TYPE-PRESCRIPTION NAME))
                                    AS I FROM 0 WHEN FLG
                                    COLLECT (LIST (QUOTE EQUAL)
                                                  (CONS NAME ARGS)
                                                  (NTH I ARGS)))))
               (COND ((EQ (CAR TEMP-TEMP) 'F)
                      (SETQ TEMP-TEMP (CDR TEMP-TEMP))))
               (SETQ CONCL (COND ((NULL TEMP-TEMP) 'F)
                                 ((NULL (CDR TEMP-TEMP))
                                  (CAR TEMP-TEMP))
                                 (T (CONS (QUOTE OR)
                                          TEMP-TEMP))))
               (PRINEVAL (PQUOTE (PROGN (? (|Note| |that|)
                                           (|Observe| |that|)
                                           (|From| |the| |definition| |we|
                                                   |can| |conclude| |that|))
                                        (!PPR CONCL NIL)
                                        |is| |a| |theorem| |.|))
                         `((CONCL . ,CONCL))
                         0 PROVE-FILE)))
        (SETQ IO-TIME (- (TIME-IN-60THS)
                         TIME))
        (RETURN NIL)))

(DEFUN !TERM (TERM PUNCT)
  (!PPR (UNTRANSLATE TERM) PUNCT))

(DEFUN !TERM-LIST (TERM-LST PUNCT)
  (!PPR-LIST (ITERATE FOR X IN TERM-LST
                      COLLECT (UNTRANSLATE X))
             PUNCT))

(DEFUN TH-IFY (N)
  (COND ((NOT (NUMBERP N)) N)
        ((INT= N 1) (QUOTE |first|))
        ((INT= N 2) (QUOTE |second|))
        ((INT= N 3) (QUOTE |third|))
        ((INT= N 4) (QUOTE |fourth|))
        ((INT= N 5) (QUOTE |fifth|))
        ((INT= N 6) (QUOTE |sixth|))
        ((INT= N 7) (QUOTE |seventh|))
        ((INT= N 8) (QUOTE |eighth|))
        ((INT= N 9) (QUOTE |ninth|))
        ((INT= N 10) (QUOTE |tenth|))
        ((INT= N 11) (QUOTE |11th|))
        ((INT= N 12) (QUOTE |12th|))
        ((INT= N 13) (QUOTE |13th|))
        (T (PACK (LIST N
                       (LET ((TEMP (OUR-REMAINDER N 10)))
                         (COND ((INT= TEMP 1) (QUOTE |st|))
                               ((INT= TEMP 2) (QUOTE |nd|))
                               ((INT= TEMP 3) (QUOTE |rd|))
                               (T (QUOTE |th|)))))))))

(DEFUN UN-NOTICE-CLAUSE (CL)
  (SETQ TEMP-TEMP (ASSOC-EQ CL CLAUSE-ALIST))
  (COND ((NULL TEMP-TEMP)
         (ER HARD NIL UN-NOTICE-CLAUSE |was| |called| |on| |a| |clause| |not|
             |in| CLAUSE-ALIST EXCL)))
  (SETQ CLAUSE-ALIST (DELETE TEMP-TEMP CLAUSE-ALIST))
  TEMP-TEMP)

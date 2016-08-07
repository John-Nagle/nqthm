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

(DEFUN ELIMINABLE-VAR-CANDS (CL HIST)
  HIST
  (SET-DIFF (ALL-VARS-LST CL) ELIM-VARIABLE-NAMES1))

(DEFUN ELIMINABLEP (SET)
  (OR (ITERATE FOR LIT IN SET ALWAYS (PRIMITIVEP LIT))
      (AND (INT= (LENGTH SET) 1)
           (OR (AND (ITERATE FOR ARG IN (SARGS (CAR SET))
                             ALWAYS (VARIABLEP ARG))
                    (NO-DUPLICATESP (SARGS (CAR SET))))
               (AND (EQ (QUOTE NOT) (FN-SYMB (CAR SET)))
                    (ITERATE FOR ARG IN (SARGS (ARGN (CAR SET) 1))
                             ALWAYS (VARIABLEP ARG))
                    (NO-DUPLICATESP (SARGS (ARGN (CAR SET) 1))))))))

(DEFUN ELIMINATE-DESTRUCTORS-CANDIDATEP (TERM)

;   Recognizes candidates for destructor elimination.  It is assumed the input
;   term is NVARIABLEP and not QUOTEP.  To be a candidate the term must have an
;   enabled destructor elim lemma.  Furthermore, the crucial argument position
;   of the term must be occupied by a variable or must itself be a candidate
;   for elimination.  Finally, if occupied by a variable, that variable must
;   occur nowhere else in the arguments.  Note that if the crucial arg is an
;   eliminable term then the process of eliminating it will introduce a
;   suitable distinct var.  The answer returned is either NIL or else is the
;   innermost term to be eliminated -- possibly TERM itself.

  (PROG (LEMMA VAR)
        (SETQ LEMMA (GET (FFN-SYMB TERM) (QUOTE ELIMINATE-DESTRUCTORS-SEQ)))
        (COND ((OR (NULL LEMMA) (DISABLEDP (ACCESS REWRITE-RULE NAME LEMMA)))
               (RETURN NIL)))

;   We now identify the crucial arg.

        (SETQ VAR
              (ITERATE FOR ARG IN (FARGS TERM)
                       AS V IN
                       (FARGS (CAR (GET
                                    (FFN-SYMB TERM)
                                    (QUOTE ELIMINATE-DESTRUCTORS-DESTS))))
                       WHEN (EQ V (FARGN (ACCESS REWRITE-RULE CONCL LEMMA)
                                         2))
                       DO (RETURN ARG)))
        (RETURN (COND ((VARIABLEP VAR)

;   If it is a variable, we make sure it occurs nowhere else.

                       (COND
                        ((ITERATE
                          FOR ARG IN (FARGS TERM) AS V
                          IN (FARGS
                              (CAR (GET
                                    (FFN-SYMB TERM)
                                    (QUOTE ELIMINATE-DESTRUCTORS-DESTS))))
                          UNLESS (EQ V
                                     (FARGN
                                      (ACCESS REWRITE-RULE CONCL LEMMA) 2))
                          NEVER (OCCUR VAR ARG))
                         TERM)
                        (T NIL)))
                      (T (ELIMINATE-DESTRUCTORS-CANDIDATEP VAR))))))

(DEFUN ELIMINATE-DESTRUCTORS-CANDIDATES (CL)

;   Returns a list of pockets.  The CAR of each pocket is an eliminable
;   destructor term.  The CDR of each pocket is a list of all destructor terms
;   that will in turn be eliminated as a result of eliminating the CAR.

  (LET (ANS)
    (ITERATE FOR LIT IN CL DO (ELIMINATE-DESTRUCTORS-CANDIDATES1 LIT))
    (MERGE-DESTRUCTOR-CANDIDATES ANS)))

(DEFUN ELIMINATE-DESTRUCTORS-CANDIDATES1 (TERM)

;   This function adds some lists to ANS.  Each list has two elements.  The
;   first is a term that can be eliminated.  The second is a term containing
;   the first which will be eliminated in the same round as the first is
;   eliminated.

  (COND ((OR (VARIABLEP TERM) (FQUOTEP TERM)) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM)
                    DO (ELIMINATE-DESTRUCTORS-CANDIDATES1 ARG))
           (COND ((SETQ TEMP-TEMP (ELIMINATE-DESTRUCTORS-CANDIDATEP TERM))
                  (SETQ ANS (ADD-TO-SET (LIST TEMP-TEMP TERM) ANS)))))))

(DEFUN ELIMINATE-DESTRUCTORS-CLAUSE (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET (ELIMINABLES NEW-CL TO-DO CANDS REWRITE-RULE HYPS LHS RHS
                    DESTS ALIST INST-DESTS INST-RHS INST-LHS INST-HYPS)

;   TO-DO is a list that controls the elimination.  The invariant maintained is
;   that the all the clauses in PROCESS-CLAUSES and all the clauses in TO-DO
;   are theorems then so is the initial CL.  When a clause is removed from
;   TO-DO either it is added to PROCESS-CLAUSES or else an elimination is
;   performed on it and the resulting cases are all added to TO-DO for any
;   additional elims required on the new variables introduced.

;   TO-DO is a list of pockets.  Each pocket contains a clause, the list of all
;   variables in the clause not introduced by an elim, and some candidate
;   destructor pockets.  The candidate destructor pockets each contain in their
;   CAR a term that might be eliminated and in their CDR all of the terms that
;   could recursively be eliminated should the CAR be eliminated.  These
;   pockets are ordered from most desirable elim to least desirable elim.  At
;   the moment the ordering is determined by the sum of the level numbers of
;   the terms in the CDRs.

    (SETQ TO-DO
          (LIST (LIST CL (ELIMINABLE-VAR-CANDS CL HIST)
                      (SORT-DESTRUCTOR-CANDIDATES
                       (ELIMINATE-DESTRUCTORS-CANDIDATES CL)))))
    (SETQ PROCESS-CLAUSES NIL)
    (SETQ PROCESS-HIST NIL)
    (ITERATE
     WHILE TO-DO DO
     (PROGN
       (SETQ CL (CAAR TO-DO))
       (SETQ ELIMINABLES (CADAR TO-DO))
       (SETQ CANDS (CADDAR TO-DO))
       (SETQ TO-DO (CDR TO-DO))
       (COND
        ((OR (NULL ELIMINABLES) (NULL CANDS))
         (SETQ PROCESS-CLAUSES (CONS CL PROCESS-CLAUSES)))
        ((ITERATE FOR CAND-TAIL ON CANDS WITH CAND THEREIS

;   CAND is the candidate destructor term to be eliminated.
                  (PROGN
                    (SETQ CAND (CAR (CAR CAND-TAIL)))
                    (SETQ REWRITE-RULE
                          (GET (FFN-SYMB CAND)
                               (QUOTE ELIMINATE-DESTRUCTORS-SEQ)))

;   We know this rule is not disabled because ELIMINATE-DESTRUCTORS-CANDIDATES
;   checks DISABLED-LEMMAS before saying a term is a candidate.

                    (SETQ HYPS (ACCESS REWRITE-RULE HYPS REWRITE-RULE))
                    (SETQ LHS (FARGN (ACCESS REWRITE-RULE CONCL REWRITE-RULE)
                                     1))
                    (SETQ RHS (FARGN (ACCESS REWRITE-RULE CONCL REWRITE-RULE)
                                     2))
                    (SETQ DESTS
                          (GET (FFN-SYMB CAND)
                               (QUOTE ELIMINATE-DESTRUCTORS-DESTS)))
                    (SETQ ALIST (ITERATE FOR VAR IN (FARGS (CAR DESTS))
                                         AS VAL IN (FARGS CAND)
                                         COLLECT (CONS VAR VAL)))
                    (SETQ INST-RHS (SUBLIS-VAR ALIST RHS))
                    (COND
                     ((AND (MEMBER-EQ INST-RHS ELIMINABLES)
                           (ITERATE FOR HYP IN HYPS
                                    NEVER (MEMBER-EQUAL
                                           (SUBLIS-VAR ALIST HYP)
                                           CL)))
                      (SETQ INST-DESTS (SUBLIS-VAR-LST ALIST DESTS))
                      (SETQ INST-HYPS (SUBLIS-VAR-LST ALIST HYPS))
                      (SETQ INST-LHS (SUBLIS-VAR ALIST LHS))
                      (SETQ
                       TO-DO
                       (APPEND
                        (ITERATE FOR HYP IN INST-HYPS
                                 UNLESS (EQUAL TRUE-CLAUSE
                                               (SETQ NEW-CL
                                                     (ADD-LITERAL HYP CL NIL)))
                                 COLLECT
                                 (LIST
                                  NEW-CL ELIMINABLES
                                  (COND
                                   (PROCESS-HIST
                                    (ITERATE FOR POCKET IN (CDR CAND-TAIL)
                                             UNLESS (MEMBER-EQUAL
                                                     (CAR POCKET)
                                                     INST-DESTS)
                                             COLLECT POCKET))
                                   (T NIL))))
                        TO-DO))
                      (SETQ NEW-CL
                            (ELIMINATE-DESTRUCTORS-CLAUSE1 CL INST-HYPS
                                                           INST-LHS
                                                           INST-RHS
                                                           INST-DESTS))
                      (COND ((NOT (EQUAL TRUE-CLAUSE NEW-CL))
                             (SETQ TO-DO
                                   (CONS
                                    (LIST
                                     NEW-CL
                                     (UNION-EQ GENERALIZING-SKOS
                                               (REMOVE INST-RHS ELIMINABLES
                                                       :TEST #'EQUAL))
                                     (SORT-DESTRUCTOR-CANDIDATES
                                      (MERGE-DESTRUCTOR-CANDIDATES
                                       (UNION-EQUAL
                                        (COND (PROCESS-HIST
                                               (ITERATE FOR POCKET
                                                        IN (CDR CAND-TAIL)
                                                        WHEN
                                                        (OCCUR-LST (CAR POCKET)
                                                                   NEW-CL)
                                                        COLLECT POCKET))
                                              (T NIL))
                                        (ITERATE
                                         FOR POCKET IN
                                         (ELIMINATE-DESTRUCTORS-CANDIDATES
                                          NEW-CL)
                                         WHEN
                                         (ITERATE FOR VAR
                                                  IN (FARGS (CAR POCKET))
                                                  THEREIS
                                                  (MEMBER-EQ
                                                   VAR
                                                   GENERALIZING-SKOS))
                                         COLLECT POCKET)))))
                                    TO-DO))))
                      (SETQ PROCESS-HIST
                            (CONS (LIST (ACCESS REWRITE-RULE NAME REWRITE-RULE)
                                        INST-DESTS OBVIOUS-RESTRICTIONS
                                        GENERALIZE-LEMMA-NAMES INST-RHS
                                        (SUB-PAIR-EXPR INST-DESTS
                                                       GENERALIZING-SKOS
                                                       INST-LHS))
                                  PROCESS-HIST))
                      T)
                     (T NIL)))))
        (T (SETQ PROCESS-CLAUSES (CONS CL PROCESS-CLAUSES))))))
    (ITERATE FOR PAIR IN PROCESS-HIST
             DO (SETQ ALL-LEMMAS-USED
                      (UNION-EQUAL (CADDDR PAIR)
                                   (ADD-TO-SET (CAR PAIR)
                                               ALL-LEMMAS-USED))))
    (SETQ PROCESS-CLAUSES (SCRUNCH-CLAUSE-SET PROCESS-CLAUSES))
    (NOT (NULL PROCESS-HIST))))

(DEFUN ELIMINATE-DESTRUCTORS-CLAUSE1 (CL HYPS LHS RHS DESTS)
  (LET (GEN-CL GEN-LHS CL1)
    (SETQ CL1 CL)

;   We preserve the order of the hyps just for the hell of it.

    (ITERATE FOR HYP IN (REVERSE HYPS)
             DO (SETQ CL1 (ADD-LITERAL (NEGATE-LIT HYP) CL1 NIL)))
    (SETQ GEN-CL (GENERALIZE1 CL1 DESTS ELIM-VARIABLE-NAMES1))
    (SETQ GEN-LHS (SUB-PAIR-EXPR DESTS GENERALIZING-SKOS LHS))
    (SUBST-VAR-LST GEN-LHS RHS GEN-CL)))

(DEFUN ELIMINATE-DESTRUCTORS-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE ELIMINATE-DESTRUCTORS-CLAUSE)
           CL HIST (QUOTE SIMPLIFY-SENT)
           (QUOTE FERTILIZE-SENT)))

(DEFUN ELIMINATE-IRRELEVANCE-CLAUSE (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  HIST
  (PROG (PARTITION ELIMINABLES)
        (COND ((NOT (ASSOC-EQ (QUOTE BEING-PROVED) STACK)) (RETURN NIL)))
        (SETQ PARTITION
              (TRANSITIVE-CLOSURE
               (ITERATE FOR LIT IN CL
                        COLLECT (CONS (ALL-VARS LIT) (LIST LIT)))
               (FUNCTION (LAMBDA (X Y)
                           (COND ((INTERSECTP (CAR X) (CAR Y))
                                  (CONS (UNION-EQUAL (CAR X) (CAR Y))
                                        (UNION-EQUAL (CDR X) (CDR Y))))
                                 (T NIL))))))
        (SETQ ELIMINABLES (ITERATE FOR PAIR IN PARTITION
                                   WHEN (ELIMINABLEP (CDR PAIR))
                                   NCONC (CDR PAIR)))
        (COND ((NULL ELIMINABLES) (RETURN NIL))
              (T (SETQ PROCESS-CLAUSES
                       (LIST (ITERATE FOR LIT IN CL
                                      UNLESS (MEMBER-EQ LIT ELIMINABLES)
                                      COLLECT LIT)))
                 (SETQ PROCESS-HIST NIL)
                 (RETURN T)))))

(DEFUN ELIMINATE-IRRELEVANCE-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE ELIMINATE-IRRELEVANCE-CLAUSE)
           CL HIST (QUOTE STORE-SENT)
           (QUOTE STORE-SENT)))

(DEFUN ELIMINATE-SOME-EVAL$S (TERM)
  
;  Returns a term t such that if (V&C T t standard) returns non-F
;  then (V&C T 'TERM standard) returns non-F and has the same CAR.
;  This function is used by the compiler to eliminate unnecessary
;  calls of EVAL$.  
  
  (LET (FLG BODY ALIST)
    (COND ((EQ *1*THM-MODE$ (QUOTE THM)) TERM)
          ((OR (VARIABLEP TERM)
               (FQUOTEP TERM))
           TERM)
          ((AND (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                   (LIST (QUOTE QUOTE) BODY)
                                   ALIST))
                (NOT (EQ FLG (QUOTE LIST)))
                (TERMP BODY)
                (NOT (ERRATICP BODY))
                (SEMI-CONCRETE-ALISTP ALIST)
                (ITERATE FOR PAIR IN
                         (SETQ ALIST
                               (MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST
                                ALIST))
                         ALWAYS
                         (TAMEP (CDR PAIR))))
           (ELIMINATE-SOME-EVAL$S (SUBLIS-VAR
                                   (APPEND ALIST
                                           (ITERATE FOR VAR
                                                    IN (ALL-VARS BODY)
                                                    COLLECT (CONS VAR ZERO)))
                                   BODY)))
          (T (CONS-TERM (FFN-SYMB TERM)
                        (ITERATE FOR ARG IN (FARGS TERM) COLLECT
                                 (ELIMINATE-SOME-EVAL$S ARG)))))))

(DEFUN EQUATIONAL-PAIR-FOR (WINNING-PAIR POLY)
  (CONS (CAR WINNING-PAIR)
        (CONS-PLUS (LIST (QUOTE QUOTE)
                         (ABS (ACCESS POLY CONSTANT POLY)))
                   (BUILD-SUM WINNING-PAIR (ACCESS POLY ALIST POLY)))))

(DEFUN ERRATICP (TERM)

;   A term t is "erratic" if the interpretation of its quotation
;   terminates but computes something other than t.
;   More precisely, t is erratic if it is not a theorem that:

;      (V&C$ T 't a) /= F
;    ->
;      (CAR (V&C$ T 't a)) = t/c(a),

;   where a is semi-concrete and c(a) is its completion.

;   This predicate returns T if TERM is or may be erratic and NIL
;   otherwise.

;   The erratic property is necessary because of a subtle bug in the theorem
;   prover as it existed before the erratic property was identified.  We had
;   made an implicit assumption that there was a correspondence between
;   the value of a function and its behavior under V&C$ and/or V&C-APPLY$.
;   I.e., that no term was erratic.

;   Of particular interest in thinking about the erratic property are those
;   declared function symbols for which axioms have been added
;   specifying the values of SUBRP and APPLY-SUBR or BODY.  Suppose
;   we introduce a new declared function of no args:

;   (DCL ERRATIC NIL)

;   and add three axioms:

;   (ERRATIC) = 1
;   (SUBRP 'ERRATIC) = F, and
;   (BODY 'ERRATIC) = '(QUOTE 2).

;   There is nothing inconsistent about this; nowhere in our axioms
;   have we said that the value of a function must be consistent with
;   that computed by its BODY.  It just happens that for (almost) all
;   the fns we introduce with BOOT-STRAP, ADD-SHELL, and DEFN that is
;   the case.  WARNING:  If we ever attempt to extend the theorem-prover
;   with set theory and to give a body to a construct such as SETOF,
;   the BODY would be inevitably erratic.

;   Before we introduced the notion of ERRATICP we had two flaws
;   in the code that were related to this.  First, via
;   ELIMINATE-SOME-EVAL$S, we compiled (EVAL$ T 'term a) to term/a for
;   all terms.  But for '(ERRATIC) the EVAL$ expression is provably 2
;   while (ERRATIC) is provably 1.  In fact, both expressions execute to
;   (NOT REDUCIBLE) but only because the *1*functions do not know
;   about user-supplied axioms.  It is dangerous to make the soundness
;   of the system rest upon the inadequacy of our implementation!

;   The second flaw was in REWRITE-CAR-V&C$, where we simplified (CAR
;   (V&C$ T '(ERRATIC) NIL)) to (IF (V&C$ T '(ERRATIC) NIL) (ERRATIC)
;   0).  That is unsound.  The first expression is proveably 2.  The
;   second is provably 1.

;   Similar problems can arise under the axioms:

;   (SUBRP 'ERRATIC) = T
;   (APPLY-SUBR 'ERRATIC NIL) = 2
;   (ERRATIC) = 1.

;   Prior to the identification of the erratic property we used
;   REWRITE-APPLY-SUBR to simplify (APPLY-SUBR 'ERRATIC NIL) to (ERRATIC).
;   This could not be used to get an inconsistency because instead of
;   asking whether (SUBRP 'ERRATIC) was T we only asked whether (*1**SUBRP
;   'ERRATIC) was *1*T.  But again, had we made *1**SUBRP smarter, we
;   would have had an unsoundness.  (In effect, the SUBRP property of
;   a symbol was overloaded to mean the symbol "has the SUBRP axiom"
;   of the manual, not just that the value of SUBRP is T.  But there
;   is no requirement that (APPLY-SUBR 'fn args) = (fn arg1 ...)
;   whenever (SUBRP 'fn) = T, it just happens that way for the
;   primitive subrs.)

;   An alternative way to think about the erratic property for a function
;   symbol fn is that the axiomatization of SUBRP, APPLY-SUBR and BODY
;   on 'fn are at variance with the axiomatization of (fn ...).  Intuitively,
;   V&C$ computes whatever the meta-axioms about 'fn tell it and
;   if they are consistent with (fn ...) then V&C$ computes (fn ...) if
;   it terminates.  This consistency between the meta-axioms and the
;   values certainly holds for all of the primitive functions in the logic
;   including V&C$ and friends!  It also holds for all defined and shell
;   functions.  The only occasion on which the user can add consistent
;   meta-axioms at variance with the values is for DCLd functions.

;   We compute ERRATICP as follows.  Variables and quoted
;   expressions are not erratic.  A call is erratic if either the
;   function symbol is erratic or one of the args is erratic.

;   A function is erratic as follows: All user DCLd functions are erratic.
;   No shell fn or boot-strap fn is erratic.  A defined function is
;   erratic if its body is erratic under the assumption that its name
;   is not erratic.

;   Thus, the only functions that are erratic are those that are DCLd
;   or those defined functions whose bodies involve erratic functions.
;   In particular, partial functions employing (non-erratic) defined
;   functions such as (RUSSELL)=(EVAL$ T '(NOT (RUSSELL)) NIL), or the
;   non-terminating LEN are non-erratic.

;   It may be surprising that V&C$ is not erratic.  At first sight one
;   expects (V&C$ flg x va) to be erratic if x is something weird like
;   not a quotation or the quotation of an erratic term.  Now, like
;   all terms, (V&C$ flg x va) is erratic if any arg is erratic.  But
;   let's suppose flg, x and va are not erratic.  But suppose x is the
;   quotation of an erratic term.  In particular, ignoring the first
;   and third args of V&C$, suppose (V&C$ '(V&C$ (QUOTE x))) is non-F.
;   Is (CAR (V&C$ '(V&C$ (QUOTE x)))) = (V&C$ (QUOTE x))?  Yes.  No
;   matter how bad x is, V&C$ just goes through the meta-axioms on
;   both the left- and right-hand sides.  Neither side calls a DCL'd
;   function because V&C$ never calls a DCLd function.

;   The whole idea of ERRATICP is irrelevant to THM mode.  We
;   therefore do not bother to store values for the ERRATICP
;   property in THM mode and it is thus a mistake if this function is
;   ever called while in THM mode.  To insure that ERRATICP is not
;   used without reconsideration of this decision, we check that we
;   are in NQTHM mode whenever ERRATICP is used.

  (CHK-NQTHM-MODE$ 'ERRATICP)
  (ERRATICP1 TERM))

(DEFUN ERRATICP1 (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        ((GET (FFN-SYMB TERM) 'ERRATICP) T)
        (T (ITERATE FOR ARG IN (FARGS TERM) THEREIS (ERRATICP1 ARG)))))

(DEFUN ERROR1 (SENTENCE ALIST HARDNESS)
  (COND ((AND PETITIO-PRINCIPII (EQ HARDNESS 'WARNING))
         (RETURN-FROM ERROR1 T)))
  (SETQ ALIST `((SENTENCE . ,SENTENCE)
                (HARDNESS . ,HARDNESS)
                ,@ ALIST))
  (COND ((AND (NOT (EQ HARDNESS 'WARNING))
              (EQ *READTABLE* (NQTHM-READTABLE)))
         (FORMAT *STANDARD-OUTPUT* "~%Resetting *READTABLE*.~%")
         (SETQ *READTABLE* (COPY-READTABLE NIL))))
  (COND ((NULL HARDNESS) (SETQ HARDNESS (QUOTE HARD))))

;   Error messages may be printed as many as three different times.
;   We print to the PROVE-FILE, to the ERR-FILE, and to NIL, but never
;   to the same place twice.

  (SETQ LAST-PRINEVAL-CHAR NIL)
  (PRINEVAL (PQUOTE (PROGN CR (COND ((EQ HARDNESS (QUOTE WARNING)) WARNING)
                                    ((EQ HARDNESS (QUOTE HARD)) FATAL ERROR)
                                    (T ERROR))
                           |:| (@ SENTENCE) CR CR))
            ALIST 0 PROVE-FILE)
  (COND ((NOT (EQ ERR-FILE PROVE-FILE))
         (SETQ LAST-PRINEVAL-CHAR NIL)
         (PRINEVAL (PQUOTE (PROGN CR (COND ((EQ HARDNESS (QUOTE WARNING))
                                            WARNING)
                                           ((EQ HARDNESS (QUOTE HARD))
                                            FATAL ERROR)
                                           (T ERROR)) |:| (@ SENTENCE) CR CR))
                   ALIST 0 ERR-FILE)))
  (COND ((AND (NOT (EQ ERR-FILE NIL))
              (NOT (EQ PROVE-FILE NIL))
              (NOT (EQ HARDNESS (QUOTE WARNING))))
         (SETQ LAST-PRINEVAL-CHAR NIL)
         (PRINEVAL (PQUOTE (PROGN CR (COND ((EQ HARDNESS (QUOTE WARNING))
                                            WARNING)
                                           ((EQ HARDNESS (QUOTE HARD))
                                            FATAL ERROR)
                                           (T ERROR)) |:| (@ SENTENCE) CR CR))
                   ALIST 0 NIL)))

;  If we are under PROVEALL then we must also create the .fail file and
;  write into it (and the .err file) the event that caused the failure.

    (COND ((AND PROVEALL-FLG
                (NOT (EQ HARDNESS (QUOTE WARNING))))
           (COND ((NOT (AND (EQ HARDNESS (QUOTE SOFT))
                            ERROR1-SET-FLG))
                  (PRINEVAL
                   (PQUOTE (PROGN CR CR
                                  |The| PROVEALL |named| (!PPR FILENAME NIL)
                                  |failed| |when| |executing| |the| |command|
                                  (!PPR EVENT (QUOTE |.|)) CR CR))
                   (LIST (CONS (QUOTE FILENAME) PROVEALL-FILENAME)
                         (CONS (QUOTE EVENT) (CAR UNDONE-EVENTS)))
                   0 ERR-FILE)
                  (IPRINC FAILURE-MSG ERR-FILE)
                  (ITERPRI ERR-FILE)))
           (WITH-OPEN-FILE (FILE (EXTEND-FILE-NAME PROVEALL-FILENAME
                                                   FILE-EXTENSION-FAIL)
                                 :DIRECTION :OUTPUT
                                 :IF-EXISTS :RENAME-AND-DELETE)
             (PRINEVAL
              (PQUOTE (PROGN CR CR
                             |The| PROVEALL |named| (!PPR FILENAME NIL)
                             |failed| |when| |executing| |the| |command|
                             (!PPR EVENT (QUOTE |.|)) CR CR))
              (LIST (CONS (QUOTE FILENAME) PROVEALL-FILENAME)
                    (CONS (QUOTE EVENT) (CAR UNDONE-EVENTS)))
              0 FILE))))


;  The disposition of an error is as follows:  WARNINGs do nothing;
;  soft ERRORs return to the most recent ERROR1-SET, if any, and otherwise
;  abort; hard (FATAL) ERRORs abort.

  (COND ((EQ HARDNESS (QUOTE WARNING)) NIL)
        ((AND (EQ HARDNESS (QUOTE SOFT))
              ERROR1-SET-FLG)
         (THROW (QUOTE ERROR1-SET) NIL))
        (T 

;  If we are about to abort, close the PROVE-FILE and
;  ERR-FILE and redirect future output to the terminal.
;  It will be very rare that this occurs -- the user will
;  have had to set the files up himself and then called
;  an event command without using DO-EVENTS.

         (CLOSE-THM-FILES)
         (ERROR ""))))

(DEFUN EVENT1-OCCURRED-BEFORE-EVENT2 (EVENT1 EVENT2 EVENT-LST)
  (COND ((MEMBER-EQ EVENT1 (CDR (MEMBER-EQ EVENT2 EVENT-LST))) T)
        (T NIL)))

(DEFUN EVENT-THAT-PROVED-CONSTRAINT
  (NAME LOCAL-FS AVAILABLE-EVENT-FS-PAIRS-ALIST)

; Here AVAILABLE-EVENT-FS-PAIRS-ALIST is an alist with entries of
; the form (name (ev1 . fs1) (ev2 . fs2) ... (ev-k . fs-k)).  This
; function returns the name of the FUNCTIONALLY-INSTANTIATE event
; that proved the result of functionally-instantiating the event
; called name with functional substitution local-fs.

  (ITERATE FOR NAME-EVENT-FS-LIST IN AVAILABLE-EVENT-FS-PAIRS-ALIST
           WHEN
           (ITERATE FOR PAIR IN (CDR NAME-EVENT-FS-LIST)
                    THEREIS (AND (EQ (CAR PAIR) NAME)
                                 (EQUAL (CDR PAIR) LOCAL-FS)))
           DO (RETURN (CAR NAME-EVENT-FS-LIST))))

(DEFUN EVENTS-SINCE (EVENT)
  (COND ((MEMBER-EQ EVENT CHRONOLOGY)
         (CONS (GET EVENT (QUOTE EVENT))
               (NREVERSE (ITERATE FOR E IN CHRONOLOGY UNTIL (EQ E EVENT)
                                  COLLECT (GET E (QUOTE EVENT))))))))

(DEFUN EVG (Y)
  (COND
   ((ATOM Y)
    (COND ((INTEGERP Y)
           (COND ((>= Y 0) TYPE-SET-NUMBERS)
                 (T TYPE-SET-NEGATIVES)))
          ((EQ Y *1*T) TYPE-SET-TRUE)
          ((EQ Y *1*F) TYPE-SET-FALSE)
          ((ILLEGAL-NAME Y) NIL)
          (T TYPE-SET-LITATOMS)))
   ((EQ (CAR Y) *1*SHELL-QUOTE-MARK)
    (COND
     ((AND (CONSP (CDR Y))
           (EQ (CDR (OUR-LAST Y)) NIL)
           (SYMBOLP (CADR Y))
           (NOT (NULL (ARITY (CADR Y))))
           (INT= (LENGTH (CDDR Y)) (ARITY (CADR Y)))
           (OR (MEMBER-EQ (CADR Y) *1*BTM-OBJECTS)
               (AND (ASSOC-EQ (CADR Y) SHELL-ALIST)
                    (ITERATE FOR RESTRICTION
                             IN (GET (CADR Y) (QUOTE TYPE-RESTRICTIONS))
                             AS ARG IN (CDDR Y)
                             ALWAYS (AND (SETQ TEMP-TEMP (EVG ARG))
                                         (TSLOGSUBSETP
                                          TEMP-TEMP
                                          (ACCESS TYPE-RESTRICTION
                                                  TYPE-SET
                                                  RESTRICTION))))))
           (COND ((EQ (QUOTE PACK) (CADR Y))
                  (NOT (AND (LEGAL-CHAR-CODE-SEQ (CADDR Y))
                            (EQUAL 0 (CDR (OUR-LAST (CADDR Y)))))))
                 ((EQ (QUOTE MINUS) (CADR Y))
                  (EQUAL (CADDR Y) 0))
                 (T (NOT (MEMBER-EQ (CADR Y) (QUOTE (ADD1 ZERO CONS)))))))
      (CAR (TYPE-PRESCRIPTION (CADR Y))))
     (T NIL)))
   ((AND (EVG (CAR Y)) (EVG (CDR Y))) TYPE-SET-CONS)
   (T NIL)))

(DEFUN EVG-OCCUR-LEGAL-CHAR-CODE-SEQ (L EVG)
  (COND ((ATOM EVG)
         (COND ((EQ EVG *1*T) NIL)
               ((EQ EVG *1*F) NIL)
               ((INTEGERP EVG) NIL)
               ((< (LENGTH (SYMBOL-NAME EVG)) (LENGTH-TO-ATOM L)) NIL)
               (T (ITERATE FOR TAIL ON L UNTIL (ATOM TAIL)
                           AS J FROM (1+
                                      (- (LENGTH (SYMBOL-NAME EVG))
                                         (LENGTH-TO-ATOM L)))
                           ALWAYS (INT= (CAR TAIL) (OUR-GETCHARN EVG J))))))
        ((EQ (CAR EVG)
             *1*SHELL-QUOTE-MARK)
         (ITERATE FOR ARG IN (CDDR EVG) THEREIS (EVG-OCCUR-LEGAL-CHAR-CODE-SEQ
                                                 L ARG)))
        ((EQUAL L EVG) T)
        (T (OR (EVG-OCCUR-LEGAL-CHAR-CODE-SEQ L (CAR EVG))
               (EVG-OCCUR-LEGAL-CHAR-CODE-SEQ L (CDR EVG))))))

(DEFUN EVG-OCCUR-NUMBER (N EVG)
  (COND ((ATOM EVG)
         (COND ((EQ EVG *1*T) NIL)
               ((EQ EVG *1*F) NIL)
               ((INTEGERP EVG)
                (COND ((< N 0) (EQUAL N EVG))
                      (T (<= N (ABS EVG)))))
               ((< N 0) NIL)
               (T (ITERATE FOR I FROM 1 TO (LENGTH (SYMBOL-NAME EVG))
                           THEREIS (<= N (OUR-GETCHARN EVG I))))))
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK)
         (ITERATE FOR ARG IN (CDDR EVG) THEREIS (EVG-OCCUR-NUMBER N ARG)))
        (T (OR (EVG-OCCUR-NUMBER N (CAR EVG))
               (EVG-OCCUR-NUMBER N (CDR EVG))))))

(DEFUN EVG-OCCUR-OTHER (X EVG)

;   X must be an evg other than a INTEGERP or a LEGAL-CHAR-CODE-SEQ
;   with 0 final CDR.

  (COND ((EQUAL X EVG) T)
        ((ATOM EVG) NIL)
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK)
         (ITERATE FOR ARG IN (CDDR EVG) THEREIS (EVG-OCCUR-OTHER X ARG)))
        (T (OR (EVG-OCCUR-OTHER X (CAR EVG))
               (EVG-OCCUR-OTHER X (CDR EVG))))))

;   
;   Was EXECUTE - renamed due to name clash with EXT package.

(DEFUN EXECUTE-PROCESS (PROCESS CL HIST NORMAL-EXIT NO-CHANGE-EXIT)
  (LET (NEW-HIST)
    (COND ((FUNCALL PROCESS CL HIST)
           (SETQ NEW-HIST
                 (ADD-PROCESS-HIST PROCESS CL HIST
                                   PROCESS-CLAUSES PROCESS-HIST))
           (ITERATE FOR CL1 IN PROCESS-CLAUSES
                    DO (FUNCALL NORMAL-EXIT CL1 NEW-HIST)))
          (T (FUNCALL NO-CHANGE-EXIT CL HIST)))))

(DEFUN EXPAND-ABBREVIATIONS (TERM ALIST)

;   Apply all unconditional rewrite rules and nonrec defns that are
;   ABBREVIATIONPs.  Adds to ABBREVIATIONS-USED the names of the lemmas and fns
;   applied.

  (LET (TEMP LEMMA RHS LHS)
    (COND ((VARIABLEP TERM)
           (COND ((SETQ TEMP (ASSOC-EQ TERM ALIST)) (CDR TEMP))
                 (T TERM)))
          ((FQUOTEP TERM) TERM)
          ((MEMBER-EQ (FFN-SYMB TERM) FNS-TO-BE-IGNORED-BY-REWRITE)
           (CONS-TERM
            (FFN-SYMB TERM)
            (ITERATE FOR ARG IN (FARGS TERM)
                     COLLECT (EXPAND-ABBREVIATIONS ARG ALIST))))
          ((AND (SETQ TEMP (NON-RECURSIVE-DEFNP (FFN-SYMB TERM)))
                (ABBREVIATIONP (CADR TEMP) (CADDR TEMP)))
           (SETQ ABBREVIATIONS-USED (ADD-TO-SET (FFN-SYMB TERM)
                                                ABBREVIATIONS-USED))
           (EXPAND-ABBREVIATIONS
            (CADDR TEMP)
            (ITERATE FOR V IN (CADR TEMP) AS ARG IN (FARGS TERM)
                     COLLECT (CONS V (EXPAND-ABBREVIATIONS ARG ALIST)))))
          (T (SETQ TERM (CONS-TERM
                         (FFN-SYMB TERM)
                         (ITERATE FOR ARG IN (FARGS TERM)
                                  COLLECT (EXPAND-ABBREVIATIONS ARG ALIST))))
             (COND
              ((FQUOTEP TERM) TERM)
              ((SETQ LEMMA
                     (ITERATE FOR LEMMA IN (GET (FFN-SYMB TERM) (QUOTE LEMMAS))
                              WHEN (AND (NOT (DISABLEDP (ACCESS REWRITE-RULE
                                                                NAME LEMMA)))
                                        (NOT (META-LEMMAP LEMMA))
                                        (NULL (ACCESS REWRITE-RULE HYPS
                                                      LEMMA))
                                        (NULL (ACCESS REWRITE-RULE
                                                      LOOP-STOPPER LEMMA))
                                        (MATCH (ACCESS REWRITE-RULE CONCL
                                                       LEMMA)
                                               (EQUAL LHS RHS))
                                        (ABBREVIATIONP (ALL-VARS-BAG LHS) RHS)
                                        (ONE-WAY-UNIFY LHS TERM))
                              DO (RETURN LEMMA)))
               (SETQ ABBREVIATIONS-USED
                     (ADD-TO-SET (ACCESS REWRITE-RULE NAME LEMMA)
                                 ABBREVIATIONS-USED))
               (EXPAND-ABBREVIATIONS RHS UNIFY-SUBST))
              (T TERM))))))

(DEFUN EXPAND-AND-ORS (TERM BOOL)

;   Expands the top-level fn symbol of TERM provided the expansion produces an
;   AND -- when BOOL is FALSE -- or OR -- when BOOL is TRUE -- or returns NIL
;   if no expansion is appropriate.  Side-effects ABBREVIATIONS-USED.

  (LET (TEMP LEMMA RHS LHS C2 C3)
    (COND ((VARIABLEP TERM) NIL)
          ((FQUOTEP TERM) NIL)
          ((AND (SETQ TEMP (NON-RECURSIVE-DEFNP (FFN-SYMB TERM)))
                (OR (AND (MATCH (CADDR TEMP) (IF & C2 C3))
                         (OR (EQUAL C2 BOOL) (EQUAL C3 BOOL)))
                    (COND ((EQUAL BOOL FALSE)
                           (MATCH (CADDR TEMP) (AND & &)))
                          (T (MATCH (CADDR TEMP) (OR & &))))))
           (SETQ ABBREVIATIONS-USED
                 (ADD-TO-SET (FFN-SYMB TERM) ABBREVIATIONS-USED))
           (EXPAND-ABBREVIATIONS (SUB-PAIR-VAR (CADR TEMP)
                                               (FARGS TERM)
                                               (CADDR TEMP))
                                 NIL))
          ((SETQ LEMMA
                 (ITERATE FOR LEMMA IN (GET (FFN-SYMB TERM) (QUOTE LEMMAS))
                          WHEN (AND (NOT (DISABLEDP (ACCESS REWRITE-RULE
                                                            NAME LEMMA)))
                                    (NOT (META-LEMMAP LEMMA))
                                    (NULL (ACCESS REWRITE-RULE HYPS LEMMA))
                                    (NULL (ACCESS REWRITE-RULE
                                                  LOOP-STOPPER LEMMA))
                                    (MATCH (ACCESS REWRITE-RULE CONCL LEMMA)
                                           (EQUAL LHS RHS))
                                    (MATCH RHS (IF & C2 C3))
                                    (OR (EQUAL C2 BOOL) (EQUAL C3 BOOL))
                                    (ONE-WAY-UNIFY LHS TERM))
                          DO (RETURN LEMMA)))
           (SETQ ABBREVIATIONS-USED
                 (ADD-TO-SET (ACCESS REWRITE-RULE NAME LEMMA)
                             ABBREVIATIONS-USED))
           (EXPAND-ABBREVIATIONS (SUBLIS-VAR UNIFY-SUBST RHS)
                                 NIL))
          (T NIL))))

(DEFUN EXPAND-BOOT-STRAP-NON-REC-FNS (TERM)
  (COND ((VARIABLEP TERM) TERM)
        ((FQUOTEP TERM) TERM)
        ((MEMBER-EQ (FFN-SYMB TERM)
                    (QUOTE (AND OR NOT IMPLIES FIX ZEROP IFF NLISTP)))
         (EXPAND-BOOT-STRAP-NON-REC-FNS
          (SUB-PAIR-VAR (CADR (GET (FFN-SYMB TERM) (QUOTE SDEFN)))
                        (FARGS TERM)
                        (CADDR (GET (FFN-SYMB TERM) (QUOTE SDEFN))))))
        (T (CONS-TERM (FFN-SYMB TERM)
                      (ITERATE FOR ARG IN (FARGS TERM)
                               COLLECT
                               (EXPAND-BOOT-STRAP-NON-REC-FNS ARG))))))

(DEFUN EXPAND-NON-REC-FNS (TERM)
  (COND ((VARIABLEP TERM) TERM)
        ((FQUOTEP TERM) TERM)
        ((NON-RECURSIVE-DEFNP (FFN-SYMB TERM))
         (EXPAND-NON-REC-FNS (SUB-PAIR-VAR (CADR (GET (FFN-SYMB TERM)
                                                      (QUOTE SDEFN)))
                                           (FARGS TERM)
                                           (CADDR (GET (FFN-SYMB TERM)
                                                       (QUOTE SDEFN))))))
        (T (CONS-TERM (FFN-SYMB TERM)
                      (ITERATE FOR ARG IN (FARGS TERM)
                               COLLECT (EXPAND-NON-REC-FNS ARG))))))

(DEFUN EXTEND-ALIST (ALIST1 ALIST2)

;   Extend ALIST2 by adding to it every pair from ALIST1 that does not conflict
;   with an existing pair in ALIST2.

  (APPEND ALIST2 (ITERATE FOR X IN ALIST1
                          UNLESS (ASSOC-EQ (CAR X) ALIST2) COLLECT X)))

#|
;  This function is duplicated in nqthm.lisp, but included here for
;  completeness should nqthm.lisp be flushed.

(DEFUN EXTEND-FILE-NAME (FILE EXTENSION)
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
|#

(DEFUN EXTERNAL-LINEARIZE (TERM FLG)
  (LET (HEURISTIC-TYPE-ALIST LITS-THAT-MAY-BE-ASSUMED-FALSE)
    (LINEARIZE TERM FLG)))

(DEFUN EXTRACT-CONJUNCTS (TERM)
  (LET (TEST TRUE-BRANCH FALSE-BRANCH)
    (COND ((OR (VARIABLEP TERM) (FQUOTEP TERM)) (LIST TERM))
          ((MATCH TERM (IF TEST TRUE-BRANCH FALSE-BRANCH))
           (COND ((EQUAL FALSE-BRANCH FALSE)
                  (CONS TEST (EXTRACT-CONJUNCTS TRUE-BRANCH)))
                 ((EQUAL TRUE-BRANCH FALSE)
                  (CONS (FCONS-TERM* (QUOTE NOT) TEST)
                        (EXTRACT-CONJUNCTS FALSE-BRANCH)))
                 (T (LIST TERM))))
          (T (LIST TERM)))))

(DEFUN EXTRACT-DEPENDENCIES-FROM-HINTS (HINTS)
  (ITERATE FOR HINT IN HINTS
           WITH ITERATE-ANS
           DO (SETQ ITERATE-ANS
                    (UNION-EQ (CASE (CAR HINT)
                                    (USE (ITERATE FOR X IN (CDR HINT)
                                                  COLLECT (CAR X)))
                                    (INDUCT (LIST (FFN-SYMB (CADR HINT))))
                                    ((ENABLE-THEORY DISABLE-THEORY)
                                     (ITERATE FOR X IN (CDR HINT)
                                              WHEN (NOT (EQ X T))
                                              COLLECT X))
                                    (OTHERWISE NIL))
                              ITERATE-ANS))
           FINALLY (RETURN ITERATE-ANS)))

(DEFUN FALSE-NONFALSEP (TERM)
  (LET (TEMP)
    (COND ((QUOTEP TERM)
           (SETQ DEFINITELY-FALSE (EQUAL TERM FALSE))
           T)
          (T (SETQ TEMP (TYPE-SET TERM))
             (COND ((TS= TEMP TYPE-SET-FALSE)
                    (SETQ DEFINITELY-FALSE T)
                    T)
                   ((TS= 0 (TSLOGAND TEMP TYPE-SET-FALSE))
                    (SETQ DEFINITELY-FALSE NIL)
                    T)
                   (T NIL))))))

(DEFUN FAVOR-COMPLICATED-CANDIDATES (CANDLST)
  (MAXIMAL-ELEMENTS
   CANDLST
   (FUNCTION (LAMBDA (CAND)
               (ITERATE FOR TERM
                        IN (CONS (ACCESS CANDIDATE INDUCTION-TERM CAND)
                                 (ACCESS CANDIDATE OTHER-TERMS CAND))
                        COUNT (NOT (PRIMITIVE-RECURSIVEP
                                    (FN-SYMB TERM))))))))

(DEFUN FCONS-TERM-NTH (N TERM)

;   Creates the formal term for the Nth element of TERM, i.e.,
;   (CAR (CDR (CDR ... TERM)...)), with N=1 being (CAR TERM).

  (ITERATE FOR I FROM 1 TO (1- N)
           DO (SETQ TERM (FCONS-TERM* (QUOTE CDR) TERM)))
  (FCONS-TERM* (QUOTE CAR) TERM))
                 

(DEFUN FERTILIZE-CLAUSE (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (PROG (LIT LHS1 RHS1 LHS2 RHS2 DONT-DELETE-LIT-FLG MASS-SUBST-FLG
             CROSS-FERT-FLG DIRECTION)
        (SETQ LIT (ITERATE FOR LIT IN CL
                           WHEN (AND (MATCH LIT (NOT (EQUAL LHS1 RHS1)))
                                     (SETQ DIRECTION
                                           (FERTILIZE1 LIT CL LHS1 RHS1 HIST)))
                           DO (RETURN LIT)))
        (COND ((NULL LIT) (RETURN NIL)))
        (SETQ MASS-SUBST-FLG (OR (QUOTEP LHS1) (QUOTEP RHS1)))
        (SETQ DONT-DELETE-LIT-FLG
              (OR (QUOTEP LHS1)
                  (QUOTEP RHS1)
                  (AND (NOT (AND IN-PROVE-LEMMA-FLG
                                 (ASSOC-EQ (QUOTE INDUCT) HINTS)))
                       (NOT (ASSOC-EQ (QUOTE BEING-PROVED) STACK)))))
        (SETQ CROSS-FERT-FLG
              (AND (ASSOC-EQ (QUOTE BEING-PROVED) STACK)
                   (ITERATE FOR LIT2 IN CL
                            THEREIS
                            (AND (MATCH LIT2 (EQUAL LHS2 RHS2))
                                 (COND ((EQ DIRECTION (QUOTE LEFT-FOR-RIGHT))
                                        (OCCUR RHS1 RHS2))
                                       (T (OCCUR LHS1 LHS2)))))
                   (ITERATE FOR LIT2 IN CL
                            THEREIS
                            (AND (MATCH LIT2 (EQUAL LHS2 RHS2))
                                 (COND ((EQ DIRECTION (QUOTE LEFT-FOR-RIGHT))
                                        (OCCUR RHS1 LHS2))
                                       (T (OCCUR LHS1 RHS2)))))))
        (SETQ PROCESS-CLAUSES
              (LIST (ITERATE FOR LIT2 IN CL WHEN (OR DONT-DELETE-LIT-FLG
                                                     (NOT (EQ LIT LIT2)))
                             COLLECT (COND ((EQ LIT LIT2) LIT)
                                           ((OR MASS-SUBST-FLG
                                                (NOT CROSS-FERT-FLG)
                                                (MATCH LIT2 (NOT (EQUAL & &))))
                                            (COND ((EQ DIRECTION
                                                       (QUOTE LEFT-FOR-RIGHT))
                                                   (SUBSTITUTE-EXPR LHS1 RHS1
                                                                    LIT2))
                                                  (T (SUBSTITUTE-EXPR
                                                      RHS1 LHS1 LIT2))))
                                           ((MATCH LIT2 (EQUAL LHS2 RHS2))
                                            (COND ((EQ DIRECTION
                                                       (QUOTE LEFT-FOR-RIGHT))
                                                   (FCONS-TERM*
                                                    (QUOTE EQUAL)
                                                    LHS2
                                                    (SUBSTITUTE-EXPR LHS1
                                                                     RHS1
                                                                     RHS2)))
                                                  (T (FCONS-TERM*
                                                      (QUOTE EQUAL)
                                                      (SUBSTITUTE-EXPR
                                                       RHS1 LHS1 LHS2)
                                                      RHS2))))
                                           (T LIT2)))))
        (SETQ PROCESS-HIST (LIST MASS-SUBST-FLG CROSS-FERT-FLG
                                 DIRECTION LHS1 RHS1
                                 DONT-DELETE-LIT-FLG))
        (RETURN T)))

(DEFUN FERTILIZE-FEASIBLE (LIT CL TERM HIST)
  (AND (NOT (ALMOST-QUOTEP TERM))
       (OR (VARIABLEP TERM) (NOT (SKO-DEST-NESTP TERM NIL)))
       (ITERATE FOR LIT2 IN CL WHEN (NOT (EQ LIT2 LIT))
                THEREIS (OCCUR TERM LIT2))
       (NOT (ITERATE FOR ENTRY IN HIST WITH (LHS RHS)
                     THEREIS (AND (MATCH ENTRY (FERTILIZE-CLAUSE & & & & LHS
                                                                 RHS &))
                                  (EQUAL (FARGN (FARGN LIT 1) 1) LHS)
                                  (EQUAL (FARGN (FARGN LIT 1) 2) RHS))))))

(DEFUN FERTILIZE-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE FERTILIZE-CLAUSE)
           CL HIST
           (QUOTE SIMPLIFY-SENT)
           (QUOTE GENERALIZE-SENT)))

(DEFUN FERTILIZE1 (LIT CL LHS RHS HIST)
  (COND ((FERTILIZE-FEASIBLE LIT CL LHS HIST)
         (COND ((FERTILIZE-FEASIBLE LIT CL RHS HIST)
                (COND ((< (COMPLEXITY LHS) (COMPLEXITY RHS))
                       (QUOTE LEFT-FOR-RIGHT))
                      (T (QUOTE RIGHT-FOR-LEFT))))
               (T (QUOTE RIGHT-FOR-LEFT))))
        ((FERTILIZE-FEASIBLE LIT CL RHS HIST)
         (QUOTE LEFT-FOR-RIGHT))
        (T NIL)))

(DEFUN FILTER-ARGS (SUBSET FORMALS ARGS)
  (ITERATE FOR VAR IN SUBSET
           COLLECT (ITERATE FOR TERM IN ARGS AS FORMAL IN FORMALS
                            WHEN (EQ FORMAL VAR)
                            DO (RETURN TERM))))

(DEFUN FIND-EQUATIONAL-POLY (HIST POT)

;   Look for an equation to be derived from this pot.  If one is found, add to
;   LEMMAS-USED-BY-LINEAR and LINEAR-ASSUMPTIONS the appropriate entries from
;   the two polys involved.  In addition, add an extra entry to
;   LEMMAS-USED-BY-LINEAR to store the fact that this equation has been
;   deduced.  Finally, do not do any of this if HIST records that the deduced
;   equation has been previously deduced.  See the comment in
;   PROCESS-EQUATIONAL-POLYS for details.

  (ITERATE FOR POLY1 IN (ACCESS LINEAR-POT POSITIVES POT)
           WITH (WINNING-PAIR POLY2 PAIR HYP1 HYP2)
           WHEN (SETQ TEMP-TEMP (TRIVIAL-POLYP POLY1)) DO
           (PROGN
             (SETQ WINNING-PAIR (CAR TEMP-TEMP))
             (SETQ POLY1 (CDR TEMP-TEMP))

;   POLY1 is in lowest form now.

             (COND ((SETQ POLY2 (ITERATE FOR POLY2
                                         IN (ACCESS LINEAR-POT NEGATIVES POT)
                                         WHEN (COMPLEMENTARY-MULTIPLEP
                                               WINNING-PAIR
                                               POLY1 POLY2)
                                         DO (RETURN POLY2)))
                    (SETQ PAIR (EQUATIONAL-PAIR-FOR WINNING-PAIR POLY1))
                    (SETQ HYP1 (NUMBERP? (CAR PAIR)))
                    (SETQ HYP2 (NUMBERP? (CDR PAIR)))
                    (COND ((AND
                            (NOT (EQUAL HYP1 FALSE))
                            (NOT (EQUAL HYP2 FALSE))
                            (ITERATE FOR HIST-ENTRY IN HIST
                                     NEVER
                                     (AND
                                      (EQ (CAR HIST-ENTRY)
                                          (QUOTE SIMPLIFY-CLAUSE))
                                      (ITERATE
                                       FOR X IN (CDDR HIST-ENTRY)
                                       THEREIS
                                       (AND
                                        (CONSP X)
                                        (CONSP (CAR X))
                                        (EQ (CAR (CAR X))
                                            (QUOTE
                                             FIND-EQUATIONAL-POLY))
                                        (OR (EQUAL PAIR
                                                   (CDR (CAR X)))
                                            (AND
                                             (EQUAL
                                              (CDR PAIR)
                                              (CAR (CDR (CAR X))))
                                             (EQUAL
                                              (CAR PAIR)
                                              (CDR (CDR (CAR X)))))))))))
                           (SETQ LINEAR-ASSUMPTIONS
                                 (UNION-EQUAL (UNION-EQUAL
                                               (ACCESS POLY ASSUMPTIONS POLY1)
                                               (ACCESS POLY ASSUMPTIONS POLY2))
                                              LINEAR-ASSUMPTIONS))
                           (OR (EQUAL TRUE HYP1)
                               (SETQ LINEAR-ASSUMPTIONS
                                     (ADD-TO-SET HYP1 LINEAR-ASSUMPTIONS)))
                           (OR (EQUAL TRUE HYP2)
                               (SETQ LINEAR-ASSUMPTIONS
                                     (ADD-TO-SET HYP2 LINEAR-ASSUMPTIONS)))
                           (SETQ LEMMAS-USED-BY-LINEAR
                                 (CONS (LIST (CONS (QUOTE FIND-EQUATIONAL-POLY)
                                                   PAIR))
                                       (UNION-EQ (UNION-EQ
                                                  (ACCESS POLY LEMMAS POLY1)
                                                  (ACCESS POLY LEMMAS POLY2))
                                                 LEMMAS-USED-BY-LINEAR)))
                           (RETURN PAIR))))))))

(DEFUN FIRST-COEFFICIENT (EQUATION)
  (CDAR (ACCESS POLY ALIST EQUATION)))

(DEFUN FIRST-VAR (EQUATION)
  (CAAR (ACCESS POLY ALIST EQUATION)))

(DEFUN FITS (ALIST1 ALIST2 VARS)

;   Return T iff the two alists agree on every var in VARS.

  (ITERATE FOR VAR IN VARS
           ALWAYS (EQUAL (COND ((SETQ TEMP-TEMP (ASSOC-EQ VAR ALIST1))
                                (CDR TEMP-TEMP))
                               (T VAR))
                         (COND ((SETQ TEMP-TEMP (ASSOC-EQ VAR ALIST2))
                                (CDR TEMP-TEMP))
                               (T VAR)))))

(DEFUN FIX-CASE (TEST ALIST)
 (COND ((EQ (CAAR ALIST) 'OTHERWISE)
        (CDAR ALIST))
       (T (FCONS-TERM* 'IF
                       (FCONS-TERM* 'EQUAL TEST (CAR (CAR ALIST)))
                       (CDR (CAR ALIST))
                       (FIX-CASE TEST (CDR ALIST))))))

(DEFUN FIX-COND (ALIST)
  (COND ((NULL (CDR ALIST)) (CDR (CAR ALIST)))
        (T (FCONS-TERM* 'IF
                        (CAR (CAR ALIST))
                        (CDR (CAR ALIST))
                        (FIX-COND (CDR ALIST))))))

(DEFUN FIXCAR-CDR (TERM)
  (LET (TEMP)
    (COND ((SETQ TEMP (CAR-CDRP (CAR TERM)))
           (SETQ TERM (CADR TERM))
           (ITERATE FOR A-D IN TEMP
                    DO (SETQ TERM (LIST (COND ((EQL A-D #\A) (QUOTE CAR))
                                              (T (QUOTE CDR))) TERM)))))
    TERM))

(DEFUN FLATTEN-TERM (TERM FN)
  (COND ((VARIABLEP TERM) (LIST TERM))
        ((FQUOTEP TERM) (LIST TERM))
        ((EQ FN (FFN-SYMB TERM))
         (ITERATE FOR ARG IN (FARGS TERM) NCONC (FLATTEN-TERM ARG FN)))
        (T (LIST TERM))))

(DEFUN FLATTEN-ANDS-IN-LIT (TERM)
  (LET (C1 C2 C3)
    (COND ((EQUAL TERM TRUE) NIL)
          ((MATCH TERM (IF C1 C2 C3))
           (COND ((EQUAL C2 FALSE)
                  (APPEND (FLATTEN-ANDS-IN-LIT (DUMB-NEGATE-LIT C1))
                          (FLATTEN-ANDS-IN-LIT C3)))
                 ((EQUAL C3 FALSE)
                  (APPEND (FLATTEN-ANDS-IN-LIT C1) (FLATTEN-ANDS-IN-LIT C2)))
                 (T (LIST TERM))))
          ((MATCH TERM (AND C1 C2))
           (APPEND (FLATTEN-ANDS-IN-LIT C1) (FLATTEN-ANDS-IN-LIT C2)))
          (T (LIST TERM)))))

(DEFUN FLESH-OUT-IND-PRIN
  (TERM FORMALS MACHINE JUSTIFICATION MASK QUICK-BLOCK-INFO)
  QUICK-BLOCK-INFO

;   Constructs a CANDIDATE record for TERM given, for the fn symbol of TERM,
;   the FORMALS, the INDUCTION-MACHINE property, a JUSTIFICATION, a sound
;   induction principle MASK, and the QUICK-BLOCK-INFO.

  (MAKE
   CANDIDATE
   (/ (FLOAT (ITERATE FOR FLG IN MASK COUNT FLG)) (LENGTH FORMALS))
   (ITERATE FOR A IN (FARGS TERM) AS V IN FORMALS
            WITH ITERATE-ANS
            WHEN (MEMBER-EQ V (ACCESS JUSTIFICATION SUBSET JUSTIFICATION))
            DO (SETQ ITERATE-ANS (UNION-EQ (ALL-VARS A) ITERATE-ANS))
            FINALLY (RETURN ITERATE-ANS))
   (ITERATE FOR ACTUAL IN (SARGS TERM) AS FLG IN MASK
            WHEN (EQ FLG (QUOTE CHANGEABLE))
            COLLECT ACTUAL)
   (ITERATE FOR ACTUAL IN (SARGS TERM) AS FLG IN MASK
            WITH ITERATE-ANS
            WHEN (EQ FLG (QUOTE UNCHANGEABLE))
            DO (SETQ ITERATE-ANS (UNION-EQ (ALL-VARS ACTUAL) ITERATE-ANS))
            FINALLY (RETURN ITERATE-ANS))
   (ITERATE FOR X IN MACHINE
            COLLECT
            (MAKE
             TESTS-AND-ALISTS
             (SUB-PAIR-VAR-LST FORMALS (SARGS TERM)
                               (ACCESS TESTS-AND-CASES TESTS X))
             (ITERATE FOR ARGLIST IN (ACCESS TESTS-AND-CASES CASES X)
                      COLLECT
                      (ITERATE FOR ACTUAL IN (SARGS TERM) AS FLG IN MASK AS ARG
                               IN ARGLIST
                               WITH ITERATE-ANS
                               DO (SETQ
                                   ITERATE-ANS
                                   (UNION-EQUAL
                                    (COND ((NULL FLG) NIL)
                                          ((EQ FLG (QUOTE CHANGEABLE))
                                           (LIST (CONS ACTUAL
                                                       (SUB-PAIR-VAR
                                                        FORMALS
                                                        (SARGS TERM)
                                                        ARG))))
                                          (T (ITERATE FOR VAR
                                                      IN (ALL-VARS ACTUAL)
                                                      COLLECT
                                                      (CONS VAR VAR))))
                                    ITERATE-ANS))
                               FINALLY (RETURN ITERATE-ANS)))))
   JUSTIFICATION TERM NIL))

(DEFUN FLUSH-CAND1-DOWN-CAND2 (CAND1 CAND2)
  (LET (SCORE1 CONTROLLERS1 CHANGED-VARS1 UNCHANGEABLES1
               TESTS-AND-ALISTS-LST1 TERM1 OTHER-TERMS1)
    (LET (SCORE2 CONTROLLERS2 CHANGED-VARS2 UNCHANGEABLES2
                 TESTS-AND-ALISTS-LST2 JUSTIFICATION2 TERM2 OTHER-TERMS2)
      (MATCH CAND1 (CANDIDATE SCORE1 CONTROLLERS1 CHANGED-VARS1
                              UNCHANGEABLES1 TESTS-AND-ALISTS-LST1
                              & TERM1 OTHER-TERMS1))
      (MATCH CAND2 (CANDIDATE SCORE2 CONTROLLERS2 CHANGED-VARS2
                              UNCHANGEABLES2 TESTS-AND-ALISTS-LST2
                              JUSTIFICATION2 TERM2 OTHER-TERMS2))
      (COND ((AND
              (SUBSETP-EQ CHANGED-VARS1 CHANGED-VARS2)
              (SUBSETP-EQ UNCHANGEABLES1 UNCHANGEABLES2)
              (PIGEON-HOLE
               TESTS-AND-ALISTS-LST1 TESTS-AND-ALISTS-LST2
               (FUNCTION
                (LAMBDA (TA1 TA2)
                  (AND
                   (SUBSETP-EQUAL (ACCESS TESTS-AND-ALISTS TESTS TA1)
                                  (ACCESS TESTS-AND-ALISTS TESTS TA2))
                   (OR
                    (AND (NULL (ACCESS TESTS-AND-ALISTS ALISTS TA1))
                         (NULL (ACCESS TESTS-AND-ALISTS ALISTS TA2)))
                    (PIGEON-HOLE
                     (ACCESS TESTS-AND-ALISTS ALISTS TA1)
                     (ACCESS TESTS-AND-ALISTS ALISTS TA2)
                     (FUNCTION (LAMBDA (ALIST1 ALIST2)
                                 (PIGEON-HOLE
                                  ALIST1 ALIST2
                                  (FUNCTION (LAMBDA (PAIR1 PAIR2)
                                              (AND (EQ (CAR PAIR1)
                                                       (CAR PAIR2))
                                                   (OCCUR (CDR PAIR1)
                                                          (CDR PAIR2)))))
                                  T T)))
                     T T)))))
               T T))
             (MAKE CANDIDATE (+ SCORE1 SCORE2)
                   (UNION-EQ CONTROLLERS1 CONTROLLERS2)
                   CHANGED-VARS2 UNCHANGEABLES2 TESTS-AND-ALISTS-LST2
                   JUSTIFICATION2 TERM2
                   (ADD-TO-SET TERM1
                               (UNION-EQUAL OTHER-TERMS1 OTHER-TERMS2))))
            (T NIL)))))

(DEFUN FN-SYMB0 (X)
  (COND ((SYMBOLP X)
         (COND ((EQ X *1*T) (QUOTE TRUE))
               ((EQ X *1*F) (QUOTE FALSE))
               (T (QUOTE PACK))))
        ((INTEGERP X)
         (COND ((< X 0) (QUOTE MINUS))
               ((EQUAL X 0) (QUOTE ZERO))
               (T (QUOTE ADD1))))
        ((EQ (CAR X) *1*SHELL-QUOTE-MARK)
         (CADR X))
        (T (QUOTE CONS))))

(DEFUN FNNAMEP (FN TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM)
         (COND ((OR (MEMBER-EQ FN *1*BTM-OBJECTS) (ASSOC-EQ FN SHELL-ALIST))
                (MEMBER-EQ FN (ALL-FNNAMES TERM)))
               (T NIL)))
        ((EQ FN (FFN-SYMB TERM)) T)
        (T (ITERATE FOR X IN (FARGS TERM) THEREIS (FNNAMEP FN X)))))

(DEFUN FNNAMEP-IF (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        ((EQ (FFN-SYMB TERM) (QUOTE IF)) T)
        (T (ITERATE FOR X IN (FARGS TERM) THEREIS (FNNAMEP-IF X)))))

(DEFUN FORM-COUNT (TERM)

;   Returns the number of open parentheses in the unabbreviated presentation of
;   TERM.  Also sets NUMBER-OF-VARIABLES to the number of variables in TERM.

  (SETQ NUMBER-OF-VARIABLES 0)
  (FORM-COUNT1 TERM))

(DEFUN FORM-COUNT-EVG (EVG)
  (COND
   ((ATOM EVG)
    (COND
     ((EQ EVG *1*T) 1)
     ((EQ EVG *1*F) 1)
     ((INTEGERP EVG)
      (COND ((< EVG 0) (+ 2 (- EVG)))
            (T (1+ EVG))))
     (T (SETQ TEMP-TEMP (ASSOC-EQ EVG LITATOM-FORM-COUNT-ALIST))
        (COND (TEMP-TEMP (CDR TEMP-TEMP))
              (T (CDAR (SETQ LITATOM-FORM-COUNT-ALIST
                             (CONS (CONS EVG
                                         (+ 2 (* 2
                                                 (LENGTH (SYMBOL-NAME
                                                          EVG)))
                                            (ITERATE FOR I FROM 1
                                                     TO (LENGTH
                                                         (SYMBOL-NAME EVG))
                                                     SUM
                                                     (OUR-GETCHARN EVG I))))
                                   LITATOM-FORM-COUNT-ALIST))))))))
   ((EQ (CAR EVG)
        *1*SHELL-QUOTE-MARK)
    (1+ (ITERATE FOR X IN (CDDR EVG) SUM (FORM-COUNT-EVG X))))
   (T (+ 1 (FORM-COUNT-EVG (CAR EVG))
         (FORM-COUNT-EVG (CDR EVG))))))

(DEFUN FORM-COUNT1 (TERM)
  (COND ((VARIABLEP TERM)
         (SETQ NUMBER-OF-VARIABLES (1+ NUMBER-OF-VARIABLES))
         0)
        ((FQUOTEP TERM)
         (FORM-COUNT-EVG (CADR TERM)))
        (T
         (1+ (ITERATE FOR T1 IN (FARGS TERM) SUM (FORM-COUNT1 T1))))))

(DEFUN FORM-INDUCTION-CLAUSE (TESTS HYPS CONCL TERMS)
  TERMS

;   We once implemented the idea of "homographication" in which we combined
;   both induction, opening up of the recursive fns in the conclusion, and
;   generalizing away some recursive calls.  This function did the expansion
;   and generalization.  If the idea is reconsidered the following theorems are
;   worthy of consideration:

;       (ORDERED (SORT X)),
;       (IMPLIES (ORDERED X)
;                (ORDERED (ADDTOLIST I X))),
;       (IMPLIES (AND (NUMBER-LISTP X)
;                     (ORDERED X)
;                     (NUMBERP I)
;                     (NOT (< (CAR X) I)))
;                (EQUAL (ADDTOLIST I X) (CONS I X))), and
;       (IMPLIES (AND (NUMBER-LISTP X) (ORDERED X)) (EQUAL (SORT X) X)).

  (APPEND TESTS (APPEND HYPS CONCL)))

(DEFUN FORM-THEORY (EVENT-OR-EVENT-LIST)
  (LET ((RESULT (FORM-THEORY-AUX
                 (COND ((AND (ATOM EVENT-OR-EVENT-LIST)
                             EVENT-OR-EVENT-LIST)
                        (LIST EVENT-OR-EVENT-LIST))
                       (T EVENT-OR-EVENT-LIST)))))
    (IF (OR (EQ EVENT-OR-EVENT-LIST 'GROUND-ZERO)
            (EQUAL EVENT-OR-EVENT-LIST '(GROUND-ZERO)))
        RESULT
      (MAKE-SET! RESULT))))

(DEFUN FORM-THEORY-AUX (EVENT-LIST)

; This function must return new list structure.

  (ITERATE FOR NAME IN EVENT-LIST
           WITH TEMP
           NCONC
           (COND
            ((EQ NAME 'GROUND-ZERO)
             (COPY-LIST (GET 'GROUND-ZERO 'SATELLITES)))
            ((AND (SETQ TEMP (GET NAME (QUOTE EVENT)))
                  (EQ (CAR TEMP) (QUOTE DEFTHEORY)))
             (FORM-THEORY-AUX (CADDR TEMP)))
            (T (CONS NAME (COPY-LIST (GET NAME (QUOTE SATELLITES))))))))

(DEFUN FORMULA-OF (NAME)
  (LET ((EVENT (GET NAME (QUOTE EVENT))))
    (COND (EVENT
           (CASE (CAR EVENT)
                 (DEFN (FCONS-TERM* (QUOTE EQUAL)
                                    (FCONS-TERM (CADR EVENT)
                                                (CADDR EVENT))
                                    (CADDDR EVENT)))
                 ((ADD-AXIOM PROVE-LEMMA CONSTRAIN FUNCTIONALLY-INSTANTIATE)
                  (CADDDR EVENT))
                 (OTHERWISE NIL)))
          ((AND (EQ (QUOTE GROUND-ZERO) (GET NAME (QUOTE MAIN-EVENT)))
                (SETQ EVENT (GET NAME (QUOTE SDEFN))))
           (FCONS-TERM* (QUOTE EQUAL)
                        (FCONS-TERM NAME (CADR EVENT))
                        (CADDR EVENT)))
          (T NIL))))

(DEFUN FREE-VAR-CHK (NAME ARGS FORM)
  (LET (TEMP)
    (SETQ FORM (ALL-VARS FORM))
    (SETQ TEMP (SET-DIFF FORM ARGS))
    (COND (TEMP (ER SOFT (NAME TEMP) |Illegal| |free|
                    (PLURAL? TEMP |variables| |variable|) |,|
                    (!TERM-LIST TEMP (QUOTE  |,|)) |in| |the| |definition| |of|
                    (!PPR NAME (QUOTE |.|)))))
    (SETQ TEMP (SET-DIFF ARGS FORM))
    (COND (TEMP (ER WARNING (NAME TEMP)
                    (!LIST TEMP) (PLURAL? TEMP |are| |is|) |in| |the|
                    |arglist| |but| |not| |in| |the| |body| |of| |the|
                    |definition| |of| (!PPR NAME (QUOTE |.|)))))
    NIL))

(DEFUN FREE-VARSP (TERM ALIST)
  (COND ((VARIABLEP TERM) (NOT (ASSOC-EQ TERM ALIST)))
        ((FQUOTEP TERM) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM) THEREIS (FREE-VARSP ARG ALIST)))))

(DEFUN GEN-VARS1 (BIG LITTLE N)
  (COND ((ZEROP N) NIL)
        ((ATOM BIG)
         (ER SOFT nil
             |Nqthm| |has| |run| |out| |of| |variable| |names| |for| |use|
             |in| |either| |destructor| |elimination| |or| |generalization|
             |.|  |We| |have| |never| |seen| |a| |circumstance| |in| |which|
             |a| |larger| |initial| |supply| |would| |have| |led| |to| |a|
             |successful| |proof| |.|))
        ((MEMBER-EQ (CAR BIG) LITTLE)
         (GEN-VARS1 (CDR BIG) LITTLE N))
        (T (CONS (CAR BIG) (GEN-VARS1 (CDR BIG) LITTLE (1- N))))))

(DEFUN GEN-VARS (CL N VARIABLE-NAMES)

;   Generates N skolem constants not occurring in clause CL.

  (GEN-VARS1 VARIABLE-NAMES (ITERATE FOR LIT IN CL WITH ITERATE-ANS
                                     DO (SETQ ITERATE-ANS
                                              (UNION-EQ (ALL-VARS LIT)
                                                        ITERATE-ANS))
                                     FINALLY (RETURN ITERATE-ANS))
             N))

(DEFUN GENERALIZE-CLAUSE (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  HIST

;   Generalize the smallest common subterms in CL -- as defined by COMSUBTERMS
;   -- using the lemmas on GENERALIZE-LEMMAS to supply typing info.

  (PROG (COMMONSUBTERMS)
        (COND ((OR (NOT (ASSOC-EQ (QUOTE BEING-PROVED) STACK))
                   DO-NOT-GENERALIZE-FLG)
               (RETURN NIL)))
        (SETQ COMMONSUBTERMS (GENRLTERMS CL))
        (COND ((NULL COMMONSUBTERMS) (RETURN NIL))
              (T (SETQ PROCESS-CLAUSES
                       (LIST (GENERALIZE1 CL COMMONSUBTERMS
                                          GEN-VARIABLE-NAMES1)))
                 (SETQ PROCESS-HIST (LIST GENERALIZING-SKOS
                                          COMMONSUBTERMS
                                          OBVIOUS-RESTRICTIONS
                                          GENERALIZE-LEMMA-NAMES))
                 (SETQ ALL-LEMMAS-USED
                       (UNION-EQ GENERALIZE-LEMMA-NAMES ALL-LEMMAS-USED))
                 (RETURN T)))))

(DEFUN GENERALIZE-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE GENERALIZE-CLAUSE)
           CL HIST (QUOTE SIMPLIFY-SENT)
           (QUOTE ELIMINATE-IRRELEVANCE-SENT)))

(DEFUN GENERALIZE1 (CL SUBTERMLST VARIABLE-NAMES)

;   Replaces all occurrences of the subterms in SUBTERMLST in CL by new vars,
;   and qualifies each var with all the information known to GET-TYPES.

  (SETQ GENERALIZING-SKOS (GEN-VARS CL (LENGTH SUBTERMLST)
                                    VARIABLE-NAMES))
  (SETQ OBVIOUS-RESTRICTIONS NIL)
  (SETQ GENERALIZE-LEMMA-NAMES NIL)
  (GENERALIZE2 SUBTERMLST GENERALIZING-SKOS CL))

(DEFUN GENERALIZE2 (TERMLST VARLST CL)
  (ITERATE FOR LIT
           IN (SCRUNCH (NCONC (ITERATE FOR SUBTERM IN TERMLST
                                       NCONC (ITERATE
                                              FOR HYP
                                              IN (GET-TYPES
                                                  SUBTERM CL)
                                              COLLECT
                                              (DUMB-NEGATE-LIT
                                               HYP)))
                              CL))
           COLLECT (SUB-PAIR-EXPR TERMLST VARLST LIT)))

(DEFUN GENRLT1 (CL)
  (LET (LHS RHS)
    (ITERATE FOR LIT IN CL WHEN (OR (MATCH LIT (EQUAL LHS RHS))
                                    (MATCH LIT (NOT (EQUAL LHS RHS))))
             DO (COMSUBTERMS LHS RHS))
    (ITERATE FOR TAIL ON CL DO (ITERATE FOR LIT2 IN (CDR TAIL)
                                        DO (COMSUBTERMS (CAR TAIL)
                                                        LIT2)))
    NIL))

(DEFUN GENRLTERMS (CL) (LET (GENRLTLIST) (GENRLT1 CL) GENRLTLIST))

(DEFUN GET-CANDS (TERM)

;   Returns all of the induction principles -- see POSSIBLE-IND-PRINCIPLES --
;   connected to terms in TERM, which is the conjecture to be proved.

  (COND ((VARIABLEP TERM) NIL)
        ((QUOTEP TERM) NIL)
        (T (NCONC (POSSIBLE-IND-PRINCIPLES TERM)
                  (ITERATE FOR ARG IN (FARGS TERM) NCONC (GET-CANDS ARG))))))

(DEFUN GET-LISP-SEXPR (FN)
  (LET (SEXPR)
    (SETQ SEXPR (GET (GET FN (QUOTE LISP-CODE)) (QUOTE SEXPR)))
    (COND ((NULL SEXPR)
           (ER SOFT (FN) (!PPR FN NIL) |is| |either| |DCLd| |or| |is| |part|
               |of| |the| |basic| |system| |and| |has| |a| |hand-coded| LISP
               |definition| |.|))
          (T SEXPR))))

(DEFUN GET-LEVEL-NO (FNNAME)
  (OR (GET FNNAME (QUOTE LEVEL-NO)) 0))

(DEFUN GET-STACK-NAME (STACKV)
  (PACK (CONS (QUOTE *)
              (CDR (ITERATE FOR I IN (NREVERSE (GET-STACK-NAME1 STACKV))
                            NCONC (LIST (QUOTE |.|) I))))))

(DEFUN GET-STACK-NAME1 (STACKV)
  (LET (ANS)
    (COND ((NULL STACKV) (LIST 1))
          ((EQ (CAAR STACKV) (QUOTE TO-BE-PROVED))
           (SETQ ANS (GET-STACK-NAME1 (CDR STACKV)))
           (RPLACA ANS (1+ (CAR ANS))))
          (T (CONS 1 (GET-STACK-NAME1 (CDR STACKV)))))))

(DEFUN GET-STATUS (EVENT-NAME ALIST)

; Look up the status assigned to EVENT-NAME in the status alist ALIST
; and return it.  We know the ALIST has an OTHERWISE clause.

  (ITERATE FOR X IN ALIST
           WHEN (OR (EQ EVENT-NAME (CAR X))
                    (AND (CONSP (CAR X))
                         (MEMBER-EQ EVENT-NAME (CAR X)))
                    (EQ (CAR X) 'OTHERWISE))
           DO (RETURN (CADR X))))

(DEFUN GET-TYPES (TERM CL)
  (LET (TYPE-RESTRICTION LEMMA-RESTRICTIONS TYPE PAIR INST-LEMMA)
    CL
    (SETQ TYPE (TYPE-SET TERM))
    (SETQ TYPE-RESTRICTION
          (COND ((SETQ PAIR (ITERATE FOR PAIR IN RECOGNIZER-ALIST
                                     WHEN (TS= TYPE (CDR PAIR))
                                     DO (RETURN PAIR)))
                 (FCONS-TERM* (CAR PAIR) TERM))
                (T NIL)))
    (COND (TYPE-RESTRICTION (SETQ OBVIOUS-RESTRICTIONS
                                  (ADD-TO-SET TYPE-RESTRICTION
                                              OBVIOUS-RESTRICTIONS))))
    (SETQ LEMMA-RESTRICTIONS
          (ITERATE FOR LEMMA IN GENERALIZE-LEMMAS
                   UNLESS (DISABLEDP (ACCESS GENERALIZE-LEMMA NAME LEMMA))
                   WHEN (AND (ARG1-IN-ARG2-UNIFY-SUBST TERM
                                                       (ACCESS GENERALIZE-LEMMA
                                                               TERM LEMMA))
                             (NOT (FREE-VARSP (ACCESS GENERALIZE-LEMMA TERM
                                                      LEMMA)
                                              UNIFY-SUBST))
                             (NOT (FNNAMEP (FN-SYMB TERM)
                                           (SUBST-EXPR
                                            (QUOTE X)
                                            TERM
                                            (SETQ INST-LEMMA
                                                  (SUBLIS-VAR
                                                   UNIFY-SUBST
                                                   (ACCESS
                                                    GENERALIZE-LEMMA
                                                    TERM LEMMA)))))))
                   COLLECT
                   (PROGN (SETQ GENERALIZE-LEMMA-NAMES
                                (CONS (ACCESS GENERALIZE-LEMMA NAME LEMMA)
                                      GENERALIZE-LEMMA-NAMES))
                          INST-LEMMA)))
    (COND (TYPE-RESTRICTION (CONS TYPE-RESTRICTION
                                  LEMMA-RESTRICTIONS))
          (T LEMMA-RESTRICTIONS))))

(DEFUN GUARANTEE-CITIZENSHIP (NAME)
  (COND ((AND (NOT (GET NAME (QUOTE EVENT)))
              (NOT (GET NAME (QUOTE MAIN-EVENT))))
         (PUT1 MAIN-EVENT-NAME (CONS NAME (GET MAIN-EVENT-NAME
                                               (QUOTE SATELLITES)))
               (QUOTE SATELLITES))
         (PUT1 NAME MAIN-EVENT-NAME
               (QUOTE MAIN-EVENT)))))

(DEFUN GUESS-NEW-EVENT-NAME (ROOT)

; This function returns a symbol without LIB-PROPS, but there is no guarantee
; that it is an appropriate event name, e.g.  we do not check ILLEGAL-NAME or
; PROPERTYLESS-SYMBOLP.

  (ITERATE FOR I FROM 0
           WITH NEW-NAME
           WHEN (NOT (HAS-LIB-PROPS (SETQ NEW-NAME (PACK (LIST ROOT I)))))
           DO (RETURN NEW-NAME)))

(DEFUN GUESS-RELATION-MEASURE-LST (FORMALS MACHINE)

;   We assume MACHINE is a list of TESTS-AND-CASE.  We will guess that the
;   COUNT goes down with LESSP on formal tested and changed in every line of
;   the machine.

  (ITERATE FOR VAR IN FORMALS AS I FROM 0
           WHEN (ITERATE FOR X IN MACHINE
                         ALWAYS (AND (OCCUR-LST VAR (ACCESS TESTS-AND-CASE
                                                            TESTS X))
                                     (NOT (EQ VAR (NTH I (ACCESS
                                                          TESTS-AND-CASE
                                                          CASE X))))))
           COLLECT (LIST (QUOTE LESSP)
                         (LIST (QUOTE COUNT)
                               VAR))))

(DEFUN HAS-LIB-PROPS (ATM)
  (OR (ITERATE FOR PROP IN LIB-PROPS THEREIS (HAS-PROP ATM PROP))
      (HAS-PROP ATM (QUOTE SEXPR))))

(DEFUN HAS-PROP (SYMBOL INDICATOR)
  (NOT (EQ A-VERY-RARE-CONS
           (GET SYMBOL INDICATOR A-VERY-RARE-CONS))))

(DEFUN HIGH-PERSISTENCEP (I)
  (COND ((NULL REWRITE-PATH-STK-PTR) NIL)
        ((INT= I REWRITE-PATH-STK-PTR) NIL)
        (T (> (- (ACCESS REWRITE-PATH-FRAME CNT
                         (AREF REWRITE-PATH-STK (1+ I)))
                 (ACCESS REWRITE-PATH-FRAME CNT
                         (AREF REWRITE-PATH-STK I)))
              (* PERSISTENCE-RATIO
                 (- REWRITE-PATH-FRAME-CNT
                    (ACCESS REWRITE-PATH-FRAME CNT
                            (AREF REWRITE-PATH-STK I))))))))

(DEFUN HIGHLIGHT-REWRITE-PATH (FILE)
  (LET (W X P)
    (COND
     ((AND REWRITE-PATH-STK-PTR
           (NOT (INT= REWRITE-PATH-STK-PTR -1)))
      (SETQ W (OUR-FLATC
               (- REWRITE-PATH-FRAME-CNT
                  (ACCESS REWRITE-PATH-FRAME CNT
                          (AREF REWRITE-PATH-STK 0)))))
      (TERPRI FILE)
      (ITERATE FOR I FROM 0 TO REWRITE-PATH-STK-PTR
               DO
               (SETQ X (AREF REWRITE-PATH-STK I))
               (SETQ P (- REWRITE-PATH-FRAME-CNT
                          (ACCESS REWRITE-PATH-FRAME CNT
                                  X)))
               (COND ((HIGH-PERSISTENCEP I)
                      (FORMAT FILE "*"))
                     (T (FORMAT FILE " ")))
               (COND ((<= W 3) (FORMAT FILE "(~3D)" P))
                     ((INT=  W 4) (FORMAT FILE "(~4D)" P))
                     ((INT=  W 5) (FORMAT FILE "(~5D)" P))
                     ((INT=  W 6) (FORMAT FILE "(~6D)" P))
                     ((INT=  W 7) (FORMAT FILE "(~7D)" P))
                     ((INT=  W 8) (FORMAT FILE "(~8D)" P))
                     (T        (FORMAT FILE "(~9D)" P)))
               (FORMAT FILE " ~3D. " I)
               (CASE (ACCESS REWRITE-PATH-FRAME PROG X)
                     (SIMPLIFY-CLAUSE
                      (PRINC "(top)" FILE))
                     (SET-SIMPLIFY-CLAUSE-POT-LST
                      (PRINC "(initializing the linear database)"
                             FILE))
                     (REWRITE
                      (PRINC "Rewriting " FILE)
                      (PRINC (COND ((VARIABLEP (ACCESS REWRITE-PATH-FRAME
                                                       TERM X))
                                    (ACCESS REWRITE-PATH-FRAME TERM X))
                                   (T (LIST (CAR (ACCESS
                                                  REWRITE-PATH-FRAME TERM X))
                                            '|...|)))
                             FILE))
                     ((REWRITE-WITH-LEMMAS ADD-EQUATIONS-TO-POT-LST)
                      (PRINC "Applying  " FILE)
                      (PRINC (COND ((EQ (CAR (ACCESS REWRITE-PATH-FRAME TERM
                                                     X))
                                        'LINEAR-LEMMA)
                                    (ACCESS LINEAR-LEMMA NAME
                                            (ACCESS REWRITE-PATH-FRAME TERM
                                                    X)))
                                   (T (ACCESS REWRITE-RULE NAME
                                              (ACCESS REWRITE-PATH-FRAME TERM
                                                      X))))
                             FILE))
                     (REWRITE-WITH-LINEAR
                      (PRINC "(entering linear arithmetic)" FILE))
                     (OTHERWISE
                      (ER HARD ((NAME (ACCESS REWRITE-PATH-FRAME PROG
                                              X)))
                          |Unrecognized| REWRITE-PATH |frame|
                          (!PPR NAME '|.|))))
               (TERPRI FILE))))))

(DEFUN HITABLE-AXIOM-INTRODUCED-BY (NAME)
  (LET ((EV (GET NAME 'EVENT)))
       (CASE (CAR EV)
             (DEFN (FCONS-TERM* 'EQUAL
                                (FCONS-TERM (CADR EV) (CADDR EV))
                                (CADDDR EV)))
             ((ADD-AXIOM CONSTRAIN) (CADDDR EV))
             ((DCL ADD-SHELL) TRUE)
             (OTHERWISE (ER HARD () HITABLE-AXIOM-INTRODUCED-BY |was|
                            |called| |on| |something| |other|
                            |than| |a| DEFN |,| ADD-AXIOM |,| 
                            CONSTRAIN |,| DCL |,|  |or| ADD-SHELL |.|)))))

(DEFUN HITP (TERM FS)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        (T (OR (ASSOC-EQ (FFN-SYMB TERM) FS)
               (ITERATE FOR ARG IN (FARGS TERM) THEREIS (HITP ARG FS))))))

(DEFUN IDATE ()
  (POWER-EVAL
   (ITERATE FOR I FROM 1 TO 6
            AS J IN (MULTIPLE-VALUE-LIST (GET-DECODED-TIME))
            COLLECT
            (COND ((INT= I 6) (- J 1900))
                  (T J)))
   100))

(DEFUN IF-NOT-NQTHM-MODE (EV)
  (COND ((EQ *1*THM-MODE$ (QUOTE THM))
         (APPLY (CAR EV) (CDR EV)))))

(DEFUN IF-NQTHM-MODE (EV)
  (COND ((EQ *1*THM-MODE$ (QUOTE NQTHM))
         (APPLY (CAR EV) (CDR EV)))))

(DEFUN ILLEGAL-NAME (NAME)
  (NOT (AND (SYMBOLP NAME)
            (OK-SYMBOLP NAME)
            (LEGAL-CHAR-CODE-SEQ (OUR-EXPLODEN NAME)))))

(DEFUN IMMEDIATE-DEPENDENTS-OF (NAME)
  (LET (ATM)
    (COND ((EQ NAME (QUOTE GROUND-ZERO))
           (REMOVE1 (QUOTE GROUND-ZERO) CHRONOLOGY))
          ((OR (NOT (SYMBOLP NAME))
               (NOT (GET NAME (QUOTE EVENT))))
           (ER HARD (NAME) IMMEDIATE-DEPENDENTS-OF |was| |called| |on| |a|
               |nonevent| |,| (!PPR NAME (QUOTE |.|))))
          ((SETQ ATM (TYPE-PRESCRIPTION-LEMMAP NAME))

;   NAME is a type prescription lemma hung under ATM.  In this case, we must
;   include in the dependents of NAME all events dependent upon ATM that
;   occurred after NAME was introduced.

;   This clause in the UNDO mechanism is the source of doubt that the mechanism
;   correctly identifies all of the dependents of an event.  The problem starts
;   with the fact that the use of type set lemmas is not tracked like other
;   lemmas.  In fact, no code in the theorem prover actually notes when or how
;   a particular type set lemma is used.  How then can we hope to determine
;   which proofs (or other events) depend upon a type set lemma?  We have tried
;   several approaches to the question.  Some have turned out incorrect.  We
;   believe the current one to be correct.  Our hand-waving proof of its
;   correctness is this.  If a type set lemma about the function FN is used in
;   the proof of THM, then either (1) THM mentions FN, (2) some lemma used in
;   the proof of THM (other than a type set lemma) mentions FN, (3) some lemma
;   used in the proof of THM mentions a function whose definition mentions FN,
;   (3.a) some lemma used in the proof of THM uses a function whose definition
;   mentions a function that either (3.b) mentions FN or (3.c) mentions a
;   function whose definition mentions FN, or ... But we believe that any such
;   lemma introducing FN into the proof is in ALL-LEMMAS-USED when the proof is
;   done and thus has THM as one of its IMMEDIATE-DEPENDENTS0.  To put it in
;   terms of the following code, we believe that there is a "tree-path," i.e.
;   an IMMEDIATE-DEPENDENTS0 path, from FN to THM.  Given that hypothesis, we
;   then correctly identify a superset of the dependents of a type set lemma by
;   the draconian strategy of claiming as a dependent event any event on a
;   tree-path that took place later than the type set lemma.  Note that this
;   computation is not trying to get all of the theorems dependent (somehow)
;   upon the type set lemma in question but only those immediately dependent --
;   i.e., whose proofs might have actually appealed to this type set lemma.  It
;   is assumed that any function using IMMEDIATE-DEPENDENTS-OF to explore the
;   logical graph of events will recurse on each of the dependent events, and
;   thus catch things like THMs dependent upon type set lemmas dependent upon
;   the type set lemma in question.

           (UNION-EQUAL (ITERATE FOR X
                                 IN (TREE-DEPENDENTS (MAIN-EVENT-OF ATM))
                                 WHEN (EVENT1-OCCURRED-BEFORE-EVENT2
                                       NAME X CHRONOLOGY)
                                 COLLECT X)
                        (ITERATE FOR X IN
                                 (GET NAME (QUOTE IMMEDIATE-DEPENDENTS0))
                                 COLLECT X)))
          (T (ITERATE FOR X IN (GET NAME (QUOTE IMMEDIATE-DEPENDENTS0))
                      COLLECT X)))))

(DEFUN IMMEDIATE-SUPPORTERS-OF (NAME)
  (LET (TEMP IDATE)
    (COND ((EQ NAME (QUOTE GROUND-ZERO))
           NIL)
          ((OR (NOT (SYMBOLP NAME))
               (NOT (GET NAME (QUOTE EVENT))))
           (ER HARD (NAME) IMMEDIATE-SUPPORTERS-OF |was| |called| |on| |a|
               |nonevent| |,| (!PPR NAME (QUOTE |.|))))
          (T (SETQ IDATE (GET NAME (QUOTE IDATE)))
             (SETQ TEMP
                   (CONS 'GROUND-ZERO
                         (ITERATE FOR X IN (GET NAME
                                                (QUOTE LOCAL-UNDO-TUPLES))
                                  WHEN (AND (CONSP X)
                                            (EQ (CAR X)
                                                (QUOTE
                                                 IMMEDIATE-DEPENDENTS0)))
                                  COLLECT (CADR X))))

;   TEMP is the list of all "immediate supporters0", that is, the names
;   that claim NAME among their immediate dependents0.  We now wish to add
;   to the supporters every type prescription lemma about every function
;   in mentioned in TEMP, including the satellite functions.  For example,
;   FOO may be a satellite of BAR, BAR might be mentioned in TEMP, and we
;   might find a type prescription lemma about FOO.

             (SETQ
              FNS
              (ITERATE
               FOR X IN TEMP
               WITH ITERATE-ANS
               DO (SETQ ITERATE-ANS
                        (UNION-EQ
                         (ITERATE FOR FN
                                  IN (CONS X (GET X
                                                  (QUOTE SATELLITES)))
                                  WHEN (GET FN (QUOTE TYPE-PRESCRIPTION-LST))
                                  COLLECT FN)
                         ITERATE-ANS))
               FINALLY (RETURN ITERATE-ANS)))
             (UNION-EQ
              TEMP
              (ITERATE
               FOR FN IN FNS
               WITH ITERATE-ANS
               DO
               (SETQ
                ITERATE-ANS
                (UNION-EQ
                 (ITERATE FOR X IN (GET FN (QUOTE TYPE-PRESCRIPTION-LST))
                          WHEN (AND (NOT (EQ (MAIN-EVENT-OF (CAR X))
                                             (MAIN-EVENT-OF FN)))
                                    (< (GET (MAIN-EVENT-OF (CAR X))
                                            (QUOTE IDATE))
                                       IDATE))
                          COLLECT (CAR X))
                 ITERATE-ANS))
               FINALLY (RETURN ITERATE-ANS)))))))
                                       
(DEFUN IMPLIES? (TESTS TERM)
  (MEMBER-EQUAL TERM TESTS))

(DEFUN IMPOSSIBLE-POLYP (POLY)
  (AND (> (ACCESS POLY CONSTANT POLY) 0)
       (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                ALWAYS (>= (CDR PAIR) 0))))

(DEFUN IND-FORMULA (TESTS-AND-ALISTS-LST TERMS CL-SET)

;   TESTS-AND-ALISTS-LST is a such a list that the disjunction of the
;   conjunctions of the TESTS components of the members is T.  Furthermore,
;   there exists a measure M, a well-founded relation R, and a sequence of
;   variables x1, ..., xn such that for each T&Ai in TESTS-AND-ALISTS-LST, for
;   each alist alst in the ALISTS component of T&Ai, the conjunction of the
;   TESTS component, say qi, implies that (R (M x1 ... xn)/alst (M x1 ... xn)).

;   To prove thm, the conjunction of the disjunctions of the members of CL-SET,
;   it is sufficient, by the principle of induction, to prove instead the
;   conjunction of the terms qi & thm' & thm'' ...  -> thm, where the primed
;   terms are the results of substituting the alists in the ALISTS field of the
;   ith member of TESTS-AND-ALISTS-LST into thm.

;   If thm1, thm2, ..., thmn are the disjunctions of the members of CL-SET,
;   then it is sufficient to prove all of the formulas qi & thm' & thm'' ...
;   -> thmj.  This is a trivial proposition fact, to prove (IMPLIES A (AND B
;   C)) it is sufficient to prove (IMPLIES A B) and (IMPLIES A C).

;   The (ITERATE FOR PICK ...) expression below returns a list of clauses whose
;   conjunction propositionally implies qi & thm' & thm'' ...  -> thmj, where
;   TA is the ith member of TESTS-AND-ALISTS-LST and CL is the jth member of
;   CL-SET.  Proof:  Let THM have the form:
;
;        (AND (OR a1 ...)
;             (OR b1 ...)
;             ...
;             (OR z1 ...)).

;   Then qi & thm' & thm'' ... -> thmj has the form:

;       (IMPLIES (AND qi
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))'
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))''
;                     ...
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... )))'''...'
;                thmj).
;
;   Suppose this formula is false for some values of the free variables.  Then
;   under those values, each disjunction in the hypothesis is true.  Thus there
;   exists a way of choosing one literal from each of the disjunctions, all of
;   which are true.  This choice is one of the PICKs below.  But we prove that
;   (IMPLIES (AND qi PICK) thmj).

  (DELETE-TAUTOLOGIES
   (SCRUNCH-CLAUSE-SET
    (ITERATE FOR CL IN CL-SET
             NCONC
             (ITERATE FOR TA IN TESTS-AND-ALISTS-LST
                      NCONC
                      (ITERATE FOR PICK
                               IN
                               (ALL-PICKS
                                (ITERATE
                                 FOR CL1 IN CL-SET
                                 NCONC
                                 (ITERATE
                                  FOR ALIST
                                  IN (ACCESS TESTS-AND-ALISTS
                                             ALISTS TA)
                                  COLLECT
                                  (ITERATE FOR LIT IN CL1
                                           COLLECT (NEGATE-LIT
                                                    (SUBLIS-VAR ALIST
                                                                LIT))))))
                               COLLECT
                               (FORM-INDUCTION-CLAUSE
                                (ITERATE FOR TEST
                                         IN (ACCESS TESTS-AND-ALISTS
                                                    TESTS
                                                    TA)
                                         COLLECT (NEGATE-LIT TEST))
                                PICK CL TERMS)))))))

(DEFUN INDUCT (CL-SET)
  (LET (GET-CANDS-ANS MERGED-CANDS-ANS PICK-HIGH-SCORES-ANS
                      WINNING-CAND INDUCT-ANS COMPUTE-VETOES-ANS
                      FAVOR-COMPLICATED-CANDIDATES-ANS)
    (SETQ
     WINNING-CAND
     (CAR
      (SETQ
       PICK-HIGH-SCORES-ANS
       (PICK-HIGH-SCORES
        (SETQ FAVOR-COMPLICATED-CANDIDATES-ANS
              (FAVOR-COMPLICATED-CANDIDATES
               (SETQ COMPUTE-VETOES-ANS
                     (COMPUTE-VETOES
                      (SETQ MERGED-CANDS-ANS
                            (TRANSITIVE-CLOSURE
                             (SETQ GET-CANDS-ANS
                                   (REMOVE-UNCHANGING-VARS
                                    (ITERATE FOR CL IN CL-SET
                                             NCONC (ITERATE FOR LIT IN CL
                                                            NCONC
                                                            (GET-CANDS LIT)))
                                    CL-SET))
                             (FUNCTION MERGE-CANDS)))))))))))
    (COND (WINNING-CAND (SETQ INDUCT-ANS
                              (IND-FORMULA (ACCESS CANDIDATE
                                                   TESTS-AND-ALISTS-LST
                                                   WINNING-CAND)
                                           (CONS (ACCESS CANDIDATE
                                                         INDUCTION-TERM
                                                         WINNING-CAND)
                                                 (ACCESS CANDIDATE OTHER-TERMS
                                                         WINNING-CAND))
                                           CL-SET))
                        (INFORM-SIMPLIFY (ACCESS CANDIDATE
                                                 TESTS-AND-ALISTS-LST
                                                 WINNING-CAND)
                                         (CONS (ACCESS CANDIDATE
                                                       INDUCTION-TERM
                                                       WINNING-CAND)
                                               (ACCESS CANDIDATE
                                                       OTHER-TERMS
                                                       WINNING-CAND))))
          (T (IO (QUOTE INDUCT)
                 CL-SET NIL (LIST NIL)
                 (LIST (GET-STACK-NAME (CDR STACK)) NIL 0 0 0 0 0))
             (WRAPUP NIL)))
    (SETQ ALL-LEMMAS-USED
          (UNION-EQ (ACCESS JUSTIFICATION LEMMAS
                            (ACCESS CANDIDATE JUSTIFICATION WINNING-CAND))
                    ALL-LEMMAS-USED))
    (IO (QUOTE INDUCT)
        CL-SET NIL INDUCT-ANS
        (LIST (GET-STACK-NAME (CDR STACK))
              WINNING-CAND
              (LENGTH GET-CANDS-ANS)
              (LENGTH MERGED-CANDS-ANS)
              (COND ((EQ COMPUTE-VETOES-ANS MERGED-CANDS-ANS) 0)
                    (T (LENGTH COMPUTE-VETOES-ANS)))
              (LENGTH PICK-HIGH-SCORES-ANS)
              (LENGTH FAVOR-COMPLICATED-CANDIDATES-ANS)))
    INDUCT-ANS))

(DEFUN INDUCT-VARS (CAND)

;   Get all skos occupying controller slots in any of the terms associated with
;   this candidate.

  (ITERATE FOR TERM IN (CONS (ACCESS CANDIDATE INDUCTION-TERM CAND)
                             (ACCESS CANDIDATE OTHER-TERMS CAND))
           WITH ITERATE-ANS DO
           (SETQ ITERATE-ANS
                 (UNION-EQ
                  (ITERATE FOR ARG IN (FARGS TERM) AS I FROM 0
                           WHEN (AND (VARIABLEP ARG)
                                     (ITERATE
                                      FOR MASK
                                      IN
                                      (GET (FFN-SYMB TERM)
                                           (QUOTE CONTROLLER-POCKETS))
                                      THEREIS
                                      (NOT
                                       (CT= 0
                                            (CTLOGAND 1
                                                      (CTASH MASK
                                                             (- I)))))))
                           COLLECT ARG)
                  ITERATE-ANS))
           FINALLY (RETURN ITERATE-ANS)))

(DEFUN INDUCTION-MACHINE (FNNAME TERM TESTS)

;   See the comment for TERMINATION-MACHINE.

  (COND ((OR (VARIABLEP TERM)
             (FQUOTEP TERM)
             (NOT (EQ (FFN-SYMB TERM)
                      (QUOTE IF))))
         (LIST (MAKE TESTS-AND-CASES (REMOVE-REDUNDANT-TESTS TESTS NIL)
                     (UNION-EQUAL (ITERATE FOR TEST IN TESTS
                                           WITH ITERATE-ANS
                                           DO (SETQ ITERATE-ANS
                                                    (UNION-EQUAL
                                                     (ALL-ARGLISTS FNNAME TEST)
                                                     ITERATE-ANS))
                                           FINALLY (RETURN ITERATE-ANS))
                                  (ALL-ARGLISTS FNNAME TERM)))))
        (T (NCONC (INDUCTION-MACHINE FNNAME (FARGN TERM 2)
                                     (APPEND TESTS (LIST (FARGN TERM 1))))
                  (INDUCTION-MACHINE
                   FNNAME
                   (FARGN TERM 3)
                   (APPEND TESTS (LIST (NEGATE-LIT (FARGN TERM 1)))))))))

(DEFUN INFORM-SIMPLIFY (TESTS-AND-ALISTS-LST TERMS)

;   Two of the variables effecting REWRITE are TERMS-TO-BE-IGNORED-BY-REWRITE
;   and EXPAND-LST.  When any term on the former is encountered REWRITE returns
;   it without rewriting it.  Terms on the latter must be calls of defined fns
;   and when encountered are replaced by the rewritten body.

;   We believe that the theorem prover will perform significantly faster on
;   many theorems if, after an induction, it does not waste time (a) trying to
;   simplify the recursive calls introduced in the induction hypotheses and (b)
;   trying to decide whether to expand the terms inducted for in the induction
;   conclusion.  This suspicion is due to some testing done with the idea of
;   "homographication" which was just a jokingly suggested name for the idea of
;   generalizing the recursive calls away at INDUCT time after expanding the
;   induction terms in the conclusion.  Homographication speeded the
;   theorem-prover on many theorems but lost on several others because of the
;   premature generalization.  See the comment in FORM-INDUCTION-CLAUSE.

;   To avoid the generalization at INDUCT time we are going to try using
;   TERMS-TO-BE-IGNORED-BY-REWRITE.  The idea is this, during the initial
;   simplification of a clause produced by INDUCT we will have the recursive
;   terms on TERMS-TO-BE-IGNORED-BY-REWRITE.  When the clause settles down --
;   hopefully it will often be proved first -- we will restore
;   TERMS-TO-BE-IGNORED-BY-REWRITE to its pre-INDUCT value.  Note however that
;   we have to mess with TERMS-TO-BE-IGNORED-BY-REWRITE on a clause by clause
;   basis, not just once in INDUCT.

;   So here is the plan.  INDUCT will set INDUCTION-HYP-TERMS to the list of
;   instances of the induction terms, and will set INDUCTION-CONCL-TERMS to the
;   induction terms themselves.  SIMPLIFY-CLAUSE will look at the history of
;   the clause to determine whether it has settled down since induction.  If
;   not it will bind TERMS-TO-BE-IGNORED-BY-REWRITE to the concatenation of
;   INDUCTION-HYP-TERMS and its old value and will analogously bind EXPAND-LST.
;   A new process, called SETTLED-DOWN-SENT, will be used to mark when in the
;   history the clause settled down.

  (SETQ INDUCTION-CONCL-TERMS TERMS)
  (SETQ INDUCTION-HYP-TERMS
        (ITERATE FOR TA IN TESTS-AND-ALISTS-LST
                 NCONC (ITERATE FOR ALIST IN (ACCESS TESTS-AND-ALISTS
                                                     ALISTS TA)
                                NCONC (SUBLIS-VAR-LST ALIST TERMS)))))

(DEFUN INIT-LEMMA-STACK NIL (SETQ LEMMA-STACK ORIG-LEMMA-STACK) NIL)

(DEFUN INIT-LIB (PROPS VARS)

;   Initialize the variables used to keep track of the state of the theorem
;   prover.

  (KILL-LIB)
  (SETQ LIB-PROPS PROPS)
  (SETQ LIB-VARS VARS)
  (MAKUNBOUND (QUOTE LIB-DATE))
  (MAKUNBOUND (QUOTE LIB-VERSION))
  (ITERATE FOR VAR IN LIB-VARS DO (SET VAR NIL))
  (SETQ LIB-ATOMS-WITH-PROPS NIL)
  (SETQ LIB-ATOMS-WITH-DEFS NIL)
  (MAKUNBOUND (QUOTE LIB-FILE)))

(DEFUN INIT-LINEARIZE-ASSUMPTIONS-STACK NIL
  (SETQ LINEARIZE-ASSUMPTIONS-STACK ORIG-LINEARIZE-ASSUMPTIONS-STACK)
  NIL)

(DEFUN INSURE-FREE-V-ASSUMPTION (VAR TERM1 TERM2)

;   This function implicitly takes the linearize assumptions
;   stack as an arg and modifies it.  The function removes
;   from the top frame of that stack those hyps involving
;   the variable symbol VAR (leaving the top frame containing
;   only terms in which VAR does not occur freely), and returns
;   the term:  (IF var-hyps TERM2 TERM1).  See the comment in
;   REWRITE-FOR.

  (LET ((HYPS (POP-LINEARIZE-ASSUMPTIONS-FRAME))
        (VAR-HYPS NIL))
    (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
    (ITERATE FOR X IN HYPS
             DO
             (COND ((OCCUR VAR X) (SETQ VAR-HYPS (CONS X VAR-HYPS)))
                   (T (PUSH-LINEARIZE-ASSUMPTION X))))
    (COND (VAR-HYPS (FCONS-TERM* (QUOTE IF)
                                 (CONJOIN VAR-HYPS T)
                                 TERM2
                                 TERM1))
          (T TERM2))))

(DEFUN INTERESTING-SUBTERMS (FORM)

;   Returns a list of all of the subterms of FORM that are not variables or
;   quotes or terms whose function symbol is CAR CDR LISTP EQ NOT.  Returns
;   the EQ subterms.  This fact is used to catch and optimize common
;   subexpression evaluation.

  (COND ((VARIABLEP FORM) NIL)
        ((FQUOTEP FORM) NIL)
        ((MEMBER-EQ (FFN-SYMB FORM)
                    (QUOTE (CAR CDR LISTP EQ NOT)))
         (ITERATE FOR ARG IN (FARGS FORM) APPEND (INTERESTING-SUBTERMS ARG)))
        (T (CONS FORM (ITERATE FOR ARG IN (FARGS FORM)
                               APPEND (INTERESTING-SUBTERMS ARG))))))

(DEFUN INTERSECTION-EQ (X Y)
  (ITERATE FOR A IN X WHEN (MEMBER-EQ A Y) COLLECT A))

(DEFUN INTERSECTP (X Y) (ITERATE FOR E IN X THEREIS (MEMBER-EQUAL E Y)))

(DEFUN INTRODUCE-ANDS (X)
  (LET (REST1 REST2)
    (COND ((ATOM X) X)
          ((EQ (CAR X) (QUOTE QUOTE)) X)
          ((MATCH X (*2*IF & & (QUOTE NIL)))
           (SETQ REST1 (INTRODUCE-ANDS (CADR X)))
           (SETQ REST2 (INTRODUCE-ANDS (CADDR X)))
           (COND ((AND (CONSP REST1) (EQ (CAR REST1) (QUOTE AND)))
                  (COND ((AND (CONSP REST2) (EQ (CAR REST2) (QUOTE AND)))
                         (APPEND REST1 (CDR REST2)))
                        (T (APPEND REST1 (CONS REST2 NIL)))))
                 ((AND (CONSP REST2) (EQ (CAR REST2) (QUOTE AND)))
                  (CONS (QUOTE AND) (CONS REST1 (CDR REST2))))
                 (T (LIST (QUOTE AND) REST1 REST2))))
          (T (CONS (CAR X)
                   (ITERATE FOR ARG IN (CDR X)
                            COLLECT (INTRODUCE-ANDS ARG)))))))

(DEFUN INTRODUCE-LISTS (X)
  (LET (REST)
    (COND ((ATOM X) X)
          ((EQ (CAR X) (QUOTE QUOTE)) (KWOTE (CADR X)))
          ((EQ (CAR X) (QUOTE CONS))
           (SETQ REST (INTRODUCE-LISTS (CADDR X)))
           (COND ((NULL REST) (LIST (QUOTE LIST) (INTRODUCE-LISTS (CADR X))))
                 ((AND (CONSP REST) (EQ (CAR REST) (QUOTE LIST)))
                  (CONS (QUOTE LIST)
                        (CONS (INTRODUCE-LISTS (CADR X)) (CDR REST))))
                 (T (LIST (QUOTE CONS)
                          (INTRODUCE-LISTS (CADR X))
                          REST))))
          (T (CONS (CAR X)
                   (ITERATE FOR ARG IN (CDR X)
                            COLLECT (INTRODUCE-LISTS ARG)))))))

(DEFUN INVERT (ALIST)
  (ITERATE FOR PAIR IN ALIST
           COLLECT (CONS (CDR PAIR) (CAR PAIR))))

(DEFUN IPOSITION (FILE N FLG)
  (LET (PAIR)
    (COND ((NULL (SETQ PAIR (ASSOC-EQ FILE IPOSITION-ALIST)))
           (SETQ IPOSITION-ALIST
                 (CONS (SETQ PAIR (CONS FILE 0)) IPOSITION-ALIST))))
    (COND ((NULL N) (CDR PAIR))
          (FLG (PROG1 (CDR PAIR) (RPLACD PAIR (+ N (CDR PAIR)))))
          (T (PROG1 (CDR PAIR) (RPLACD PAIR N))))))

(DEFUN IPRINC (X FILE)
  (IPOSITION FILE
             (COND ((SYMBOLP X) (LENGTH (SYMBOL-NAME X)))
                   (T (OUR-FLATC X)))
             T)
  (PRINC X FILE)
  (IF (AND (OR (NULL FILE)
               (EQ FILE *STANDARD-OUTPUT*))
           FORCE-OUTPUT-ON-STANDARD-OUTPUT)
      (FORCE-OUTPUT FILE)))

(DEFUN ISPACES (N FILE)
  (COND ((<= N 0) NIL)
        (T (IPOSITION FILE N T)
           (ITERATE FOR I FROM 1 TO N DO (WRITE-CHAR #\Space FILE)))))

(DEFUN ITERPRI (FILE) (IPOSITION FILE 0 NIL) (TERPRI FILE))

(DEFUN ITERPRIN (N FILE) (ITERATE FOR I FROM 1 TO N DO (ITERPRI FILE)))

(DEFUN ITERPRISPACES (N FILE)
  (ITERPRI FILE)
  (TABULATE N FILE))

;  We do not provide IPRINT and IPRIN1 in the Common Lisp version
;  because we could not find in CLTL anything like FLATSIZE and
;  using (FORMAT NIL "~S" x) seemed too expensive.

(DEFUN JUMPOUTP (OLD NEW)

;   It is claimed that JUMPOUTP is a mere optimization of the book version of
;   the rewriter.  The proof rests on two observations.  The first is that if
;   any subterm of the rewritten function body fails to satisfy REWRITE-FNCALLP
;   then the entire body fails -- i.e., it does not matter if other parts are
;   super-good.  This means that as soon as we lay our hands on a subterm that
;   is GUARANTEED to survive future rewriting and be returned as part of the
;   value of the REWRITE call in REWRITE-FNCALL we can check that it satisfies
;   REWRITE-FNCALLP and if not, abort then and there.  The second lemma is that
;   if the DEFN-FLG of REWRITE is T then the value of that rewrite will survive
;   to be part of the value computed by the REWRITE call in REWRITE-FNCALL.
;   Proof of this is by inspection of the places REWRITE is called.  In
;   particular, if REWRITE's value is that of a recursive call, the call may be
;   passed the same value of the DEFN-FLG, the DEFN-FLG may be turned on only
;   by REWRITE-FNCALL, and must be NIL in rewriting arguments to non-IFs (which
;   might disappear as a result of higher level rewrites), tests to IF's even
;   on the main path through a defn (because the tests may be eliminated by (IF
;   x y y)) and in rewrite calls to relieve hyps (which do not have any
;   relation to what is seen by the REWRITE-FNCALLP check in REWRITE-FNCALL);
;   the most subtle part of the proof is that if you are simplifying an (IF
;   test left right) that is guaranteed to participate in the value returned to
;   REWRITE-FNCALL, then both the values of left and right will be -- at least,
;   they will be when they are non-trivial values that might possible offend
;   REWRITE-FNCALLP.  The proof of this is by inspection of REWRITE-IF1 which
;   either returns the newly consed up IF of the values, which is perfect, or
;   else returns pieces (i.e., test, or left, or right's value alone) under
;   conditions that guarantee that nothing is lost.  Thus, if the DEFN-FLG is
;   on, JUMPOUTP can call REWRITE-FNCALLP and jump out of the lowest
;   REWRITE-FNCALL if the newly computed value offends it.  Since JUMPOUTP is
;   only called on the branches of IFs there must still be a call of
;   REWRITE-FNCALLP on the final answer in REWRITE-FNCALL since tests (which
;   could have been eliminated by (IF x y y)) might still offend.  Finally, to
;   avoid calling REWRITE-FNCALLP exponentially while backing out of an
;   IF-tree, we do not even bother to call it if the old value of the term was
;   itself an IF, since JUMPOUTP okay'd its branches -- but not its test --
;   earlier.

  (COND ((AND DEFN-FLG (NVARIABLEP OLD)
              (NOT (EQ (FN-SYMB OLD) (QUOTE IF)))
              (NOT (REWRITE-FNCALLP (CAR FNSTACK) NEW)))
         (POP-LEMMA-FRAME) ;In adding the REWRITE-PATH stuff
;I found this POP-LEMMA-FRAME which
;seems unnecessary in the face of
;the coming THROW.

;   Because we accumulate the persistence of stack entries as we pop things
;   off the REWRITE-PATH, we must pop our way back to the point at which we
;   entered the CATCH to which we are about to THROW.

         (COND (REWRITE-PATH-STK-PTR
                (ITERATE UNTIL (INT= REWRITE-PATH-STK-PTR0
                                     REWRITE-PATH-STK-PTR)
                         DO (POP-REWRITE-PATH-FRAME))))
         (THROW (QUOTE REWRITE-FNCALL)
                (LET ((TYPE-ALIST *TYPE-ALIST*))
                  (REWRITE-SOLIDIFY (CONS-TERM *FNNAME* *ARGLIST*)))))
        (T NEW)))

(DEFUN KILL-DEFINITION (ATM)
  (REMPROP ATM (QUOTE SEXPR))
  (FMAKUNBOUND ATM)
  (SETQ LIB-ATOMS-WITH-DEFS (REMOVE ATM LIB-ATOMS-WITH-DEFS)))

(DEFUN KILL-EVENT (NAME)
  (COND ((EQ NAME (QUOTE GROUND-ZERO)) (KILL-LIB))
        (T (ITERATE FOR TUPLE IN (GET NAME (QUOTE LOCAL-UNDO-TUPLES))
                    DO (ADD-SUB-FACT NIL NIL NIL TUPLE NIL))
           (ITERATE FOR SATELLITE IN (GET NAME (QUOTE SATELLITES))
                    DO (KILL-PROP-LIST SATELLITE))
           (KILL-PROP-LIST NAME)
           (SETQ CHRONOLOGY (REMOVE1 NAME CHRONOLOGY))
           NAME)))

(DEFUN KILL-LIB NIL
  
;   Erase all trace of the lib file.
  
  (COND ((BOUNDP (QUOTE LIB-ATOMS-WITH-PROPS))
         (LET ((LST LIB-ATOMS-WITH-PROPS)
               (LIB-ATOMS-WITH-PROPS NIL))
           (ITERATE FOR ATM IN LST DO (KILL-PROP-LIST ATM)))
         (MAKUNBOUND (QUOTE LIB-ATOMS-WITH-PROPS))))
  (COND ((BOUNDP (QUOTE LIB-ATOMS-WITH-DEFS))
         (LET ((LST LIB-ATOMS-WITH-DEFS)
               (LIB-ATOMS-WITH-DEFS NIL))
           (ITERATE FOR FN IN LST DO
                    (KILL-DEFINITION FN)))
         (MAKUNBOUND (QUOTE LIB-ATOMS-WITH-DEFS))))
  (COND ((BOUNDP (QUOTE LIB-VARS))
         (ITERATE FOR VAR IN LIB-VARS DO (MAKUNBOUND VAR))
         (MAKUNBOUND (QUOTE LIB-VARS))))
  (MAKUNBOUND (QUOTE LIB-DATE))
  (MAKUNBOUND (QUOTE LIB-VERSION))
  (MAKUNBOUND (QUOTE LIB-FILE))
  (MAKUNBOUND (QUOTE LIB-PROPS)))

(DEFUN KILL-PROP-LIST (ATM)

;   Kill all properties of ATM that are maintained by the lib file.

  (ITERATE FOR PROP IN LIB-PROPS DO
           (REMPROP ATM PROP))
  (SETQ LIB-ATOMS-WITH-PROPS (REMOVE ATM LIB-ATOMS-WITH-PROPS)))

(DEFUN LEGAL-CHAR-CODE-SEQ (LST)

;   WARNING The EVG-OCCUR functions make delicate use of the ascii codes
;   permitted in litatoms in evgs.

  (AND
   (CONSP LST)
   (ITERATE FOR TAIL ON LST WITH C UNTIL (ATOM TAIL)
            ALWAYS
            (PROGN
              (SETQ C (CAR TAIL))
              (AND (INTEGERP C)
                   (OR (AND (<= (CHAR-CODE #\A) C)
                            (<= C (CHAR-CODE #\Z)))
                       (AND (<= (CHAR-CODE #\0) C)
                            (<= C (CHAR-CODE #\9)))
                       (MEMBER-EQUAL C ASCII-CODES-FOR-LEGAL-SIGNS)))))
   (NOT (MEMBER-EQUAL (CAR LST) ASCII-CODES-FOR-LEGAL-SIGNS))
   (NOT (AND (<= (CHAR-CODE #\0) (CAR LST))
             (<= (CAR LST) (CHAR-CODE #\9))))))

(DEFUN LENGTH-TO-ATOM (L)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (ITERATE FOR TAIL ON L UNTIL (ATOM TAIL) COUNT T))

(DEFUN LEXORDER (X Y)

;   LEXORDER is a total ordering on LISP objects constructed from numbers,
;   litatoms, and conses.  See the comment in TERM-ORDER for the definitions of
;   "partial" and "total" orderings.

  (COND ((ATOM X)
         (COND ((ATOM Y)

;   From the VM one can conclude that ALPHORDER is a total ordering when
;   restricted to ATOMs.

                (ALPHORDER X Y))
               (T T)))
        ((ATOM Y) NIL)
        ((EQUAL (CAR X) (CAR Y))
         (LEXORDER (CDR X) (CDR Y)))
        (T (LEXORDER (CAR X) (CAR Y)))))


(DEFUN LINEARIZE (TERM FLG)

;   If FLG is T linearize TERM, else linearize the negation of TERM.  We store
;   TERM in the LITERALS field regardless of FLG.  ADD-EQUATIONS looks in the
;   LITERALS field to see if the CURRENT-LIT is a father of a POLY and if so
;   does not use it in cancellation.  Similarly ADD-EQUATIONS looks in the
;   LEMMAS field for members of the original clause, i.e.,
;   LITS-THAT-MAY-BE-ASSUMED-FALSE.

  (LET (LHS RHS LST CONTRA)
    (SETQ LST
          (COND ((COND (FLG (MATCH TERM (LESSP LHS RHS)))
                       (T (MATCH TERM (NOT (LESSP LHS RHS)))))
                 (LIST
                  (LIST (COMPRESS-POLY
                         (ADD-LINEAR-TERM
                          (CONS-TERM (QUOTE ADD1) (LIST LHS))
                          (QUOTE POSITIVE)
                          (ADD-LINEAR-TERM RHS (QUOTE NEGATIVE)
                                           (ZERO-POLY TERM)))))))
                ((COND (FLG (MATCH TERM (EQUAL LHS RHS)))
                       (T (MATCH TERM (NOT (EQUAL LHS RHS)))))
                 (COND ((OR (POSSIBLY-NUMERIC LHS)
                            (POSSIBLY-NUMERIC RHS))
                        (LIST
                         (LIST (COMPRESS-POLY
                                (ADD-LINEAR-TERM
                                 LHS
                                 (QUOTE POSITIVE)
                                 (ADD-LINEAR-TERM RHS (QUOTE NEGATIVE)
                                                  (ZERO-POLY TERM))))
                               (COMPRESS-POLY
                                (ADD-LINEAR-TERM
                                 RHS
                                 (QUOTE POSITIVE)
                                 (ADD-LINEAR-TERM LHS (QUOTE NEGATIVE)
                                                  (ZERO-POLY TERM)))))))
                       (T NIL)))
                ((COND (FLG (MATCH TERM (NOT (LESSP LHS RHS))))
                       (T (MATCH TERM (LESSP LHS RHS))))
                 (LIST
                  (LIST (COMPRESS-POLY
                         (ADD-LINEAR-TERM
                          RHS
                          (QUOTE POSITIVE)
                          (ADD-LINEAR-TERM LHS (QUOTE NEGATIVE)
                                           (ZERO-POLY TERM)))))))
                ((COND (FLG (MATCH TERM (NOT (EQUAL LHS RHS))))
                       (T (MATCH TERM (EQUAL LHS RHS))))
                 (COND ((OR (POSSIBLY-NUMERIC LHS)
                            (POSSIBLY-NUMERIC RHS))
                        (LIST
                         (LIST
                          (ADD-NUMBERP-ASSUMPTION-TO-POLY
                           LHS
                           (ADD-NUMBERP-ASSUMPTION-TO-POLY
                            RHS
                            (COMPRESS-POLY
                             (ADD-LINEAR-TERM
                              (CONS-TERM (QUOTE ADD1)
                                         (LIST LHS))
                              (QUOTE POSITIVE)
                              (ADD-LINEAR-TERM RHS (QUOTE NEGATIVE)
                                               (ZERO-POLY TERM)))))))
                         (LIST
                          (ADD-NUMBERP-ASSUMPTION-TO-POLY
                           LHS
                           (ADD-NUMBERP-ASSUMPTION-TO-POLY
                            RHS
                            (COMPRESS-POLY
                             (ADD-LINEAR-TERM
                              (CONS-TERM (QUOTE ADD1)
                                         (LIST RHS))
                              (QUOTE POSITIVE)
                              (ADD-LINEAR-TERM LHS (QUOTE NEGATIVE)
                                               (ZERO-POLY TERM)))))))))
                       (T NIL)))
                (T NIL)))
    (SETQ LST (ITERATE FOR L IN LST
                       COLLECT (ITERATE FOR POLY IN L
                                        UNLESS (MEMBER-EQUAL
                                                FALSE
                                                (ACCESS POLY
                                                        ASSUMPTIONS
                                                        POLY))
                                        COLLECT POLY)))
    (COND ((INT= (LENGTH LST) 2)

;   If either member of LST contains a contradiction, we delete that member
;   from LST after moving into each member of the other member of LST the
;   assumptions and lemmas upon which the contradiction depends.

           (COND ((SETQ CONTRA (ITERATE FOR POLY IN (CAR LST)
                                        WHEN (IMPOSSIBLE-POLYP POLY)
                                        DO (RETURN POLY)))
                  (ITERATE FOR POLY IN (CADR LST) DO
                           (PROGN
                             (CHANGE
                              POLY ASSUMPTIONS POLY
                              (UNION-EQUAL (ACCESS POLY ASSUMPTIONS CONTRA)
                                           (ACCESS POLY ASSUMPTIONS POLY)))
                             (CHANGE POLY LEMMAS POLY
                                     (UNION-EQ (ACCESS POLY LEMMAS CONTRA)
                                               (ACCESS POLY
                                                       LEMMAS POLY)))))
                  (SETQ LST (LIST (CADR LST))))
                 ((SETQ CONTRA (ITERATE FOR POLY IN (CADR LST)
                                        WHEN (IMPOSSIBLE-POLYP POLY)
                                        DO (RETURN POLY)))
                  (ITERATE FOR POLY IN (CAR LST) DO
                           (PROGN (CHANGE POLY ASSUMPTIONS POLY
                                          (UNION-EQUAL
                                           (ACCESS POLY ASSUMPTIONS CONTRA)
                                           (ACCESS POLY ASSUMPTIONS POLY)))
                                  (CHANGE POLY LEMMAS POLY
                                          (UNION-EQ (ACCESS POLY LEMMAS CONTRA)
                                                    (ACCESS POLY
                                                            LEMMAS POLY)))))
                  (SETQ LST (LIST (CAR LST)))))))    
    LST))

(DEFUN LISTABLE-EVG-PAIRS (EVG)
  (COND ((ATOM EVG) NIL)
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK) NIL)
        ((NULL (CDR EVG)) (LIST (CAR EVG)))
        ((SETQ TEMP-TEMP (LISTABLE-EVG-PAIRS (CDR EVG)))
         (CONS (CAR EVG) TEMP-TEMP))
        (T NIL)))

(DEFUN LOOKUP-HYP (HYP)

;   See if HYP is true by type alist or LITS-THAT-MAY-BE-ASSUMED-FALSE
;   considerations -- possibly extending the UNIFY-SUBST if necessary.  If
;   successful return T and side-effect UNIFY-SUBST and the current lemma frame
;   appropriately.  If unsuccessful, return NIL and side-effect nothing.

  (PROG (TERM NOT-FLG TYPE NEG-HYP LIT)
        (COND ((MATCH HYP (NOT TERM)) (SETQ NOT-FLG T))
              (T (SETQ NOT-FLG NIL) (SETQ TERM HYP)))
        (COND ((AND (NVARIABLEP TERM)
                    (NOT (FQUOTEP TERM))
                    (SETQ TEMP-TEMP (ASSOC-EQ (FFN-SYMB TERM)
                                              RECOGNIZER-ALIST)))
               (SETQ TYPE (CDR TEMP-TEMP))
               (SETQ TERM (FARGN TERM 1)))
              (T (SETQ TYPE (TSLOGNOT TYPE-SET-FALSE))))
        (COND (NOT-FLG (COND ((ITERATE FOR PAIR IN TYPE-ALIST
                                       THEREIS
                                       (AND
                                        (TS= 0 (TSLOGAND TYPE (CDR PAIR)))
                                        (ONE-WAY-UNIFY1
                                         TERM (CAR PAIR))))
                              (RETURN T))))
              (T (COND ((ITERATE FOR PAIR IN TYPE-ALIST
                                 THEREIS (AND (TSLOGSUBSETP (CDR PAIR) TYPE)
                                              (ONE-WAY-UNIFY1 TERM
                                                              (CAR PAIR))))
                        (RETURN T)))))

;   Having failed to find HYP on the type alist, we now try
;   LITS-THAT-MAY-BE-ASSUMED-FALSE.

        (COND (LITS-THAT-MAY-BE-ASSUMED-FALSE
               (SETQ NEG-HYP (DUMB-NEGATE-LIT HYP))
               (COND ((SETQ LIT (ITERATE FOR LIT IN
                                         LITS-THAT-MAY-BE-ASSUMED-FALSE
                                         WHEN (ONE-WAY-UNIFY1 NEG-HYP LIT)
                                         DO (RETURN LIT)))
                      (PUSH-LEMMA LIT)
                      (RETURN T))
                     (T (RETURN NIL))))
              (T (RETURN NIL)))))

(DEFUN LOOP-STOPPER (TERM)
  (LET (LHS RHS ALL-VARS)
    (COND ((AND (OR (MATCH TERM (EQUAL LHS RHS))
                    (MATCH TERM (IFF LHS RHS)))
                (VARIANTP LHS RHS))
           (SETQ ALL-VARS (ALL-VARS LHS))
           (ITERATE FOR PAIR IN UNIFY-SUBST
                    WHEN (MEMBER-EQ (CAR PAIR) (CDR (MEMBER-EQ
                                                     (CDR PAIR)
                                                     ALL-VARS)))
                    COLLECT PAIR))
          (T NIL))))

(DEFUN MAYBE-OPENABLE (X)
  (AND (NOT (EQ X T))
       (NOT (EQ X NIL))
       (STRINGP X)))

(DEFUN MAIN-EVENT-OF (NAME)
  (COND ((AND (SYMBOLP NAME) (GET NAME (QUOTE EVENT)))
         NAME)
        ((AND (SYMBOLP NAME) (GET NAME (QUOTE MAIN-EVENT))))
        (T (ER HARD (NAME) MAIN-EVENT-OF |has| |been| |called| |on| |an|
               |object| |,| |namely| (!PPR NAME (QUOTE |,|)) |that| |is|
               |neither| |an| |event| |nor| |a| |satellite| |of| |another|
               |event| EXCL))))

(DEFUN MAINTAIN-REWRITE-PATH (FLG)

;   When called with T, this function turns on the maintenance of the
;   REWRITE-PATH-STK, which describes what the rewriter is doing.  When
;   called with NIL, maintenance is shut down.

; We once called (CHK-COMMAND-STATUS NIL) here to prevent the user from turning
; on path maintenance in the middle of a proof.  (That can result in hard
; errors.)  But that also prevented Matt Wilding from calling BREAK-LEMMA
; inside of a break, which is a commonly used technique for getting a
; frequently used lemma broken at the right time.

  (COND (FLG
         (COND ((NULL REWRITE-PATH-STK)
                (PROG1
                 (LET ((REWRITE-PATH-STK-LENGTH 100))
                   (SETQ REWRITE-PATH-STK
                         (MAKE-ARRAY REWRITE-PATH-STK-LENGTH
                                     :INITIAL-CONTENTS
                                     (ITERATE FOR I FROM 1 TO
                                              REWRITE-PATH-STK-LENGTH
                                              COLLECT
                                              (MAKE REWRITE-PATH-FRAME
                                                    0 ;prog
                                                    0 ;cnt
                                                    0 ;loc
                                                    0 ;term
                                                    0 ;alist
                                                    )))))
                 (SETQ REWRITE-PATH-STK-LENGTH 100))))
         (COND ((NULL REWRITE-PATH-STK-PTR)
                (SETQ REWRITE-PATH-STK-PTR -1)))
         T)
        (T (IF BROKEN-LEMMAS
               (ER WARNING (BROKEN-LEMMAS)
                   |Rewrite| |path| |maintenance|
                   |has| |been| |disabled| |.| |However|
                   |,| |the| |following|
                   (PLURAL? BROKEN-LEMMAS
                            (progn |lemmas| |are|)
                            (progn |lemma| |is|))
                   |still| |broken| |:|
                   (!PPR-LIST BROKEN-LEMMAS (QUOTE |.|))
                   |If| |a| |broken| |lemma| |is| |applied| |,|
                   |an| |interactive| |break| |will|
                   |occur| |but| |no| |path| |information|
                   |will| |be| |available| |.|))
           (SETQ REWRITE-PATH-STK-PTR NIL))))

(DEFUN MAKE-EVENT (NAME EVENT)
  (PUT1 NAME EVENT (QUOTE EVENT))
  (PUT1 NAME (IDATE) (QUOTE IDATE))
  (SETQ CHRONOLOGY (CONS NAME CHRONOLOGY))
  (SETQ MAIN-EVENT-NAME NAME))

(DEFUN MAKE-LIB (FILE &OPTIONAL COMPILE-FLG)
  (CHK-COMMAND-STATUS NIL)
  (COND (PETITIO-PRINCIPII
         (RETURN-FROM MAKE-LIB T)))
  (LET ((*READ-BASE* 10)
        (*PRINT-BASE* 10)
        (*READTABLE* (COPY-READTABLE NIL))
        *PRINT-RADIX*
        *PRINT-PRETTY*
        *PRINT-LEVEL*
        *PRINT-LENGTH*
        (*PRINT-CASE* :UPCASE)
        TEMP PROP-FILE FN-FILE PROP-FILE-NAME FN-FILE-NAME
        (DATE (IDATE)))
    (CHK-INIT)
    (PRINC (FORMAT NIL "~%Making the lib for ~s.~%" FILE) PROVE-FILE)
    (ITERPRI PROVE-FILE)
    (SETQ PROP-FILE (OPEN (EXTEND-FILE-NAME FILE FILE-EXTENSION-LIB)
                          :DIRECTION :OUTPUT
                          :IF-EXISTS :RENAME-AND-DELETE))
    (FORMAT PROP-FILE
            ";;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; ~
            Base: 10 -*- ;;;; ~%(IN-PACKAGE \"USER\")~2%")

    (SETQ PROP-FILE-NAME
          (NAMESTRING (TRUENAME PROP-FILE)))
    (TERPRI PROP-FILE)
    (PRINC (QUOTE |;   Creation date:  |) PROP-FILE)
    (PRINT-IDATE DATE PROP-FILE)
    (TERPRI PROP-FILE)
    (PRINC (QUOTE |;   Created as:  |) PROP-FILE)
    (PRINC PROP-FILE-NAME PROP-FILE)
    (TERPRI PROP-FILE)
    (TERPRI PROP-FILE)
    (PRINC "(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))"
           PROP-FILE)
    (TERPRI PROP-FILE)
    (PRINT (LIST (QUOTE INIT-LIB) (KWOTE LIB-PROPS) (KWOTE LIB-VARS))
           PROP-FILE)
    (PRINT (LIST (QUOTE SETQ) (QUOTE LIB-DATE) DATE) PROP-FILE)
    (PRINT (LIST (QUOTE SETQ) (QUOTE LIB-VERSION)
                 (KWOTE THEOREM-PROVER-LIBRARY-VERSION))
           PROP-FILE)
    (ITERATE FOR VAR IN LIB-VARS
             DO (PRINT
                 (LIST (QUOTE SETQ) VAR (KWOTE (SYMBOL-VALUE VAR)))
                 PROP-FILE))
    (PRINT (LIST (QUOTE SETQ)
                 (QUOTE LIB-ATOMS-WITH-PROPS)
                 (KWOTE LIB-ATOMS-WITH-PROPS))
           PROP-FILE)
    (PRINT (LIST (QUOTE SETQ)
                 (QUOTE LIB-ATOMS-WITH-DEFS)
                 (KWOTE LIB-ATOMS-WITH-DEFS))
           PROP-FILE)
    (ITERATE FOR ATM IN LIB-ATOMS-WITH-PROPS DO
             (PRINT
              (LIST
               (QUOTE PUT1-LST)
               (KWOTE ATM)
               (KWOTE
                (ITERATE FOR PROP IN LIB-PROPS
                         NCONC
                         (PROGN
                           (SETQ TEMP (GET ATM PROP A-VERY-RARE-CONS))  
                           (COND ((NOT (EQ A-VERY-RARE-CONS TEMP))
                                  (LIST PROP TEMP)))))))
              PROP-FILE))
    (ITERATE FOR ATM IN (REVERSE LIB-ATOMS-WITH-DEFS) WITH TEMP DO
             (PROGN 
               (SETQ TEMP
                     (GET ATM
                          (QUOTE SEXPR)))
               (PRINT
                (LIST (QUOTE PUT1-LST)
                      (KWOTE ATM)
                      (KWOTE (LIST (QUOTE SEXPR)
                                   (LIST (QUOTE LAMBDA)
                                         (CADR TEMP)
                                         (CADDR TEMP)))))
                PROP-FILE)))
    (CLOSE PROP-FILE)
    (SETQ FN-FILE (OPEN (EXTEND-FILE-NAME FILE FILE-EXTENSION-LISP)
                        :DIRECTION :OUTPUT
                        :IF-EXISTS :RENAME-AND-DELETE))
    (FORMAT FN-FILE
            ";;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: ~
             10 -*- ;;;; ~%(IN-PACKAGE \"USER\")~2%")
    (SETQ FN-FILE-NAME
          (NAMESTRING (TRUENAME FN-FILE)))
    (TERPRI FN-FILE)
    (PRINC (QUOTE |;   Creation date:  |) FN-FILE)
    (PRINT-IDATE DATE FN-FILE)
    (TERPRI FN-FILE)
    (PRINC (QUOTE |;   Created as:  |) FN-FILE)
    (PRINC FN-FILE-NAME FN-FILE)
    (TERPRI FN-FILE)
    (PRINC (QUOTE |;   Associated file:  |) FN-FILE)
    (PRINC PROP-FILE-NAME FN-FILE)
    (TERPRI FN-FILE)
    (PRINC "(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))"
           FN-FILE)
    (TERPRI FN-FILE)
    (PRINT `(COND ((NOT (EQUAL LIB-DATE ,DATE))
                   (ERROR1 (QUOTE (PROGN |Attempt| |to| |load| |the|
                                         |wrong| |.lisp| |or| |compiled|
                                         |file| EXCL |the| |variable|
                                         |LIB-DATE| |has| |the| |value|
                                         (!PPR LIB-DATE NIL) |,|
                                         |but| |the| |date| |in| |the|
                                         |.lisp| |or| |compiled|
                                         |file| |is| (!PPR DATE NIL) |.|
                                         ))
                           (LIST (CONS 'LIB-DATE LIB-DATE)
                                 (CONS 'DATE ,DATE))
                           (QUOTE HARD))))
           FN-FILE)
    (ITERATE FOR ATM IN (REVERSE LIB-ATOMS-WITH-DEFS) WITH TEMP DO
             (PROGN (SETQ TEMP (GET ATM (QUOTE SEXPR)))
                    (PRINT (LIST (QUOTE DEFUN)
                                 ATM
                                 (CADR TEMP)
                                 (CADDR TEMP))
                           FN-FILE)))
;  Once upon a time we did this, but changed it for Release 7.  See
;  NOTE-LIB1.

;   (PRINT (LIST (QUOTE COMPILE-IF-APPROPRIATE-AND-POSSIBLE)
;                    (QUOTE LIB-ATOMS-WITH-DEFS))
;              FN-FILE)

    (CLOSE FN-FILE)
    (SETQ LIB-DATE DATE)
    (COND (COMPILE-FLG
           (PRINC
            (FORMAT NIL "~%Compiling the lib for ~s.~%" FILE)
            PROVE-FILE)
           (ITERPRI PROVE-FILE) 
           (COMPILE-FILE FN-FILE-NAME)
           (LOAD (EXTEND-FILE-NAME FILE FILE-EXTENSION-BIN))
           (PRINC
            (FORMAT NIL "~%Finished compiling the lib for ~s.~%" FILE)
            PROVE-FILE)
           (ITERPRI PROVE-FILE)))
    (SETQ LIB-FILE (EXTEND-FILE-NAME FILE FILE-EXTENSION-LIB))
    (PRINC (FORMAT NIL "~%Finished making the lib for ~s.~%" FILE)
           PROVE-FILE)
    (ITERPRI PROVE-FILE)
    (LIST PROP-FILE-NAME FN-FILE-NAME)))

(DEFUN MAKE-NEW-NAME (NAME)

;   Generates a new event name from name.  If name is new,
;   use it.  Otherwise successively try NAMEi for i=1, 2, ...
;   until a new name is found.  We assume that the initial
;   name is either a legal name (though perhaps not new) or
;   else is a legal *1* name.  If the latter, we add a G to
;   it to make it a legal name before trying anything else.

  (LET (TEMP)
    (COND ((ITERATE FOR I FROM 1 TO 3
                    AS C1 IN (OUR-EXPLODEN PREFIX-FOR-FUNCTIONS)
                    AS C2 IN (OUR-EXPLODEN NAME)
                    ALWAYS (INT= C1 C2))
           (SETQ NAME (PACK (LIST 'G NAME)))))
;   Once this function had a bug in it that caused it run forever.
;   The problem was that it was called on a NAME such that neither
;   NAME nor NAMEi was legal for any i.  Therefore, we now check
;   whether NAME is legal (though perhaps not new) first.  This
;   guarantees that CHK-NEW-NAME will eventually succeed:  it checks
;   three things:  legality, not propertyless, and no props.  If NAME
;   is legal so is every NAMEi.  Not every NAMEi is propertyless --
;   indeed no name ending in a digit is propertyless.  And there are
;   only a finite number of names with props.

    (COND ((ILLEGAL-NAME NAME)
           (ER HARD (NAME) MAKE-NEW-NAME |was| |called| |with| |an| |illegal|
               |initial| |name| |,| (!PPR NAME (QUOTE |.|))))
          ((NULL (CHK-NEW-NAME NAME T))
           (ITERATE FOR I FROM 1
                    WHILE
                    (NULL (CHK-NEW-NAME
                           (SETQ TEMP (PACK (LIST NAME I)))
                           T))
                    DO (OR NIL)) 

; We used to just do NIL, but this works around a cmulisp problem.

           TEMP)
          (T NAME))))

(DEFUN MAKE-REWRITE-RULES (NAME HYPS CONCL)

;   This fn once entertained the idea of returning as many rewrite rules as
;   there were paths through the IF structure of HYPS.  That blew us out of the
;   water on a thm whose hyp was (AND (NOT (EQUAL X Y)) (NOT (LESSP X Y)))
;   because it generated 75 paths!  So the fn now returns just one rewrite rule
;   -- or none if CONCL is an explicit value.  The rule is LISTed so that the
;   higher level functions still allow the possibility of it someday returning
;   more than one -- BUT they are all hung under the same fn symbol so this
;   probably is not a useful feature.

  (PROG (LHS RHS)
        (COND ((QUOTEP CONCL) (RETURN NIL))
              ((OR (MATCH CONCL (EQUAL LHS RHS))
                   (MATCH CONCL (IFF LHS RHS)))
               (SETQ CONCL (LIST (FN-SYMB CONCL)
                                 LHS
                                 (NORMALIZE-IFS
                                  (EXPAND-BOOT-STRAP-NON-REC-FNS RHS)
                                  NIL NIL
                                  (EQ (FN-SYMB CONCL) (QUOTE IFF)))))))
        (RETURN (LIST (CREATE-REWRITE-RULE NAME HYPS CONCL NIL)))))

(DEFUN MAKE-ALIST (VAR WHEN BODY)
  (CONSJOIN
   (NCONC1
    (ITERATE FOR V IN (UNSTABLE-SORT (UNION-EQ (ALL-VARS WHEN) (ALL-VARS BODY))
                                     (FUNCTION ALPHORDER))
             UNLESS (EQ VAR V)
             COLLECT (CONS-TERM (QUOTE CONS)
                                (LIST (LIST (QUOTE QUOTE) V) V)))
    (QUOTE (QUOTE NIL)))))

#|
(DEFUN MAKE-DECLARE-FORM (FORM)
;  Beware.  This function is duplicated in nqthm.lisp.
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

|#

(DEFUN MAKE-DISABLEDP-HASH-FROM-GLOBAL-DATA (HASH-TABLE)
  (CLRHASH HASH-TABLE)
  (ITERATE FOR X IN (REVERSE DISABLED-LEMMAS)
           DO
           (IF (CDDR X)
               (ADD-NAME-TO-HASH (CAR X) HASH-TABLE)
               (REMOVE-NAME-FROM-HASH (CAR X) HASH-TABLE))))

(DEFUN MAKE-GLOBAL-DISABLEDP-HASH ()
  (MAKE-DISABLEDP-HASH-FROM-GLOBAL-DATA GLOBAL-DISABLEDP-HASH)
  (SETQ GLOBAL-DISABLEDP-HASH-LIST DISABLED-LEMMAS)
  GLOBAL-DISABLEDP-HASH)

(DEFUN MAKE-LOCAL-DISABLEDP-HASH (TEMP-ENABLED TEMP-DISABLED)
  (COND 
   ((EQ TEMP-DISABLED T)
    (CLRHASH LOCAL-DISABLEDP-HASH)
    (ITERATE FOR X IN TEMP-ENABLED
             DO (ADD-NAME-TO-HASH X LOCAL-DISABLEDP-HASH)))
   ((EQ TEMP-ENABLED T)
    (CLRHASH LOCAL-DISABLEDP-HASH)
    (ITERATE FOR X IN TEMP-DISABLED
             DO (ADD-NAME-TO-HASH X LOCAL-DISABLEDP-HASH)))
   (T
    (MAKE-DISABLEDP-HASH-FROM-GLOBAL-DATA LOCAL-DISABLEDP-HASH)
    (ITERATE FOR X IN TEMP-DISABLED
             DO (ADD-NAME-TO-HASH X LOCAL-DISABLEDP-HASH))
    (ITERATE FOR X IN TEMP-ENABLED
             DO (REMOVE-NAME-FROM-HASH X LOCAL-DISABLEDP-HASH))))
  LOCAL-DISABLEDP-HASH)

(DEFUN MAKE-LOCAL-FS (FS TERM)

; This function exists so that each functional subsitution
; occurring in the JUSTIFICATIONS property for a
; FUNCTIONALLY-INSTANTIATE event appears in a standardized order.
; It is also used to "pare down" a functional substitution to the
; function symbols actually occurring in the term in question.
; That way, we can use EQUAL to test the equality of two functional
; substitutions, when each has the same domain.

  (LET ((FNNAMES (ALL-FNNAMES TERM)))
    (OUR-STABLE-SORT
     (ITERATE FOR PAIR IN FS
              WHEN (MEMBER-EQ (CAR PAIR) FNNAMES)
              COLLECT PAIR)
     (FUNCTION (LAMBDA (X Y) (ALPHORDER (CAR X) (CAR Y)))))))

(DEFUN MAKE-SET! (L)
; Destructively remove EQ duplicates from L.
  (DELETE-DUPLICATES L :TEST #'EQ))

(DEFUN MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST (TERM)
  (COND ((EQUAL TERM (QUOTE (QUOTE NIL)))
         NIL)
        (T (CONS (CONS (CADR (ARGN (ARGN TERM 1) 1))
                       (ARGN (ARGN TERM 1) 2))
                 (MAKE-SUBSTITUTION-FROM-SEMI-CONCRETE-ALIST (ARGN TERM 2))))))

(DEFUN MAKE-TAMEP-SUBST (TERM)

; Returns a substitution s such that term' = (SUBLIS-EXPR1 s TERM) is TAMEP
; and such that term'/(invert s) = TERM.

; As noted in rewrite-with-lemmas, Matt Kaufmann first proposed the
; handling of metalemmas that motivated the creation of this function.
; The first version of this function used GENTEMP to generate new
; variable names.  We learned that during the course of our
; benchmarking 80,000 GENTEMP symbols were hanging around and (because
; of a bug) CMU lisp was searching all of them every time it generated
; a new one.  Matt observed that the metalemma treatment did not
; require "globally" new variables, just "locally" new ones and
; implemented this new version of MAKE-TAMEP-SUBST.

  (LET ((NEW-VAR-INDEX 0))
    (MAKE-TAMEP-SUBST1 TERM TERM)))

(DEFUN MAKE-TAMEP-SUBST1 (TERM ORIG-TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        ((TOTALP (FFN-SYMB TERM))
         (ITERATE FOR ARG IN (FARGS TERM)
                  NCONC (MAKE-TAMEP-SUBST1 ARG ORIG-TERM)))
        (T (LIST (CONS TERM (NEW-TAMEP-SUBST-VAR ORIG-TERM))))))

(DEFUN MAKE-TYPE-RESTRICTION (TR DV RECOGNIZER TYPE-NO)
  (LET (TYPE-SET)
    (SETQ TYPE-SET
          (ITERATE FOR R IN (CDR TR) WITH ITERATE-ANS = 0 DO
                   (SETQ ITERATE-ANS
                         (TSLOGIOR ITERATE-ANS
                                   (CDR (ASSOC-EQ
                                         R
                                         (CONS (CONS RECOGNIZER
                                                     (TSLOGBIT
                                                      TYPE-NO))
                                               RECOGNIZER-ALIST)))))
                   FINALLY (RETURN ITERATE-ANS)))
    (COND ((EQ (CAR TR) (QUOTE NONE-OF))
           (SETQ TYPE-SET (TSLOGNOT TYPE-SET))))
    (MAKE
     TYPE-RESTRICTION
     (COND ((EQ (CAR TR) (QUOTE ONE-OF))
            (DISJOIN (ITERATE FOR R IN (CDR TR)
                              COLLECT (FCONS-TERM* R (QUOTE X)))
                     NIL))
           (T (CONJOIN (ITERATE FOR R IN (CDR TR)
                                COLLECT
                                (DUMB-NEGATE-LIT (FCONS-TERM* R (QUOTE X))))
                       NIL)))
     TYPE-SET
     (CONS-TERM DV NIL))))

(DEFUN MAYBE-IGNORE-SOME-ARGS (ARGS BODY)
  (COND ((NULL ARGS) BODY)
        (T `(PROGN ,@(ITERATE FOR ARG IN ARGS COLLECT
                              (PACK (LIST PREFIX-FOR-FORMALS
                                          ARG)))
                   ,BODY))))

(DEFUN MAYBE-MONITOR (NAME FLG CODE)
  (COND (FLG CODE)
        (T `(LET ((REDUCE-TERM-CLOCK (1- REDUCE-TERM-CLOCK)))
              (COND ((INT= 0 REDUCE-TERM-CLOCK)
                     (IPRINC (QUOTE ,NAME) COMMENT-WINDOW)
                     (IPRINC (QUOTE | aborted.  |) COMMENT-WINDOW)
                     (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))
                    (T ,CODE))))))

(DEFUN MAX-FORM-COUNT (X)
  (COND ((VARIABLEP X) 0)
        ((FQUOTEP X)

;   MAX-FORM-COUNT once used FORM-COUNT-EVG to compute the size of an evg.  But
;   that function computed MAX-FORM-COUNT for 1000 that was bigger than for 999
;   and so the REWRITE package believed it was making progress and would open
;   up something like (LESSP X 1000).  We have decided to try just measuring
;   the LISP size of the evg, as a better estimation of whether we are making
;   progress.

         (CONS-COUNT (CADR X)))
        ((EQ (FFN-SYMB X) (QUOTE IF))
         (MAX (MAX-FORM-COUNT (FARGN X 2))
              (MAX-FORM-COUNT (FARGN X 3))))
        (T (1+ (ITERATE FOR ARG IN (FARGS X) SUM (MAX-FORM-COUNT ARG))))))

(DEFUN MAXIMAL-ELEMENTS (LST MEASURE)
  (LET (ANS MAX TEMP)
    (ITERATE FOR X IN LST DO
             (PROGN (SETQ TEMP (FUNCALL MEASURE X))
                    (COND ((OR (NULL MAX) (> TEMP MAX))
                           (SETQ MAX TEMP)
                           (SETQ ANS (LIST X)))
                          ((EQUAL TEMP MAX)
                           (SETQ ANS (NCONC1 ANS X))))))
    ANS))

(DEFUN MEMB-NEGATIVE (LIT CL)
  (COND ((ATOM CL) NIL)
        ((COMPLEMENTARYP LIT (CAR CL)) T)
        (T (MEMB-NEGATIVE LIT (CDR CL)))))

(DEFUN MERGE-CAND1-INTO-CAND2 (CAND1 CAND2)

;   Note: The guts of this function is MERGE-TESTS-AND-ALISTS-LSTS.  The tests
;   preceding it are heuristic only.  If MERGE-TESTS-AND-ALISTS-LSTS returns
;   non-NIL then it returns a sound induction; indeed, it merely extends some
;   of the substitutions in the second candidate.

  (LET (SCORE1 CONTROLLERS1 CHANGED-VARS1 UNCHANGEABLES1
               TESTS-AND-ALISTS-LST1 TERM1 OTHER-TERMS1
               SCORE2 CONTROLLERS2 CHANGED-VARS2 UNCHANGEABLES2
               TESTS-AND-ALISTS-LST2 JUSTIFICATION2 TERM2 OTHER-TERMS2
               ALISTS TESTS-AND-ALISTS-LST VARS) 
      (MATCH CAND1 (CANDIDATE SCORE1 CONTROLLERS1 CHANGED-VARS1
                              UNCHANGEABLES1 TESTS-AND-ALISTS-LST1
                              & TERM1 OTHER-TERMS1))
      (MATCH CAND2 (CANDIDATE SCORE2 CONTROLLERS2 CHANGED-VARS2
                              UNCHANGEABLES2 TESTS-AND-ALISTS-LST2
                              JUSTIFICATION2 TERM2 OTHER-TERMS2))

;   We once merged only if both cands agreed on the intersection of the
;   CHANGED-VARS.  But the theorem that, under suitable conditions, (EV FLG X
;   VA FA N) = (EV FLG X VA FA K) made us realize it was important only to
;   agree on the intersection of the controllers.  Note in fact that we mean
;   the changing controllers -- there seems to be no need to merge two
;   inductions if they only share unchanging controllers.  However the theorem
;   that (GET I (SET J VAL MEM)) = ... (GET I MEM) ...  illustrates the
;   situation in which the controllers, {I} and {J} do not even overlap; but
;   the accumulators {MEM} do and we want a merge.  So we want agreement on the
;   intersection of the changing controllers (if that is nonempty) or on the
;   accumulators.

;   For soundness it does not matter what list of vars we want to agree on
;   because no matter what, MERGE-TESTS-AND-ALISTS-LSTS returns either NIL or
;   an extension of the second candidates alists.

      (AND (SETQ VARS
                 (OR (INTERSECTION-EQ
                      CONTROLLERS1
                      (INTERSECTION-EQ CONTROLLERS2
                                       (INTERSECTION-EQ
                                        CHANGED-VARS1
                                        CHANGED-VARS2)))
                     (INTERSECTION-EQ CHANGED-VARS1 CHANGED-VARS2)))
           (NOT (INTERSECTP UNCHANGEABLES1 CHANGED-VARS2))
           (NOT (INTERSECTP UNCHANGEABLES2 CHANGED-VARS1))
           (SETQ TESTS-AND-ALISTS-LST
                 (MERGE-TESTS-AND-ALISTS-LSTS TESTS-AND-ALISTS-LST1
                                              TESTS-AND-ALISTS-LST2
                                              VARS))
           (MAKE CANDIDATE (+ SCORE1 SCORE2)
                 (UNION-EQ CONTROLLERS1 CONTROLLERS2)
                 (UNION-EQ CHANGED-VARS1 CHANGED-VARS2)
                 (UNION-EQ UNCHANGEABLES1 UNCHANGEABLES2)
                 TESTS-AND-ALISTS-LST JUSTIFICATION2 TERM2
                 (ADD-TO-SET TERM1
                             (UNION-EQUAL OTHER-TERMS1 OTHER-TERMS2))))))

(DEFUN MERGE-CANDS (CAND1 CAND2)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (OR (FLUSH-CAND1-DOWN-CAND2 CAND1 CAND2)
      (FLUSH-CAND1-DOWN-CAND2 CAND2 CAND1)
      (MERGE-CAND1-INTO-CAND2 CAND1 CAND2)
      (MERGE-CAND1-INTO-CAND2 CAND2 CAND1)))

(DEFUN MERGE-DESTRUCTOR-CANDIDATES (LST)

;   The elements of LST are lists of terms.  Whenever the CARs of two elements
;   are EQUAL we UNION together the CDRs.

  (TRANSITIVE-CLOSURE LST (FUNCTION (LAMBDA (X Y)
                                      (COND ((EQUAL (CAR X) (CAR Y))
                                             (CONS (CAR X)
                                                   (UNION-EQUAL (CDR X)
                                                                (CDR Y))))
                                            (T NIL))))))

(DEFUN MERGE-TESTS-AND-ALISTS-LSTS
  (TESTS-AND-ALISTS-LST1 TESTS-AND-ALISTS-LST2 VARS)

;   If every alist in TESTS-AND-ALISTS-LST1 fits into an alist in
;   TESTS-AND-ALISTS-LST2, then return the new TESTS-AND-ALISTS-LST obtained by
;   putting each alist in TESTS-AND-ALISTS-LST1 into every alist in
;   TESTS-AND-ALISTS-LST2 into which it fits.  Else return NIL.  ALIST1 fits
;   into ALIST2 iff the two agree on every var in VARS.  To merge one alist
;   into another we extend the second alist by adding to it every pair of the
;   first, provided that pair does not clash with an existing pair of the
;   second.

  (LET (BUCKETS ALIST FLG)
    (SETQ BUCKETS (ITERATE FOR TA IN TESTS-AND-ALISTS-LST2
                           COLLECT (ITERATE FOR ALIST
                                            IN (ACCESS TESTS-AND-ALISTS
                                                       ALISTS TA)
                                            COLLECT (CONS ALIST NIL))))
    (COND ((ITERATE FOR TA1 IN TESTS-AND-ALISTS-LST1
                    ALWAYS
                    (ITERATE FOR ALIST1 IN (ACCESS TESTS-AND-ALISTS ALISTS TA1)
                             ALWAYS
                             (PROGN 
                               (SETQ FLG NIL)
                               (ITERATE FOR BUCKET IN BUCKETS DO
                                        (ITERATE FOR PAIR IN BUCKET DO
                                                 (COND ((FITS ALIST1
                                                              (CAR PAIR)
                                                              VARS)
                                                        (RPLACD
                                                         PAIR
                                                         (ADD-TO-SET
                                                          (EXTEND-ALIST
                                                           ALIST1 (CAR PAIR))
                                                          (CDR PAIR)))
                                                        (SETQ FLG T)))))
                               FLG)))
           (ITERATE FOR TA IN TESTS-AND-ALISTS-LST2 AS BUCKET IN BUCKETS
                    COLLECT (MAKE TESTS-AND-ALISTS
                                  (ACCESS TESTS-AND-ALISTS TESTS TA)
                                  (ITERATE FOR X IN BUCKET WITH ITERATE-ANS
                                           DO (SETQ ITERATE-ANS
                                                    (UNION-EQUAL (OR (CDR X) X)
                                                                 ITERATE-ANS))
                                           FINALLY (RETURN ITERATE-ANS)))))
          (T NIL))))

(DEFUN META-LEMMAP (X) (ATOM (ACCESS REWRITE-RULE CONCL X)))

(DEFUN MOST-RECENT-NON-STATUS ()
  (ITERATE FOR X IN CHRONOLOGY
           WHEN (NOT (MEMBER-EQ (CAR (GET X 'EVENT))
                                '(SET-STATUS TOGGLE TOGGLE-DEFINED-FUNCTIONS)))
           DO (RETURN X)))

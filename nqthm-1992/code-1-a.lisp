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

(DEFUN *1*ADD1 (X)
  (COND ((AND (INTEGERP X) (<= 0 X)) (1+ X))
        (T 1)))

(DEFUN *1*AND (X Y) (*1*IF X (*1*IF Y *1*T *1*F) *1*F))

(DEFUN *1*APPLY$ (FN ARGS)

;   This function is just lifted out of *1**EVAL$.  Note merely that
;   (APPLY$ fn args) = (EVAL$ T '(fn 'arg1 ... 'argn) NIL).  Inspect
;   *1**EVAL$ first and then return here.  When *1*THM-MODE$ is 'THM,
;   however, we are prohibited from APPLYing both 'APPLY$ and 'EVAL$
;   because no axiom specifies the value of such an application.

  (COND ((EQ FN (QUOTE IF))
         (COND ((EQ (*1*CAR ARGS) *1*F)
                (*1*CAR (*1*CDR (CDR ARGS))))
               (T (*1*CAR (*1*CDR ARGS)))))
        ((AND (CONSP FN)
              (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
              (EQ (CADR FN) 'PACK))
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((OR (NOT (SYMBOLP FN))
             (EQ FN *1*T)
             (EQ FN *1*F))
         *1*F)
        ((AND (EQ *1*THM-MODE$ (QUOTE THM))
              (MEMBER-EQ FN (QUOTE (APPLY$ EVAL$))))
         (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))
        (T (LET ((N (ARITY FN))
                 (G (GET FN (QUOTE LISP-CODE))))
             (COND ((OR (NULL N)
                        (NULL G))
                    (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))
                   ((INT= N 1) (FUNCALL G (*1*CAR ARGS)))
                   ((INT= N 2) (FUNCALL G (*1*CAR ARGS)
                                        (*1*CAR (*1*CDR ARGS))))
                   ((INT= N 3)
                    (FUNCALL
                     G
                     (*1*CAR ARGS)
                     (*1*CAR (*1*CDR ARGS))
                     (*1*CAR (*1*CDR (*1*CDR ARGS)))))
                   ((INT= N 4)
                    (FUNCALL
                     G
                     (*1*CAR ARGS)
                     (*1*CAR (*1*CDR ARGS))
                     (*1*CAR (*1*CDR (*1*CDR ARGS)))
                     (*1*CAR (*1*CDR (*1*CDR (*1*CDR ARGS))))))
                   ((INT= N 5)
                    (FUNCALL
                     G
                     (*1*CAR ARGS)
                     (*1*CAR (*1*CDR ARGS))
                     (*1*CAR (*1*CDR (*1*CDR ARGS)))
                     (*1*CAR (*1*CDR (*1*CDR (*1*CDR ARGS))))
                     (*1*CAR (*1*CDR (*1*CDR (*1*CDR (*1*CDR ARGS)))))))
                   ((INT= N 6)
                    (FUNCALL
                     G
                     (*1*CAR ARGS)
                     (*1*CAR (*1*CDR ARGS))
                     (*1*CAR (*1*CDR (*1*CDR ARGS)))
                     (*1*CAR (*1*CDR (*1*CDR (*1*CDR ARGS))))
                     (*1*CAR (*1*CDR (*1*CDR (*1*CDR (*1*CDR ARGS)))))
                     (*1*CAR (*1*CDR
                              (*1*CDR (*1*CDR
                                       (*1*CDR (*1*CDR ARGS))))))))
                   (T (APPLY G
                             (ITERATE FOR I FROM 1 TO N WITH TAIL = ARGS
                                      COLLECT
                                      (COND ((OR (ATOM TAIL)
                                                 (EQ (CAR TAIL)
                                                     *1*SHELL-QUOTE-MARK))
                                             0)
                                            (T (PROG1 (CAR TAIL)
                                                 (SETQ TAIL
                                                       (CDR TAIL)))))))))))))


;   The following function, *1**APPLY-SUBR is included in this file
;   for an odd reason.  It ought to be the LISP-CODE-FLG for the
;   DEFBOOT for APPLY-SUBR since APPLY-SUBR is a function defined in
;   NQTHM but not THM.  Originally the body below was written there.
;   However, that caused the following bad behavior.  BOOT-STRAP
;   compiled the body below, converting the (ITERATE ...) into a
;   (SI:DISPLACED ...)  containing some uninterned symbols #:G01234.
;   That s-expression was part of the SEXPR property for
;   *1*APPLY-SUBR.  When it was written to the .LISP file by MAKE-LIB
;   several references to the uninterned symbol #:G01234 were printed.
;   When they were read back in by a NOTE-LIB, they each read as a
;   different symbol and the compiler complained loudly that the
;   symbol was never used in each use.  The moral: do not use fancy
;   macros in the code supplied in the LISP-CODE-FLGs.

(DEFUN *1**APPLY-SUBR (FN ARGS)
  (CHK-NQTHM-MODE$ (QUOTE *1**APPLY-SUBR))
  (COND ((EQ FN (QUOTE IF))
         
;   IF is a SUBRP.  Should APPLY-SUBR be able to apply it or not?
;   We say yes, even though we never use that feature of APPLY-SUBR
;   since IF must always be special cased in evaluation.  However,
;   reasoning from axioms alone, APPLY works on IFs because V&C-APPLY$
;   works on IFs.  It would be confusing for APPLY-SUBR not to work
;   on a SUBR.  Because it is an error to call *1*IF we have to do the
;   work here.
         
         (COND ((EQ (*1*CAR ARGS) *1*F)
                (*1*CAR (CDR ARGS)))
               (T (*1*CAR (*1*CDR (*1*CDR ARGS))))))
        ((EQ (*1**SUBRP FN) *1*T)
         
;   This is one place where undo information is not maintained.
         
         (APPLY (GET FN (QUOTE LISP-CODE))
                (COND ((AND (NULL (CDR (OUR-LAST ARGS)))
                            (NOT (MEMBER-EQ *1*SHELL-QUOTE-MARK ARGS))
                            (INT= (LENGTH ARGS) (ARITY FN)))
                       ARGS)
                      (T (ITERATE FOR I FROM 1 TO (ARITY FN) WITH TAIL = ARGS
                                  COLLECT
                                  (COND ((OR (ATOM TAIL)
                                             (EQ (CAR TAIL)
                                                 *1*SHELL-QUOTE-MARK))
                                         0)
                                        (T (PROG1 (CAR TAIL)
                                             (SETQ TAIL (CDR TAIL))))))))))
        ((EQ (*1**SUBRP FN) *1*F) *1*F)
        (T (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))))

;   Recall that there are function symbols of the logic that exist in THM mode
;   and not in NQTHM mode (e.g., ASSOC) and vice versa (e.g., BODY).  These do
;   not have *1*fns defined in this file, since that would prevent them from
;   being defined by the user in the theory in which they are initially absent.
;   The DEFBOOTs for such functions include explicit LISP-CODE that gets stored
;   and compiled.  However, some programs in the theorem prover need to use
;   these *1*fns.  For example, REDUCE-TERM-TRACE1 needs to use the Lisp
;   counterparts of BODY, i.e., *1*BODY, in NQTHM mode.  And the code for
;   *1*EVAL$ below uses *1*ASSOC when running in both modes.  Thus, we need to
;   have the Lisp counterparts of these functions around.  We therefore define
;   these functions but do not use the *1* prefix, preferring instead *1**.
;   Thus, you will see *1**ASSOC and *1**BODY.

(DEFUN *1**ASSOC (X ALIST)

;   There is no CHK-NQTHM-MODE$ here because this function is used in both
;   THM and NQTHM mode, even though *1*ASSOC doesn't exist in THM mode.

  (ITERATE WITH TAIL = ALIST
           DO
           (COND ((OR (ATOM TAIL)
                      (EQ (CAR TAIL)
                          *1*SHELL-QUOTE-MARK))
                  (RETURN *1*F))
                 ((EQUAL X (*1*CAR (CAR TAIL)))
                  (RETURN (CAR TAIL)))
                 (T (SETQ TAIL (CDR TAIL))))))

(DEFUN *1**BODY (FN)
  (CHK-NQTHM-MODE$ (QUOTE *1**BODY))
  (COND ((AND (CONSP FN)
              (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
              (EQ (CADR FN) 'PACK))
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((NOT (SYMBOLP FN)) *1*F)
        ((EQ FN 'QUOTE)
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((OR (EQ FN *1*T) (EQ FN *1*F)) *1*F)
        ((EQ (*1**SUBRP FN) *1*T) *1*F)
        ((GET FN 'BODY))
        (T (LET ((PROP (GET FN (QUOTE EVENT))))
                (COND ((NOT (EQ (CAR PROP) (QUOTE DEFN)))
                       (ER HARD (FN) (!PPR FN NIL) |was| |assumed| |to| |be|
                           |a| DEFN |event| |by| *1*BODY |.|))
                      (T (CADDDR PROP)))))))

(DEFUN *1*CAR (X1)
  (COND ((ATOM X1) 0)
        ((EQ (CAR X1) *1*SHELL-QUOTE-MARK) 0)
        (T (CAR X1))))

(DEFUN *1*CDR (X1)
  (COND ((ATOM X1) 0)
        ((EQ (CAR X1) *1*SHELL-QUOTE-MARK) 0)
        (T (CDR X1))))

(DEFUN *1*CONS (X Y) (CONS X Y))

(DEFUN *1*COUNT (X)
  (COND ((ATOM X)
         (COND ((EQ X *1*T) 0)
               ((EQ X *1*F) 0)
               ((SYMBOLP X) (1+ (*1*COUNT (DTACK-0-ON-END (OUR-EXPLODEN X)))))
               ((< X 0) (1+ (- X)))
               (T X)))
        ((EQ *1*SHELL-QUOTE-MARK (CAR X))
         (COND ((MEMBER-EQ (CADR X) *1*BTM-OBJECTS) 0)
               (T (1+ (ITERATE FOR ARG IN (CDDR X) SUM (*1*COUNT ARG))))))
        (T (1+ (+ (*1*COUNT (CAR X)) (*1*COUNT (CDR X)))))))

(DEFUN *1*DIFFERENCE (I J)
  (COND ((> (SETQ I (*1*FIX I)) (SETQ J (*1*FIX J)))
         (- I J))
        (T 0)))

(DEFUN *1*EQUAL (X Y)
  (COND ((EQUAL X Y) *1*T)
        (T *1*F)))

(DEFUN *1**EVLIST$ (X VA)
  (ITERATE WITH TAIL = X UNTIL (OR (ATOM TAIL)
                                   (EQ (CAR TAIL) *1*SHELL-QUOTE-MARK))
           COLLECT
           (PROG1 (*1**EVAL$ (CAR TAIL) VA)
             (SETQ TAIL (CDR TAIL)))))

(DEFUN *1**EVAL$ (X VA)

;   The theorem prover encourages the user to apply EVAL$ and V&C$ on quoted
;   TERMPs.  That is, we do not "like" '(PLUS 1 X), preferring instead
;   '(PLUS '1 X).  Of course, the definitions of *1*EVAL$ and friends must
;   behave correctly on ill-formed "quoted terms."  However, our focus on
;   TERMPs suggests that perhaps we have not built into our own code the
;   axiomatized behavior of EVAL$ on non-terms.  Upon first exposure to our
;   implementation -- or actually re-exposure after months of absence --
;   one entertains the idea of cleaning up EVAL$ and changing its behavior
;   on non-terms, thinking "we don't ever use its current behavior in our
;   code because we've only built in its behavior on TERMPs."  This is simply
;   untrue and after nearly getting burned with that misconception I decided
;   to document here and there in the code places that we use the axiomatized
;   behavior of EVAL$ and friends on non-terms.

  (COND
   ((ATOM X)
    (COND ((EQ X *1*T) *1*T) ;eval$ of nlistp nlitatoms
          ((EQ X *1*F) *1*F)
          ((NUMBERP X) X)

;   Other atoms are looked up.  However, in THM mode, LOOKUP is used,
;   which returns NIL on unbound atoms, while in NQTHM, CDR ASSOC is
;   used.  But on non NUMBERPs LOOKUP is just CDR ASSOC unless ASSOC
;   returns F.

          (T (COND ((EQ *1*THM-MODE$ (QUOTE THM))
                    (COND ((EQ (*1**ASSOC X VA) *1*F)
                           NIL)
                          (T (*1*CDR (*1**ASSOC X VA)))))
                   (T (*1*CDR (*1**ASSOC X VA)))))))
   ((EQ (CAR X) *1*SHELL-QUOTE-MARK)
    (COND ((EQ (QUOTE PACK) (CADR X))
           (*1*CDR (*1**ASSOC X VA)))
          (T X)))
   ((EQ (CAR X) (QUOTE QUOTE)) (*1*CAR (CDR X)))
   ((EQ (CAR X) (QUOTE IF))
    (COND ((NOT (EQ *1*F (*1**EVAL$ (*1*CAR (CDR X)) VA)))
           (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA))
          (T (*1**EVAL$ (*1*CAR (*1*CDR (CDR (CDR X)))) VA))))

;   Note that we use (CDR (CDR X)) above instead of (*1*CDR (CDR X)).  That's
;   because we know (*1*CAR (CDR X)) EVAL$'d to F.  But had (CDR X) been NLISTP
;   the *1*CAR would have produced 0 and it would have EVAL$'d to 0.  So that
;   naked CDR depends upon the fact that the EVAL$ of 0 is 0. 
           
   ((AND (CONSP (CAR X))
         (EQ (CAR (CAR X)) *1*SHELL-QUOTE-MARK)
         (EQ (CADR (CAR X)) 'PACK))
    (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))
   ((OR (NOT (SYMBOLP (CAR X)))
        (EQ (CAR X) *1*T)
        (EQ (CAR X) *1*F))

;   Similarly, the result above, that the EVAL$ of (fn a1 ... an) is F if fn is
;   not a LITATOM relies on the V&C$ of F being F.  According to the axiom for
;   EVAL$, this case is equal to (APPLY fn (EVLIST ...)) = (CAR (FIX-COST (V&C$
;   T (BODY fn) ...) ...)) = (CAR (FIX-COST (V&C$ T F ...) ...)) = F.

    *1*F)

   ((AND (EQ *1*THM-MODE$ (QUOTE THM))
         (MEMBER-EQ (CAR X) (QUOTE (APPLY$ EVAL$))))

;   In THM mode we don't know how to EVAL$ either APPLY$ or EVAL$ calls.

    (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))

   (T (LET ((N (ARITY (CAR X)))
            (FN (GET (CAR X) (QUOTE LISP-CODE))))

;   Also below we use the fact that EVAL$ of 0 is 0.  The axiom for EVAL$ does
;   not EVAL$ the 0's that are fetched for non-existent arguments.  Those 0's
;   are supplied by PAIRLIST when we apply the fn.  But here we fetch all the
;   args, non-existent ones included, and EVAL$ them before applying the
;   function.

           (COND ((OR (NULL N)
                      (NULL FN))
                  (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED)))
                 ((INT= N 1) (FUNCALL FN
                                      (*1**EVAL$ (*1*CAR (CDR X)) VA)))
                 ((INT= N 2) (FUNCALL
                              FN
                              (*1**EVAL$ (*1*CAR (CDR X)) VA)
                              (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA)))
                 ((INT= N 3)
                  (FUNCALL
                   FN
                   (*1**EVAL$ (*1*CAR (CDR X)) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (*1*CDR (CDR X)))) VA)))
                 ((INT= N 4)
                  (FUNCALL
                   FN
                   (*1**EVAL$ (*1*CAR (CDR X)) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (*1*CDR (CDR X)))) VA)
                   (*1**EVAL$
                    (*1*CAR (*1*CDR (*1*CDR (*1*CDR (CDR X)))))
                    VA)))
                 ((INT= N 5)
                  (FUNCALL
                   FN
                   (*1**EVAL$ (*1*CAR (CDR X)) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (*1*CDR (CDR X)))) VA)
                   (*1**EVAL$
                    (*1*CAR (*1*CDR (*1*CDR (*1*CDR (CDR X)))))
                    VA)
                   (*1**EVAL$
                    (*1*CAR
                     (*1*CDR (*1*CDR (*1*CDR (*1*CDR (CDR X))))))
                    VA)))
                 ((INT= N 6)
                  (FUNCALL
                   FN
                   (*1**EVAL$ (*1*CAR (CDR X)) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (CDR X))) VA)
                   (*1**EVAL$ (*1*CAR (*1*CDR (*1*CDR (CDR X)))) VA)
                   (*1**EVAL$
                    (*1*CAR (*1*CDR (*1*CDR (*1*CDR (CDR X)))))
                    VA)
                   (*1**EVAL$
                    (*1*CAR
                     (*1*CDR (*1*CDR (*1*CDR (*1*CDR (CDR X))))))
                    VA)
                   (*1**EVAL$
                    (*1*CAR
                     (*1*CDR
                      (*1*CDR (*1*CDR (*1*CDR (*1*CDR (CDR X)))))))
                    VA)))
                 (T (APPLY
                     FN
                     (ITERATE
                      FOR I FROM 1 TO N WITH TAIL = (CDR X)
                      COLLECT
                      (COND ((OR (ATOM TAIL)
                                 (EQ (CAR TAIL) *1*SHELL-QUOTE-MARK))
                             0)
                            (T (PROG1 (*1**EVAL$ (CAR TAIL) VA)
                                      (SETQ TAIL (CDR TAIL)))))))))))))

(DEFUN *1*FALSE NIL *1*F)

(DEFUN *1*FALSEP (X)
  (COND ((EQ X *1*F) *1*T)
        (T *1*F)))

(DEFUN *1*FIX (X)
  (COND ((AND (INTEGERP X) (<= 0 X)) X)
        (T 0)))

(DEFUN *1**FORMALS (FN)
  (CHK-NQTHM-MODE$ (QUOTE *1*FORMALS))
  (COND ((AND (CONSP FN)
              (EQ (CAR FN) *1*SHELL-QUOTE-MARK)
              (EQ (CADR FN) 'PACK))
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((NOT (SYMBOLP FN)) *1*F)
        ((EQ FN 'QUOTE)
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((OR (EQ FN *1*T) (EQ FN *1*F)) *1*F)
        ((EQ (*1*SUBRP FN) *1*T) *1*F)
        (T (LET ((PROP (GET FN (QUOTE SDEFN))))
                (COND ((NULL PROP)
                       (ER HARD (FN) (!PPR FN NIL) |was| |assumed| |to|
                           |have| |an| SDEFN |by| *1*FORMALS |EXCL|))
                      (T (CADR PROP)))))))

(DEFUN *1*IF-ERROR (X Y Z)
  X Y Z
  (ER HARD NIL |the| LISP-CODE |for| IF |should| |never| |be| |APPLYd| |.|))

(DEFUN *1*IMPLIES (X Y) (*1*IF X (*1*IF Y *1*T *1*F) *1*T))

(DEFUN *1*LESSP (X Y)
  (COND ((< (*1*FIX X) (*1*FIX Y)) *1*T)
        (T *1*F)))

(DEFUN *1*LISTP (X)
  (COND ((AND (CONSP X) (NOT (EQ (CAR X) *1*SHELL-QUOTE-MARK)))
         *1*T)
        (T *1*F)))

(DEFUN *1*LITATOM (X)
  (COND ((OR (AND (SYMBOLP X) (NOT (EQ X *1*T)) (NOT (EQ X *1*F)))
             (AND (CONSP X)
                  (EQ (CAR X) *1*SHELL-QUOTE-MARK)
                  (EQ (CADR X) (QUOTE PACK))))
         *1*T)
        (T *1*F)))

(DEFUN *1*MINUS (X)
  (COND ((AND (INTEGERP X) (< 0 X))
         (- X))
        (T (LIST *1*SHELL-QUOTE-MARK (QUOTE MINUS) 0))))

(DEFUN *1*NEGATIVE-GUTS (X)
  (COND ((AND (INTEGERP X) (< X 0)) (- X))
        (T 0)))

(DEFUN *1*NEGATIVEP (X)
  (COND ((OR (AND (INTEGERP X) (< X 0))
             (AND (CONSP X)
                  (EQ (CAR X) *1*SHELL-QUOTE-MARK)
                  (EQ (CADR X) (QUOTE MINUS))))
         *1*T)
        (T *1*F)))

(DEFUN *1*NLISTP (X)
  (COND ((AND (CONSP X)
              (NOT (EQ (CAR X) *1*SHELL-QUOTE-MARK)))
         *1*F)
        (T *1*T)))

(DEFUN *1*NOT (X) (*1*IF X *1*F *1*T))

(DEFUN *1*NUMBERP (X)
  (COND ((AND (INTEGERP X) (<= 0 X)) *1*T)
        (T *1*F)))

(DEFUN *1*OR (X Y) (*1*IF X *1*T (*1*IF Y *1*T *1*F)))

(DEFUN *1*PACK (X)
  (COND ((AND (LEGAL-CHAR-CODE-SEQ X) (EQUAL 0 (CDR (OUR-LAST X))))
         (INTERN (COERCE  (ITERATE FOR TAIL ON X UNTIL (ATOM TAIL)
                                   COLLECT (CODE-CHAR (CAR TAIL)))
                          (QUOTE STRING))
                 'USER))
        (T (LIST *1*SHELL-QUOTE-MARK (QUOTE PACK) X))))

(DEFUN *1*PLUS (X Y)
  (+ (*1*FIX X) (*1*FIX Y)))

(DEFUN *1*QUOTIENT (I J)
  (COND ((EQUAL 0 (SETQ J (*1*FIX J))) 0)
        (T (OUR-QUOTIENT (*1*FIX I) J))))

(DEFUN *1*REMAINDER (I J)
  (COND ((EQUAL 0 (SETQ J (*1*FIX J)))
         (*1*FIX I))
        (T (OUR-REMAINDER (*1*FIX I) J))))

(DEFUN *1*SUB1 (X)
  (COND ((AND (INTEGERP X) (< 0 X))
         (1- X))
        (T 0)))

(DEFUN *1**SUBRP (X)
  (CHK-NQTHM-MODE$ (QUOTE *1**SUBRP))
  (COND ((AND (CONSP X)
              (EQ (CAR X) *1*SHELL-QUOTE-MARK)
              (EQ (CADR X) 'PACK))
         (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))
        ((NOT (SYMBOLP X)) *1*F)
        ((OR (EQ X *1*T) (EQ X *1*F)) *1*F)
        ((GET X (QUOTE SUBRP)))
        (T (THROW (QUOTE REDUCE-TERM)(QUOTE *1*FAILED)))))

(DEFUN *1*TIMES (I J) (* (*1*FIX I) (*1*FIX J)))

(DEFUN *1*TRUE NIL *1*T)

(DEFUN *1*TRUEP (X) (COND ((EQ X *1*T) *1*T) (T *1*F)))

(DEFUN *1*UNPACK (X)
  (COND ((AND (SYMBOLP X) (NOT (EQ X *1*T)) (NOT (EQ X *1*F)))
         (LET ((TEMP (OUR-EXPLODEN X))) (RPLACD (OUR-LAST TEMP) 0)
              TEMP))
        ((AND (CONSP X)
              (EQ *1*SHELL-QUOTE-MARK (CAR X))
              (EQ (CADR X) (QUOTE PACK)))
         (CADDR X))
        (T 0)))

(DEFUN *1*ZERO NIL 0)

(DEFUN *1*ZEROP (X)
  (COND ((INTEGERP X)
         (COND ((< X 1) *1*T)
               (T *1*F)))
        (T *1*T)))

(DEFUN ABBREVIATIONP (VARS TERM)

;   Suppose VARS is the bag of vars in a term LHS.  Then we say LHS=TERM is an
;   abbreviation if the bag of vars occurring in TERM is a subbag of VARS and
;   TERM contains no IF, AND, OR, NOT, or IMPLIES.  The property of VARS that
;   we actually check is that the number of occurrences of vars in TERM is no
;   greater than the length of VARS.

  (LET ((ANS VARS)) (ABBREVIATIONP1 TERM)))

(DEFUN ABBREVIATIONP1 (TERM)
  (COND ((VARIABLEP TERM)
         (COND ((ATOM ANS) NIL)
               (T (SETQ ANS (CDR ANS)) T)))
        ((FQUOTEP TERM) T)
        ((MEMBER-EQ (FFN-SYMB TERM) (QUOTE (IF AND OR NOT IMPLIES)))
         NIL)
        (T (ITERATE FOR X IN (FARGS TERM) ALWAYS (ABBREVIATIONP1 X)))))

(DEFUN ACCEPTABLE-COMPOUND-RECOGNIZER-LEMMAP (HYPS CONCL)

;   There are three forms of compound recognizer lemmas:
;     (IMPLIES (fn X) type-set-term)
;     (IMPLIES (NOT (fn X)) type-set-term)
;     (EQUAL (fn X) type-set-term)
;   where type-set-term is a type set term about X.  We do not look for
;   syntactic variants.

;   Let lemma be (IMPLIES HYPS CONCL) or CONCL if HYPS=NIL.  Then if lemma  
;   is of one of these forms, we return a triple <form, fn, ts>
;   where form is one of TRUE, FALSE, or BOTH, fn is the function
;   symbol involved, and ts is the type-set described by the type-set-term.
;   Otherwise we return NIL.

;   When built in as a REWRITE rule, lemma has the following effect on
;   SMART-ASSUME-TRUE-FALSE according to form above:

;   TRUE - If (fn a) is assumed true, the type set of a is intersected 
;   with ts.

;   FALSE - If (fn a) is assumed false -- which is equivalent to assuming
;   (NOT (fn a)) true -- the type set of a is intersected with ts.

;   BOTH - This case is handled as though both (fn a) -> type-set-term
;   and (NOT (fn a)) -> (NOT type-set-term) had been processed.  So, if
;   (fn a) is assumed true, the type set of a is intersected with ts;
;   and if (fn a) is assumed false, the type set of a is intersected with
;   (LOGNOT ts).

;   Here are some examples.  Suppose that STACKP is a user shell with a
;   bottom object.  Suppose we define
;   (ATOM X) = (IF (LISTP X) F (IF (STACKP X) (EQUAL X (EMPTY)) T)).
;   Thus, an ATOM is any object except a LISTP or a non-empty STACKP.
;   Let's suppose the shells are ordered STACK, NEGATIVEP, LISTP, LITATOM,
;   NUMBERP, TRUEP and FALSEP for concreteness.

;   Here are three compound recognizer lemmas:
;   1. (IMPLIES (ATOM X) (NOT (LISTP X)))
;      form: TRUE,  ts=11...1101111
;   2. (IMPLIES (NOT (ATOM X)) (OR (LISTP X) (STACKP X)))
;      form: FALSE, ts=00...1010000
;   3. (EQUAL (BOOLP X) (OR (TRUEP X) (FALSEP X)))
;      form: BOTH,  ts=00...0000011

;   So, if (ATOM A) is assumed true, we logand the type set of A with
;   11...1101111, turning off the LISTP bit.  If (ATOM A) is assumed false
;   we logand the type set of A with 00...1010000, turning off all bits
;   except STACKP and LISTP.  Thus, if A is known to be a LISTP or LITATOM
;   (i.e., 00...0011000) and we then assume false (ATOM A), we get that
;   A is a LISTP.  Finally, (BOOLP A), when assumed true, intersects
;   the type of A with 00...0000011 and when assumed false intersects it with
;   11...1111100.

  (LET (FN VAR PROP PAIR)
    (COND ((AND (NULL HYPS)
                (MATCH CONCL (EQUAL (LIST FN VAR) PROP))
                (NOT (EQ FN (QUOTE QUOTE)))
                (VARIABLEP VAR)
                (SETQ PAIR (TYPE-SET-TERMP PROP))
                (EQUAL VAR (CAR PAIR)))
           (LIST (QUOTE BOTH) FN (CDR PAIR)))
          ((AND (MATCH HYPS (LIST (LIST FN VAR)))
                (NOT (EQ FN (QUOTE QUOTE)))
                (VARIABLEP VAR)
                (SETQ PAIR (TYPE-SET-TERMP CONCL))
                (EQUAL VAR (CAR PAIR)))
           (LIST (QUOTE TRUE) FN (CDR PAIR)))
          ((AND (MATCH HYPS (LIST (NOT (LIST FN VAR))))
                (NOT (EQ FN (QUOTE QUOTE)))
                (VARIABLEP VAR)
                (SETQ PAIR (TYPE-SET-TERMP CONCL))
                (EQUAL VAR (CAR PAIR)))
           (LIST (QUOTE FALSE) FN (CDR PAIR)))
          (T NIL))))

(DEFUN ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP (HYPS CONCL)

;   If (IMPLIES HYPS CONCL) is a type prescription lemma for some function
;   symbol, compute the function symbol and return the function symbol consed
;   onto the type prescription described by the lemma.  Otherwise return NIL.

  (PROG (TERM RECOG CLAUSES VARS NEGFLG CONST ARG VAR)

;   Set TERM to the IF form of (IMPLIES HYP CONCL).

        (SETQ TERM (EXPAND-BOOT-STRAP-NON-REC-FNS
                    (FCONS-TERM* (QUOTE IF)
                                 (CONJOIN HYPS T)
                                 (FCONS-TERM* (QUOTE IF) CONCL TRUE FALSE)
                                 TRUE)))

        (COND ((NOT (INT= 1 (ITERATE FOR FN IN (ALL-FNNAMES TERM) COUNT
                                     (AND (NOT (ASSOC-EQ FN RECOGNIZER-ALIST))
                                          (NOT
                                           (SINGLETON-CONSTRUCTOR-TO-RECOGNIZER
                                            FN))))))

;   Acceptable type prescription lemmas must contain exactly one function
;   symbol other than IF, EQUAL, recognizers and singleton constructors.

               (RETURN NIL))
              ((CLEARLY-NOT-ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP TERM)

;   This short-circuit helps speed up ADD-SHELL, possibly a lot.

               (RETURN NIL)))

;   Consider a clause in the clausification of a type prescription lemma.  You
;   should be able to divide the literals into two sets.  The first set should
;   consist entirely of recognizers applied to some term (fn v1 ... vn) or of
;   negations of recognizers applied to such a term.  The second set should
;   consist entirely of equations between that term and some of the variables
;   vi.  Actually, some literals are of the form (EQUAL term (TRUE)) but these
;   are equivalent to (TRUEP term).

        (SETQ CLAUSES (CLAUSIFY TERM))

;   We now map over CLAUSES and replace all atoms of the form
;   (EQUAL & (singleton)) by (singletonp &) just to reduce the number of cases.

        (SETQ
         CLAUSES
         (ITERATE
          FOR CL IN CLAUSES
          COLLECT
          (ITERATE FOR LIT IN CL COLLECT
                   (PROGN
                     (SETQ NEGFLG (MATCH LIT (NOT LIT)))
                     (SETQ
                      LIT
                      (COND
                       ((OR (AND (MATCH LIT (EQUAL TERM CONST))
                                 (NVARIABLEP CONST)
                                 (SETQ TEMP-TEMP
                                       (SINGLETON-CONSTRUCTOR-TO-RECOGNIZER
                                        (FN-SYMB CONST))))
                            (AND (MATCH LIT (EQUAL CONST TERM))
                                 (NVARIABLEP CONST)
                                 (SETQ TEMP-TEMP
                                       (SINGLETON-CONSTRUCTOR-TO-RECOGNIZER
                                        (FN-SYMB CONST)))))
                        (FCONS-TERM* TEMP-TEMP TERM))
                       (T LIT)))
                     (COND (NEGFLG (FCONS-TERM* (QUOTE NOT) LIT))
                           (T LIT))))))

;   We now try to find the function that this supposed type prescription is
;   about.  We look at the first literal of the first clause and it had better
;   be a recognizer applied to something, a NOT recognizer applied to
;   something, or the equality of a non variable something and another term.
;   If we can find such a something, we set it to TERM.  Otherwise, we say this
;   is not a type prescription lemma.

        (COND ((NOT (AND (CONSP CLAUSES)
                         (CONSP (CAR CLAUSES))
                         (OR (AND (MATCH (CAAR CLAUSES)
                                         (NOT (LIST RECOG TERM)))
                                  (ASSOC-EQ RECOG RECOGNIZER-ALIST))
                             (AND (MATCH (CAAR CLAUSES)
                                         (LIST RECOG TERM))
                                  (ASSOC-EQ RECOG RECOGNIZER-ALIST))
                             (AND (MATCH (CAAR CLAUSES)
                                         (EQUAL TERM &))
                                  (NVARIABLEP TERM))
                             (AND (MATCH (CAAR CLAUSES) (EQUAL & TERM))
                                  (NVARIABLEP TERM)))))
               (RETURN NIL)))

;   TERM must be a function application to distinct variables.

        (COND ((NOT (AND (NVARIABLEP TERM)
                         (ITERATE FOR ARG IN (SARGS TERM)
                                  ALWAYS (VARIABLEP ARG))
                         (NO-DUPLICATESP (SARGS TERM))))
               (RETURN NIL)))

;   Every literal of every clause must be a recognizer applied to TERM, the
;   negation of a recognizer applied to TERM, or the equality between TERM and
;   one of the vars in its arglist.  As a side-effect of this check, we collect
;   in VARS all of the variables equated to TERM.

        (COND
         ((NOT (ITERATE FOR CL IN CLAUSES
                        ALWAYS
                        (ITERATE
                         FOR LIT IN CL
                         ALWAYS (OR (AND (MATCH LIT (LIST RECOG ARG))
                                         (ASSOC-EQ RECOG RECOGNIZER-ALIST)
                                         (EQUAL ARG TERM))
                                    (AND (MATCH LIT
                                                (NOT (LIST RECOG ARG)))
                                         (ASSOC-EQ RECOG RECOGNIZER-ALIST)
                                         (EQUAL ARG TERM))
                                    (AND (MATCH LIT (EQUAL ARG VAR))
                                         (EQUAL ARG TERM)
                                         (MEMBER-EQ VAR (SARGS TERM))
                                         (SETQ VARS
                                               (ADD-TO-SET VAR VARS)))
                                    (AND (MATCH LIT (EQUAL VAR ARG))
                                         (EQUAL ARG TERM)
                                         (MEMBER-EQ VAR (SARGS TERM))
                                         (SETQ VARS
                                               (ADD-TO-SET VAR VARS)))))))
          (RETURN NIL)))

;   Every clause must contain the same set of equations of TERM with vars.
;   Since VARS contains all of the vars ever equated with TERM in any clause,
;   all that remains is to make sure that every clause contains an equation
;   with each var in VARS.

        (COND ((NOT
                (ITERATE FOR VAR IN VARS ALWAYS
                         (ITERATE
                          FOR CL IN CLAUSES ALWAYS
                          (OR (MEMBER-EQUAL (FCONS-TERM* (QUOTE EQUAL)
                                                         TERM VAR)
                                            CL)
                              (MEMBER-EQUAL (FCONS-TERM* (QUOTE EQUAL)
                                                         VAR TERM)
                                            CL)))))
               (RETURN NIL)))

;   So we believe that (IMPLIES HYP CONCL) is a type prescription lemma.
;   Return the function symbol of TERM, consed onto the type prescription.  The
;   type prescription is itself a cons of the type bits and flags indicating
;   which args are in VARS.  The type bits are obtained by anding together the
;   disjunction of recognizers in each clause.

        (RETURN
         (CONS
          (FN-SYMB TERM)
          (CONS
           (ITERATE FOR CL IN CLAUSES WITH ITERATE-ANS = -1 DO
                    (SETQ
                     ITERATE-ANS
                     (TSLOGAND
                      ITERATE-ANS
                      (ITERATE FOR LIT IN CL WITH ITERATE-ANS = 0
                               WHEN (NOT (EQ (FN-SYMB LIT) (QUOTE EQUAL))) DO
                               (SETQ
                                ITERATE-ANS
                                (TSLOGIOR
                                 ITERATE-ANS
                                 (COND
                                  ((MATCH LIT (NOT LIT))
                                   (TSLOGNOT (CDR (ASSOC-EQ
                                                   (FN-SYMB LIT)
                                                   RECOGNIZER-ALIST))))
                                  (T (CDR (ASSOC-EQ (FN-SYMB LIT)
                                                    RECOGNIZER-ALIST))))))
                               FINALLY (RETURN ITERATE-ANS))))
                    FINALLY (RETURN ITERATE-ANS))
           (ITERATE FOR V IN (SARGS TERM) COLLECT
                    (COND ((MEMBER-EQ V VARS) T) (T NIL))))))))

(DEFUN ACCESS-ERROR (REC)
  (ER HARD (REC)
      |Attempt| |to| |use| |a| |record| |of| |the| |wrong| |type|
      (!PPR REC NIL)))

(DEFUN ACCUMULATED-PERSISTENCE (&OPTIONAL (BOUND1 20) (BOUND2 5))
  (COND (REWRITE-PATH-STK-PTR
         (LET ((REWRITE-PATH-STK-PTR REWRITE-PATH-STK-PTR)
               (REWRITE-PATH-PERSISTENCE-ALIST
                (COPY-ALIST REWRITE-PATH-PERSISTENCE-ALIST))
               ALIST0
               ALIST1)
           
;   The effect of the preceding bindings is that we can pop the stack
;   to empty it, thus accumulating the current counts into the alist.
;   When we exit the stack will be as it was when this function was
;   called -- because popping is non-destructive on the stack except
;   for the (protected) stack ptr and the (protected) alist.  If we
;   did not protect the alist the totals would be misleading later
;   because they would have in them the partial results from
;   earlier calls of this fn.  If we tried to do this by reinitializing
;   the CNT fields of the popped frames, we could not use those
;   fields reliably to investigate which ones are costing a lot.
           
           (ITERATE UNTIL (INT= REWRITE-PATH-STK-PTR -1)
                    DO (POP-REWRITE-PATH-FRAME))
           (TERPRI NIL)
           (PRINC "Number of function and lemma names mentioned:  " NIL)
           (PRINC (LENGTH REWRITE-PATH-PERSISTENCE-ALIST) NIL)
           (TERPRI NIL)
           (TERPRI NIL)
           (ITERATE FOR PAIR IN REWRITE-PATH-PERSISTENCE-ALIST
                    DO
                    (COND ((EQ (DATA-BASE 'PRIMARY (CAR PAIR))
                               'GROUND-ZERO)
                           (SETQ ALIST0 (CONS PAIR ALIST0)))
                          (T (SETQ ALIST1 (CONS PAIR ALIST1)))))
           (PRINC (format nil "The ~d Most Persistent User-Defined Names:"
                          bound1)
                  NIL)
           (TERPRI NIL)
           (PRINT-TWO-COLUMN-TABLE
            "    name               persistence" 0 25
            (ITERATE FOR I FROM 1 TO bound1
                     AS X IN (OUR-STABLE-SORT ALIST1
                                              (FUNCTION
                                               (LAMBDA (X Y)
                                                 (>= (CDR X) (CDR Y)))))
                     COLLECT X)
            NIL)
           (TERPRI NIL)
           (PRINC (format nil "The ~d Most Persistent Primitive Names:" bound2)
                  NIL)
           (TERPRI NIL)
           (PRINT-TWO-COLUMN-TABLE
            "    name               persistence" 0 25
            (ITERATE FOR I FROM 1 TO bound2
                     AS X IN (OUR-STABLE-SORT ALIST0
                                              (FUNCTION
                                               (LAMBDA (X Y)
                                                 (>= (CDR X) (CDR Y)))))
                     COLLECT X)
            NIL)
           (TERPRI NIL)
           T))
        (T (TERPRI NIL)
           (PRINC "The rewrite path is not being maintained." NIL)
           (TERPRI NIL)
           NIL)))

(DEFUN ADD-AXIOM1 (NAME TYPES TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

;   Note that this function is not really a subroutine of ADD-AXIOM which must
;   check that the term is a legal axiom of the types requested and then set up
;   for an event.  This function is used by ADD-SHELL0 and the boot strapping
;   to add axioms without creating events.  If the system were static those
;   calls of ADD-AXIOM1 could be replaced by ADD-LEMMA0 since we know the
;   lemmas we add are always acceptable.  However, we still run the
;   acceptability checks just in case we someday change the criteria for
;   acceptance but forget to change the built in additions of axioms.

  (MATCH! (CHK-ACCEPTABLE-LEMMA NAME TYPES TERM)
          (LIST NAME TYPES TERM))
  (ADD-LEMMA0 NAME TYPES TERM))

(DEFUN ADD-DCELL (NAME ONE-NAME EXPR)
  (COND ((NOT (MATCH EXPR (LAMBDA & &)))
         (ER HARD (EXPR) ADD-DCELL |was| |asked| |to| |store|
             |an| |inappropriate| |LAMBDA-expression| |.| MAKE-LIB
             |and| |other| |routines| |assume| |dcells| |contain|
             |LAMBDA-expressions| |of| |the| |form| |(LAMBDA & &)| |.|)))
  (ADD-FACT NAME (QUOTE LISP-CODE) ONE-NAME)
  (ADD-FACT ONE-NAME (QUOTE DCELL) EXPR))

(DEFUN ADD-ELIM-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  TYPE
  (LET (HYPS CONCL REWRITE-RULE DESTS)
    (SETQ TEMP-TEMP (UNPRETTYIFY TERM))
    (SETQ HYPS (CAAR TEMP-TEMP))
    (SETQ CONCL (CDAR TEMP-TEMP))
    (SETQ DESTS (DESTRUCTORS (LIST (ARGN CONCL 1))))
    (SETQ REWRITE-RULE (CREATE-REWRITE-RULE NAME HYPS CONCL NIL))
    (ITERATE FOR X IN DESTS
             DO (PROGN (ADD-FACT (FN-SYMB X)
                                 (QUOTE ELIMINATE-DESTRUCTORS-SEQ)
                                 REWRITE-RULE)
                       (ADD-FACT (FN-SYMB X)
                                 (QUOTE ELIMINATE-DESTRUCTORS-DESTS)
                                 (CONS X (REMOVE X DESTS :TEST #'EQUAL)))))
    NIL))

(DEFUN ADD-EQUATION (EQUATION POT-LST)

;   This function returns an EQ POT-LST in the event that EQUATION caused
;   nothing to change.

  (LET (ADD-EQUATION-ANS TO-DO-NEXT NEW-POT-- NEW-POT-+)
    (COND
     ((OR (NULL POT-LST)
          (NOT (TERM-ORDER (ACCESS LINEAR-POT VAR (CAR POT-LST))
                           (FIRST-VAR EQUATION))))
      (SETQ ADD-EQUATIONS-TO-DO
            (COND ((SETQ TEMP-TEMP (CANCEL-POSITIVE EQUATION))
                   (LIST TEMP-TEMP))
                  (T NIL)))
      (CONS (COND ((> (FIRST-COEFFICIENT EQUATION)
                      0)
                   (MAKE LINEAR-POT (FIRST-VAR EQUATION)
                         (LIST EQUATION)
                         NIL))
                  (T (MAKE LINEAR-POT (FIRST-VAR EQUATION)
                           NIL
                           (LIST EQUATION))))
            POT-LST))
     ((EQUAL (ACCESS LINEAR-POT VAR (CAR POT-LST))
             (FIRST-VAR EQUATION))
      (COND
       ((POLY-MEMBER EQUATION
                     (COND ((> (FIRST-COEFFICIENT
                                EQUATION)
                               0)
                            (ACCESS LINEAR-POT POSITIVES
                                    (CAR POT-LST)))
                           (T (ACCESS LINEAR-POT NEGATIVES
                                      (CAR POT-LST)))))
        (SETQ ADD-EQUATIONS-TO-DO NIL)
        POT-LST)
       (T (SETQ ADD-EQUATIONS-TO-DO
                (ITERATE FOR EQUATION1
                         IN (COND ((> (FIRST-COEFFICIENT EQUATION) 0)
                                   (ACCESS LINEAR-POT NEGATIVES (CAR POT-LST)))
                                  (T (ACCESS LINEAR-POT POSITIVES
                                             (CAR POT-LST))))
                         WITH TEMP
                         UNLESS (OR (TO-BE-IGNOREDP EQUATION1)
                                    (NULL (SETQ TEMP
                                                (CANCEL-POLYS EQUATION
                                                              EQUATION1))))
                         COLLECT TEMP))
          (COND ((SETQ TEMP-TEMP (CANCEL-POSITIVE EQUATION))
                 (SETQ ADD-EQUATIONS-TO-DO
                       (CONS TEMP-TEMP ADD-EQUATIONS-TO-DO))))
          (CONS (COND ((> (FIRST-COEFFICIENT EQUATION)
                          0)
                       (MAKE LINEAR-POT (ACCESS LINEAR-POT VAR
                                                (CAR POT-LST))
                             (CONS EQUATION
                                   (ACCESS LINEAR-POT POSITIVES
                                           (CAR POT-LST)))
                             (ACCESS LINEAR-POT NEGATIVES
                                     (CAR POT-LST))))
                      (T (MAKE LINEAR-POT (ACCESS LINEAR-POT VAR
                                                  (CAR POT-LST))
                               (ACCESS LINEAR-POT POSITIVES
                                       (CAR POT-LST))
                               (CONS EQUATION
                                     (ACCESS LINEAR-POT NEGATIVES
                                             (CAR POT-LST))))))
                (CDR POT-LST)))))
     (T
      (SETQ ADD-EQUATION-ANS (ADD-EQUATION EQUATION
                                           (CDR POT-LST)))
      (SETQ TO-DO-NEXT NIL)
      (SETQ NEW-POT-+ (ACCESS LINEAR-POT POSITIVES (CAR POT-LST)))
      (SETQ NEW-POT-- (ACCESS LINEAR-POT NEGATIVES (CAR POT-LST)))
      (ITERATE FOR EQUATION IN ADD-EQUATIONS-TO-DO
               DO
               (COND
                ((EQUAL (ACCESS LINEAR-POT VAR (CAR POT-LST))
                        (FIRST-VAR EQUATION))
                 (ITERATE FOR EQUATION1
                          IN (COND ((> (FIRST-COEFFICIENT EQUATION) 0)
                                    (COND
                                     ((POLY-MEMBER EQUATION NEW-POT-+)
                                      NIL)
                                     (T (COND ((SETQ TEMP-TEMP
                                                     (CANCEL-POSITIVE
                                                      EQUATION))
                                               (SETQ TO-DO-NEXT
                                                     (CONS TEMP-TEMP
                                                           TO-DO-NEXT))))
                                        (SETQ NEW-POT-+ (CONS EQUATION
                                                              NEW-POT-+))
                                        NEW-POT--)))
                                   (T (COND ((POLY-MEMBER EQUATION NEW-POT--)
                                             NIL)
                                            (T (SETQ NEW-POT--
                                                     (CONS EQUATION NEW-POT--))
                                               NEW-POT-+))))
                          WITH TEMP
                          UNLESS (OR (TO-BE-IGNOREDP EQUATION1)
                                     (NULL (SETQ TEMP
                                                 (CANCEL-POLYS EQUATION
                                                               EQUATION1))))
                          DO (SETQ TO-DO-NEXT (CONS TEMP TO-DO-NEXT))))
                (T (SETQ TO-DO-NEXT (CONS EQUATION TO-DO-NEXT)))))
      (SETQ ADD-EQUATIONS-TO-DO TO-DO-NEXT)
      (COND ((AND (EQ ADD-EQUATION-ANS (CDR POT-LST))
                  (EQ (ACCESS LINEAR-POT POSITIVES (CAR POT-LST)) NEW-POT-+)
                  (EQ (ACCESS LINEAR-POT NEGATIVES (CAR POT-LST)) NEW-POT--))

;   This is where we make sure we return an EQ POT-LST if nothing happened.

             POT-LST)
            (T (CONS (MAKE LINEAR-POT (ACCESS LINEAR-POT VAR (CAR POT-LST))
                           NEW-POT-+ NEW-POT--)
                     ADD-EQUATION-ANS)))))))

(DEFUN ADD-EQUATIONS (EQUATIONS POT-LST)
  (CATCH
      (QUOTE ADD-EQUATIONS)
    (LET (NEW-EQUATIONS ADD-EQUATIONS-TO-DO)
      (SETQ EQUATIONS
            (ITERATE FOR EQUATION IN EQUATIONS
                     WHEN (COND ((IMPOSSIBLE-POLYP EQUATION)
                                 (SETQ LINEAR-ASSUMPTIONS
                                       (ACCESS POLY ASSUMPTIONS EQUATION))
                                 (SETQ LEMMAS-USED-BY-LINEAR
                                       (UNION-EQ (ACCESS POLY LEMMAS EQUATION)
                                                 (ACCESS POLY LITERALS
                                                         EQUATION)))
                                 (THROW (QUOTE ADD-EQUATIONS)
                                        (QUOTE CONTRADICTION)))
                                ((TRUE-POLYP EQUATION)
                                 NIL)
                                (T T))
                     COLLECT EQUATION))
      (ITERATE WHILE EQUATIONS
               DO
               (PROGN (ITERATE FOR EQUATION IN EQUATIONS
                               DO (PROGN (SETQ POT-LST (ADD-EQUATION EQUATION
                                                                     POT-LST))
                                         (SETQ NEW-EQUATIONS
                                               (NCONC ADD-EQUATIONS-TO-DO
                                                      NEW-EQUATIONS))))
                      (SETQ EQUATIONS NEW-EQUATIONS)
                      (SETQ NEW-EQUATIONS NIL)))

; This following odd expression avoids a bug in the Sun/Lucid 3.0
; Sparc compiler.  This bug has been fixed by Lucid in later releases
; but we'll preserve our workaround out of courtesy to sites with 3.0.
; The expression is equivalent to POT-LST.

      (COND (POT-LST)))))

(DEFUN ADD-EQUATIONS-TO-POT-LST (POLY-LST POT-LST ALL-NEW-FLG)
  (CATCH (QUOTE ADD-EQUATIONS-TO-POT-LST)
    (PROG (NEW-POT-LST NEW-VARS REWRITTEN-CONCL LST
                       BREAK-REWRITE-COMMAND-HANDLER-STATE)
          (SETQ NEW-POT-LST (ADD-EQUATIONS POLY-LST POT-LST))
          (COND ((EQ NEW-POT-LST (QUOTE CONTRADICTION))
                 (RETURN (QUOTE CONTRADICTION))))
          TOP (SETQ NEW-VARS
                    (ITERATE
                     FOR X IN NEW-POT-LST
                     WHEN (AND (NOT (VARIABLEP (ACCESS LINEAR-POT VAR X)))
                               (OR ALL-NEW-FLG
                                   (NOT (ASSOC-EQUAL (ACCESS LINEAR-POT VAR X)
                                                     POT-LST))))
                     COLLECT (ACCESS LINEAR-POT VAR X)))
          (SETQ ALL-NEW-FLG NIL)
          (COND ((NULL NEW-VARS) (RETURN NEW-POT-LST)))
          (SETQ POT-LST NEW-POT-LST)
          (ITERATE
           FOR VAR IN NEW-VARS
           DO
           (ITERATE FOR LEMMA IN (GET (FN-SYMB VAR)
                                      (QUOTE LINEAR-LEMMAS))
                    UNLESS (DISABLEDP (ACCESS LINEAR-LEMMA NAME LEMMA))
                    DO

;   We will rewrite the conclusion of the linear lemma and rewrite the hyps to
;   relieve them.  This will generate both a list of lemmas used and some
;   linear assumptions.  They will be collected in the frames pushed here and
;   will be popped and smashed into the polys we add to the pot should we
;   succeed.

                    (PROGN
                      (PUSH-REWRITE-PATH-FRAME 'ADD-EQUATIONS-TO-POT-LST
                                               LEMMA
                                               NIL
                                               VAR)
                      (PUSH-LEMMA-FRAME)
                      (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
                      (COND
                       ((AND
                         (ONE-WAY-UNIFY (ACCESS LINEAR-LEMMA
                                                MAX-TERM LEMMA)
                                        VAR)
                         (LET ((SIMPLIFY-CLAUSE-POT-LST NEW-POT-LST)
                               RELIEVE-HYPS-ANS)
                           (PUT-REWRITE-PATH-ALIST UNIFY-SUBST)
                           (AND BROKEN-LEMMAS
                                (BREAK-BEFORE-RELIEVE-HYPS
                                 (ACCESS LINEAR-LEMMA NAME LEMMA)
                                 LEMMA
                                 VAR))
                           (SETQ RELIEVE-HYPS-ANS
                                 (RELIEVE-HYPS
                                  (ACCESS LINEAR-LEMMA HYPS LEMMA)))
                           (AND BROKEN-LEMMAS
                                (BREAK-AFTER-RELIEVE-HYPS
                                 (ACCESS LINEAR-LEMMA NAME LEMMA)
                                 LEMMA
                                 VAR
                                 RELIEVE-HYPS-ANS))
                           RELIEVE-HYPS-ANS)
                         (SETQ LST
                               (LET ((SIMPLIFY-CLAUSE-POT-LST
                                      NEW-POT-LST))
                                 (SETQ REWRITTEN-CONCL
                                       (REWRITE-LINEAR-CONCL
                                        (ACCESS LINEAR-LEMMA CONCL
                                                LEMMA)))
                                 (AND BROKEN-LEMMAS
                                      (BREAK-AFTER-REWRITE-LINEAR-CONCL
                                       (ACCESS LINEAR-LEMMA NAME LEMMA)
                                       LEMMA
                                       VAR
                                       REWRITTEN-CONCL))
                                 (LINEARIZE REWRITTEN-CONCL
                                            T)))
                         (PROGN (AND BROKEN-LEMMAS
                                     (BREAK-AFTER-LINEARIZE-REWRITTEN-CONCL
                                      (ACCESS LINEAR-LEMMA NAME LEMMA)
                                      LEMMA
                                      VAR
                                      REWRITTEN-CONCL
                                      LST))
                                (NULL (CDR LST)))
                         (LET (WORSE-THAN-FLG)
                           (SETQ WORSE-THAN-FLG
                                 (ITERATE
                                  FOR POLY IN (CAR LST) NEVER
                                  (ITERATE FOR PAIR1
                                           IN (ACCESS POLY ALIST POLY)
                                           THEREIS
                                           (ITERATE
                                            FOR POT IN POT-LST ALWAYS
                                            (AND
                                             (NOT
                                              (EQUAL
                                               (CAR PAIR1)
                                               (ACCESS LINEAR-POT VAR
                                                       POT)))
                                             (>=
                                              (FORM-COUNT (CAR PAIR1))
                                              (FORM-COUNT (ACCESS
                                                           LINEAR-POT VAR
                                                           POT)))
                                             (WORSE-THAN-OR-EQUAL
                                              (CAR PAIR1)
                                              (ACCESS LINEAR-POT
                                                      VAR POT)))))))
                           (AND BROKEN-LEMMAS
                                (BREAK-AFTER-LINEAR-WORSE-THAN
                                 (ACCESS LINEAR-LEMMA NAME LEMMA)
                                 LEMMA
                                 VAR
                                 REWRITTEN-CONCL
                                 LST
                                 WORSE-THAN-FLG))
                           WORSE-THAN-FLG))
                        (ITERATE FOR POLY IN (CAR LST) WITH
                                 LEMMAS  =
                                 (ADD-TO-SET
                                  (ACCESS LINEAR-LEMMA NAME LEMMA)
                                  (POP-LEMMA-FRAME))
                                 AND HYPS =
                                 (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                                 DO
                                 (PROGN (CHANGE POLY LEMMAS POLY LEMMAS)
                                        (CHANGE
                                         POLY ASSUMPTIONS POLY
                                         (UNION-EQUAL
                                          HYPS
                                          (ACCESS POLY
                                                  ASSUMPTIONS POLY)))))
                        (POP-REWRITE-PATH-FRAME)
                        (SETQ NEW-POT-LST (ADD-EQUATIONS (CAR LST)
                                                         NEW-POT-LST))
                        (COND ((EQ NEW-POT-LST (QUOTE CONTRADICTION))
                               (THROW (QUOTE ADD-EQUATIONS-TO-POT-LST)
                                      (QUOTE CONTRADICTION)))))
                       (T (POP-LEMMA-FRAME)
                          (POP-LINEARIZE-ASSUMPTIONS-FRAME)
                          (POP-REWRITE-PATH-FRAME))))))
          (GO TOP))))

(DEFUN ADD-FACT (ATM PROP VAL)
  (COND (ATM (GUARANTEE-CITIZENSHIP ATM)))
  (ADD-SUB-FACT ATM PROP VAL NIL NIL))

(DEFUN ADD-GENERALIZE-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  TYPE
  (ADD-FACT NIL (QUOTE GENERALIZE-LEMMAS)
            (MAKE GENERALIZE-LEMMA NAME TERM)))

(DEFUN ADD-LEMMA NIL
  (ER SOFT NIL ADD-LEMMA |is| |undefined.| |Use| |either| ADD-AXIOM |,|
      ADD-SHELL |,| CONSTRAIN |,| DEFN |,| FUNCTIONALLY-INSTANTIATE
      |or| |PROVE-LEMMA| |.|))

(DEFUN ADD-LEMMA0 (NAME TYPES TERM)
  (GUARANTEE-CITIZENSHIP NAME)
  (SETQ TYPES (SCRUNCH TYPES))
  (ITERATE FOR TYPE IN TYPES DO
           (FUNCALL (PACK (LIST (QUOTE ADD) (QUOTE -)
                                (COND ((CONSP TYPE) (CAR TYPE)) (T TYPE))
                                (QUOTE -) (QUOTE LEMMA)))
                    NAME TYPE TERM)))

(DEFUN ADD-LESSP-ASSUMPTION-TO-POLY (X Y POLY)

;   We add the assumption (LESSP X Y) to POLY.  See the comment in
;   ADD-NUMBERP-ASSUMPTION-TO-POLY.

  (PROG (TEMP TERM)
        (SETQ TEMP (TYPE-SET (SETQ TERM (FCONS-TERM* (QUOTE LESSP) X Y))))
        (COND ((TS= TEMP TYPE-SET-TRUE) NIL)
              ((TS= TEMP TYPE-SET-FALSE)
               (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
              ((AND HEURISTIC-TYPE-ALIST
                    (TS= (LET ((TYPE-ALIST HEURISTIC-TYPE-ALIST))
                           (TYPE-SET TERM))
                         TYPE-SET-FALSE))
               (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
              ((SETQ TEMP-TEMP (ITERATE FOR LIT
                                        IN LITS-THAT-MAY-BE-ASSUMED-FALSE
                                        WHEN (COMPLEMENTARYP TERM LIT)
                                        DO (RETURN LIT)))
               (CHANGE POLY LEMMAS POLY (ADD-TO-SET-EQ
                                         TEMP-TEMP
                                         (ACCESS POLY LEMMAS POLY))))
              (T (CHANGE POLY ASSUMPTIONS POLY
                         (ADD-TO-SET TERM (ACCESS POLY ASSUMPTIONS POLY)))))
        (RETURN POLY)))

(DEFUN ADD-LINEAR-TERM (TERM PARITY POLY)
  (COND
   ((VARIABLEP TERM) (ADD-LINEAR-VARIABLE TERM PARITY POLY))
   ((FQUOTEP TERM)
    (COND
     ((AND (INTEGERP (CADR TERM))
           (> (CADR TERM)
              -1))
      (COND ((EQ PARITY (QUOTE POSITIVE))
             (CHANGE POLY CONSTANT POLY (+ (ACCESS POLY CONSTANT POLY)
                                           (CADR TERM))))
            (T (CHANGE POLY CONSTANT POLY (- (ACCESS POLY CONSTANT
                                                     POLY)
                                             (CADR TERM))))))))
   (T (CASE (FFN-SYMB TERM)
            (ADD1 (CHANGE POLY CONSTANT POLY
                          (COND ((EQ PARITY (QUOTE POSITIVE))
                                 (1+ (ACCESS POLY CONSTANT POLY)))
                                (T (1- (ACCESS POLY CONSTANT POLY)))))
                  (ADD-LINEAR-TERM (FARGN TERM 1) PARITY POLY))
            (ZERO NIL)
            (SUB1 (COND ((EQ PARITY (QUOTE POSITIVE))
                         (CHANGE POLY CONSTANT POLY
                                 (1- (ACCESS POLY CONSTANT POLY)))
                         (ADD-LINEAR-TERM (FARGN TERM 1)
                                          PARITY POLY))
                        (T (ADD-NOT-LESSP-ASSUMPTION-TO-POLY
                            (FARGN TERM 1)
                            (QUOTE (QUOTE 1))
                            POLY)
                           (CHANGE POLY CONSTANT POLY
                                   (1+ (ACCESS POLY CONSTANT POLY)))
                           (ADD-LINEAR-TERM (FARGN TERM 1) PARITY POLY))))
            (PLUS (ADD-LINEAR-TERM (FARGN TERM 2) PARITY POLY)
                  (ADD-LINEAR-TERM (FARGN TERM 1) PARITY POLY))
            (DIFFERENCE (COND ((EQ PARITY (QUOTE POSITIVE))
                               (ADD-LINEAR-TERM (FARGN TERM 2)
                                                (QUOTE NEGATIVE)
                                                POLY)
                               (ADD-LINEAR-TERM (FARGN TERM 1) PARITY POLY))
                              (T (ADD-NOT-LESSP-ASSUMPTION-TO-POLY
                                  (FARGN TERM 1)
                                  (FARGN TERM 2)
                                  POLY)
                                 (ADD-LINEAR-TERM (FARGN TERM 2)
                                                  (QUOTE POSITIVE)
                                                  POLY)
                                 (ADD-LINEAR-TERM (FARGN TERM 1)
                                                  PARITY POLY))))
            (OTHERWISE
             (ADD-LINEAR-VARIABLE TERM PARITY POLY)))))
  POLY)

(DEFUN ADD-LINEAR-VARIABLE (VAR PARITY POLY)
  (LET (N TERM)
    (COND ((AND (MATCH VAR (TIMES N TERM))
                (QUOTEP N)
                (INTEGERP (CADR N))
                (> (CADR N) -1)
                (NOT (QUOTEP TERM)))
           (COND ((TSLOGSUBSETP TYPE-SET-NUMBERS (TYPE-SET TERM))
                  (CHANGE POLY ALIST POLY (ADD-LINEAR-VARIABLE1
                                           (CADR N)
                                           TERM PARITY
                                           (ACCESS POLY ALIST POLY))))))
          ((TSLOGSUBSETP TYPE-SET-NUMBERS (TYPE-SET VAR))
           (CHANGE POLY ALIST POLY (ADD-LINEAR-VARIABLE1 1 VAR PARITY
                                                         (ACCESS POLY ALIST
                                                                 POLY)))))
    POLY))

(DEFUN ADD-LINEAR-VARIABLE1 (N VAR PARITY ALIST)
  (COND ((ATOM ALIST)
         (CONS (CONS VAR (COND ((EQ PARITY (QUOTE POSITIVE))
                                N)
                               (T (- N))))
               NIL))
        ((TERM-ORDER VAR (CAAR ALIST))
         (COND ((EQUAL VAR (CAAR ALIST))
                (COND ((EQ PARITY (QUOTE POSITIVE))
                       (RPLACD (CAR ALIST) (+ N (CDAR ALIST))))
                      (T (RPLACD (CAR ALIST)
                                 (- (CDAR ALIST) N))))
                ALIST)
               (T (RPLACD ALIST (ADD-LINEAR-VARIABLE1 N VAR PARITY
                                                      (CDR ALIST))))))
        (T (CONS (CONS VAR (COND ((EQ PARITY (QUOTE POSITIVE))
                                  N)
                                 (T (- N))))
                 ALIST))))

(DEFUN ADD-LITERAL (LIT CL AT-END-FLG)

;   We assume that LIT has been subjected to NEGATE-LIT or PEGATE-LIT before
;   passed to ADD-LITERAL, and that CL is the result of previous such
;   ADD-LITERALS.  Thus, we make the trivial checks that LIT is neither T nor
;   F, but do not use a full blown FALSE-NONFALSEP.

  (COND ((EQUAL LIT FALSE)
         CL)
        ((EQUAL LIT TRUE)
         TRUE-CLAUSE)
        ((EQUAL CL TRUE-CLAUSE)
         TRUE-CLAUSE)
        ((ITERATE FOR LIT2 IN CL THEREIS (COMPLEMENTARYP LIT LIT2))
         TRUE-CLAUSE)
        ((MEMBER-EQUAL LIT CL) CL)
        (AT-END-FLG (APPEND CL (LIST LIT)))
        (T (CONS LIT CL))))

(DEFUN ADD-LITERAL-TO-END-AFTER-REVERSING (LIT CL)
  (REVERSE (ADD-LITERAL LIT CL NIL)))

(DEFUN ADD-META-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET (FN)
    (MATCH TERM (EQUAL & (EVAL$ & (LIST FN &) &)))
    (ITERATE FOR X IN (CDR TYPE)
             DO (ADD-FACT X (QUOTE LEMMAS)
                          (MAKE REWRITE-RULE NAME NIL
                                (GET FN (QUOTE LISP-CODE)) NIL)))))

(DEFUN ADD-NOT-EQUAL-0-ASSUMPTION-TO-POLY (TERM POLY)

;   We add the assumption (NOT (EQUAL TERM 0)) to POLY.  See the comment in
;   ADD-NUMBERP-ASSUMPTION-TO-POLY.

  (LET (X Y TEMP EQUALITY)
    (COND
     ((MATCH TERM (DIFFERENCE X Y))
      (ADD-LESSP-ASSUMPTION-TO-POLY Y X POLY))
     ((EQUAL TERM ZERO)
      (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE))
      POLY)
     ((OR (MATCH TERM (ADD1 &))
          (AND (QUOTEP TERM)
               (NOT (EQUAL (CADR TERM)
                           0))))
      POLY)
     (T (SETQ EQUALITY (FCONS-TERM* (QUOTE EQUAL) TERM ZERO))
        (SETQ TEMP (TYPE-SET EQUALITY))
        (COND
         ((TS= TEMP TYPE-SET-TRUE)
          (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
         ((TS= TEMP TYPE-SET-FALSE)
          NIL)
         ((AND HEURISTIC-TYPE-ALIST
               (TS= (LET ((TYPE-ALIST HEURISTIC-TYPE-ALIST))
                      (TYPE-SET EQUALITY))
                    TYPE-SET-TRUE))
          (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
         ((SETQ TEMP-TEMP (MEMBER-EQUAL EQUALITY
                                        LITS-THAT-MAY-BE-ASSUMED-FALSE))
          (CHANGE POLY LEMMAS POLY (ADD-TO-SET-EQ (CAR TEMP-TEMP)
                                                  (ACCESS POLY
                                                          LEMMAS POLY))))
         (T (CHANGE POLY ASSUMPTIONS POLY
                    (ADD-TO-SET (FCONS-TERM* (QUOTE NOT)
                                             EQUALITY)
                                (ACCESS POLY ASSUMPTIONS POLY)))))
        POLY))))

(DEFUN ADD-NOT-LESSP-ASSUMPTION-TO-POLY (X Y POLY)

;   We add the assumption (NOT (LESSP X Y)) to POLY.  See the comment in
;   ADD-NUMBERP-ASSUMPTION-TO-POLY.

  (PROG (TEMP TERM)
        (COND
         ((EQUAL Y (QUOTE (QUOTE 1)))
          (COND ((TS= (TYPE-SET X)
                      TYPE-SET-NUMBERS)
                 (RETURN (ADD-NOT-EQUAL-0-ASSUMPTION-TO-POLY X POLY)))
                ((SETQ TEMP-TEMP
                       (ITERATE FOR LIT IN LITS-THAT-MAY-BE-ASSUMED-FALSE
                                WITH TERM = (FCONS-TERM* (QUOTE NUMBERP) X)
                                WHEN (COMPLEMENTARYP TERM LIT)
                                DO (RETURN LIT)))
                 (CHANGE POLY LEMMAS POLY (ADD-TO-SET-EQ TEMP-TEMP
                                                         (ACCESS POLY LEMMAS
                                                                 POLY)))
                 (RETURN (ADD-NOT-EQUAL-0-ASSUMPTION-TO-POLY X POLY))))))
        (SETQ TEMP (TYPE-SET (SETQ TERM (FCONS-TERM* (QUOTE LESSP) X Y))))
        (COND ((TS= TEMP TYPE-SET-FALSE)
               NIL)
              ((TS= TEMP TYPE-SET-TRUE)
               (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
              ((AND HEURISTIC-TYPE-ALIST
                    (TS= (LET ((TYPE-ALIST HEURISTIC-TYPE-ALIST))
                           (TYPE-SET TERM))
                         TYPE-SET-TRUE))
               (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
              ((SETQ TEMP-TEMP (MEMBER-EQUAL TERM
                                             LITS-THAT-MAY-BE-ASSUMED-FALSE))
               (CHANGE POLY LEMMAS POLY (ADD-TO-SET-EQ (CAR TEMP-TEMP)
                                                       (ACCESS
                                                        POLY LEMMAS POLY))))
              (T (CHANGE POLY ASSUMPTIONS POLY
                         (ADD-TO-SET (FCONS-TERM* (QUOTE NOT)
                                                  TERM)
                                     (ACCESS POLY ASSUMPTIONS POLY)))))
        (RETURN POLY)))

(DEFUN ADD-NUMBERP-ASSUMPTION-TO-POLY (TERM POLY)

;   We add the assumption (NUMBERP TERM) to the assumptions field of POLY but
;   we first check to see if the assumption is obviously true or false.  We
;   assume TYPE-ALIST is correctly set.  If the HEURISTIC-TYPE-ALIST is set and
;   says the assumption is false, we add the false assumption -- this is sound,
;   even though HEURISTIC-TYPE-ALIST may be irrelevant, because we can always
;   add a false assumption to a poly which will prevent the poly from being
;   used.  We assume that LITS-THAT-MAY-BE-ASSUMED-FALSE is NIL unless we are
;   under the ADD-TERMS-TO-POT-LST in SIMPLIFY-CLAUSE0.  If the complement of
;   the assumption we wish to add is in LITS-THAT-MAY-BE-ASSUMED-FALSE then the
;   assumption is true but we record the literal that makes it true in the
;   LEMMAS field of POLY.  We assume that if (NUMBERP TERM) is in
;   LITS-THAT-MAY-BE-ASSUMED-FALSE then it was false under the
;   HEURISTIC-TYPE-ALIST and we do not bother to check.

  (LET (TEMP)
    (SETQ TEMP (TYPE-SET TERM))
    (COND
     ((TS= TEMP TYPE-SET-NUMBERS)
      NIL)
     ((NOT (TSLOGSUBSETP TYPE-SET-NUMBERS TEMP))
      (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
     ((AND HEURISTIC-TYPE-ALIST
           (NOT (TSLOGSUBSETP TYPE-SET-NUMBERS
                              (LET ((TYPE-ALIST
                                     HEURISTIC-TYPE-ALIST))
                                (TYPE-SET TERM)))))

;   On heuristic grounds, we here decide not to use this poly.

      (CHANGE POLY ASSUMPTIONS POLY (LIST FALSE)))
     (T (SETQ TEMP (FCONS-TERM* (QUOTE NUMBERP) TERM))
        (COND ((SETQ TEMP-TEMP (ITERATE FOR LIT
                                        IN LITS-THAT-MAY-BE-ASSUMED-FALSE
                                        WHEN (COMPLEMENTARYP LIT TEMP)
                                        DO (RETURN LIT)))
               (CHANGE POLY LEMMAS POLY
                       (ADD-TO-SET-EQ TEMP-TEMP (ACCESS POLY LEMMAS POLY))))
              (T (CHANGE POLY ASSUMPTIONS POLY
                         (ADD-TO-SET TEMP (ACCESS POLY ASSUMPTIONS POLY)))))))
    POLY))

(DEFUN ADD-PROCESS-HIST (PROCESS PARENT PARENT-HIST DESCENDANTS HIST-ENTRY)
  (IO PROCESS PARENT PARENT-HIST DESCENDANTS HIST-ENTRY)
  (CONS (CONS PROCESS (CONS PARENT HIST-ENTRY)) PARENT-HIST))

(DEFUN ADD-REWRITE-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  TYPE
  (ITERATE FOR X IN (UNPRETTYIFY

; We've already done the check, presumably, so there is no need to see error
; messages again.

                     (REMOVE-IDENTITY TERM NIL))
           WITH (LEMMA ALL-VARS-HYPS ALL-VARS-CONCL MAX-TERMS LST TEMP HYPS
                       CONCL FORM FN TS)
           DO
           (PROGN
             (SETQ HYPS (CAR X))
             (SETQ CONCL (CDR X))
             (COND
              ((SETQ TEMP (ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP HYPS CONCL))
               (ADD-FACT (CAR TEMP)
                         (QUOTE TYPE-PRESCRIPTION-LST)
                         (CONS NAME (CDR TEMP))))
              ((SETQ TEMP (ACCEPTABLE-COMPOUND-RECOGNIZER-LEMMAP HYPS CONCL))
               (MATCH TEMP (LIST FORM FN TS))
               (COND ((EQ FORM (QUOTE TRUE))
                      (ADD-FACT NIL
                                (QUOTE TRUE-COMPOUND-RECOGNIZER-ALIST)
                                (CONS FN (CONS TS NAME))))
                     ((EQ FORM (QUOTE FALSE))
                      (ADD-FACT NIL
                                (QUOTE FALSE-COMPOUND-RECOGNIZER-ALIST)
                                (CONS FN (CONS TS NAME))))
                     (T (ADD-FACT NIL
                                  (QUOTE TRUE-COMPOUND-RECOGNIZER-ALIST)
                                  (CONS FN (CONS TS NAME)))
                        (ADD-FACT NIL
                                  (QUOTE FALSE-COMPOUND-RECOGNIZER-ALIST)
                                  (CONS FN (CONS (TSLOGNOT TS) NAME))))))
              ((AND (NOT NO-BUILT-IN-ARITH-FLG)
                    (OR (MATCH CONCL (NOT (LESSP & &)))
                        (MATCH CONCL (LESSP & &))))
               (SETQ LST (EXTERNAL-LINEARIZE CONCL T))
               (SETQ ALL-VARS-HYPS (ALL-VARS-LST HYPS))
               (SETQ ALL-VARS-CONCL (ALL-VARS CONCL))
               (SETQ MAX-TERMS
                     (ITERATE FOR PAIR IN (ACCESS POLY ALIST (CAR (CAR LST)))
                              WHEN
                              (AND (NVARIABLEP (CAR PAIR))
                                   (SUBSETP-EQ
                                    ALL-VARS-CONCL
                                    (UNION-EQ (ALL-VARS (CAR PAIR))
                                              ALL-VARS-HYPS))
                                   (ITERATE
                                    FOR PAIR2 IN
                                    (ACCESS POLY ALIST (CAR (CAR LST)))
                                    WHEN (NOT (EQ PAIR2 PAIR))
                                    NEVER (AND (< (FORM-COUNT (CAR PAIR))
                                                  (FORM-COUNT (CAR PAIR2)))
                                               (SUBBAGP
                                                (ALL-VARS-BAG (CAR PAIR))
                                                (ALL-VARS-BAG (CAR PAIR2))))))
                              COLLECT (CAR PAIR)))
               (ITERATE FOR TERM IN MAX-TERMS
                        DO (PROGN (SETQ LEMMA (MAKE LINEAR-LEMMA NAME
                                                    (PREPROCESS-HYPS HYPS)
                                                    CONCL TERM))
                                  (ADD-FACT (FN-SYMB TERM)
                                            (QUOTE LINEAR-LEMMAS)
                                            LEMMA))))
              (T (ITERATE FOR REWRITE-RULE
                          IN (MAKE-REWRITE-RULES NAME HYPS CONCL)
                          WITH (LHS RHS)
                          DO (COND ((OR (MATCH CONCL (EQUAL LHS RHS))
                                        (MATCH CONCL (IFF LHS RHS)))
                                    (ITERATE FOR VAR
                                             IN (SET-DIFF (ALL-VARS RHS)
                                                          (UNION-EQ
                                                           (ALL-VARS LHS)
                                                           (ALL-VARS-LST
                                                            HYPS)))
                                             DO
                                             (ADD-FACT
                                              NIL
                                              (QUOTE
                                               FREE-VARS-IN-REWRITE-RHSS)
                                              VAR))))
                          (ADD-FACT (TOP-FNNAME CONCL)
                                    (QUOTE LEMMAS)
                                    REWRITE-RULE)))))))

(DEFUN ADD-SHELL-ROUTINES (SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)
  (PROG
   NIL
   (COND (IN-BOOT-STRAP-FLG
          (ITERATE FOR NAME
                   IN (CONS SHELL-NAME
                            (CONS RECOGNIZER
                                  (APPEND (ITERATE FOR X IN DESTRUCTOR-TUPLES
                                                   COLLECT (CAR X))
                                          (COND (BTM-FN-SYMB
                                                 (LIST BTM-FN-SYMB))
                                                (T NIL)))))
                   DO (ADD-FACT NAME (QUOTE LISP-CODE)
                                (PACK (LIST PREFIX-FOR-FUNCTIONS NAME)))
                   (GUARANTEE-CITIZENSHIP
                    (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))))
          (RETURN NIL)))
   (AND BTM-FN-SYMB
        (ADD-DCELL BTM-FN-SYMB
                   (PACK (LIST PREFIX-FOR-FUNCTIONS BTM-FN-SYMB))
                   (SUB-PAIR (QUOTE (*1*SHELL-QUOTE-MARK BTM))
                             (LIST *1*SHELL-QUOTE-MARK BTM-FN-SYMB)
                             (QUOTE (LAMBDA NIL
                                      (QUOTE (*1*SHELL-QUOTE-MARK BTM)))))))
   (ADD-DCELL
    RECOGNIZER
    (PACK (LIST PREFIX-FOR-FUNCTIONS RECOGNIZER))
    (COND (BTM-FN-SYMB
           (SUB-PAIR (QUOTE (SHELL-NAME BTM))
                     (LIST SHELL-NAME BTM-FN-SYMB)
                     (QUOTE (LAMBDA (X)
                              (COND ((AND (CONSP X)
                                          (EQ (CAR X)
                                              *1*SHELL-QUOTE-MARK)
                                          (OR (EQ (CADR X)
                                                  (QUOTE SHELL-NAME))
                                              (EQ (CADR X)
                                                  (QUOTE BTM))))
                                     *1*T)
                                    (T *1*F))))))
          (T (SUB-PAIR (QUOTE (SHELL-NAME))
                       (LIST SHELL-NAME)
                       (QUOTE (LAMBDA (X)
                                (COND ((AND (CONSP X)
                                            (EQ (CAR X)
                                                *1*SHELL-QUOTE-MARK)
                                            (EQ (CADR X)
                                                (QUOTE SHELL-NAME)))
                                       *1*T)
                                      (T *1*F))))))))
   (ITERATE FOR TUPLE IN DESTRUCTOR-TUPLES AS I FROM 2 DO
            (ADD-DCELL
             (CAR TUPLE)
             (PACK (LIST PREFIX-FOR-FUNCTIONS (CAR TUPLE)))
             (SUB-PAIR (QUOTE (R CELL DV BTM))
                       (LIST (PACK (LIST PREFIX-FOR-FUNCTIONS RECOGNIZER))
                             (CELL I (QUOTE X))
                             (PACK (LIST PREFIX-FOR-FUNCTIONS (CADDR TUPLE)))
                             BTM-FN-SYMB)
                       (COND (BTM-FN-SYMB
                              (QUOTE (LAMBDA (X)
                                       (COND ((AND (EQ (R X) *1*T)
                                                   (NOT (EQ (CADR X)
                                                            (QUOTE BTM))))
                                              (CAR CELL))
                                             (T (DV))))))
                             (T (QUOTE (LAMBDA (X)
                                         (COND ((EQ (R X) *1*T)
                                                (CAR CELL))
                                               (T (DV))))))))))
   (ADD-DCELL
    SHELL-NAME
    (PACK (LIST PREFIX-FOR-FUNCTIONS SHELL-NAME))
    (LIST
     (QUOTE LAMBDA)
     (ITERATE FOR X IN DESTRUCTOR-TUPLES COLLECT (CAR X))
     (CONS
      (QUOTE LIST)
      (CONS
       (QUOTE *1*SHELL-QUOTE-MARK)
       (CONS
        (LIST (QUOTE QUOTE)
              SHELL-NAME)
        (ITERATE FOR TUPLE IN DESTRUCTOR-TUPLES WITH TEMP
                 COLLECT
                 (PROGN
                   (SETQ
                    TEMP
                    (CONS (QUOTE OR)
                          (ITERATE FOR R IN (CDR (CADR TUPLE))
                                   COLLECT (LIST (QUOTE EQ)
                                                 (QUOTE *1*T)
                                                 (LIST
                                                  (PACK
                                                   (LIST
                                                    PREFIX-FOR-FUNCTIONS R))
                                                  (CAR TUPLE))))))
                   (COND ((NULL (CDR TEMP))
                          (COND ((EQ (CAR (CADR TUPLE))
                                     (QUOTE ONE-OF))
                                 (LIST (PACK (LIST PREFIX-FOR-FUNCTIONS
                                                   (CADDR TUPLE)))))
                                (T (CAR TUPLE))))
                         (T (LIST (QUOTE IF)
                                  (COND ((EQ (CAR (CADR TUPLE))
                                             (QUOTE ONE-OF))
                                         TEMP)
                                        (T (LIST (QUOTE NOT)
                                                 TEMP)))
                                  (CAR TUPLE)
                                  (LIST (PACK (LIST PREFIX-FOR-FUNCTIONS
                                                    (CADDR TUPLE))))))))))))))
    
   (RETURN NIL)))

(DEFUN ADD-SHELL0 (SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET ((IN-ADD-SHELL0 T)
        DEST-EXPRS-X SHELL-EXPR CURRENT-TYPE-NO DESTRUCTOR-ALIST
                     RENAMED-SHELL-EXPR DESTRUCTOR-NAMES DV TERM
                     NEW-TYPE-NO NAMES DEST-NAME ARG-NAME)
    (SETQ NEW-TYPE-NO (NEXT-AVAILABLE-TYPE-NO))
    (SETQ DESTRUCTOR-NAMES (ITERATE FOR TUPLE IN DESTRUCTOR-TUPLES
                                    COLLECT (CAR TUPLE)))
    (ADD-SHELL-ROUTINES SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)

; We here set the ERRATICP property to NIL for all the fn names 
; introduced.  Since the NIL isn't stored we don't actually do
; anything.

; The following ADD-FACT is out of place in the sense that it declares the
; type of the RECOGNIZER, but that is done for all the other new fn symbols
; after we have computed the DESTRUCTOR-ALIST.  If we do not do it now,
; the type restrictions involving RECOGNIZER may have unnecessary tests to
; coerce the term to be Boolean.

    (ADD-FACT RECOGNIZER (QUOTE TYPE-PRESCRIPTION-LST)
              (CONS SHELL-NAME (CONS TYPE-SET-BOOLEAN
                                     (QUOTE (NIL)))))
    (SETQ DESTRUCTOR-ALIST
          (ITERATE FOR X IN DESTRUCTOR-TUPLES
                   COLLECT (CONS (CAR X)
                                 (MAKE-TYPE-RESTRICTION
                                  (CADR X)
                                  (CADDR X)
                                  RECOGNIZER NEW-TYPE-NO))))
    (ADD-TYPE-SET-LEMMAS SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-ALIST)
    (COND (DESTRUCTOR-NAMES
           (SETQ SHELL-EXPR (CONS-TERM SHELL-NAME DESTRUCTOR-NAMES))
           (ITERATE FOR PAIR IN DESTRUCTOR-ALIST DO
                    (PROGN
                      (SETQ DEST-NAME (CAR PAIR))
                      (SETQ ARG-NAME DEST-NAME)
                      (MATCH (CDR PAIR) (TYPE-RESTRICTION TERM & DV))
                      (ADD-AXIOM1
                       (PACK (LIST DEST-NAME (QUOTE -) SHELL-NAME))
                       (QUOTE (REWRITE))
                       (FCONS-TERM*
                        (QUOTE EQUAL)
                        (FCONS-TERM* DEST-NAME SHELL-EXPR)
                        (COND ((EQUAL TERM TRUE)
                               ARG-NAME)
                              (T (FCONS-TERM* (QUOTE IF)
                                              (SUBST-VAR ARG-NAME
                                                         (QUOTE X)
                                                         TERM)
                                              ARG-NAME DV)))))
                      (ADD-AXIOM1 (PACK (LIST DEST-NAME (QUOTE -N)
                                              RECOGNIZER))
                                  (QUOTE (REWRITE))
                                  (FCONS-TERM*
                                   (QUOTE IMPLIES)
                                   (FCONS-TERM* (QUOTE NOT)
                                                (FCONS-TERM* RECOGNIZER
                                                             (QUOTE X)))
                                   (FCONS-TERM* (QUOTE EQUAL)
                                                (FCONS-TERM* DEST-NAME
                                                             (QUOTE X))
                                                DV)))
                      (AND (NOT (EQUAL TERM TRUE))
                           (ADD-AXIOM1
                            (PACK (LIST DEST-NAME (QUOTE -TYPE-RESTRICTION)))
                            (QUOTE (REWRITE))
                            (FCONS-TERM* (QUOTE IMPLIES)
                                         (NEGATE (SUBST-VAR DEST-NAME
                                                            (QUOTE X)
                                                            TERM))
                                         (FCONS-TERM* (QUOTE EQUAL)
                                                      SHELL-EXPR
                                                      (SUBST-VAR
                                                       DV
                                                       DEST-NAME
                                                       SHELL-EXPR)))))
                      (ADD-AXIOM1
                       (PACK (LIST DEST-NAME (QUOTE -LESSP)))
                       (QUOTE (REWRITE))
                       (FCONS-TERM*
                        (QUOTE IMPLIES)
                        (COND (BTM-FN-SYMB
                               (FCONS-TERM*
                                (QUOTE AND)
                                (FCONS-TERM* RECOGNIZER (QUOTE X))
                                (FCONS-TERM* (QUOTE NOT)
                                             (FCONS-TERM* (QUOTE EQUAL)
                                                          (QUOTE X)
                                                          (CONS-TERM
                                                           BTM-FN-SYMB NIL)))))
                              (T (FCONS-TERM* RECOGNIZER (QUOTE X))))
                        (FCONS-TERM* (QUOTE LESSP)
                                     (FCONS-TERM*
                                      (QUOTE COUNT)
                                      (FCONS-TERM* DEST-NAME
                                                   (QUOTE X)))
                                     (FCONS-TERM* (QUOTE COUNT)
                                                  (QUOTE X)))))
                      (ADD-AXIOM1
                       (PACK (LIST DEST-NAME (QUOTE -LESSEQP)))
                       (QUOTE (REWRITE))
                       (FCONS-TERM*
                        (QUOTE NOT)
                        (FCONS-TERM* (QUOTE LESSP)
                                     (FCONS-TERM* (QUOTE COUNT) (QUOTE X))
                                     (FCONS-TERM*
                                      (QUOTE COUNT)
                                      (FCONS-TERM* DEST-NAME (QUOTE X))))))))
           (SETQ RENAMED-SHELL-EXPR
                 (CONS-TERM SHELL-NAME
                            (ITERATE FOR DEST IN DESTRUCTOR-NAMES
                                     COLLECT (PACK (LIST DEST (QUOTE -))))))
           (ADD-AXIOM1
            (PACK (LIST SHELL-NAME (QUOTE -EQUAL)))
            (QUOTE (REWRITE))
            (FCONS-TERM*
             (QUOTE EQUAL)
             (FCONS-TERM* (QUOTE EQUAL) SHELL-EXPR RENAMED-SHELL-EXPR)
             (CONJOIN
              (ITERATE FOR ARG1 IN (FARGS SHELL-EXPR)
                       AS ARG2 IN (FARGS RENAMED-SHELL-EXPR)
                       AS PAIR IN DESTRUCTOR-ALIST
                       COLLECT
                       (PROGN
                         (MATCH (CDR PAIR) (TYPE-RESTRICTION TERM & DV))
                         (COND
                          ((EQUAL TERM TRUE)
                           (FCONS-TERM* (QUOTE EQUAL) ARG1 ARG2))
                          (T (FCONS-TERM*
                              (QUOTE IF)
                              (SUBST-VAR ARG1 (QUOTE X) TERM)
                              (FCONS-TERM* (QUOTE IF)
                                           (SUBST-VAR ARG2 (QUOTE X) TERM)
                                           (FCONS-TERM* (QUOTE EQUAL)
                                                        ARG1 ARG2)
                                           (FCONS-TERM* (QUOTE EQUAL) ARG1 DV))
                              (FCONS-TERM* (QUOTE IF)
                                           (SUBST-VAR ARG2 (QUOTE X) TERM)
                                           (FCONS-TERM* (QUOTE EQUAL) DV ARG2)
                                           TRUE))))))
              NIL)))
           (SETQ DEST-EXPRS-X (ITERATE FOR DEST-NAME IN DESTRUCTOR-NAMES
                                       COLLECT
                                       (FCONS-TERM* DEST-NAME (QUOTE X))))
           (ADD-AXIOM1
            (PACK (CONS SHELL-NAME
                        (ITERATE FOR DEST-NAME IN DESTRUCTOR-NAMES
                                 NCONC (LIST (QUOTE -) DEST-NAME))))
            (QUOTE (REWRITE))
            (FCONS-TERM*
             (QUOTE EQUAL)
             (CONS-TERM SHELL-NAME DEST-EXPRS-X)
             (FCONS-TERM*
              (QUOTE IF)
              (COND
               (BTM-FN-SYMB
                (FCONS-TERM*
                 (QUOTE AND)
                 (FCONS-TERM* RECOGNIZER (QUOTE X))
                 (FCONS-TERM* (QUOTE NOT)
                              (FCONS-TERM* (QUOTE EQUAL)
                                           (QUOTE X)
                                           (CONS-TERM
                                            BTM-FN-SYMB NIL)))))
               (T (FCONS-TERM* RECOGNIZER (QUOTE X))))
              (QUOTE X)
              (CONS-TERM SHELL-NAME
                         (ITERATE FOR X IN DESTRUCTOR-ALIST
                                  COLLECT (ACCESS TYPE-RESTRICTION DEFAULT
                                                  (CDR X)))))))
           (ADD-AXIOM1
            (PACK (NCONC1 (CDR (ITERATE FOR DEST-NAME IN DESTRUCTOR-NAMES
                                        NCONC (LIST (QUOTE -) DEST-NAME)))
                          (QUOTE -ELIM)))
            (QUOTE (ELIM))
            (FCONS-TERM*
             (QUOTE IMPLIES)
             (COND
              (BTM-FN-SYMB
               (FCONS-TERM* (QUOTE AND)
                            (FCONS-TERM* RECOGNIZER (QUOTE X))
                            (FCONS-TERM*
                             (QUOTE NOT)
                             (FCONS-TERM* (QUOTE EQUAL)
                                          (QUOTE X)
                                          (CONS-TERM
                                           BTM-FN-SYMB NIL)))))
              (T (FCONS-TERM* RECOGNIZER (QUOTE X))))
             (FCONS-TERM* (QUOTE EQUAL)
                          (CONS-TERM SHELL-NAME DEST-EXPRS-X)
                          (QUOTE X))))
           (ADD-AXIOM1
            (PACK (LIST (QUOTE COUNT-) SHELL-NAME))
            (QUOTE (REWRITE))
            (FCONS-TERM*
             (QUOTE EQUAL)
             (FCONS-TERM* (QUOTE COUNT) SHELL-EXPR)
             (FCONS-TERM*
              (QUOTE ADD1)
              (PLUSJOIN
               (ITERATE FOR X IN (FARGS SHELL-EXPR)
                        AS PAIR IN DESTRUCTOR-ALIST
                        COLLECT
                        (PROGN
                          (MATCH (CDR PAIR) (TYPE-RESTRICTION TERM & DV))
                          (COND ((EQUAL TERM TRUE)
                                 (FCONS-TERM* (QUOTE COUNT) X))
                                (T (FCONS-TERM* (QUOTE IF)
                                                (SUBST-VAR X (QUOTE X)
                                                           TERM)
                                                (FCONS-TERM* (QUOTE COUNT) X)
                                                ZERO))))))))))

;  The following clause fixes an omission noted by Bill Bevier.

          (BTM-FN-SYMB
           (ADD-AXIOM1
            (PACK (LIST RECOGNIZER (QUOTE -ELIMINATOR)))
            (LIST (QUOTE (REWRITE)))
            (FCONS-TERM* (QUOTE EQUAL)
                         (FCONS-TERM* RECOGNIZER (QUOTE X))
                         (FCONS-TERM* (QUOTE OR)
                                      (FCONS-TERM* (QUOTE EQUAL)
                                                   (QUOTE X)
                                                   (CONS-TERM BTM-FN-SYMB NIL))
                                      (FCONS-TERM* (QUOTE EQUAL)
                                                   (QUOTE X)
                                                   (CONS-TERM SHELL-NAME
                                                              NIL)))))))
    (LIST SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)))

(DEFUN ADD-SUB-FACT (ATM PROP VAL TUPLE INIT)

;   Here is the spec for ADD-SUB-FACT.  It takes 5 args ATM PROP VAL TUPLE and
;   INIT but only a few of these make sense in combination.  To store a new
;   fact you call ADD-SUB-FACT using ATM PROP and VAL.  If PROP is a variable
;   declared below we either CONS VAL to the front of PROPs top level value or
;   set PROP to VAL depending on whether PROP is ADDITIVE or SINGLE.  SET is
;   used in both cases.  If PROP is DCELL it means PUTD1 ATM to VAL.
;   Otherwise, PROP had better be an additive or single property declared below
;   and if so the appropriate ADDITIVE or SINGLE PUT1 is done.  If you want to
;   delete a previously added fact you call ADD-SUB-FACT with all args but
;   TUPLE NIL.  TUPLE should be the undo tuple produced by the adding of the
;   fact in question.  Before you begin to add or sub facts you must first
;   initialize the library file.  You do that by calling ADD-SUB-FACT with INIT
;   T and all other args NIL.  The initialization sets LIB-PROPS to the list of
;   properties declared below in the order of declaration -- making the first
;   property declared the one of highest priority.  Because the list of
;   declarations is used to generated LIB-PROPS you must include in it all of
;   the properties used by the event level abstraction itself, even those these
;   properties aren't technically yours.  These properties are IDATE SATELLITES
;   MAIN-EVENT EVENT, SEXPR and LOCAL-UNDO-TUPLES.  They should all be declared
;   with type HIDDEN rather than ADDITIVE or SINGLE.  The code will cause an
;   error if you leave out any built-in prop or use HIDDEN on any nonbuilt-in
;   one -- the whole purpose of your knowing about these properties and the
;   token HIDDEN is just to allow you to specify where in the list of
;   priorities they should be kept.  The other thing that initialization does
;   is set all variables declared below to NIL.  The HIDDEN variable CHRONOLOGY
;   should be declared explicitly.  We force you to do that so you'll always
;   remember we've claimed that variable name.

;   No property or variable name may contain lower case letters or be NIL.  If
;   this convention is violated the code produced for ADD-SUB-FACT is garbage
;   because we generate the code with SUBST's that hit lower case names and we
;   sometimes generate SELECTQs with NIL first elements of clauses.

;   For ADDITIVE data you must supply a form, which may involve VAL as a free
;   var, for computing from VAL some datum to be stored in the undo tuple.
;   This datum must be sufficient for distinguishing that VAL from all others
;   in that ADDITIVE pot.  In particular, to find the VAL in question the
;   undoing mechanism scans the pot and evaluates the form again for each
;   entry, with VAL bound to the entry, and removes from the pot the first
;   entry for which that form computes an EQUAL datum.  The form in question
;   must not contain any free variables other than VAL and must not cause any
;   side-effects.

  (ADD-SUB-FACT-BODY (TYPE-PRESCRIPTION-LST ADDITIVE PROPERTY (CAR VAL))
                     (LEMMAS ADDITIVE PROPERTY (ACCESS REWRITE-RULE NAME VAL))
                     (TOTALP-LST ADDITIVE PROPERTY (CAR VAL))
                     (LINEAR-LEMMAS ADDITIVE PROPERTY
                                    (ACCESS LINEAR-LEMMA NAME VAL))
                     (QUICK-BLOCK-INFO SINGLE PROPERTY)
                     (SDEFN SINGLE PROPERTY)
                     (LISP-CODE SINGLE PROPERTY)
                     (SUBRP SINGLE PROPERTY)
                     (BODY SINGLE PROPERTY)
                     (ERRATICP SINGLE PROPERTY)
                     (TYPE-RESTRICTIONS SINGLE PROPERTY)
                     (INDUCTION-MACHINE SINGLE PROPERTY)
                     (LEVEL-NO SINGLE PROPERTY)
                     (JUSTIFICATIONS SINGLE PROPERTY)
                     (IDATE HIDDEN PROPERTY)
                     (ELIMINATE-DESTRUCTORS-SEQ SINGLE PROPERTY)
                     (ELIMINATE-DESTRUCTORS-DESTS SINGLE PROPERTY)
                     (CONTROLLER-POCKETS SINGLE PROPERTY)
                     (SATELLITES HIDDEN PROPERTY)
                     (MAIN-EVENT HIDDEN PROPERTY)
                     (IMMEDIATE-DEPENDENTS0 ADDITIVE PROPERTY VAL)
                     (EVENT HIDDEN PROPERTY)
                     (LOCAL-UNDO-TUPLES HIDDEN PROPERTY)
                     (SEXPR HIDDEN PROPERTY)

;   SEXPR is used to remember the defn of 1fns and is managed by PUTD1 and
;   friends.  It is never hit with ADD-FACT and the 1fn never finds its way
;   onto LIB-ATOMS-WITH-PROPS.  We include it here to remind ourselves that
;   this property name is used already.

                     (NONCONSTRUCTIVE-AXIOM-NAMES ADDITIVE VARIABLE VAL)
                     (*1*BTM-OBJECTS ADDITIVE VARIABLE VAL)
                     (RECOGNIZER-ALIST ADDITIVE VARIABLE VAL)
                     (TRUE-COMPOUND-RECOGNIZER-ALIST ADDITIVE VARIABLE
                                                     (CDDR VAL))
                     (FALSE-COMPOUND-RECOGNIZER-ALIST ADDITIVE VARIABLE
                                                      (CDDR VAL))
                     (SHELL-ALIST ADDITIVE VARIABLE VAL)
                     (SINGLETON-TYPE-SETS ADDITIVE VARIABLE VAL)
                     (GENERALIZE-LEMMAS ADDITIVE
                                        VARIABLE
                                        (ACCESS GENERALIZE-LEMMA NAME VAL))
                     (SHELL-POCKETS ADDITIVE VARIABLE VAL)
                     (DEFINED-FUNCTIONS-TOGGLED ADDITIVE VARIABLE VAL)
                     (DISABLED-LEMMAS ADDITIVE VARIABLE VAL)
                     (*1*THM-MODE$ SINGLE VARIABLE VAL)
                     (FREE-VARS-IN-REWRITE-RHSS ADDITIVE VARIABLE VAL)
                     (CHRONOLOGY HIDDEN VARIABLE)))

(DEFUN ADD-TERM-TO-POT-LST (TERM POT-LST FLG ALL-NEW-FLG)
  (PROG NIL
        (COND ((EQ CURRENT-LIT CURRENT-ATM)
               (COND ((AND (EQ FLG NIL)
                           (EQUAL TERM CURRENT-LIT))
                      (RETURN POT-LST))))
              (T (COND ((AND FLG (EQUAL TERM CURRENT-ATM))
                        (RETURN POT-LST)))))
        (RPLACA ADD-TERM-TO-POT-LST-TEMP TERM)
        (RETURN (ADD-TERMS-TO-POT-LST ADD-TERM-TO-POT-LST-TEMP
                                      POT-LST FLG ALL-NEW-FLG))))

(DEFUN ADD-TERMS-TO-POT-LST (TERM-LST POT-LST FLG ALL-NEW-FLG)

;   Only called with POT-LST EQ to SIMPLIFY-CLAUSE-POT-LST.

;   Either returns 'CONTRADICTION, in which case there is a proof of F
;   from TYPE-ALIST, the assumption of the members of TERM-LST true or
;   false according as FLG is T or NIL, LINEAR-ASSUMPTIONS, and a
;   subset S of the polys in POT-LST such that if x = (LIST 'MARK) is
;   a MEMBER-EQ of the LEMMAS of a member of S then x is in
;   LEMMAS-USED-BY-LINEAR,

;   or returns a new pot lst such that for each poly p in the new pot
;   lst there is a proof of p from TYPE-ALIST, the assumption of the
;   members of TERM-LST true or false according as FLG is T or NIL,
;   and a subset S of the polys in the input POT-LST such that if x =
;   (LIST 'MARK) is a MEMBER-EQ of the lemmas of a member of S, then x
;   is in the LEMMAS field of p.

;   In no case is the lemma stack or linearize assumptions stack visibly
;   affected by this call.

;   Not necessary for soundness, but true, are the facts that the lemmas
;   (ignoring typeset lemmas, of course) that are used in the proofs are
;   included in the LEMMAS fields.  Furthermore, the LITERALS fields contain
;   the literals that were passed in TERM-LST to ADD-TERMS-TO-POT-LST and used
;   to construct, with LINEARIZE, the original polynomials.

;   If ALL-NEW-FLG is T then every addend in the pot list is treated as new for
;   the consideration of lemmas to be added.  Otherwise, we add lemmas for the
;   addends that are introduced by this call.

  (PROG (POLY-LST SPLIT-LST LST BASIC-POT-LST UNIFY-SUBST POT-LST1
                  POT-LST2)
        (COND (NO-BUILT-IN-ARITH-FLG (RETURN NIL)))
        (ITERATE FOR TERM IN TERM-LST DO
                 (PROGN (SETQ LST (LINEARIZE TERM FLG))
                        (COND ((NULL LST))
                              ((NULL (CDR LST))
                               (SETQ POLY-LST (APPEND (CAR LST) POLY-LST)))
                              ((NULL (CDDR LST))
                               (SETQ SPLIT-LST (CONS LST SPLIT-LST)))
                              (T (ER HARD NIL LINEARIZE |returned| |a| |list|
                                     |with|
                                     |more| |than| 2 |elements| EXCL)))))
        (SETQ BASIC-POT-LST (ADD-EQUATIONS-TO-POT-LST POLY-LST
                                                      POT-LST
                                                      ALL-NEW-FLG))
        (ITERATE
         FOR PAIR IN SPLIT-LST WITH MARK = (LIST (QUOTE MARK))
         WHILE (NOT (EQ BASIC-POT-LST (QUOTE CONTRADICTION)))
         DO

;   We will add both branches separately and hope at least one gives a
;   contradiction.  Suppose the first branch does not but the second does.
;   Then we will use the first branch's pot list in the future.  But we must
;   add to the assumptions and lemmas of the first branch those of the second.
;   To recognize the polys in the first branch's pot lst that descend from the
;   polys in the first branch we will mark them by putting a unique CONS in the
;   lemmas field.

         (PROGN
           (ITERATE FOR POLY IN (CAR PAIR)
                    DO (CHANGE POLY LEMMAS POLY (LIST MARK)))
           (SETQ POT-LST1 (ADD-EQUATIONS-TO-POT-LST
                           (CAR PAIR) BASIC-POT-LST ALL-NEW-FLG))
           (COND
            ((EQ POT-LST1 (QUOTE CONTRADICTION))
             (ITERATE FOR POLY IN (CADR PAIR)
                      DO (PROGN (CHANGE POLY LEMMAS POLY
                                        (REMOVE MARK LEMMAS-USED-BY-LINEAR))
                                (CHANGE POLY ASSUMPTIONS POLY
                                        (UNION-EQUAL LINEAR-ASSUMPTIONS
                                                     (ACCESS POLY
                                                             ASSUMPTIONS
                                                             POLY)))))
             (SETQ BASIC-POT-LST (ADD-EQUATIONS-TO-POT-LST
                                  (CADR PAIR)
                                  BASIC-POT-LST ALL-NEW-FLG)))
            (T (SETQ POT-LST2 (ADD-EQUATIONS-TO-POT-LST
                               (CADR PAIR)
                               BASIC-POT-LST ALL-NEW-FLG))
               (COND
                ((EQ POT-LST2 (QUOTE CONTRADICTION))
                 (ITERATE FOR POT IN POT-LST1
                          DO
                          (PROGN
                            (ITERATE FOR POLY
                                     IN (ACCESS LINEAR-POT POSITIVES POT)
                                     WHEN (MEMBER-EQ MARK (ACCESS POLY LEMMAS
                                                                  POLY))
                                     DO
                                     (PROGN (CHANGE
                                             POLY ASSUMPTIONS POLY
                                             (UNION-EQUAL
                                              LINEAR-ASSUMPTIONS
                                              (ACCESS POLY ASSUMPTIONS POLY)))
                                            (CHANGE
                                             POLY LEMMAS POLY
                                             (UNION-EQ
                                              LEMMAS-USED-BY-LINEAR
                                              (REMOVE MARK
                                                      (ACCESS POLY
                                                              LEMMAS
                                                              POLY))))))
                            (ITERATE FOR POLY
                                     IN (ACCESS LINEAR-POT NEGATIVES POT)
                                     WHEN (MEMBER-EQ MARK
                                                     (ACCESS POLY LEMMAS POLY))
                                     DO
                                     (PROGN
                                       (CHANGE POLY ASSUMPTIONS POLY
                                               (UNION-EQUAL
                                                LINEAR-ASSUMPTIONS
                                                (ACCESS POLY
                                                        ASSUMPTIONS POLY)))
                                       (CHANGE POLY LEMMAS POLY
                                               (UNION-EQ LEMMAS-USED-BY-LINEAR
                                                         (REMOVE MARK
                                                                 (ACCESS
                                                                  POLY
                                                                  LEMMAS
                                                                  POLY))))))))
                 (SETQ BASIC-POT-LST POT-LST1)))))))
        (RETURN BASIC-POT-LST)))

(DEFUN ADD-TO-SET (X Y)
  (COND ((MEMBER-EQUAL X Y) Y)
        (T (CONS X Y))))

(DEFUN ADD-TO-SET-EQ (X LST)
  (COND ((MEMBER-EQ X LST) LST)
        (T (CONS X LST))))

(DEFUN ADD-TYPE-SET-LEMMAS
  (SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-ALIST)
  (LET (CURRENT-TYPE-NO)
    (SETQ CURRENT-TYPE-NO (NEXT-AVAILABLE-TYPE-NO))
    (ADD-FACT NIL (QUOTE SHELL-ALIST)
              (CONS SHELL-NAME CURRENT-TYPE-NO))
    (ADD-FACT NIL (QUOTE SHELL-POCKETS)
              (CONS SHELL-NAME
                    (ITERATE FOR X IN DESTRUCTOR-ALIST COLLECT (CAR X))))
    (ADD-FACT SHELL-NAME (QUOTE TYPE-PRESCRIPTION-LST)
              (CONS SHELL-NAME
                    (CONS (TSLOGBIT CURRENT-TYPE-NO)
                          (MAKE-LIST (LENGTH DESTRUCTOR-ALIST)))))
    (ADD-FACT SHELL-NAME (QUOTE SUBRP) *1*T)
    (ADD-FACT SHELL-NAME (QUOTE TOTALP-LST) (CONS SHELL-NAME T))
    (AND DESTRUCTOR-ALIST
         (ADD-FACT SHELL-NAME (QUOTE TYPE-RESTRICTIONS)
                   (ITERATE FOR X IN DESTRUCTOR-ALIST COLLECT (CDR X))))
    (COND ((AND (NULL DESTRUCTOR-ALIST)
                (NULL BTM-FN-SYMB))
           (ADD-FACT NIL (QUOTE SINGLETON-TYPE-SETS)
                     (TSLOGBIT CURRENT-TYPE-NO))))
    (AND BTM-FN-SYMB (ADD-FACT NIL (QUOTE *1*BTM-OBJECTS)
                               BTM-FN-SYMB))
    (COND (BTM-FN-SYMB
           (ADD-FACT BTM-FN-SYMB (QUOTE TYPE-PRESCRIPTION-LST)
                     (CONS SHELL-NAME
                           (CONS (TSLOGBIT CURRENT-TYPE-NO)
                                 NIL)))
           (ADD-FACT BTM-FN-SYMB (QUOTE SUBRP) *1*T)
           (ADD-FACT BTM-FN-SYMB (QUOTE TOTALP-LST) (CONS SHELL-NAME T))))
    (ADD-FACT NIL (QUOTE RECOGNIZER-ALIST)
              (CONS RECOGNIZER (TSLOGBIT CURRENT-TYPE-NO)))

; Here we once had:
;
;   (ADD-FACT RECOGNIZER (QUOTE TYPE-PRESCRIPTION-LST)
;             (CONS SHELL-NAME (CONS TYPE-SET-BOOLEAN
;                                    (QUOTE (NIL)))))
;
; But it was moved out into ADD-SHELL0 so that it takes place before
; the destructor alist is built.  Thus, if the new RECOGNIZER is used
; in the type restrictions of the destructors, it is known to be Boolean.

    (ADD-FACT RECOGNIZER (QUOTE SUBRP) *1*T)
    (ADD-FACT RECOGNIZER (QUOTE TOTALP-LST) (CONS SHELL-NAME T))
    (ITERATE FOR PAIR IN DESTRUCTOR-ALIST
             DO (PROGN (ADD-FACT (CAR PAIR)
                                 (QUOTE TYPE-PRESCRIPTION-LST)
                                 (CONS SHELL-NAME
                                       (CONS (ACCESS TYPE-RESTRICTION TYPE-SET
                                                     (CDR PAIR))
                                             (QUOTE (NIL)))))
                       (ADD-FACT (CAR PAIR) (QUOTE SUBRP) *1*T)
                       (ADD-FACT (CAR PAIR) (QUOTE TOTALP-LST)
                                 (CONS SHELL-NAME T))))
    NIL))

(DEFUN ADMITTED-FUNCTIONP (FNNAME)
  (AND (GET FNNAME 'TYPE-PRESCRIPTION-LST)
       (OR (NON-RECURSIVE-DEFNP FNNAME)
           (GET FNNAME (QUOTE JUSTIFICATIONS)))))

(DEFUN ALL-ARGLISTS (FNNAME TERM)

;   Returns the set of arglists of all subterms of TERM with function symbol
;   FNNAME.

  (COND
   ((VARIABLEP TERM)
    NIL)
   ((FQUOTEP TERM)
    (COND
     ((OR (ASSOC-EQ FNNAME SHELL-ALIST)
          (MEMBER-EQ FNNAME *1*BTM-OBJECTS))
      (ER HARD NIL ALL-ARGLISTS |does| |not| |know| |how| |to| |go| |into|
          |QUOTEd| |constants| |for| |bottom| |objects| |and| |shell|
          |constructors| |.|))
     (T NIL)))
   ((EQ (FFN-SYMB TERM)
        FNNAME)
    (ADD-TO-SET (FARGS TERM)
                (ITERATE FOR ARG IN (FARGS TERM)
                         WITH ITERATE-ANS
                         DO (SETQ ITERATE-ANS
                                  (UNION-EQUAL (ALL-ARGLISTS FNNAME ARG)
                                               ITERATE-ANS))
                         FINALLY (RETURN ITERATE-ANS))))
   (T (ITERATE FOR ARG IN (FARGS TERM) WITH ITERATE-ANS
               DO (SETQ ITERATE-ANS
                        (UNION-EQUAL (ALL-ARGLISTS FNNAME ARG) ITERATE-ANS))
               FINALLY (RETURN ITERATE-ANS)))))

(DEFUN ALL-FNNAMES (TERM)
  (LET (ANS) (ALL-FNNAMES1 TERM) ANS))

(DEFUN ALL-FNNAMES1 (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) (ALL-FNNAMES1-EVG (CADR TERM)))
        (T (COND ((AND (NOT (EQ (QUOTE IF) (FFN-SYMB TERM)))
                       (NOT (EQ (QUOTE EQUAL) (FFN-SYMB TERM))))
                  (SETQ ANS (ADD-TO-SET (FFN-SYMB TERM)
                                        ANS))))
           (ITERATE FOR ARG IN (FARGS TERM) DO (ALL-FNNAMES1 ARG)))))

(DEFUN ALL-FNNAMES1-EVG (EVG)
  (COND ((ATOM EVG)
         (SETQ ANS (UNION-EQ ANS (COND ((EQ EVG *1*T) (QUOTE (TRUE)))
                                       ((EQ EVG *1*F) (QUOTE (FALSE)))
                                       ((INTEGERP EVG)
                                        (COND ((< EVG 0)
                                               (QUOTE (MINUS ADD1 ZERO)))
                                              ((EQUAL EVG 0)
                                               (QUOTE (ZERO)))
                                              (T (QUOTE (ADD1 ZERO)))))
                                       (T (QUOTE (PACK CONS ADD1 ZERO)))))))
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK)
         (SETQ ANS (ADD-TO-SET (CADR EVG) ANS))
         (ITERATE FOR X IN (CDDR EVG) DO (ALL-FNNAMES1-EVG X)))
        (T (SETQ ANS (ADD-TO-SET (QUOTE CONS) ANS))
           (ALL-FNNAMES1-EVG (CAR EVG))
           (ALL-FNNAMES1-EVG (CDR EVG)))))

(DEFUN ALL-INSERTIONS (X FINAL-SEG INIT-SEG)

;   Inserts X into FINAL-SEG in all possible ways - assuming INIT-SEG is NIL
;   at the top most call.

  (COND ((NULL FINAL-SEG) (LIST (APPEND INIT-SEG (LIST X))))
        (T (CONS (APPEND INIT-SEG (APPEND (LIST X) FINAL-SEG))
                 (ALL-INSERTIONS X (CDR FINAL-SEG)
                                 (NCONC1 INIT-SEG (CAR FINAL-SEG)))))))

(DEFUN ALL-PATHS (FORM)

;   This function is used only by OPTIMIZE-COMMON-SUBTERMS.  It is assumed that
;   FORM is as described in the documentation of OPTIMIZE-COMMON-SUBTERMS.  In
;   particular, *2*IF and QUOTE are the only symbols used as function symbols
;   in FORM that are not spread LAMBDAs.

;   A real-path through FORM is defined to be a list of all of the subterms
;   of FORM that are MEMBers of COMMONSUBTERMS and that are evaluated in the
;   evaluation of FORM under some assignment of values to the variables in
;   FORM.  The terms are listed in reverse order of evaluation completion, with
;   FORM coming first.

;   ALL-PATHS returns a list L of pairs.  Each pair consists of a flag doted
;   with a list of subterms of FORM that are members of COMMONSUBTERMS.  For
;   each real-path P through FORM, there exists a member (FLG . L1) of L such
;   that L1 is PATH-EQ to P and (a) if FLG is NIL, then any evaluation of FORM
;   whose real-path is P returns NIL and (b) if FLG is T, then any such
;   evaluation returns something other than NIL.  If FLG is ?, nothing is
;   asserted.

;   Not every member of L need correspond to real-path.  For example, even if
;   FOO always returns T, (ALL-PATHS (*2*IF (FOO X) (G X) (H X))) will return a
;   list of length two.

;   In the documentation of OPTIMIZE-COMMON-SUBTERMS, we define the concepts
;   FIRST, SECOND, and ISOLATED on a path.  From the foregoing specification of
;   the output of ALL-PATHS, we may conclude that if a MEMBer of COMMONSUBTERMS
;   is SECOND on every path in (ALL-PATHS FORM) on which it occurs, then it is
;   SECOND on any real-path through FORM on which it occurs.  Furthermore, we
;   may conclude that if a MEMBer of COMMON-SUBTERMS is ever FIRST on any
;   real-path through FORM, then it is FIRST on some path in (ALL-PATHS FORM).
;   These two observations are the key to the soundness of
;   OPTIMIZE-COMMON-SUBTERMS. (A) If a term is ever FIRST on any path of
;   ALL-PATHS, then the appropriate *2*variable is set when it is executed (if
;   it has not already been set.)  (B) If a term is SECOND on each path of
;   (ALL-PATHS FORM), then we assume that the appropriate *2*variable has been
;   set and we use it.

;   If a term is FIRST on each path of ALL-PATHS on which it occurs, then it
;   is first on each real-path.  Thus there is no loss of efficiency in simply
;   SETting the appropriate *2*variable.

  (LET (TEMP)
    (COND ((OR (EQ FORM NIL) (EQUAL FORM (QUOTE (QUOTE NIL))))
           (LIST (CONS NIL NIL)))
          ((OR (EQ FORM T)
               (AND (CONSP FORM) (EQ (CAR FORM) (QUOTE QUOTE)))
               (INTEGERP FORM))
           (LIST (CONS T NIL)))
          ((ATOM FORM)
           (LIST (CONS (QUOTE ?) NIL)))
          ((NOT (EQ (FFN-SYMB FORM) (QUOTE *2*IF)))
           (ITERATE FOR PICK
                    IN (ALL-PICKS (ITERATE FOR ARG IN (REVERSE (FARGS FORM))
                                           COLLECT (CDR-ALL (ALL-PATHS ARG))))
                    WITH ITERATE-ANS
                    DO
                    (SETQ ITERATE-ANS
                          (PATH-ADD-TO-SET
                           (CONS (QUOTE ?)
                                 (COND ((MEMBER-EQ FORM COMMONSUBTERMS)
                                        (CONS FORM
                                              (ITERATE FOR P IN PICK
                                                       APPEND P)))
                                       (T (ITERATE FOR P IN PICK APPEND P))))
                           ITERATE-ANS))
                    FINALLY (RETURN ITERATE-ANS)))
          (T
           (PATH-UNION
            (ITERATE FOR PICK
                     IN (ALL-PICKS
                         (LIST (ALL-PATHS (CADDR FORM))
                               (ITERATE FOR X IN (SETQ TEMP
                                                       (ALL-PATHS (CADR FORM)))
                                        UNLESS (EQ (CAR X) NIL)
                                        COLLECT (CDR X))))
                     WITH ITERATE-ANS
                     DO
                     (SETQ ITERATE-ANS
                           (PATH-ADD-TO-SET
                            (CONS (CAR (CAR PICK))
                                  (COND ((MEMBER-EQ FORM COMMONSUBTERMS)
                                         (CONS FORM (APPEND (CDR (CAR PICK))
                                                            (CADR PICK))))
                                        (T (APPEND (CDR (CAR PICK))
                                                   (CADR PICK)))))
                            ITERATE-ANS))
                     FINALLY (RETURN ITERATE-ANS))
            (ITERATE FOR PICK
                     IN (ALL-PICKS (LIST (ALL-PATHS (CADDDR FORM))
                                         (ITERATE FOR X IN TEMP
                                                  UNLESS (EQ T (CAR X))
                                                  COLLECT (CDR X))))
                     WITH ITERATE-ANS
                     DO
                     (SETQ ITERATE-ANS
                           (PATH-ADD-TO-SET
                            (CONS (CAR (CAR PICK))
                                  (COND ((MEMBER-EQ FORM COMMONSUBTERMS)
                                         (CONS FORM (APPEND (CDR (CAR PICK))
                                                            (CADR PICK))))
                                        (T (APPEND (CDR (CAR PICK))
                                                   (CADR PICK)))))
                            ITERATE-ANS))
                     FINALLY (RETURN ITERATE-ANS)))))))

(DEFUN ALL-PICKS (POCKET-LIST)

;   POCKET-LIST is a list of pockets and this fn returns all of the possible
;   ways you can pick one thing from each pocket.

  (COND ((NULL POCKET-LIST) (LIST NIL))
        (T (ITERATE FOR PICK IN (ALL-PICKS (CDR POCKET-LIST))
                    NCONC (ITERATE FOR CHOICE IN (CAR POCKET-LIST)
                                   COLLECT (CONS CHOICE PICK))))))

(DEFUN ALL-VARS (TERM)

;   Collects vars in TERM in reverse print order of first occurrences.  This
;   ordering is exploited in LOOP-STOPPER.

  (LET (ANS) (ALL-VARS1 TERM) ANS))

(DEFUN ALL-VARS-BAG (TERM) (LET (ANS) (ALL-VARS-BAG1 TERM) ANS))

(DEFUN ALL-VARS-BAG1 (TERM)
  (COND ((VARIABLEP TERM) (SETQ ANS (CONS TERM ANS)))
        ((FQUOTEP TERM) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM) DO (ALL-VARS-BAG1 ARG)))))

(DEFUN ALL-VARS-LST (LST)
  (ITERATE FOR TERM IN LST WITH ITERATE-ANS
           DO (SETQ ITERATE-ANS (UNION-EQ (ALL-VARS TERM) ITERATE-ANS))
           FINALLY (RETURN ITERATE-ANS)))

(DEFUN ALL-VARS1 (TERM)
  (COND ((VARIABLEP TERM) (SETQ ANS (ADD-TO-SET TERM ANS)))
        ((FQUOTEP TERM) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM) DO (ALL-VARS1 ARG)))))

(DEFUN ALMOST-QUOTEP (TERM) (AND (NVARIABLEP TERM) (ALMOST-QUOTEP1 TERM)))

(DEFUN ALMOST-QUOTEP1 (TERM)
  (COND ((VARIABLEP TERM) T)
        ((FQUOTEP TERM) T)
        ((SHELLP TERM)
         (ITERATE FOR ARG IN (FARGS TERM) ALWAYS (ALMOST-QUOTEP1 ARG)))
        (T NIL)))

(DEFUN ALMOST-SUBSUMES (CL1 CL2)
  (COND ((NULL CL1)
         (SETQ ALMOST-SUBSUMES-LITERAL ALMOST-SUBSUMES-CONSTANT)
         T)
        ((MEMBER-EQUAL (CAR CL1) CL2)
         (ALMOST-SUBSUMES (CDR CL1) CL2))
        ((MEMB-NEGATIVE (CAR CL1) CL2)
         (COND ((SUBSETP-EQUAL (CDR CL1) CL2)
                (SETQ ALMOST-SUBSUMES-LITERAL (CAR CL1))
                T)
               (T NIL)))
        (T NIL)))

(DEFUN ALMOST-SUBSUMES-LOOP (LST)
  (LET (HITFLG ANS DEADLST)
    (SETQ HITFLG T)
    (ITERATE WHILE HITFLG
             DO
             (PROGN
               (SETQ HITFLG NIL)
               (SETQ ANS NIL)
               (SETQ DEADLST NIL)
               (ITERATE FOR CL1 IN LST
                        DO
                        (COND
                         ((ITERATE FOR CL2 IN LST
                                   WHEN (AND (NOT (EQ CL1 CL2))
                                             (NOT (MEMBER-EQ CL2 DEADLST)))
                                   THEREIS
                                   (COND
                                    ((ALMOST-SUBSUMES CL2 CL1)
                                     (SETQ DEADLST (CONS CL1 DEADLST))
                                     (COND
                                      ((EQ ALMOST-SUBSUMES-LITERAL
                                           ALMOST-SUBSUMES-CONSTANT)
                                       T)
                                      (T (SETQ HITFLG T)
                                         (SETQ ANS
                                               (CONS (REMOVE-NEGATIVE
                                                      ALMOST-SUBSUMES-LITERAL
                                                      CL1)
                                                     ANS))
                                         T)))
                                    (T NIL))))
                         (T (SETQ ANS (CONS CL1 ANS)))))
               (SETQ LST ANS)))
    ANS))

(DEFUN ALPHORDER (X Y)

;   ALPHORDER works on litatoms and numbers only.  It is a "less
;   than or equal" on the ordering in which numbers are compared
;   arithmetically, litatoms are compared with alphabetic ordering,
;   and all numbers come before all litatoms.

  (COND ((NUMBERP X)
         (COND ((NUMBERP Y) (<= X Y))
               (T T)))
        ((NUMBERP Y) NIL)
        (T (STRING<= (SYMBOL-NAME X)
                     (SYMBOL-NAME Y)))))

(DEFUN ANCESTORS (FNS)

;  ANCESTORS takes a list of functions symbols, FNS, and computes a
;  list of the DEFN, CONSTRAIN, ADD-SHELL and DCL events which introduce
;  functions symbols which are ancestors of members of FNS.

  (COND ((OR (AND FNS (ATOM FNS))
             (CDR (OUR-LAST FNS)))
         (ER SOFT (FNS) ANCESTORS |takes| |as| |its| |argument| |a|
             |list| |of| |function| |symbols| |but| (!PPR FNS NIL)
             |is| |not| |a| |list| |.|)))
  (ITERATE FOR FN IN FNS DO
           (OR (AND (SYMBOLP FN) (ARITY FN))
               (ER SOFT (FN) ANCESTORS |takes| |as| |its| |argument| |a|
                   |list| |of| |function| |symbols| |but| (!PPR FN NIL)
                   |is| |not| |a| |function| |symbol| |.|)))
  (ITERATE FOR EVN IN CHRONOLOGY DO
    (REMPROP EVN ANCESTORS-PROPERTY))
  (ITERATE FOR FN IN FNS DO
           (ANCESTORS1 (MAIN-EVENT-OF FN)))
  (ITERATE FOR EVN IN CHRONOLOGY
           WHEN (AND (GET EVN ANCESTORS-PROPERTY)
                     (NOT (EQ EVN 'GROUND-ZERO)))
           COLLECT EVN))

(DEFUN ANCESTORS1 (EVN)

;  EVN is the name of an event that introduces some function symbols,
;  e.g., a DEFN, DCL, CONSTRAIN, ADD-SHELL, or the BOOT-STRAP.

  (COND ((GET EVN ANCESTORS-PROPERTY)
         NIL)
        (T (SETF (GET EVN ANCESTORS-PROPERTY) T)
           (LET ((EVENT (GET EVN 'EVENT)))
                (COND ((OR (EQ (CAR EVENT) 'DEFN)
                           (EQ (CAR EVENT) 'CONSTRAIN))
                       (ITERATE FOR FN IN (ALL-FNNAMES (CADDDR EVENT))
                                DO
                                (ANCESTORS1 (MAIN-EVENT-OF FN))))
                      ((EQ (CAR EVENT) 'ADD-SHELL)
                       (ITERATE FOR TUPLE IN (CAR (CDDDDR EVENT))
                                DO
;   A TUPLE is of the form (ac (ONE-OF/NONE-OF r1 ... rn) base-fn)

                                (ITERATE FOR R IN (CDR (CADR TUPLE))
                                         DO (ANCESTORS1
                                             (MAIN-EVENT-OF R)))
                                (ANCESTORS1
                                 (MAIN-EVENT-OF (CADDR TUPLE))))))))))

(DEFUN APPLY-THEORY-HINTS (ENABLE-THEORIES DISABLE-THEORIES)
  (LET ((ENABLE-VAR (CADR (ASSOC-EQ (QUOTE ENABLE) HINT-VARIABLE-ALIST)))
        (DISABLE-VAR (CADR (ASSOC-EQ (QUOTE DISABLE) HINT-VARIABLE-ALIST))))
       (LET ((SAVED-ENABLE-LIST (SYMBOL-VALUE ENABLE-VAR))
             (SAVED-DISABLE-LIST (SYMBOL-VALUE DISABLE-VAR)))
            (COND
             ((EQUAL ENABLE-THEORIES '(T))
              (SET ENABLE-VAR T)
              (SET DISABLE-VAR
                   (SET-DIFF-EQ
                    (UNION-EQ (FORM-THEORY DISABLE-THEORIES)
                              SAVED-DISABLE-LIST)
                    SAVED-ENABLE-LIST)))
             ((EQUAL DISABLE-THEORIES '(T))
              (SET ENABLE-VAR
                   (UNION-EQ (SET-DIFF-EQ (FORM-THEORY ENABLE-THEORIES)
                                          SAVED-DISABLE-LIST)
                             SAVED-ENABLE-LIST))
              (SET DISABLE-VAR T))
             (T
              (SET ENABLE-VAR
                   (UNION-EQ (SET-DIFF-EQ (FORM-THEORY ENABLE-THEORIES)
                                          SAVED-DISABLE-LIST)
                             SAVED-ENABLE-LIST))
              (SET DISABLE-VAR
                   (UNION-EQ (SET-DIFF-EQ (FORM-THEORY DISABLE-THEORIES)
                                          SAVED-ENABLE-LIST)
                             SAVED-DISABLE-LIST)))))))

(DEFUN APPLY-HINTS (HINTS TERM)
  (COND (PETITIO-PRINCIPII (RETURN-FROM APPLY-HINTS TERM)))
  (COND ((ASSOC-EQ (QUOTE INDUCT) HINTS)
         (SETQ TERM (APPLY-INDUCT-HINT
                     (CADR (ASSOC-EQ (QUOTE INDUCT) HINTS))
                     TERM))))
  (COND ((ASSOC-EQ (QUOTE USE) HINTS)
         (SETQ TERM (APPLY-USE-HINT (CDR (ASSOC-EQ (QUOTE USE) HINTS)) TERM))))
  (ITERATE FOR X IN HINT-VARIABLE-ALIST WHEN (ASSOC-EQ (CAR X) HINTS)
           DO (SET (CADR X) (CDR (ASSOC-EQ (CAR X) HINTS))))
  (APPLY-THEORY-HINTS (CDR (ASSOC-EQ (QUOTE ENABLE-THEORY) HINTS))
                      (CDR (ASSOC-EQ (QUOTE DISABLE-THEORY) HINTS))) 
  (COND ((OR TEMPORARILY-DISABLED-LEMMAS
             TEMPORARILY-ENABLED-LEMMAS)
         (MAKE-LOCAL-DISABLEDP-HASH
          TEMPORARILY-ENABLED-LEMMAS TEMPORARILY-DISABLED-LEMMAS)
         (SETQ LOCAL-DISABLEDP-HASH-FLAG T))
        (T (SETQ LOCAL-DISABLEDP-HASH-FLAG NIL)))
  TERM)

(DEFUN APPLY-INDUCT-HINT (HINT TERM)
  (LET (FORMALS)
    (SETQ FORMALS (CADR (GET (FFN-SYMB HINT) (QUOTE SDEFN))))
    (CONJOIN
     (ITERATE FOR CL IN
              (IND-FORMULA
               (ITERATE FOR TA IN (GET (FN-SYMB HINT)
                                       (QUOTE INDUCTION-MACHINE))
                        COLLECT
                        (MAKE TESTS-AND-ALISTS
                              (SUB-PAIR-VAR-LST FORMALS (FARGS HINT)
                                                (ACCESS TESTS-AND-CASES
                                                        TESTS TA))
                              (ITERATE FOR ARGLIST
                                       IN (ACCESS TESTS-AND-CASES CASES TA)
                                       COLLECT
                                       (ITERATE FOR ARG IN ARGLIST AS ACTUAL
                                                IN (FARGS HINT)
                                                COLLECT
                                                (CONS ACTUAL
                                                      (SUB-PAIR-VAR
                                                       FORMALS
                                                       (FARGS HINT)
                                                       ARG))))))
               (LIST HINT)
               (LIST (LIST TERM)))
              COLLECT (DISJOIN CL NIL))
     NIL)))

(DEFUN APPLY-USE-HINT (HINT TERM)
  (COND ((NULL HINT) TERM)
        (T (DUMB-IMPLICATE-LITS
            (CONJOIN
             (ITERATE FOR PAIR IN HINT
                      COLLECT
                      (SUBLIS-VAR
                       (ITERATE FOR X IN (CDR PAIR)
                                COLLECT (CONS (CAR X) (CADR X)))
                       (FORMULA-OF (CAR PAIR))))
             NIL)
            TERM))))

(DEFUN ARG1-IN-ARG2-UNIFY-SUBST (ARG1 ARG2)
  (COND ((OR (VARIABLEP ARG2) (FQUOTEP ARG2)) NIL)
        ((ONE-WAY-UNIFY ARG2 ARG1) T)
        (T (ITERATE FOR ARG IN (FARGS ARG2)
                    THEREIS (ARG1-IN-ARG2-UNIFY-SUBST ARG1 ARG)))))

(DEFUN ARGN0 (TERM N)
  (COND ((NOT (EQ (CAR TERM) (QUOTE QUOTE)))
         (NTH N TERM))
        ((SYMBOLP (CADR TERM))
         (LIST (QUOTE QUOTE)
               (DTACK-0-ON-END (OUR-EXPLODEN (CADR TERM)))))
        ((INTEGERP (CADR TERM))
         (COND ((< (CADR TERM) 0)
                (LIST (QUOTE QUOTE)
                      (- (CADR TERM))))
               (T (LIST (QUOTE QUOTE)
                        (1- (CADR TERM))))))
        ((EQ (CAR (CADR TERM)) *1*SHELL-QUOTE-MARK)
         (LIST (QUOTE QUOTE)
               (NTH N (CDR (CADR TERM)))))
        (T (COND ((INT= N 1)
                  (LIST (QUOTE QUOTE)
                        (CAR (CADR TERM))))
                 (T (LIST (QUOTE QUOTE)
                          (CDR (CADR TERM))))))))

(DEFUN ARITY (FNNAME)
  (COND ((SETQ TEMP-TEMP (TYPE-PRESCRIPTION FNNAME))
         (LENGTH (CDR TEMP-TEMP)))
        ((SETQ TEMP-TEMP (ASSOC-EQ FNNAME ARITY-ALIST))
         (CDR TEMP-TEMP))
        (T NIL)))

(DEFUN ASSOC-OF-APP NIL
  (DO-EVENTS
   (QUOTE
    ((DEFN APP (X Y)
       (IF (LISTP X) (CONS (CAR X) (APP (CDR X) Y)) Y))
     (PROVE-LEMMA ASSOC-OF-APP (REWRITE)
                  (EQUAL (APP (APP A B) C)
                         (APP A (APP B C))))))))

(DEFUN ASSUME-TRUE-FALSE (TERM)
  (LET (NOT-FLG TYPE-ARG1 TYPE-ARG2 TRUE-SEG FALSE-SEG PAIR ARG1
                ARG2 INTERSECTION SWAPPED-TERM SWAP-FLG
                LOCAL-MUST-BE-TRUE LOCAL-MUST-BE-FALSE)
    (COND ((MATCH TERM (NOT TERM)) (SETQ NOT-FLG T)))
    (COND ((AND (NVARIABLEP TERM)
                (NOT (FQUOTEP TERM))
                (SETQ PAIR (ASSOC-EQ (FFN-SYMB TERM)
                                     RECOGNIZER-ALIST)))
           (SETQ TYPE-ARG1 (TYPE-SET (FARGN TERM 1)))
           (COND ((TS= 0 (TSLOGAND TYPE-ARG1 (CDR PAIR)))
                  (SETQ LOCAL-MUST-BE-FALSE T))
                 ((TSLOGSUBSETP TYPE-ARG1 (CDR PAIR))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 (T (SETQ TRUE-SEG (LIST (CONS (FARGN TERM 1)
                                               (CDR PAIR))))
                    (SETQ FALSE-SEG
                          (LIST (CONS (FARGN TERM 1)
                                      (TSLOGAND (TSLOGNOT (CDR PAIR))
                                                TYPE-ARG1)))))))
          ((MATCH TERM (EQUAL ARG1 ARG2))
           (COND ((EQUAL ARG1 ARG2)
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 ((AND (SETQ TEMP-TEMP (CDR (ASSOC-EQUAL TERM TYPE-ALIST)))
                       (TS= TEMP-TEMP TYPE-SET-TRUE))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 ((AND TEMP-TEMP (TS= TEMP-TEMP TYPE-SET-FALSE))
                  (SETQ LOCAL-MUST-BE-FALSE T))
                 ((AND (SETQ TEMP-TEMP
                             (CDR (ASSOC-EQUAL (SETQ SWAPPED-TERM
                                                     (FCONS-TERM* (QUOTE EQUAL)
                                                                  ARG2 ARG1))
                                               TYPE-ALIST)))
                       (EQUAL TEMP-TEMP TYPE-SET-TRUE))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 ((AND TEMP-TEMP (TS= TEMP-TEMP TYPE-SET-FALSE))
                  (SETQ LOCAL-MUST-BE-FALSE T))
                 (T (SETQ SWAP-FLG (TERM-ORDER ARG1 ARG2))
                    (SETQ TYPE-ARG1 (TYPE-SET ARG1))
                    (SETQ TYPE-ARG2 (TYPE-SET ARG2))
                    (SETQ INTERSECTION (TSLOGAND TYPE-ARG1 TYPE-ARG2))
                    (COND ((TS= 0 INTERSECTION)
                           (SETQ LOCAL-MUST-BE-FALSE T))
                          ((AND (TS= TYPE-ARG1 TYPE-ARG2)
                                (MEMBER-EQUAL TYPE-ARG1 SINGLETON-TYPE-SETS))
                           (SETQ LOCAL-MUST-BE-TRUE T))
                          (T (SETQ TRUE-SEG
                                   (COND (SWAP-FLG (LIST (CONS SWAPPED-TERM
                                                               TYPE-SET-TRUE)))
                                         (T (LIST (CONS TERM TYPE-SET-TRUE)))))
                             (OR (TS= TYPE-ARG1 INTERSECTION)
                                 (NOT SWAP-FLG)
                                 (SETQ TRUE-SEG
                                       (CONS (CONS ARG1 INTERSECTION)
                                             TRUE-SEG)))
                             (OR (TS= TYPE-ARG2 INTERSECTION)
                                 SWAP-FLG
                                 (SETQ TRUE-SEG
                                       (CONS (CONS ARG2 INTERSECTION)
                                             TRUE-SEG)))
                             (SETQ FALSE-SEG
                                   (LIST (CONS TERM TYPE-SET-FALSE)
                                         (CONS SWAPPED-TERM TYPE-SET-FALSE)))
                             (OR (NOT (MEMBER-EQUAL TYPE-ARG2
                                                    SINGLETON-TYPE-SETS))
                                 (SETQ FALSE-SEG
                                       (CONS (CONS ARG1
                                                   (TSLOGAND (TSLOGNOT
                                                              TYPE-ARG2)
                                                             TYPE-ARG1))
                                             FALSE-SEG)))
                             (OR (NOT (MEMBER-EQUAL TYPE-ARG1
                                                    SINGLETON-TYPE-SETS))
                                 (SETQ FALSE-SEG
                                       (CONS (CONS ARG2
                                                   (TSLOGAND (TSLOGNOT
                                                              TYPE-ARG1)
                                                             TYPE-ARG2))
                                             FALSE-SEG))))))))
          (T (SETQ TYPE-ARG1 (TYPE-SET TERM))
             (COND ((TS= TYPE-ARG1 TYPE-SET-FALSE)
                    (SETQ LOCAL-MUST-BE-FALSE T))
                   ((TS= 0 (TSLOGAND TYPE-ARG1 TYPE-SET-FALSE))
                    (SETQ LOCAL-MUST-BE-TRUE T))
                   (T (SETQ
                       TRUE-SEG
                       (LIST (CONS TERM
                                   (TSLOGAND TYPE-ARG1
                                             (TSLOGNOT TYPE-SET-FALSE)))))
                      (SETQ FALSE-SEG (LIST (CONS TERM TYPE-SET-FALSE)))))))
    (COND (NOT-FLG (OUR-SWAP LOCAL-MUST-BE-TRUE LOCAL-MUST-BE-FALSE)
                   (OUR-SWAP TRUE-SEG FALSE-SEG)))
    (SETQ TRUE-TYPE-ALIST (NCONC TRUE-SEG TYPE-ALIST))
    (SETQ FALSE-TYPE-ALIST (NCONC FALSE-SEG TYPE-ALIST))
    (SETQ MUST-BE-TRUE LOCAL-MUST-BE-TRUE)
    (SETQ MUST-BE-FALSE LOCAL-MUST-BE-FALSE)
    NIL))

(DEFUN ASSUME-TRUE-LST (L TYPE-ALIST)

;   To be called on a list of terms.  When finished, TRUE-TYPE-ALIST
;   represents the conjunction of the terms with the assumptions on
;   TYPE-ALIST.  If MUST-BE-TRUE and MUST-BE-FALSE are set then the
;   whole conjunction is respectively true or false under TYPE-ALIST.

  (ITERATE FOR L1 IN L WITH RUNNING-MUST-BE-TRUE = T AND
           RUNNING-MUST-BE-FALSE = NIL DO
           (PROGN
             (ASSUME-TRUE-FALSE L1)
             (SETQ RUNNING-MUST-BE-FALSE (OR MUST-BE-FALSE
                                             RUNNING-MUST-BE-FALSE))
             (SETQ RUNNING-MUST-BE-TRUE (AND MUST-BE-TRUE
                                             RUNNING-MUST-BE-TRUE))
             (SETQ TYPE-ALIST TRUE-TYPE-ALIST))
           FINALLY
           (PROGN (SETQ MUST-BE-TRUE RUNNING-MUST-BE-TRUE)
                  (SETQ MUST-BE-FALSE RUNNING-MUST-BE-FALSE))))

(DEFUN ATTEMPT-TO-REWRITE-RECOGNIZER (TERM)
  (MATCH TERM (NOT TERM))
  (AND (NVARIABLEP TERM)
       (ASSOC-EQ (FN-SYMB TERM) RECOGNIZER-ALIST)
       (VARIABLEP (ARGN TERM 1))))

(DEFUN AVAILABLE-EVENT-FS-PAIRS-ALIST (OLD-NAME-OR-LIST)

; Here old-name-or-list is of the form of the fourth argument to
; FUNCTIONALLY-INSTANTIATE, i.e. it's a symbol or else a list of
; the form (event-name fs-1 fs-2 ... fs-n), where 
; (fs-1 fs-2 ...  fs-n) is a list of previous
; functionally-instantiate events.  This function returns an alist
; with entries of the form (fi-event (event1 . fs1) (event2 . fs2)
; ... (eventk . fsk)) .

  (IF (CONSP OLD-NAME-OR-LIST)
      (SCRUNCH (ITERATE FOR NAME IN (CDR OLD-NAME-OR-LIST)
                        COLLECT (CONS NAME (GET NAME 'JUSTIFICATIONS))))
      (SCRUNCH
       (ITERATE FOR NAME IN CHRONOLOGY
                WHEN (EQ (CAR (GET NAME 'EVENT)) 'FUNCTIONALLY-INSTANTIATE)
                COLLECT (CONS NAME (GET NAME 'JUSTIFICATIONS))))))
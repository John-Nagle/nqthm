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

(DEFUN S (VAR VAL)

;   This function is intended to be used in conjunction with R. 
;   The idea is that one might type, to LISP, (S 'X (some hairy lisp expr))
;   to manufacture (or, more likely, recover from some other object) an
;   explicit value too big to type.  Then you could use X inside expressions
;   given to R.


  (COND ((NOT (ERROR1-SET (SETQ TEMP-TEMP (TRANSLATE VAR))))
         NIL)
        ((OR (NOT (EQ VAR TEMP-TEMP))
             (NOT (VARIABLEP VAR)))
         (ER SOFT (VAR) (!PPR VAR NIL) |is| |not|
             |a| |variable| |symbol| |.|))

        ((NOT (ERROR1-SET (SETQ VAL (TRANSLATE VAL))))
         NIL)
        ((NOT (QUOTEP VAL))
         (ER SOFT (VAL) |The| |second| |argument| |to| S |must|
             |be| |an| |explicit| |value| |--| |i.e.,|
             |composed| |entirely| |of| |shell|
             |constructors| |and| |bottom| |objects| |--|
             |and| (!PPR VAL NIL) |is| |not| |.|))
        (T (SETQ TEMP-TEMP (OR (ASSOC-EQ VAR R-ALIST)
                               (CAR (SETQ R-ALIST
                                          (CONS (CONS VAR VAL)
                                                R-ALIST)))))
           (RPLACD TEMP-TEMP (CADR VAL))
           VAR)))

(DEFUN SARGS (TERM)
  (COND ((NOT (EQ (CAR TERM) (QUOTE QUOTE))) (CDR TERM))
        ((SYMBOLP (CADR TERM))
         (COND ((EQ (CADR TERM) *1*T) NIL)
               ((EQ (CADR TERM) *1*F) NIL)
               (T (LIST (LIST (QUOTE QUOTE)
                              (DTACK-0-ON-END (OUR-EXPLODEN (CADR TERM))))))))
        ((INTEGERP (CADR TERM))
         (COND ((< (CADR TERM) 0)
                (LIST (LIST (QUOTE QUOTE) (- (CADR TERM)))))
               ((EQUAL (CADR TERM) 0) NIL)
               (T (LIST (LIST (QUOTE QUOTE) (1- (CADR TERM)))))))
        ((EQ (CAR (CADR TERM)) *1*SHELL-QUOTE-MARK)
         (ITERATE FOR X IN (CDDR (CADR TERM)) COLLECT (LIST (QUOTE QUOTE) X)))
        (T (LIST (LIST (QUOTE QUOTE) (CAR (CADR TERM)))
                 (LIST (QUOTE QUOTE) (CDR (CADR TERM)))))))

(DEFUN SCONS-TERM (FN ARGS)
  (COND ((EQ FN (QUOTE EQUAL))
         (COND ((EQUAL (CAR ARGS) (CADR ARGS)) TRUE)
               ((AND (QUOTEP (CAR ARGS)) (QUOTEP (CADR ARGS))) FALSE)
               (T (FCONS-TERM (QUOTE EQUAL) ARGS))))
        (T (CONS-TERM FN ARGS))))

(DEFUN SCRUNCH (L)
  (ITERATE FOR TAIL ON L UNLESS (MEMBER-EQUAL (CAR TAIL) (CDR TAIL))
           COLLECT (CAR TAIL)))

(DEFUN SCRUNCH-CLAUSE (CL)
  (ITERATE FOR TAIL ON CL
           UNLESS (OR (AND (FALSE-NONFALSEP (CAR TAIL)) DEFINITELY-FALSE)
                      (MEMBER-EQUAL (CAR TAIL) (CDR TAIL)))
           COLLECT (CAR TAIL)))

(DEFUN SCRUNCH-CLAUSE-SET (CLAUSES)
  (TRANSITIVE-CLOSURE (ITERATE FOR CL IN CLAUSES COLLECT (SCRUNCH-CLAUSE CL))
                      (FUNCTION (LAMBDA (CL1 CL2)
                                  (COND ((SUBSETP-EQUAL CL1 CL2) CL1)
                                        ((SUBSETP-EQUAL CL2 CL1) CL2)
                                        (T NIL))))))

(DEFUN SEARCH-GROUND-UNITS (HYP)

;   Like LOOKUP-HYP except looks through ground unit REWRITE lemmas.

  (PROG (TERM FN REWRITE-RULE)
        (COND ((MATCH HYP (NOT TERM))
               (COND ((VARIABLEP TERM) (RETURN NIL))
                     ((FQUOTEP TERM) (RETURN (EQUAL TERM FALSE)))
                     (T (SETQ FN (FFN-SYMB TERM)))))
              ((VARIABLEP HYP) (RETURN NIL))
              ((FQUOTEP HYP) (RETURN (NOT (EQUAL HYP FALSE))))
              (T (SETQ FN (FFN-SYMB HYP))))
        (COND
         ((SETQ REWRITE-RULE
                (ITERATE FOR REWRITE-RULE IN (GET FN (QUOTE LEMMAS))
                         WHEN (AND (NOT (DISABLEDP (ACCESS REWRITE-RULE NAME
                                                           REWRITE-RULE)))
                                   (NOT (META-LEMMAP REWRITE-RULE))
                                   (NOT (ACCESS REWRITE-RULE
                                                HYPS REWRITE-RULE))
                                   (NOT (FREE-VARSP (ACCESS REWRITE-RULE CONCL
                                                            REWRITE-RULE)
                                                    NIL))
                                   (ONE-WAY-UNIFY1 HYP
                                                   (ACCESS REWRITE-RULE CONCL
                                                           REWRITE-RULE)))
                         DO (RETURN REWRITE-RULE)))
          (PUSH-LEMMA (ACCESS REWRITE-RULE NAME REWRITE-RULE))
          (RETURN T))
         (T (RETURN NIL)))))

(DEFUN SEMI-CONCRETE-ALISTP (X)

;   X is known to be a term.  We want to know whether it has the form
;   (LIST ... (CONS (QUOTE var) term) ...)

  (COND ((VARIABLEP X) NIL)
        ((EQUAL X (QUOTE (QUOTE NIL))) T)
        (T (AND (EQ (FN-SYMB X) (QUOTE CONS))
                (NVARIABLEP (ARGN X 1))
                (EQ (FN-SYMB (ARGN X 1)) (QUOTE CONS))
                (QUOTEP (ARGN (ARGN X 1) 1))
                (TERMP (CADR (ARGN (ARGN X 1) 1)))
                (VARIABLEP (CADR (ARGN (ARGN X 1) 1)))
                (SEMI-CONCRETE-ALISTP (ARGN X 2))))))

(DEFUN SET-DIFF (X Y)
  (ITERATE FOR ELE IN X UNLESS (MEMBER-EQUAL ELE Y) COLLECT ELE))

(DEFUN SET-DIFF-EQ (X Y)
  (ITERATE FOR ELE IN X UNLESS (MEMBER-EQ ELE Y) COLLECT ELE))

(DEFUN SET-SIMPLIFY-CLAUSE-POT-LST (CL HEURISTIC-TYPE-ALIST)

;   We use the same basic pot list for all the calls REWRITE for a given
;   clause.  However, to keep from biting our tail, we must know which literals
;   each poly descends from and avoid the polys descending from the negation of
;   our current lit.  In order to keep track of which literals are being used
;   we set TYPE-ALIST to NIL before setting up the pot list, and use the
;   special hacks LITS-THAT-MAY-BE-ASSUMED-FALSE and HEURISTIC-TYPE-ALIST.  The
;   pot list we thus construct is immediately tested against CONTRADICTION to
;   see if CL is a consequence of linear.  However, the failure to use
;   everything we know has burned us here.  In particular, the type alist might
;   contain an equality that could be used as a rewrite rule to help us
;   establish the hypothesis of some needed lemma.  Imagine for example that
;   the clause contains b=a and p (a) as hyps and we need to prove p (b) to get
;   some lemma.  We try to handle this as follows.  After setting up
;   SIMPLIFY-CLAUSE-POT-LST -- the pot list we will use subsequently and which
;   has all the dependencies carefully tracked -- we go at the pot list again
;   with the ALL-NEW-FLG of ADD-TERMS-TO-POT-LST set to T.  This causes us to
;   treat every addend in the pot list as new and reconsider the adding of all
;   the lemmas.  If this produces CONTRADICTION, we win.  If not, we pretend we
;   did not do it -- since the resulting pot list has hidden dependencies in
;   it.

  (LET ((LITS-THAT-MAY-BE-ASSUMED-FALSE CL) (TYPE-ALIST NIL))
    (PUSH-REWRITE-PATH-FRAME 'SET-SIMPLIFY-CLAUSE-POT-LST
                             CL
                             NIL
                             NIL)
    (SETQ SIMPLIFY-CLAUSE-POT-LST (ADD-TERMS-TO-POT-LST CL NIL NIL NIL))
    (COND ((NOT (EQ SIMPLIFY-CLAUSE-POT-LST (QUOTE CONTRADICTION)))
           (SETQ TYPE-ALIST HEURISTIC-TYPE-ALIST)
           (COND ((EQ (ADD-TERMS-TO-POT-LST NIL SIMPLIFY-CLAUSE-POT-LST
                                            NIL T)
                      (QUOTE CONTRADICTION))
                  (SETQ SIMPLIFY-CLAUSE-POT-LST (QUOTE CONTRADICTION))))))
    (POP-REWRITE-PATH-FRAME)
    NIL))

(DEFUN SET-STATUS1 (NAME FLG)

; NAME is some citizen.  FLG is one of 'ENABLE, 'DISABLE, 'AS-IS or
; (if name is a satellite of ground-zero) 'INITIAL.  We determine
; whether we need to change the status of NAME and if so we push
; NAME onto one of two lists:  SET-STATUS-ENABLE-NAMES or
; SET-STATUS-DISABLE-NAMES.  We also accumulate the MAIN-EVENTs of
; the names we need to change so we can DEPEND on them.


; Note:  In an earlier prototype we actually changed the status of
; NAME appropriately here.  But that has the bad effect of outdating
; the DISABLED-LEMMAS hash table and so the next call of DISABLEDP
; causes a re-hash.  Since DISABLEDP is called below, it meant we
; re-hashed the entire DISABLED-LEMMAS list once for every NAME
; we consider.

  (COND ((EQ FLG 'INITIAL)
         (SETQ FLG
               (COND ((DISABLED-BY-BOOT-STRAPP NAME)
                      'DISABLE)
                     (T 'ENABLE)))))
  (CASE FLG
        (ENABLE
         (COND
          ((DISABLEDP NAME)
           (PUSH NAME SET-STATUS-ENABLE-NAMES)
           (SETQ SET-STATUS-DEPENDENTS
                 (ADD-TO-SET (MAIN-EVENT-OF NAME)
                             SET-STATUS-DEPENDENTS)))
          (T NIL)))
        (DISABLE
         (COND
          ((DISABLEDP NAME) NIL)
          (T (PUSH NAME SET-STATUS-DISABLE-NAMES)
             (SETQ SET-STATUS-DEPENDENTS
                   (ADD-TO-SET (MAIN-EVENT-OF NAME)
                               SET-STATUS-DEPENDENTS)))))
        (OTHERWISE NIL)))

(DEFUN SET-TIME-LIMIT (&OPTIONAL N)
  (COND ((NULL N)
         (SETQ TIME-LIMIT-IN-60THS NIL))
        ((AND (INTEGERP N) (> N 0))
         (SETQ TIME-LIMIT-IN-60THS (* 60 N)))
        (T
         (ER SOFT (N) |Impossible| |to| |set| |time| |limit| |of|
             (!PPR N NIL) |,| |as| |the| |time| |limit| |must| |be| |a|
             |positive| |integer| |or| | NIL| |.|))))

(DEFUN SETTLED-DOWN-CLAUSE (CL HIST)
  (COND ((ASSOC-EQ (QUOTE SETTLED-DOWN-CLAUSE) HIST) NIL)
        (T (SETQ PROCESS-HIST NIL) (SETQ PROCESS-CLAUSES (LIST CL)) T)))

(DEFUN SETTLED-DOWN-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE SETTLED-DOWN-CLAUSE)
           CL HIST (QUOTE SIMPLIFY-SENT)
           (QUOTE ELIMINATE-DESTRUCTORS-SENT)))

(DEFUN SETUP (FORM CLAUSES LEMMAS)
  (SETQ ORIGTHM FORM)
  (SETQ EXPAND-LST HINTED-EXPANSIONS)
  (SETQ TERMS-TO-BE-IGNORED-BY-REWRITE NIL)
  (SETQ INDUCTION-HYP-TERMS NIL)
  (SETQ INDUCTION-CONCL-TERMS NIL)
  (SETQ ALL-LEMMAS-USED LEMMAS)
  (SETQ STACK NIL)
  (SETQ FNSTACK NIL)
  (SETQ LAST-PRINT-CLAUSES NIL)
  (SETQ TYPE-ALIST NIL)
  (SETQ LITS-THAT-MAY-BE-ASSUMED-FALSE NIL)
  (SETQ CURRENT-LIT 0)
  (SETQ CURRENT-ATM 0)
  (SETQ ANCESTORS NIL)
  (COND (REWRITE-PATH-STK-PTR
         (SETQ REWRITE-PATH-STK-PTR -1)
         (SETQ REWRITE-PATH-FRAME-CNT 0)
         (SETQ REWRITE-PATH-PERSISTENCE-ALIST NIL)))
  (INIT-LEMMA-STACK)
  (INIT-LINEARIZE-ASSUMPTIONS-STACK)
  (SETQ LAST-PRINEVAL-CHAR (QUOTE |.|))
  (RANDOM-INITIALIZATION ORIGTHM)
  (IO (QUOTE SETUP)
      (LIST ORIGTHM)
      NIL CLAUSES LEMMAS))

(DEFUN SETUP-V&C$ (X) X

; The equation implied by the following SETF can be proved from
; the preceding events in boot strap.

  (CHK-NQTHM-MODE$ (QUOTE SETUP-V&C$))
  (SETF (GET (QUOTE V&C$)
             (QUOTE SDEFN))
        `(LAMBDA (FLG X VA)
           ,(TRANSLATE
             (QUOTE (IF (EQUAL FLG (QUOTE LIST))
                        (IF (NLISTP X)
                            NIL
                            (CONS (V&C$ T (CAR X) VA)
                                  (V&C$ (QUOTE LIST) (CDR X) VA)))
                        (IF (LITATOM X) (CONS (CDR (ASSOC X VA)) 0)
                            (IF (NLISTP X) (CONS X 0)
                                (IF (EQUAL (CAR X) (QUOTE QUOTE))
                                    (CONS (CADR X) 0)
                                    (V&C-APPLY$
                                     (CAR X)
                                     (V&C$ (QUOTE LIST) (CDR X) VA))))))))))
  (ADD-FACT NIL (QUOTE DISABLED-LEMMAS)
            (CONS (QUOTE V&C-APPLY$) (CONS (QUOTE GROUND-ZERO) T)))
  (ADD-FACT NIL (QUOTE DISABLED-LEMMAS)
            (CONS (QUOTE APPLY$) (CONS (QUOTE GROUND-ZERO) T)))

;  The following yuky smashing causes 
;  (CAR (V&C$ T (LIST 'PLUS ...) VA)) to open up.
  
  (ADD-FACT (QUOTE V&C$) (QUOTE CONTROLLER-POCKETS) (QUOTE (2))))

(DEFUN SHELL-CONSTRUCTORP (TERM)
  (COND ((VARIABLEP TERM) NIL)
        (T (ASSOC-EQ (FN-SYMB TERM) SHELL-ALIST))))

(DEFUN SHELL-DESTRUCTOR-NESTP (VAR TERM)
  (COND ((VARIABLEP TERM) (EQ VAR TERM))
        ((FQUOTEP TERM) NIL)
        (T (AND (ITERATE FOR POCKET IN SHELL-POCKETS
                         THEREIS (MEMBER-EQ (FFN-SYMB TERM) (CDR POCKET)))
                (SHELL-DESTRUCTOR-NESTP VAR (FARGN TERM 1))))))

(DEFUN SHELL-OCCUR (TERM1 TERM2)

;   Returns T if TERM1 properly occurs in a nest of shells TERM2.  That is
;   whether TERM1 occurs as an arg at some depth in the shell TERM2, and that
;   the chain of shells from the occurrence to TERM1 all the way up to the top
;   of TERM2 is properly typed.  See the comment in SHELL-OCCUR1.  Does not
;   bother to do anything if TERM1 is a SHELLP, because (assuming the terms are
;   coming from EQUAL expressions) the two shells would be either different and
;   we wouldn't be here, or the same, in which case they would be rewritten.
;   At the moment the only fn to call SHELL-OCCUR is NOT-IDENT and we only use
;   NOT-IDENT to decide EQUALs or else one of the two terms is FALSE.

  (LET (TYPE-SET-TERM1)
    (COND ((SHELLP TERM1) NIL)
          ((VARIABLEP TERM2) NIL)
          ((FQUOTEP TERM2) NIL)
          ((ASSOC-EQ (FFN-SYMB TERM2) SHELL-ALIST)
           (SETQ TYPE-SET-TERM1 (TYPE-SET TERM1))
           (ITERATE FOR ARG IN (FARGS TERM2)
                    AS TR IN (GET (FFN-SYMB TERM2) (QUOTE TYPE-RESTRICTIONS))
                    THEREIS (AND (SETQ TEMP-TEMP (SHELL-OCCUR1 TERM1 ARG))
                                 (TSLOGSUBSETP TEMP-TEMP
                                               (ACCESS TYPE-RESTRICTION
                                                       TYPE-SET TR)))))
          (T NIL))))

(DEFUN SHELL-OCCUR1 (TERM1 TERM2)

;   This function wants to see whether TERM1 occurs as an arg to a shell in
;   TERM2.  However, because of type restrictions, one must not be fooled into
;   thinking that, for example, (ADD1 0) occurs inside of (ADD1 (CONS (ADD1 0)
;   NIL)) despite the fact that it occurs as an arg to a shell.  The basic idea
;   is that TERM1 must either be TERM2 or else must shell-occur inside the
;   shell TERM2 -- in a spot of the right type.  Thus, one way to compute it
;   would be to see if TERM1 shell-occurred in an arg position of shell TERM2
;   and if so to then determine if the typeset of the arg was suitable.
;   However, that would involve either a general purpose call on typeset or
;   else looking ahead to see whether the arg in which TERM1 occurred was
;   itself a shell -- in which case its typeset is just on its
;   type-prescription -- or was a TERM1 occurrence itself -- in which case a
;   full blown typeset is necessary.  Rather than do it that way we have fixed
;   SHELL-OCCUR1 so that it returns the typeset of TERM2 if an occurrence was
;   found, and otherwise NIL.

  (COND ((EQUAL TERM1 TERM2) TYPE-SET-TERM1)
        ((VARIABLEP TERM2) NIL)
        ((FQUOTEP TERM2) NIL)
        ((AND (ASSOC-EQ (FFN-SYMB TERM2) SHELL-ALIST)
              (ITERATE FOR ARG IN (FARGS TERM2) AS TR
                       IN (GET (FFN-SYMB TERM2) (QUOTE TYPE-RESTRICTIONS))
                       THEREIS (AND (SETQ TEMP-TEMP (SHELL-OCCUR1 TERM1 ARG))
                                    (TSLOGSUBSETP TEMP-TEMP
                                                  (ACCESS
                                                   TYPE-RESTRICTION
                                                   TYPE-SET TR)))))
         (CAR (TYPE-PRESCRIPTION (FFN-SYMB TERM2))))
        (T NIL)))

(DEFUN SHELLP (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) T)
        (T (OR (MEMBER-EQ (FFN-SYMB TERM) *1*BTM-OBJECTS)
               (ASSOC-EQ (FFN-SYMB TERM) SHELL-ALIST)))))

(DEFUN SIMPLIFY-CLAUSE (CURRENT-SIMPLIFY-CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.


;   If T is returned, then the conjunction of PROCESS-CLAUSES implies
;   CURRENT-SIMPLIFY-CL.  Equivalently, if T is returned, then under the
;   assumption that CURRENT-SIMPLIFY-CL is F, CURRENT-SIMPLIFY-CL is equivalent
;   to the conjunction of PROCESS-CLAUSES.

;   Note that PROCESS-CLAUSES may be the facetious answer F, i.e., false
;   generalization may and does happen.  We know such tail biting can occur
;   through use of linear arithmetic.  We are uncertain whether it can occur
;   without use of linear arithmetic.  To make it happen with linear we just
;   need two slightly different versions of the same inequality literal.  The
;   poly arising from the second is used to rewrite the first to false and the
;   poly arising from the first -- which is still in the pot list -- is used to
;   rewrite the second to false.  LITS-TO-BE-IGNORED-BY-LINEAR actually
;   prevents this direct example from working -- the poly arising from the
;   first is ignored after its literal has been rewritten to false.  To
;   overcome this minor obstacle, it is necessary to cause the first literal to
;   be rewritten to something that will prove to be false eventually but isn't
;   syntactically F.

;   We have since discovered, with Matt Kaufmann, that tail-biting is in fact
;   possible even without linear arithmetic.  When you call (prove 'z), for
;   example, REMOVE-TRIVIAL-EQUATIONS produces the empty clause.

  (LET ((TERMS-TO-BE-IGNORED-BY-REWRITE TERMS-TO-BE-IGNORED-BY-REWRITE)
        ANS
        (EXPAND-LST EXPAND-LST)
        FREE-VARS-IN-SIGHT)
    (PROG NIL
          (COND ((SETQ TEMP-TEMP (ASSOC-EQ (QUOTE SETTLED-DOWN-CLAUSE) HIST))

;   The clause has settled down under rewriting with the INDUCTION-HYP-TERMS
;   ignored and the INDUCTION-CONCL-TERMS forcibly expanded.  In general then
;   we now want to stop treating these terms specially and continue
;   simplifying.  However, there is a special case that will save a little
;   time.  Suppose that the clause just settled down -- that is, the most
;   recent HIST entry is the settled mark.  And suppose that none of the
;   specially treated terms occurs in the clause we're to simplify.  Then we
;   needn't simplify it again.  The first supposition is important.  Imagine
;   that the clause settled down long ago and we have done much since then.

                 (COND ((AND (EQ TEMP-TEMP (CAR HIST))
                             (ITERATE FOR TERM IN INDUCTION-HYP-TERMS
                                      NEVER (DUMB-OCCUR-LST
                                             TERM CURRENT-SIMPLIFY-CL)))

;   Since we know the INDUCTION-CONCL-TERMS couldn't occur in the clause --
;   they would have been expanded -- it suffices to check for just the hyp
;   terms.  This test should speed up base cases and the preinduction
;   simplification at least.

                        (RETURN NIL))))
                (T

;   The clause has not yet settled down, so arrange to ignore
;   INDUCTION-HYP-TERMS during rewriting and to expand without question
;   INDUCTION-CONCL-TERMS.

                 (SETQ TERMS-TO-BE-IGNORED-BY-REWRITE
                       (APPEND INDUCTION-HYP-TERMS
                               TERMS-TO-BE-IGNORED-BY-REWRITE))
                 (SETQ EXPAND-LST (APPEND INDUCTION-CONCL-TERMS
                                          EXPAND-LST))))
          (INIT-LEMMA-STACK)
          (PUSH-LEMMA-FRAME)
          (PUSH-REWRITE-PATH-FRAME 'SIMPLIFY-CLAUSE
                                   CURRENT-SIMPLIFY-CL
                                   NIL
                                   NIL)
          (SETQ FREE-VARS-IN-SIGHT
                (UNION-EQ FREE-VARS-IN-REWRITE-RHSS
                          (ALL-VARS-LST CURRENT-SIMPLIFY-CL)))
          (SETQ PROCESS-CLAUSES (SIMPLIFY-CLAUSE0 CURRENT-SIMPLIFY-CL HIST))
          (POP-REWRITE-PATH-FRAME)
          (SETQ PROCESS-HIST (ITERATE FOR X IN (POP-LEMMA-FRAME)
                                      UNLESS (AND (CONSP X) (ATOM (CAR X)))
                                      COLLECT X))

;   The lemmas ignored are really literals from LITS-THAT-MAY-BE-ASSUMED-FALSE
;   that get put in by REWRITE-SOLIDIFY.  The identifying test for these
;   literals is not a simple CONSP because PROCESS-EQUATIONAL-POLYS puts in
;   some CONSP elements to encode its additions to the clause and we must
;   preserve them.

          (ITERATE FOR X IN PROCESS-HIST
                   UNLESS (OR (CONSP X)
                              (MEMBER-EQ X ALL-LEMMAS-USED))
                   DO (SETQ ALL-LEMMAS-USED (CONS X ALL-LEMMAS-USED)))
          (RETURN (NOT (AND (INT= (LENGTH PROCESS-CLAUSES) 1)
                            (EQUAL (CAR PROCESS-CLAUSES)
                                   CURRENT-SIMPLIFY-CL)))))))

(DEFUN SIMPLIFY-CLAUSE-MAXIMALLY (CURRENT-CL)
  (LET (SIMPLIFY-CLAUSE-MAXIMALLY-CLAUSES SIMPLIFY-CLAUSE-MAXIMALLY-HIST)
    (SIMPLIFY-CLAUSE-MAXIMALLY1 CURRENT-CL)
    (SETQ PROCESS-HIST SIMPLIFY-CLAUSE-MAXIMALLY-HIST)
    (SETQ PROCESS-CLAUSES SIMPLIFY-CLAUSE-MAXIMALLY-CLAUSES)
    (NOT (EQUAL PROCESS-CLAUSES (LIST CURRENT-CL)))))

(DEFUN SIMPLIFY-CLAUSE-MAXIMALLY1 (CL)
  (COND ((SIMPLIFY-CLAUSE CL NIL)
         (ITERATE FOR X IN PROCESS-HIST
                  UNLESS (OR (CONSP X)
                             (MEMBER-EQ X SIMPLIFY-CLAUSE-MAXIMALLY-HIST))
                  DO (SETQ SIMPLIFY-CLAUSE-MAXIMALLY-HIST
                           (CONS X SIMPLIFY-CLAUSE-MAXIMALLY-HIST)))
         (ITERATE FOR CL IN PROCESS-CLAUSES
                  DO (SIMPLIFY-CLAUSE-MAXIMALLY1 CL)))
        (T (SETQ SIMPLIFY-CLAUSE-MAXIMALLY-CLAUSES
                 (CONS CL SIMPLIFY-CLAUSE-MAXIMALLY-CLAUSES)))))

(DEFUN SIMPLIFY-CLAUSE0 (CL HIST)
  (PROG (TYPE-ALIST SIMPLIFY-CLAUSE-POT-LST CLS NEG-HYPS)
        (SETQ CL (REMOVE-TRIVIAL-EQUATIONS CL))
        (SETQ TYPE-ALIST (TYPE-ALIST-CLAUSE CL))
        (COND ((EQ (QUOTE CONTRADICTION) TYPE-ALIST) (RETURN NIL)))
        (SET-SIMPLIFY-CLAUSE-POT-LST CL TYPE-ALIST)
        (COND ((EQ SIMPLIFY-CLAUSE-POT-LST (QUOTE CONTRADICTION))
               (SETQ CLS NIL))
              (T (SETQ CLS (LIST (PROCESS-EQUATIONAL-POLYS
                                  CL HIST
                                  SIMPLIFY-CLAUSE-POT-LST)))))
        (COND ((NOT (AND (INT= (LENGTH CLS) 1) (EQUAL (CAR CLS) CL)))
               (PUSH-LEMMA (QUOTE ZERO))
               (ITERATE FOR X IN LEMMAS-USED-BY-LINEAR DO (PUSH-LEMMA X))
               (SETQ LINEAR-ASSUMPTIONS
                     (ITERATE FOR HYP IN LINEAR-ASSUMPTIONS
                              UNLESS (ITERATE FOR LIT IN CL
                                              THEREIS (COMPLEMENTARYP HYP LIT))
                              COLLECT HYP))
               (SETQ NEG-HYPS (ITERATE FOR HYP IN LINEAR-ASSUMPTIONS
                                       COLLECT (DUMB-NEGATE-LIT HYP)))
               (SETQ CLS (ITERATE FOR CL IN CLS
                                  COLLECT (DISJOIN-CLAUSES NEG-HYPS CL)))
               (ITERATE FOR TERM IN LINEAR-ASSUMPTIONS
                        DO (SETQ CLS (CONS (CONS TERM CL) CLS)))
               (RETURN CLS))
              (T (RETURN (SIMPLIFY-CLAUSE1 CL NIL NIL 1))))))

(DEFUN SIMPLIFY-CLAUSE1 (TAIL NEW-CLAUSE LITS-TO-BE-IGNORED-BY-LINEAR I)

;   Returns a list of clauses whose conjunction is equivalent to the clause CL
;   formed by appending TAIL to NEW-CLAUSE under the hypothesis of the polys in
;   SIMPLIFY-CLAUSE-POT-LST and under the hypothesis that CL is false.

  (PROG (VAL SEGS TYPE-ALIST NEG-HYPS CURRENT-LIT CURRENT-ATM BRANCHES)
        (COND ((AND TIME-LIMIT-IN-60THS
                    (> (- (TIME-IN-60THS) PROOF-START-TIME-IN-60THS)
                       TIME-LIMIT-IN-60THS))
               (ER SOFT ((X (/ TIME-LIMIT-IN-60THS 60)))
                   |The| |time| |limit| |of| (!PPR X NIL)
                   |seconds| |has| |expired| |.| CR)))
        (COND
         ((NULL TAIL) (RETURN (LIST NEW-CLAUSE)))
         (T (SETQ CURRENT-LIT (SETQ CURRENT-ATM (CAR TAIL)))
            (MATCH CURRENT-ATM (NOT CURRENT-ATM))
            (SETQ LITS-TO-BE-IGNORED-BY-LINEAR
                  (CONS CURRENT-LIT LITS-TO-BE-IGNORED-BY-LINEAR))
            (SETQ FNSTACK NIL)
            (SETQ TYPE-ALIST (TYPE-ALIST-CLAUSE NEW-CLAUSE))
            (COND ((EQ TYPE-ALIST (QUOTE CONTRADICTION)) (RETURN NIL)))
            (SETQ TYPE-ALIST (TYPE-ALIST-CLAUSE (CDR TAIL)))
            (COND ((EQ TYPE-ALIST (QUOTE CONTRADICTION)) (RETURN NIL)))
            (INIT-LINEARIZE-ASSUMPTIONS-STACK)
            (PUSH-LINEARIZE-ASSUMPTIONS-FRAME)
            (SETQ VAL (REWRITE CURRENT-ATM NIL TYPE-ALIST
                               (QUOTE ?)
                               (QUOTE IFF)
                               NIL
                               I))
            (COND ((NOT (EQ CURRENT-LIT CURRENT-ATM))
                   (SETQ VAL (NEGATE-LIT VAL))))
            (SETQ LINEAR-ASSUMPTIONS (POP-LINEARIZE-ASSUMPTIONS-FRAME))
            (SETQ NEG-HYPS (ITERATE FOR HYP IN LINEAR-ASSUMPTIONS
                                    COLLECT (NEGATE-LIT HYP)))
            (SETQ BRANCHES (CLAUSIFY VAL))
            (SETQ SEGS
                  (CONJOIN-CLAUSE-SETS
                   (ITERATE FOR SEG IN BRANCHES
                            COLLECT (DISJOIN-CLAUSES NEG-HYPS SEG))
                   (ITERATE FOR HYP IN LINEAR-ASSUMPTIONS
                            WITH CL  = (ADD-LITERAL (PEGATE-LIT CURRENT-LIT)
                                                    NIL NIL)
                            COLLECT (ADD-LITERAL HYP CL NIL))))
            (RETURN (ITERATE FOR SEG IN SEGS
                             NCONC
                             (SIMPLIFY-CLAUSE1
                              (CDR TAIL)
                              (APPEND NEW-CLAUSE SEG)
                              (COND ((EQUAL BRANCHES (QUOTE (NIL)))
                                     LITS-TO-BE-IGNORED-BY-LINEAR)
                                    (T (CDR LITS-TO-BE-IGNORED-BY-LINEAR)))
                              (1+ I))))))))

(DEFUN SIMPLIFY-LOOP (CLAUSES)

;   This function just serves as a target for the RETFROM in STORE-SENT in the
;   event that we are working on the original input and find that we have split
;   it into more than one goal and want to back up and use induction on the
;   input term.

  (CATCH (QUOTE SIMPLIFY-LOOP)
    (ITERATE FOR CURRENT-CL IN CLAUSES DO (SIMPLIFY-SENT CURRENT-CL NIL))))

(DEFUN SIMPLIFY-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (EXECUTE-PROCESS (QUOTE SIMPLIFY-CLAUSE)
           CL HIST (QUOTE SIMPLIFY-SENT)
           (QUOTE SETTLED-DOWN-SENT)))

(DEFUN SINGLETON-CONSTRUCTOR-TO-RECOGNIZER (FNNAME)
  (COND ((SETQ TEMP-TEMP (ASSOC-EQ FNNAME SHELL-ALIST))
         (SETQ TEMP-TEMP (TSLOGBIT (CDR TEMP-TEMP)))
         (COND ((MEMBER-EQUAL TEMP-TEMP SINGLETON-TYPE-SETS)
                (CAR (ITERATE FOR PAIR IN RECOGNIZER-ALIST
                              WHEN (EQUAL TEMP-TEMP (CDR PAIR))
                              DO (RETURN PAIR))))
               (T NIL)))
        (T NIL)))

(DEFUN SKETCH (N X)
  (COND ((ATOM X) X)
        ((INT= 0 N) '|#|)
        (T (CONS (CAR X) (SKETCH-LST (1- N) (CDR X))))))

(DEFUN SKETCH-LST (N LST)
  (COND ((ATOM LST) LST)
        (T (CONS (SKETCH N (CAR LST)) (SKETCH-LST N (CDR LST))))))

(DEFUN SKIM-FILE (INFILE-ROOT &REST R)
  (PRINEVAL (PQUOTE
             (PROGN CR CR WARNING |:| |Skimming| |in| |the| |events|
                    |from| (!PPR INFILE-ROOT NIL) |may| |render|
                    |Nqthm| |inconsistent| |.| |The| |user| |is| |also|
                    |reminded| |that| |output| |is| |suppressed| |while|
                    |skimming| |.| CR))
            (list (cons 'infile-root infile-root))
            0 prove-file)
  (APPLY (FUNCTION PROVE-FILE)
         INFILE-ROOT
         :PETITIO-PRINCIPII T
         :WRITE-FLAG-FILES NIL
         R))

(DEFUN SKO-DEST-NESTP (TERM DEEPFLG)
  (COND ((VARIABLEP TERM) T)
        ((FQUOTEP TERM) NIL)
        ((AND (SETQ TEMP-TEMP (GET (FFN-SYMB TERM)
                                   (QUOTE ELIMINATE-DESTRUCTORS-SEQ)))
              (NOT (DISABLEDP (ACCESS REWRITE-RULE NAME TEMP-TEMP))))
         (COND (DEEPFLG (ITERATE FOR X IN (FARGS TERM)
                                 ALWAYS (SKO-DEST-NESTP X DEEPFLG)))
               (T (ITERATE FOR X IN (FARGS TERM) ALWAYS (VARIABLEP X)))))
        (T NIL)))

(DEFUN SMART-ASSUME-TRUE-FALSE (TERM)

;   The difference between this function and the primitive
;   ASSUME-TRUE-FALSE is that we here know about compound recognizers
;   and push names onto the lemma stack.  Don't use this function
;   unless there is a PUSH-LEMMA-FRAME provided during the running.

  (PROG (FN A TSA TPAIR FPAIR NEG-FLG)
        (ASSUME-TRUE-FALSE TERM)
        (COND ((AND (NULL TRUE-COMPOUND-RECOGNIZER-ALIST)
                    (NULL FALSE-COMPOUND-RECOGNIZER-ALIST))

;   If there are no compound recognizers yet, don't waste any further time.
;   Probably there will many many times when compound recognizers are not
;   around.

               (RETURN NIL))
              ((OR MUST-BE-TRUE MUST-BE-FALSE)

;   If the test is already decided, don't change the type alists.  There is
;   a question here.  Perhaps (BOOLP A) is known to be true by some mechanism
;   that didn't put (A . bool) on the type alist.  If so, we'll lose the chance
;   to add it.
              
               (RETURN NIL)))

;   We now strip off the NOT that may be present.  By so negating the
;   TERM we are considering we must also swap the roles of TRUE- and
;   FALSE-TYPE-ALIST, which were set up for the other parity.  Henceforth,
;   any exit from this fn must consider NEG-FLG.  We therefore always exit
;   through the label EXIT below.

        (COND ((MATCH TERM (NOT TERM))
               (OUR-SWAP TRUE-TYPE-ALIST FALSE-TYPE-ALIST)
               (SETQ NEG-FLG T)))

        (COND ((OR (VARIABLEP TERM)
                   (FQUOTEP TERM)
                   (NOT (MATCH TERM (LIST FN A)))
                   (PROGN (SETQ TPAIR
                                (ASSOC-EQ FN
                                          TRUE-COMPOUND-RECOGNIZER-ALIST))
                          (SETQ FPAIR
                                (ASSOC-EQ FN
                                          FALSE-COMPOUND-RECOGNIZER-ALIST))
                          (COND ((AND TPAIR (DISABLEDP (CDDR TPAIR)))
                                 (SETQ TPAIR NIL)))
                          (COND ((AND FPAIR (DISABLEDP (CDDR FPAIR)))
                                 (SETQ FPAIR NIL)))
                          (AND (NULL TPAIR) (NULL FPAIR))))

;   If TERM is not of the form (fn a), where fn is a compound recognizer of
;   one parity of the other, then leave the type alists alone.

               (GO EXIT)))

;   If we get here one or both of TPAIR and FPAIR is set to the available
;   compound recognizer facts.  We will deal with the two type alists in
;   turn, augmenting either according to whether we have a compound recognizer
;   fact of the appropriate parity.  Conceivably, either may lead to a
;   contradiction, in which case we set the MUST-BE-TRUE or -FALSE flag
;   and NIL out the alists.  Here is how it can happen.  Suppose we know
;   about BOOLP as a compound recognizer but have it disabled.  Suppose we
;   are proving (IF (LISTP A) (IF (BOOLP A) F T) T).  Then when we assume
;   the BOOLP with the primitive ASSUME-TRUE-FALSE nothing inconsistent is
;   detected.  But with the smart one we are forced to conclude that the
;   type set of A is empty, which is a contradiction.

        (SETQ TSA (TYPE-SET A))

;   If either TPAIR or FPAIR lets us set MUST-BE-TRUE or -FALSE then
;   do it.  It would be prettier code to consider TPAIR (jumping to
;   EXIT if necessary) and then consider FPAIR.  But that may cause us
;   to PUSH-LEMMA the TPAIR name only to discover that the FPAIR lets
;   us decide the test.

        (COND ((AND TPAIR (TS= 0 (TSLOGAND TSA (CADR TPAIR))))
               (SETQ MUST-BE-FALSE T)
               (PUSH-LEMMA (CDDR TPAIR))
               (GO EXIT))
              ((AND FPAIR (TS= 0 (TSLOGAND TSA (CADR FPAIR))))
               (SETQ MUST-BE-TRUE T)
               (PUSH-LEMMA (CDDR FPAIR))
               (GO EXIT)))

;   Now we augment TRUE-TYPE-ALIST if we have a TPAIR and do the symmetric
;   thing for FALSE-TYPE-ALIST.  We push the name of the compound recognizer
;   lemmas used.  Note that the type set information added may not actually
;   contribute anything to the proof.  But we won't be able to tell.

        (COND (TPAIR
               (PUSH-LEMMA (CDDR TPAIR))
               (SETQ TRUE-TYPE-ALIST
                     (CONS (CONS A (TSLOGAND TSA (CADR TPAIR)))
                           TRUE-TYPE-ALIST))))
        (COND (FPAIR
               (PUSH-LEMMA (CDDR FPAIR)) 
               (SETQ FALSE-TYPE-ALIST
                     (CONS (CONS A (TSLOGAND TSA (CADR FPAIR)))
                           FALSE-TYPE-ALIST))))
        EXIT
        (COND (NEG-FLG (OUR-SWAP MUST-BE-TRUE MUST-BE-FALSE)
                       (OUR-SWAP TRUE-TYPE-ALIST FALSE-TYPE-ALIST)))
        (RETURN NIL)))

(DEFUN SOME-SUBTERM-WORSE-THAN-OR-EQUAL (TERM1 TERM2)

;   Returns T if some subterm of TERM1 is WORSE-THAN or EQUAL to TERM2 itself.

  (COND ((VARIABLEP TERM1) (EQ TERM1 TERM2))
        ((OR (EQUAL TERM1 TERM2) (QUICK-WORSE-THAN TERM1 TERM2)) T)
        ((FQUOTEP TERM1) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM1)
                    THEREIS (SOME-SUBTERM-WORSE-THAN-OR-EQUAL ARG TERM2)))))

(DEFUN SORT-DESTRUCTOR-CANDIDATES (LST)

;   Each element of LST is a list of NVARIABLEP nonQUOTEP terms.  We sort them
;   into descending order according to the sum of the level numbers of the fn
;   symbols of the terms in the CDR of each element.

  (UNSTABLE-SORT LST
                 (FUNCTION (LAMBDA (X Y)
                             (> (ITERATE FOR TERM IN (CDR X)
                                         SUM
                                         (GET-LEVEL-NO (FFN-SYMB TERM)))
                                (ITERATE FOR TERM IN (CDR Y)
                                         SUM (GET-LEVEL-NO
                                              (FFN-SYMB TERM))))))))

(DEFUN SORT-EVENTS (LST)
  (UNSTABLE-SORT LST
                 (FUNCTION
                  (LAMBDA (X Y)
                    (EVENT1-OCCURRED-BEFORE-EVENT2
                     X Y CHRONOLOGY)))))

(DEFUN SOUND-IND-PRIN-MASK (TERM JUSTIFICATION FORMALS QUICK-BLOCK-INFO)

;   TERM is a term we are considering doing induction for.  JUSTIFICATION is
;   one of the justifications associated with the function symbol of TERM.
;   FORMALS is the formals list of the fn and QUICK-BLOCK-INFO is the obvious.
;   JUSTIFICATION and the machine for fn describe an induction.  We wish to
;   determine, in the terminology of ACL, whether the induction applies to
;   TERM.  If so we return a mask indicating how to build the substitutions for
;   the induction from TERM and the machine for fn.  Otherwise we return NIL.

;   Let the changeables be those actuals of TERM that are in the measured
;   subset of JUSTIFICATION and that sometimes change in the recursion.  Let
;   the unchangeables be all of the variables occurring in measured actuals
;   that never change in recursion.  The induction applies if changeables is a
;   sequence of distinct variable names and has an empty intersection with
;   unchangeables.

;   If the induction is applicable then the substitutions should substitute for
;   the changeables just as the recursion would, and hold each unchangeable
;   fixed -- i.e., substitute each for itself.  With such substitutions it is
;   possible to prove the measure lemmas analogous to those proved in
;   JUSTIFICATION, except that the measure is obtained by instantiating the
;   measure term used in the justification by the measured actuals in
;   unchanging slots.  Actual variables that are neither among the changeables
;   or unchangeables may be substituted for arbitrarily.

;   If the induction is applicable we return a mask with as many elements as
;   there are actuals.  For each actual the mask contains either CHANGEABLE,
;   UNCHANGEABLE, or NIL.  CHANGEABLE means the actual should be instantiated
;   as specified in the recursion.  UNCHANGEABLE means each var in the actual
;   should be held fixed.  NIL means that the corresponding substitution pairs
;   in the machine for the function should be ignored.

;   Abstractly, this function builds the mask by first putting either
;   CHANGEABLE or UNCHANGEABLE in each measured slot.  It then fills in the
;   remaining slots from the left so as to permit the actual to be instantiated
;   or held fixed as desired by the recursion, provided that in so doing it
;   does not permit substitutions for previously allocated actuals.

  (PROG (UNCHANGEABLES SUBSET CHANGEABLES)
        (SETQ SUBSET (ACCESS JUSTIFICATION SUBSET JUSTIFICATION))
        (SETQ UNCHANGEABLES (ITERATE FOR ACTUAL IN (FARGS TERM) AS VAR
                                     IN FORMALS AS Q IN QUICK-BLOCK-INFO
                                     WITH ITERATE-ANS
                                     WHEN (AND (MEMBER-EQ VAR SUBSET)
                                               (EQ Q (QUOTE UNCHANGING)))
                                     DO (SETQ ITERATE-ANS
                                              (UNION-EQ (ALL-VARS ACTUAL)
                                                        ITERATE-ANS))
                                     FINALLY (RETURN ITERATE-ANS)))
        (SETQ CHANGEABLES (ITERATE FOR ACTUAL IN (FARGS TERM) AS VAR
                                   IN FORMALS AS Q IN QUICK-BLOCK-INFO
                                   WHEN (AND (MEMBER-EQ VAR SUBSET)
                                             (NOT (EQ Q (QUOTE UNCHANGING))))
                                   COLLECT ACTUAL))
        (COND ((OR (NOT (NO-DUPLICATESP CHANGEABLES))
                   (ITERATE FOR X IN CHANGEABLES THEREIS (NVARIABLEP X))
                   (INTERSECTP CHANGEABLES UNCHANGEABLES))
               (RETURN NIL)))
        (RETURN (ITERATE FOR ACTUAL IN (FARGS TERM) AS Q
                         IN QUICK-BLOCK-INFO AS VAR IN FORMALS
                         COLLECT (COND ((MEMBER-EQ VAR SUBSET)
                                        (COND ((EQ Q (QUOTE UNCHANGING))
                                               (QUOTE UNCHANGEABLE))
                                              (T (QUOTE CHANGEABLE))))
                                       ((AND (VARIABLEP ACTUAL)
                                             (EQ Q (QUOTE UNCHANGING)))
                                        (COND ((MEMBER-EQ ACTUAL CHANGEABLES)
                                               NIL)
                                              (T (SETQ UNCHANGEABLES
                                                       (ADD-TO-SET
                                                        ACTUAL
                                                        UNCHANGEABLES))
                                                 (QUOTE UNCHANGEABLE))))
                                       ((AND (VARIABLEP ACTUAL)
                                             (NOT (MEMBER-EQ ACTUAL
                                                             CHANGEABLES))
                                             (NOT (MEMBER-EQ ACTUAL
                                                             UNCHANGEABLES)))
                                        (SETQ CHANGEABLES
                                              (CONS ACTUAL CHANGEABLES))
                                        (QUOTE CHANGEABLE))
                                       (T NIL))))))

(DEFUN SPELL-NUMBER (N)
  (COND ((INT= N 0) (QUOTE |zero|))
        ((INT= N 1) (QUOTE |one|))
        ((INT= N 2) (QUOTE |two|))
        ((INT= N 3) (QUOTE |three|))
        ((INT= N 4) (QUOTE |four|))
        ((INT= N 5) (QUOTE |five|))
        ((INT= N 6) (QUOTE |six|))
        ((INT= N 7) (QUOTE |seven|))
        ((INT= N 8) (QUOTE |eight|))
        ((INT= N 9) (QUOTE |nine|))
        ((INT= N 10) (QUOTE |ten|))
        (T N)))

(DEFUN STANDARD-ALIST (VARS)
  (COND ((ATOM VARS) (QUOTE (QUOTE NIL)))
        (T (FCONS-TERM* (QUOTE CONS)
                        (FCONS-TERM* (QUOTE CONS)
                                     (LIST (QUOTE QUOTE) (CAR VARS))
                                     (CAR VARS))
                        (STANDARD-ALIST (CDR VARS))))))

(DEFUN START-STATS NIL
  (SETQ PROVE-TIME 0)
  (SETQ ELAPSED-TIME (TIME-IN-60THS))
  (SETQ IO-TIME 0))

(DEFUN STOP-STATS NIL
  (COND (PETITIO-PRINCIPII (RETURN-FROM STOP-STATS T)))
  (LET (M-TIME P-TIME I-TIME)
    (SETQ M-TIME
          (/
           (- (- (TIME-IN-60THS)
                 ELAPSED-TIME)
              (+ PROVE-TIME IO-TIME))
           60.0))
    (SETQ P-TIME
          (/ PROVE-TIME 60.0))
    (SETQ I-TIME
          (/ IO-TIME 60.0))
    (PRINT-STATS M-TIME P-TIME I-TIME PROVE-FILE)
    (SETQ TOTAL-MISC-TIME (+ TOTAL-MISC-TIME M-TIME))
    (SETQ TOTAL-PROVE-TIME (+ TOTAL-PROVE-TIME P-TIME))
    (SETQ TOTAL-IO-TIME (+ TOTAL-IO-TIME I-TIME))))

(DEFUN STORE-DEFINITION (ATM EXPR)
  (SETF (GET ATM (QUOTE SEXPR)) EXPR)
  (SETQ EXPR (COPY-TREE EXPR))
  (LET ((TEMP `(DEFUN ,ATM ,(CADR EXPR) ,@ (CDDR EXPR))))
    (EVAL TEMP)
    (MAKE-DECLARE-FORM TEMP))
  (COND (*COMPILE-FUNCTIONS-FLG*
         (COMPILE ATM))))

(DEFUN STORE-SENT (CL HIST)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET (CL-SET)
    (COND ((NULL CL)
           (IO (QUOTE STORE-SENT) CL HIST NIL (LIST (GET-STACK-NAME STACK)))
           (WRAPUP NIL))
          (DO-NOT-USE-INDUCTION-FLG
           (IO (QUOTE STORE-SENT)
               CL HIST NIL (LIST (GET-STACK-NAME STACK) (QUOTE QUIT)))
           (WRAPUP NIL))
          ((AND
            (NOT (AND IN-PROVE-LEMMA-FLG (ASSOC-EQ (QUOTE INDUCT) HINTS)))
            (OR
             (AND
              (NULL STACK)
              (ITERATE FOR X IN HIST THEREIS
                       (NOT
                        (MEMBER-EQ (CAR X)
                                   (QUOTE (SETTLED-DOWN-CLAUSE
                                           SIMPLIFY-CLAUSE
                                           SETUP))))))
             (AND STACK (NOT (ASSOC-EQ (QUOTE BEING-PROVED) STACK)))))

;   Abort and push the input clause to work on if (a) this is the first time
;   we've ever pushed anything and we've done anything to the input other than
;   simplify it, or (b) we have not yet gone into the first induction for the
;   original conjecture but have already pushed one simplified subgoal.

           (SETQ STACK NIL)
           (SETQ CL-SET (CNF-DNF THM (QUOTE C)))

;   Once upon a time we backed up to the output of PREPROCESS in PROVE.
;   However, PREPROCESS -- and CLAUSIFY-INPUT -- applies unconditional rewrite
;   rules and we want the ability as users to type in exactly what the system
;   inducts on.  The theorem that PREPROCESS screwed us on was HACK1 when it
;   distributed TIMES and GCD.

           (IO (QUOTE STORE-SENT)
               CL NIL NIL (LIST (GET-STACK-NAME STACK)
                                CL-SET))
           (PUSH-CLAUSE-SET CL-SET)
           (THROW (QUOTE SIMPLIFY-LOOP) NIL))
          (T (SETQ CL-SET (LIST CL))
             (IO (QUOTE STORE-SENT) CL HIST NIL (LIST (GET-STACK-NAME STACK)))
             (PUSH-CLAUSE-SET CL-SET)))))

#|

Below is the pre-1992 definition of STRIP-BRANCHES.  This code was
replaced by Bishop Brock, who coded the original version of what is
now STRIP-BRANCHES and STRIP-TERM.  Brock's clausifier is considerably
faster than the old one, primarily because it prunes the tree as it
goes.  Hunt and Brock found this improvement necessary simply to get
the FM9001 proofs to go through.  We find it easier to understand
Brock's code as a modification of our code however, which is why we've
preserved it below.

 (DEFUN STRIP-BRANCHES (TERM)
  (LET (CL)
    (ITERATE FOR PAIR
             IN (COND ((MATCH TERM (NOT TERM)) (STRIP-BRANCHES1 TERM T T))
                      (T (STRIP-BRANCHES1 TERM T NIL)))
             UNLESS (EQUAL (SETQ CL
                                 (ADD-LITERAL
                                  (PEGATE-LIT (CAR PAIR)) (CDR PAIR) T))
                           TRUE-CLAUSE)
             COLLECT CL)))

 (DEFUN STRIP-BRANCHES1 (TERM TOPFLG NEGATE-FLG)
  (LET (ANS1 ANS2 ANS3 ANS LST NEW-CL)
    (COND ((VARIABLEP TERM)
           (LIST (CONS (COND (NEGATE-FLG (NEGATE-LIT TERM)) (T TERM)) NIL)))
          ((FQUOTEP TERM)
           (COND (TOPFLG (COND ((EQUAL TERM FALSE)
                                (COND (NEGATE-FLG NIL)
                                      (T (LIST (CONS FALSE NIL)))))
                               (NEGATE-FLG (LIST (CONS FALSE NIL)))
                               (T NIL)))
                 (NEGATE-FLG (LIST (CONS (COND ((EQUAL TERM FALSE) TRUE)
                                               (T FALSE))
                                         NIL)))
                 (T (LIST (CONS TERM NIL)))))
          ((EQ (FFN-SYMB TERM) (QUOTE IF))
           (COND ((AND TOPFLG (OR (AND (NOT NEGATE-FLG)
                                       (EQUAL (FARGN TERM 3) FALSE))
                                  (AND NEGATE-FLG
                                       (EQUAL (FARGN TERM 3) TRUE))))
                  (APPEND
                   (ITERATE FOR PAIR IN (STRIP-BRANCHES1 (FARGN TERM 1)
                                                         TOPFLG NIL)
                            UNLESS (EQUAL (SETQ NEW-CL
                                                (ADD-LITERAL
                                                 (PEGATE-LIT (CAR PAIR))
                                                 (CDR PAIR)
                                                 T))
                                          TRUE-CLAUSE)
                            COLLECT (CONS FALSE NEW-CL))
                   (STRIP-BRANCHES1 (FARGN TERM 2) TOPFLG NEGATE-FLG)))
                 ((AND TOPFLG (OR (AND (NOT NEGATE-FLG)
                                       (EQUAL (FARGN TERM 2) FALSE))
                                  (AND NEGATE-FLG
                                       (EQUAL (FARGN TERM 2) TRUE))))
                  (APPEND
                   (ITERATE FOR PAIR IN (STRIP-BRANCHES1 (FARGN TERM 1)
                                                         TOPFLG T)
                            UNLESS (EQUAL (SETQ NEW-CL
                                                (ADD-LITERAL
                                                 (PEGATE-LIT (CAR PAIR))
                                                 (CDR PAIR)
                                                 T))
                                          TRUE-CLAUSE)
                            COLLECT (CONS FALSE NEW-CL))
                   (STRIP-BRANCHES1 (FARGN TERM 3)
                                    TOPFLG NEGATE-FLG)))
                 (T
                  (SETQ ANS1 (STRIP-BRANCHES1 (FARGN TERM 1) NIL NIL))
                  (SETQ ANS2 (STRIP-BRANCHES1 (FARGN TERM 2)
                                              TOPFLG NEGATE-FLG))
                  (SETQ ANS3 (STRIP-BRANCHES1 (FARGN TERM 3)
                                              TOPFLG NEGATE-FLG))
                  (ITERATE FOR PAIR IN ANS1 DO
                           (PROGN
                             (ITERATE FOR PAIR2 IN ANS2 UNLESS
                                      (EQUAL
                                       (CDR
                                        (SETQ ANS
                                              (CONS
                                               (CAR PAIR2)
                                               (DISJOIN-CLAUSES
                                                (CDR PAIR)
                                                (ADD-LITERAL
                                                 (NEGATE-LIT (CAR PAIR))
                                                 (CDR PAIR2)
                                                 NIL)))))
                                       TRUE-CLAUSE)
                                      DO (SETQ LST (CONS ANS LST)))
                             (ITERATE FOR PAIR3 IN ANS3
                                      UNLESS
                                      (EQUAL
                                       (CDR
                                        (SETQ ANS
                                              (CONS
                                               (CAR PAIR3)
                                               (DISJOIN-CLAUSES
                                                (CDR PAIR)
                                                (ADD-LITERAL
                                                 (PEGATE-LIT (CAR PAIR))
                                                 (CDR PAIR3)
                                                 NIL)))))
                                       TRUE-CLAUSE)
                                      DO (SETQ LST (CONS ANS LST)))))
                  LST)))
          (T
           (ITERATE FOR PICK
                    IN (ALL-PICKS (ITERATE FOR ARG IN (FARGS TERM)
                                           COLLECT (STRIP-BRANCHES1 ARG NIL
                                                                    NIL)))
                    COLLECT
                    (CONS (COND (NEGATE-FLG
                                 (DUMB-NEGATE-LIT
                                  (SCONS-TERM (FFN-SYMB TERM)
                                              (ITERATE FOR PAIR IN PICK
                                                       COLLECT (CAR PAIR)))))
                                (T (SCONS-TERM (FFN-SYMB TERM)
                                               (ITERATE FOR PAIR IN PICK
                                                        COLLECT (CAR PAIR)))))
                          (ITERATE FOR PAIR IN PICK WITH ANS
                                   UNTIL (EQUAL ANS TRUE-CLAUSE)
                                   DO (SETQ ANS
                                            (DISJOIN-CLAUSES (CDR PAIR) ANS))
                                   FINALLY (RETURN ANS))))))))
|#

; Here is Bishop Brocks "fast clausifier".  This code was refined by
; Bishop in collaboration with Matt Kaufmann, who spent many hours
; arguing its correctness.  Upon our pre-release proveall for
; Nqthm-1992, we discovered that reorderings of the clauses produced
; by the fast clausifier caused some proofs to fail.  (These were
; initially discovered in the context of Pc-Nqthm, where numbered
; hypotheses no longer had their old numbers; but one of Yuan Yu's
; machine code proofs failed under the first version of the fast
; clausifier because of reordering.)  Matt Kaufmann inserted a few
; well-chosen nreverses in the code below to make the fast clausifier
; return clauses in almost exactly the same order as the old one.  See
; remarks.text.

(DEFUN STRIP-BRANCHES (TERM)
  (ITERATE FOR (LIT . CLAUSE)
           IN (COND ((MATCH TERM (NOT TERM))
                     (STRIP-TERM TERM T T 'TOP NIL))
                    (T (STRIP-TERM TERM T NIL 'TOP NIL)))
           UNLESS (EQUAL (SETQ CLAUSE (REVERSE
                                       (ADD-LITERAL
                                        (PEGATE-LIT LIT)
                                        CLAUSE
                                        NIL)))
                         TRUE-CLAUSE)
           COLLECT CLAUSE))

(DEFUN STRIP-TERM (TERM TOPFLG NEGATE-FLG ARG-TAIL PROTO-CLAUSE)
  (COND
   ((AND TOPFLG
         (QUOTEP TERM) 
         ;; so, note that then arg-tail = 'top
         (EQ (EQUAL TERM FALSE) NEGATE-FLG))
    NIL)
   ((NOT (FNNAMEP-IF TERM))
    (COND (NEGATE-FLG (SETQ TERM (NEGATE-LIT TERM))))
    (COND
     ((LISTP ARG-TAIL)
      (LIST (CONS (CONS TERM ARG-TAIL) PROTO-CLAUSE)))
     (T (LIST (CONS TERM PROTO-CLAUSE)))))
   ((EQ (FFN-SYMB TERM) (QUOTE IF))
    (COND
     ((AND TOPFLG (OR (AND (NOT NEGATE-FLG)
                           (EQUAL (FARGN TERM 3) FALSE))
                      (AND NEGATE-FLG
                           (EQUAL (FARGN TERM 3) TRUE))))
      (NCONC
       (ITERATE FOR (LIT . CLAUSE)
                IN (STRIP-TERM (FARGN TERM 1) TOPFLG NIL ARG-TAIL PROTO-CLAUSE)
                UNLESS (EQUAL (SETQ CLAUSE (ADD-LITERAL
                                            (PEGATE-LIT LIT)
                                            CLAUSE
                                            NIL)) 
                              TRUE-CLAUSE)
                COLLECT
; Perhaps it's ok just to return clause, but then the order can
; (we think) cause clauses to get printed out in an unaesthetic manner.
                (CONS FALSE CLAUSE))
       (STRIP-TERM (FARGN TERM 2) TOPFLG NEGATE-FLG ARG-TAIL PROTO-CLAUSE)))
     ((AND TOPFLG (OR (AND (NOT NEGATE-FLG)
                           (EQUAL (FARGN TERM 2) FALSE))
                      (AND NEGATE-FLG
                           (EQUAL (FARGN TERM 2) TRUE))))
      (NCONC
       (ITERATE FOR (LIT . CLAUSE)
                IN (STRIP-TERM (FARGN TERM 1) TOPFLG T ARG-TAIL PROTO-CLAUSE)
                UNLESS (EQUAL (SETQ CLAUSE (ADD-LITERAL
                                            (PEGATE-LIT LIT)
                                            CLAUSE
                                            NIL)) 
                              TRUE-CLAUSE)
                COLLECT (CONS FALSE CLAUSE))
       (STRIP-TERM (FARGN TERM 3) TOPFLG NEGATE-FLG ARG-TAIL PROTO-CLAUSE)))
     (T
      (LET ((TEST-CLAUSES
             (STRIP-TERM (FARGN TERM 1) NIL NIL 'IF PROTO-CLAUSE)))
        (ITERATE FOR (TEST . CLAUSE) IN TEST-CLAUSES
                 WITH LST AND CLAUSE2 AND CLAUSE3
                 UNLESS
                 (EQUAL (SETQ CLAUSE2 (ADD-LITERAL (NEGATE-LIT TEST)
                                                   CLAUSE NIL) )
                        TRUE-CLAUSE)
                 DO
                 (SETQ LST
                       (NCONC
                        (NREVERSE (STRIP-TERM (FARGN TERM 2) TOPFLG
                                              NEGATE-FLG ARG-TAIL CLAUSE2))
                        LST))
                 UNLESS
                 (EQUAL (SETQ CLAUSE3 (ADD-LITERAL (PEGATE-LIT TEST)
                                                   CLAUSE NIL))
                        TRUE-CLAUSE)
                 DO
                 (SETQ LST
                       (NCONC
                        (NREVERSE (STRIP-TERM (FARGN TERM 3) TOPFLG
                                              NEGATE-FLG ARG-TAIL CLAUSE3))
                        LST))
                 FINALLY (RETURN LST))))))
   (T
    (ITERATE FOR (ARGS . CLAUSE) IN (STRIP-ARGS (FARGS TERM) PROTO-CLAUSE)
             COLLECT
             (LET ((NEW-TERM (IF NEGATE-FLG
                                 (DUMB-NEGATE-LIT
                                  (SCONS-TERM (FFN-SYMB TERM) ARGS))
                                 (SCONS-TERM (FFN-SYMB TERM) ARGS))))
               (COND
                ((LISTP ARG-TAIL)
                 (CONS (CONS NEW-TERM ARG-TAIL) CLAUSE))
                (T (CONS NEW-TERM CLAUSE))))))))

(DEFUN STRIP-ARGS (ARGS PROTO-CLAUSE)
  (COND
   ((NULL ARGS) (LIST (CONS NIL PROTO-CLAUSE)))
   (T (ITERATE FOR (ARG-TAIL . CLAUSE)
               IN (STRIP-ARGS (CDR ARGS) PROTO-CLAUSE)
               WITH ARG = (CAR ARGS)
               NCONC (STRIP-TERM ARG NIL NIL ARG-TAIL CLAUSE)))))

(DEFUN SUBBAGP (BAG1 BAG2)
  (COND ((ATOM BAG1) T)
        ((ATOM BAG2) NIL)
        ((MEMBER-EQUAL (CAR BAG1) BAG2)
         (SUBBAGP (CDR BAG1) (DELETE1 (CAR BAG1) BAG2)))
        (T NIL)))

(DEFUN SUBLIS-EXPR1 (ALIST FORM)
  (COND ((SETQ TEMP-TEMP (ASSOC-EQUAL FORM ALIST)) (CDR TEMP-TEMP))
        ((VARIABLEP FORM) FORM)
        ((FQUOTEP FORM) FORM)
        (T (CONS-TERM (FFN-SYMB FORM)
                      (ITERATE FOR ARG IN (FARGS FORM)
                               COLLECT (SUBLIS-EXPR1 ALIST ARG))))))

(DEFUN SUBLIS-FN (FS TERM)
  (LET (TEMP ARGS)
       (COND ((VARIABLEP TERM) TERM)
             ((FQUOTEP TERM) TERM)
             (T
              (SETQ ARGS (ITERATE FOR ARG IN (FARGS TERM)
                                  COLLECT
                                  (SUBLIS-FN FS ARG)))
              (COND ((SETQ TEMP (ASSOC-EQ (FFN-SYMB TERM) FS))
                     (COND ((SYMBOLP (CDR TEMP))
                            (CONS-TERM (CDR TEMP) ARGS))
                           (T (SUB-PAIR-VAR (CADR (CDR TEMP))
                                            ARGS
                                            (CADDR (CDR TEMP))))))
                    (T (CONS-TERM (FFN-SYMB TERM) ARGS)))))))

(DEFUN SUBLIS-VAR (ALIST FORM)

;   In REWRITE-WITH-LEMMAS we use this function with the NIL alist to put FORM
;   into quote normal form.  Do not optimize this function for the NIL alist.

;   This is the only function in the theorem prover that we sometimes
;   call with a "term" that is not in QUOTE normal form.  However,
;   even this function requires that FORM be at least a PSEUDO-TERMP.

  (COND ((VARIABLEP FORM)
         (COND ((SETQ TEMP-TEMP (ASSOC-EQ FORM ALIST))
                (CDR TEMP-TEMP))
               (T FORM)))
        ((FQUOTEP FORM)
         FORM)
        (T (CONS-TERM (FFN-SYMB FORM)
                      (ITERATE FOR ARG IN (FARGS FORM)
                               COLLECT (SUBLIS-VAR ALIST ARG))))))

(DEFUN SUBLIS-VAR-LST (ALIST TERMLST)
  (ITERATE FOR TERM IN TERMLST COLLECT (SUBLIS-VAR ALIST TERM)))

(DEFUN SUB-PAIR-EXPR (OLDLST NEWLST TERM)
  (ITERATE FOR X IN OLDLST DO (COND ((QUOTEP X) (SUBST-EXPR-ERROR1 X))))
  (SUB-PAIR-EXPR1 OLDLST NEWLST TERM))

(DEFUN SUB-PAIR-EXPR1 (OLDLST NEWLST TERM)
  (COND ((ITERATE FOR OLD1 IN OLDLST AS NEW1 IN NEWLST
                  THEREIS (COND ((EQUAL OLD1 TERM) (SETQ TEMP-TEMP NEW1) T)
                                (T NIL)))
         TEMP-TEMP)
        ((VARIABLEP TERM) TERM)
        ((FQUOTEP TERM) TERM)
        (T (CONS-TERM (FFN-SYMB TERM)
                      (ITERATE FOR ARG IN (FARGS TERM)
                               COLLECT (SUB-PAIR-EXPR1 OLDLST NEWLST ARG))))))

(DEFUN SUB-PAIR-VAR (OLDLST NEWLST TERM)
  (COND ((VARIABLEP TERM)
         (COND ((ITERATE FOR OLD1 IN OLDLST AS NEW1 IN NEWLST
                         THEREIS (COND ((EQ OLD1 TERM) (SETQ TEMP-TEMP NEW1) T)
                                       (T NIL)))
                TEMP-TEMP)
               (T TERM)))
        ((FQUOTEP TERM) TERM)
        (T (CONS-TERM (FFN-SYMB TERM)
                      (ITERATE FOR ARG IN (FARGS TERM)
                               COLLECT (SUB-PAIR-VAR OLDLST NEWLST ARG))))))

(DEFUN SUB-PAIR-VAR-LST (OLDLST NEWLST LST)
  (ITERATE FOR X IN LST COLLECT (SUB-PAIR-VAR OLDLST NEWLST X)))

(DEFUN SUBSETP-EQ (X Y)
  (ITERATE FOR ELE IN X ALWAYS (MEMBER-EQ ELE Y)))

(DEFUN SUBSETP-EQUAL (X Y)
  (ITERATE FOR ELE IN X ALWAYS (MEMBER-EQUAL ELE Y)))

(DEFUN SUBST-EXPR (NEW OLD FORM)
  (COND ((VARIABLEP OLD) (SUBST-VAR NEW OLD FORM))
        ((FQUOTEP OLD) (SUBST-EXPR-ERROR1 OLD))
        (T (SUBST-EXPR1 NEW OLD FORM))))

(DEFUN SUBST-EXPR-ERROR1 (OLD)
  (ER HARD (OLD) |Attempt| |to| |substitute| |for| |the| |explicit|
      |constant| (!PPR OLD (QUOTE |.|)) |the| |substitution| |functions|
      |were| |optimized| |to| |disallow| |this| |.|))

(DEFUN SUBST-EXPR-LST (NEW OLD LST)
  (ITERATE FOR X IN LST COLLECT (SUBST-EXPR NEW OLD X)))

(DEFUN SUBST-EXPR1 (NEW OLD FORM)
  (COND ((EQUAL OLD FORM) NEW)
        ((VARIABLEP FORM) FORM)
        ((FQUOTEP FORM) FORM)
        (T (CONS-TERM (FFN-SYMB FORM)
                      (ITERATE FOR ARG IN (FARGS FORM)
                               COLLECT (SUBST-EXPR1 NEW OLD ARG))))))

(DEFUN SUBST-VAR (NEW OLD FORM)
  (COND ((VARIABLEP FORM)
         (COND ((EQ FORM OLD) NEW)
               (T FORM)))
        ((FQUOTEP FORM) FORM)
        (T (CONS-TERM (FFN-SYMB FORM)
                      (ITERATE FOR ARG IN (FARGS FORM)
                               COLLECT (SUBST-VAR NEW OLD ARG))))))

(DEFUN SUBST-VAR-LST (NEW OLD TERMLST)
  (ITERATE FOR TERM IN TERMLST COLLECT (SUBST-VAR NEW OLD TERM)))

(DEFUN SUBSTITUTE-EXPR (NEW OLD FORM)
  (COND ((VARIABLEP OLD) (SUBST-VAR NEW OLD FORM))
        (T (SUBST-EXPR NEW OLD FORM))))

(DEFUN SUBSUMES (CL1 CL2)
  (LET (UNIFY-SUBST) (SUBSUMES1 CL1)))

(DEFUN SUBSUMES-REWRITE-RULE (REWRITE-RULE1 REWRITE-RULE2)
  (LET (UNIFY-SUBST (CL2 (ACCESS REWRITE-RULE HYPS REWRITE-RULE2)))
    (AND (EQ (FFN-SYMB (ACCESS REWRITE-RULE CONCL REWRITE-RULE1))
             (FFN-SYMB (ACCESS REWRITE-RULE CONCL REWRITE-RULE2)))
         (COND ((MEMBER-EQ (FFN-SYMB (ACCESS REWRITE-RULE CONCL REWRITE-RULE1))
                           '(EQUAL IFF))
                (ONE-WAY-UNIFY1 (FARGN (ACCESS REWRITE-RULE CONCL
                                               REWRITE-RULE1) 1)
                                (FARGN (ACCESS REWRITE-RULE CONCL
                                               REWRITE-RULE2) 1)))
               (T (ONE-WAY-UNIFY1 (ACCESS REWRITE-RULE CONCL REWRITE-RULE1)
                                  (ACCESS REWRITE-RULE CONCL REWRITE-RULE2))))
         (SUBSUMES1 (ACCESS REWRITE-RULE HYPS REWRITE-RULE1)))))

(DEFUN SUBSUMES1 (CL1)

;   Also called by SUBSUMES-SEQ.

  (COND ((NULL CL1) T)
        (T (ITERATE FOR LIT IN CL2 THEREIS (SUBSUMES11 LIT CL1 UNIFY-SUBST)))))

(DEFUN SUBSUMES11 (LIT CL1 UNIFY-SUBST)
  (AND (ONE-WAY-UNIFY1 (CAR CL1) LIT)
       (SUBSUMES1 (CDR CL1))))

(DEFUN SUPER-TAMEP (NAME TERM)

;   This function determines whether TERM is "super-tame" wrt NAME.  See the
;   discussion in TAMEP.  Super-tameness is like tameness except that NAME
;   is not considered total if hit by V&C$ and friends.


  (LET (FLG FORM TEST BODY)
    (CHK-NQTHM-MODE$ (QUOTE SUPER-TAMEP))
    (COND ((VARIABLEP TERM) T)
          ((FQUOTEP TERM) T)
          ((ITERATE FOR ARG IN (FARGS TERM) ALWAYS (SUPER-TAMEP NAME ARG))
           (COND ((OR (EQ NAME (FFN-SYMB TERM))
                      (TOTALP (FFN-SYMB TERM)))
                  T)
                 ((OR (MATCH TERM (V&C$ (LIST (QUOTE QUOTE) FLG)
                                        (LIST (QUOTE QUOTE) FORM)
                                        &))
                      (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                         (LIST (QUOTE QUOTE) FORM)
                                         &)))
                  (COND ((EQ FLG (QUOTE LIST))
                         (AND (TERMP-LIST FORM)
                              (TAMEP-LIST FORM)))
                        (T (AND (TERMP FORM)
                                (TAMEP FORM)))))
                 ((MATCH TERM (FOR & & (LIST (QUOTE QUOTE) TEST)
                                   & (LIST (QUOTE QUOTE) BODY) &))
                  (AND (TERMP TEST)
                       (TAMEP TEST)
                       (TERMP BODY)
                       (TAMEP BODY)))
                 (T NIL)))
          (T NIL))))

(DEFUN SUPPORTERS-OF (NAME)
  (COND ((EQ NAME (QUOTE GROUND-ZERO))
         NIL)
        ((OR (NOT (SYMBOLP NAME))
             (NOT (GET NAME (QUOTE EVENT))))
         (ER HARD (NAME) SUPPORTERS-OF |must| |be| |given| |an| |event| |and|
             (!PPR NAME NIL) |is| |not| |one| |.|))
        (T (SORT-EVENTS (SUPPORTERS-OF1 NAME NIL)))))

(DEFUN SUPPORTERS-OF1 (NAME SEEN)
  (ITERATE FOR X IN (IMMEDIATE-SUPPORTERS-OF NAME)
           UNLESS (MEMBER-EQ X SEEN)
           DO (SETQ SEEN (SUPPORTERS-OF1 X (CONS X SEEN))))
  SEEN)

(DEFUN TABULATE (N FILE)
  (ISPACES (- N (IPOSITION FILE NIL NIL)) FILE))

(DEFUN TAMEP (TERM)

;   TERM is a term.  A term is TAMEP if it is a variable, a quote, an
;   application of a TOTALP fn to tame terms, or an application of
;   V&C$, EVAL$, or FOR to tame terms with the additional property
;   that the form/form-lists interpreted are quotations/lists of
;   quotations of tame terms.

;   A fn is TOTALP as follows.   All shell fns and all boot-strap fns with the
;   exceptions of V&C$ and the four functions from which V&C$ can be reached
;   (V&C-APPLY$, EVAL$, APPLY$, and FOR) are TOTALP.  An admissible defined
;   function, (fn x) = body, is TOTALP iff the body is super-tame wrt fn.  A
;   term is super-tame (wrt fn) if the term is a variable, a quote, an
;   application of a TOTALP function or fn to super-tame (wrt fn) terms, or an
;   application of V&C$, EVAL$, or FOR to super-tame (wrt fn) terms with the
;   additional property that the form/form-lists interpreted are
;   quotations/lists of quotations of tame terms.  The function SUPER-TAMEP
;   determines if a term is super-tame wrt fn.  In fact, (TAMEP term) =
;   (SUPER-TAMEP -1 term).  Furthermore, if fn is TOTALP then its body is
;   TAMEP.

;   The Fundamental Theorem about TAMEP:
;   If (TAMEP term) and (SEMI-CONCRETE-ALISTP a)
;      then (V&C$ T 'term a) is non-F
;           and 
;           (CAR (V&C$ T 'term a)) = term/c(a),

;   where c(a) is the substitution constructed from a and extended with (v . 0)
;   pairs to include every variable in term.  See COMPLETE-ALIST.

;   A corollary:  Under the same hyps, (EVAL$ T 'term a) is term/c(a).

;   The Fundamental Theorem about TOTALP:
;   If (TOTALP fn)
;      then (V&C-APPLY$ 'fn vcs) <-> (NOT (MEMBER F vcs))
;           and
;           (CAR (V&C-APPLY$ 'fn vcs))
;             =
;           (IF (MEMBER F vcs)
;               0
;               (fn (CAAR vcs) (CAADR vcs) ... (CAAD...DR vcs)))

;   A corollary:  Under the same hyp, 
;     (APPLY$ 'fn args) = (fn (CAR args) ... (CAD...DR args))

;   Another corollary:  If fn is TOTALP then 
;   (EVAL$ T (CONS (QUOTE fn) args) a)
;     =
;   (fn (EVAL$ T (CAR args) a)
;       ...
;       (EVAL$ T (CAD...DR args) a))

;   Proof.  By the defn of EVAL$ and APPLY$ we get:
;   (1) (EVAL$ T (CONS 'fn args) a)
;       =
;   (2) (CAR (V&C-APPLY 'fn (PAIRLIST eargs 0)))

;   where eargs is (EVAL$ 'LIST args a).  Observe that the PAIRLIST
;   contains no F's and that (CAAD...DR (PAIRLIST X Y)) = (CAD...DR
;   X).  Thus, by the Fundamental Theorem about TOTALP we get that (2)
;   is (3) (fn (CAR eargs) ... (CAD...DR eargs)) or, replacing eargs
;   by its denotation (3) (fn (CAR (EVAL$ 'LIST args a)) ... (CAD...DR
;   (EVAL$ 'LIST args a))).  Finally, observe that (CAD...DR (EVAL$
;   'LIST L A)) = (EVAL$ T (CAD...DR L) A).  Suppose there are n-1
;   D's, i.e., we are going after the nth element.  If L has at least
;   n elements, both sides are equal by the recursion in EVAL$ 'LIST.
;   If L has fewer than n elements, so does (EVAL$ 'LIST L A) and so
;   the left-hand side 0.  The right-hand side is (EVAL$ T 0 A) which
;   is 0, since numbers evaluate to themselves.  Using this
;   observation, (3) becomes (4) (fn (EVAL$ T (CAR args) a) ...
;   (EVAL$ T (CAD...DR args) a)).  Q.E.D.






;   For example, (PLUS (TIMES X Z) Y) is TAMEP, hence:

;   (EVAL$ T '(PLUS (TIMES X Z) Y)
;          (LIST (CONS 'Z Z) (CONS 'X A) (CONS 'Y (RUS))))
;   =
;   (PLUS (TIMES A Z) (RUS)).

  (LET (FLG FORM TEST BODY)
    (COND ((VARIABLEP TERM) T)
          ((FQUOTEP TERM) T)
          ((ITERATE FOR ARG IN (FARGS TERM) ALWAYS (TAMEP ARG))
           (COND ((TOTALP (FFN-SYMB TERM)) T)
                 ((EQ *1*THM-MODE$ (QUOTE THM)) NIL)
                 ((OR (MATCH TERM (V&C$ (LIST (QUOTE QUOTE) FLG)
                                        (LIST (QUOTE QUOTE) FORM)
                                        &))
                      (MATCH TERM (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                         (LIST (QUOTE QUOTE) FORM)
                                         &)))
                  (COND ((EQ FLG (QUOTE LIST))
                         (AND (TERMP-LIST FORM)
                              (TAMEP-LIST FORM)))
                        (T (AND (TERMP FORM)
                                (TAMEP FORM)))))
                 ((MATCH TERM (FOR & & (LIST (QUOTE QUOTE) TEST)
                                   & (LIST (QUOTE QUOTE) BODY) &))
                  (AND (TERMP TEST)
                       (TAMEP TEST)
                       (TERMP BODY)
                       (TAMEP BODY)))
                 (T NIL)))
          (T NIL))))

(DEFUN TAMEP-LIST (X)

;   X is a proper list of terms and we check that each element is TAMEP.

  (ITERATE FOR TERM IN X ALWAYS (TAMEP TERM)))


(DEFUN TERM-ORDER (TERM1 TERM2)

;   A simple -- or complete or total -- ordering is a relation satisfying:
;   "antisymmetric" XrY & YrX -> X=Y, "transitive" XrY & Y&Z -> XrZ, and
;   "trichotomy" XrY v YrX.  A partial order weakens trichotomy to "reflexive"
;   XrX.

;   TERM-ORDER is a simple ordering on terms.  If exactly one of the
;   two is a quoted evg then that one is the smaller.  Otherwise,
;   (TERM-ORDER TERM1 TERM2) is t iff (a) the number of occurrences of
;   variables in TERM1 is strictly less than the number in TERM2, or
;   (b) the numbers of variable occurrences are equal and the
;   FORM-COUNT of TERM1 is strictly less than that of TERM2, or (c)
;   the numbers of variable occurrences are equal, the FORM-COUNTS are
;   equal, and (LEXORDER TERM1 TERM2).

;   Let (STRICT-TERM-ORDER X Y) be the LISP function defined as (AND
;   (TERM-ORDER X Y) (NOT (EQUAL X Y))).  For a fixed, finite set of function
;   symbols and variable symbols STRICT-TERM-ORDER is well founded, as can be
;   proved with the following lemma.

;   Lemma.  Suppose that M is a function whose range is well ordered by r and
;   such that the inverse image of any member of the range is finite.  Suppose
;   that L is a total order.  Define (LESSP x y) = (OR (r (M x) (M y)) (AND
;   (EQUAL (M x) (M y)) (L x y) (NOT (EQUAL x y)))). < is a well-ordering.
;   Proof.  Suppose ... < t3 < t2 < t1 is an infinite descending sequence. ...,
;   (M t3), (M t2), (M t1) is weakly descending but not infinitely descending
;   and so has a least element.  WLOG assume ... = (M t3) = (M t2) = (M t1).
;   By the finiteness of the inverse image of (M t1), { ..., t3, t2, t1} is a
;   finite set, which has a least element under L, WLOG t27.  But t28 L t27 and
;   t28 /= t27 by t28 < t27, contradicting the minimality of t27.  QED

;   If (TERM-ORDER x y) and t2 results from replacing one occurrence of y with
;   x in t1, then (TERM-ORDER t2 t1).  Cases on why x is less than y.  1. If
;   the number of occurrences of variables in x is strictly smaller than in y,
;   then the number in t2 is strictly smaller than in t1.  2. If the number of
;   occurrences of variables in x is equal to the number in y but (FORM-COUNT
;   x) is smaller than (FORM-COUNT y), then the number of occurrences in t1 is
;   equal to the number in t2 but (FORM-COUNT t1) is less than (FORM-COUNT t2).
;   3. If the number of variable occurrences and parenthesis occurrences in x
;   and y are the same, then (LEXORDER x y).  (TERM-ORDER t2 t1) reduces to
;   (LEXORDER t2 t1) because the number of variable and parenthesis occurrences
;   in t2 and t1 are the same.  The lexicographic scan of t1 and t2 will be all
;   equals until x and y are hit.

  (LET (FORM-COUNT1 FORM-COUNT2 NUMBER-OF-VARIABLES1
                    NUMBER-OF-VARIABLES2)
    (SETQ FORM-COUNT1 (FORM-COUNT TERM1))
    (SETQ NUMBER-OF-VARIABLES1 NUMBER-OF-VARIABLES)
    (SETQ FORM-COUNT2 (FORM-COUNT TERM2))
    (SETQ NUMBER-OF-VARIABLES2 NUMBER-OF-VARIABLES)
    (COND ((AND (QUOTEP TERM1) (NOT (QUOTEP TERM2))) T)
          ((AND (NOT (QUOTEP TERM1)) (QUOTEP TERM2)) NIL)
          ((< NUMBER-OF-VARIABLES1 NUMBER-OF-VARIABLES2) T)
          ((< NUMBER-OF-VARIABLES2 NUMBER-OF-VARIABLES1) NIL)
          ((< FORM-COUNT1 FORM-COUNT2) T)
          ((< FORM-COUNT2 FORM-COUNT1) NIL)
          (T (LEXORDER TERM1 TERM2)))))

(DEFUN TERMINATION-MACHINE (FNNAME TERM TESTS)

;   This function builds a list of TESTS-AND-CASE representing the function
;   FNNAME with body TERM.  For each call of FNNAME in body, a TESTS-AND-CASE
;   is returned whose TESTS are all the tests that "rule" the call and whose
;   CASE is the arglist of the call.  If a rules b, then a governs b but not
;   vice versa.  For example, in (if (g (if a b c)) d e), a governs b but does
;   not rule b.  The reason for taking this weaker notion of governance is that
;   we can show easily that the TESTS-AND-CASEs are together sufficient to
;   imply the TESTS-AND-CASES generated by INDUCTION-MACHINE.

  (COND ((OR (VARIABLEP TERM) (FQUOTEP TERM)) NIL)
        ((EQ (FFN-SYMB TERM) (QUOTE IF))
         (NCONC (ITERATE FOR ARGLIST IN (ALL-ARGLISTS FNNAME (FARGN TERM 1))
                         COLLECT (MAKE TESTS-AND-CASE TESTS ARGLIST))
                (NCONC (TERMINATION-MACHINE FNNAME (FARGN TERM 2)
                                            (APPEND TESTS
                                                    (LIST (FARGN TERM 1))))
                       (TERMINATION-MACHINE
                        FNNAME
                        (FARGN TERM 3)
                        (APPEND TESTS (LIST (NEGATE-LIT (FARGN TERM 1))))))))
        (T (ITERATE FOR ARGLIST IN (ALL-ARGLISTS FNNAME TERM)
                    COLLECT (MAKE TESTS-AND-CASE TESTS ARGLIST)))))

(DEFUN TERMP (X)

;   X must be an evg.  This function returns T or F according to whether
;   X is a term in the internal representation.  That is, (TERMP x) = T
;   iff there exists a y such that x = (TRANSLATE y).  We define a related
;   concept, namely, that of a PSEUDO-TERMP, which is like TERMP except
;   does not require QUOTE normal form.

  (COND ((ATOM X)

;   The only atoms that are terms are SYMBOLPs.  The only evgs that are
;   SYMBOLPs are *1*T, *1*F, and LEGAL-NAMES.  TRANSLATE can return any
;   LEGAL-NAME except T, F, and NIL.

;   There is confusion in our minds over the question "Is NIL a term?"
;   Or, more precisely, is NIL a legal variable symbol?  TRANSLATE never
;   returns NIL but do we ever generate NIL as a variable symbol inside
;   of the theorem prover or permit the user's metafunctions to generate
;   NIL as a variable and hence turn our code loose on the term NIL?  We
;   think not.  The metafunction possibility is ruled out by the use of
;   TERMP to approve any output.  But the other possibility still lurks
;   in the backs of our minds.  ("Lurks" is too strong.  We regard this
;   possibility as exceedingly remote.)

;   Should it happen that NIL is a term, UNTRANSLATE can produce screwy
;   output.  For example, (UNTRANSLATE '(CAR NIL)) is '(CAR NIL) but the
;   translate of that is '(CAR 'NIL).

;   In DEFN0 where we store the BODY property of a fn defined with
;   (EVAL$ T (QUOTE b) a) we use the fact that b is not NIL:  ADD-SUB-FACT
;   does not permit NIL values.

;   A related comment:  NIL can be introduced as a variable only by a
;   piece of code that introduces new variables into the problem.  If such
;   a piece of code exists under REWRITE then it is a potential soundness
;   problem because of our use of FREE-VARS-IN-SIGHT.


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
;   fn is a fn symbol of arity n, each ai is a TERMP and fn is not
;   a constructor or bottom object unless some ai is unquoted.
           
         (AND (SYMBOLP (CAR X))
              (EQ (CDR (OUR-LAST X)) NIL)
              (NOT (MEMBER-EQ *1*SHELL-QUOTE-MARK X))
              (EQUAL (ARITY (CAR X)) (LENGTH (CDR X)))
              (ITERATE FOR ARG IN (CDR X) ALWAYS (TERMP ARG))
              (OR (AND (NOT (ASSOC-EQ (CAR X) SHELL-ALIST))
                       (NOT (MEMBER-EQ (CAR X) *1*BTM-OBJECTS)))
                  (NOT (ITERATE FOR ARG IN (CDR X)
                                ALWAYS
                                (AND (CONSP ARG)
                                     (EQ (CAR ARG) (QUOTE QUOTE))))))))))

(DEFUN TERMP-LIST (LST)

;   LST must be an evg.  This function returns T or F according to whether
;   LST is a proper list of TERMPs.

;   Intuitively we wish to map over LST and check TERMP of every element LST.
;   However, we must check that the final CDR is NIL.  In addition, even though
;   LST is an evg, not every element of LST is.  In particular, some element
;   might be *1*SHELL-QUOTE-MARK.  The CDR of of LST that starts with
;   *1*SHELL-QUOTE-MARK represents the final CDR of the list represented by the
;   'LST.

  (COND ((ATOM LST) (EQ LST NIL))
        ((EQ (CAR LST) *1*SHELL-QUOTE-MARK) NIL)
        (T (AND (TERMP (CAR LST))
                (TERMP-LIST (CDR LST))))))

(DEFUN THEORYP (NAME) 
  (OR (EQ NAME 'GROUND-ZERO)
      (AND (SYMBOLP NAME)
           (EQ (CAR (GET NAME (QUOTE EVENT))) (QUOTE DEFTHEORY)))))

(DEFUN TIME-IN-60THS ()
  (FLOOR (* 60 (/ (GET-INTERNAL-RUN-TIME)
                  INTERNAL-TIME-UNITS-PER-SECOND))))

(DEFUN TIME-LIMIT ()
  (AND TIME-LIMIT-IN-60THS
       (/ TIME-LIMIT-IN-60THS 60)))

(DEFUN TO-BE-IGNOREDP (POLY)
  (LET (LEMMAS LITS)
    (SETQ LEMMAS (ACCESS POLY LEMMAS POLY))
    (SETQ LITS (ACCESS POLY LITERALS POLY))
    (ITERATE FOR LIT IN LITS-TO-BE-IGNORED-BY-LINEAR
             THEREIS (OR (MEMBER-EQ LIT LEMMAS) (MEMBER-EQ LIT LITS)))))

(DEFUN TOO-MANY-IFS (ARGS VAL)

;   Let ARGS be the list of actuals to a nonrec fn.  Let VAL be the rewritten
;   body.  We wish to determine whether the expansion of the fn call introduces
;   too many IFs all at once.  Our motivation comes from an example like (M2
;   (ZTAK & & &) (ZTAK & & &) (ZTAK & & &)) where the careless opening up of
;   everybody produces a formula with several hundred IFs in it because of M2's
;   duplication of the IFs coming from the simplification of the ZTAKs.  My
;   first thought was to never expand a nonrec fn -- at the top level of the
;   clause -- if it had some IFs in its args and to wait till CLAUSIFY has
;   cleaned things up.  That slowed a proveall down by a factor of 2 -- and by
;   a factor of 13 in PRIME-LIST-TIMES-LIST -- because of the ridiculously slow
;   expansion of such basic nonrec fns as AND, OR, NOT, and NLISTP.  I have
;   been thinking about the problem and have thought of the following ideas.
;   None except the final one have been implemented or tested.

;   I thought of permitting the expansion if VAL had fewer IFs than ARGS but
;   that is obviously bad because it does not permit the fn to introduce any
;   IFs of its own, e.g., as in AND.  So I have decided to just prohibit the
;   duplication of IF-containing-args in VAL.  That is, I do not want to expand
;   the fn if the expansion causes the duplication of some arg containing an
;   IF.  Of course, it could be that an IF-containing-arg does not occur in VAL
;   only because it has been rewritten by some rewrite rule to some other term,
;   possibly containing even more IFs, but I have decided to ignore that and
;   blame that problem on the process that permitted the introduction of those
;   IFs.  So when I say an arg is duplicated in VAL I really mean the arg
;   literally OCCURs twice.  Then it occurred to me that if arg1 and arg2 both
;   contained IFs and arg1 was duplicated in VAL but arg2 did not occur at all,
;   then perhaps one should permit the expansion if the number of IFs in the
;   arg1 occurrences are less than the number in the arg1 plus arg2.  So that
;   is what I have implemented.

;   This function computes (> (ITERATE FOR ARG IN ARGS SUM (*
;   (COUNT-IFS ARG) (OCCUR-CNT ARG VAL))) (ITERATE FOR ARG IN ARGS SUM
;   (COUNT-IFS ARG))) but does it slightly more efficiently by
;   observing that if no IFs occur in any arg then there is no point
;   in doing the OCCUR-CNTs and that once the left hand side has been
;   pushed beyond the right there is no point in continuing.

  (LET (RHS LHS)
    (SETQ RHS (ITERATE FOR ARG IN ARGS SUM (COUNT-IFS ARG)))
    (SETQ LHS 0)
    (COND ((ZEROP RHS) NIL)
          (T (ITERATE FOR ARG IN ARGS
                      WHEN (NOT (ZEROP (SETQ TEMP-TEMP (COUNT-IFS ARG))))
                      THEREIS

;   The WHEN clause above just takes advantage of the fact that if X is 0 then
;   X*Y is 0 and Y need not be computed.

                      (>
                       (SETQ LHS
                             (+ (* TEMP-TEMP (OCCUR-CNT ARG VAL)) LHS))
                       RHS))))))

(DEFUN TOP-FNNAME (CONCL)
  (OR (MATCH CONCL (NOT CONCL))
      (MATCH CONCL (EQUAL CONCL &))
      (MATCH CONCL (IFF CONCL &)))
  (COND ((VARIABLEP CONCL) NIL)
        (T (FN-SYMB CONCL))))

(DEFUN TRANSITIVE-CLOSURE (SET PRED)

;   Compares all pairs x,y of distinct occurrences of from the bag SET with
;   (PRED x y) and if PRED returns non-NIL, x and y are removed from SET and
;   the result of PRED is inserted.  This operation is repeated until no
;   changes occur.  CAUTION:  It must be the case that (PRED x y) = (PRED y x).

  (LET (ALIVE NEW RESULT)
    (SETQ ALIVE (ITERATE FOR X IN SET COLLECT (CONS X T)))
    (SETQ NEW (COPY-LIST ALIVE))
    (ITERATE WHILE NEW
             UNLESS
             (AND (CDR (CAR NEW))
                  (ITERATE FOR TAIL ON ALIVE
                           WHEN
                           (PROG NIL
                                 LOOP (COND ((NULL (CDR (CAR TAIL)))
                                             (COND ((NULL (CDR TAIL))
                                                    (RETURN NIL))
                                                   (T (RPLACA TAIL (CADR TAIL))
                                                      (RPLACD TAIL (CDDR TAIL))
                                                      (GO LOOP)))))
                                 (RETURN (COND ((EQ (CAR TAIL) (CAR NEW)) NIL)
                                               ((SETQ RESULT
                                                      (FUNCALL
                                                       PRED
                                                       (CAR (CAR TAIL))
                                                       (CAR (CAR NEW))))
                                                (SETQ RESULT (CONS RESULT T))
                                                (RPLACD (CAR TAIL) NIL)
                                                (RPLACA TAIL RESULT)
                                                (RPLACD (CAR NEW) NIL)
                                                (RPLACA NEW RESULT)
                                                T)
                                               (T NIL))))
                           DO (RETURN TAIL)))
             DO (SETQ NEW (CDR NEW)))
    (ITERATE FOR PAIR IN ALIVE
             WHEN (CDR PAIR) COLLECT (CAR PAIR))))

(DEFUN TRANSLATE (X)

;   TRANSLATE may be given any noncircular lisp object -- unlike almost all of
;   the other functions in the system, which expect terms or evgs.  TRANSLATE
;   either causes an error or returns a term.  TRANSLATE is intimately
;   connected with the functions TERMP and UNTRANSLATE.  The former recognizes
;   the output of TRANSLATE; the latter inverts output to acceptable input.

  (COND
   ((ATOM X)
    (COND ((INTEGERP X) (LIST (QUOTE QUOTE) X))
          ((SYMBOLP X)
           (COND ((EQ X T) TRUE)
                 ((EQ X (QUOTE F)) FALSE)
                 ((EQ X NIL) (QUOTE (QUOTE NIL)))
                 ((ILLEGAL-NAME X)
                  (ER SOFT (X) (!PPR X NIL) |is| |an| |illegal| |variable|
                      |name| |.|))
                 (T X)))
          (T (ER SOFT (X) |unrecognized| |syntax:| (!PPR X (QUOTE |.|))))))
   ((CDR (OUR-LAST X))
    (ER SOFT (X) |contrary| |to| |the| |rules| |of| |well-formedness| |,| |the|
        |last| CDR |of| (!PPR X NIL) |is| |non-NIL| |.|))
   ((NOT (SYMBOLP (CAR X)))
    (ER SOFT (X) |a| |function| |symbol| |must| |be| |a| |Lisp| SYMBOLP |,|
        |but| (!PPR (CAR X) NIL) |is| |not| EXCL))
   ((NOT (OK-SYMBOLP (CAR X)))
    (ER SOFT (X) (!PPR (CAR X) NIL) |is| |not| |interned| |in| |the| |right|
        |places| EXCL))
   ((PROPERTYLESS-SYMBOLP (CAR X))
    (COND ((EQ (CAR X) (QUOTE QUOTE))
           (COND ((NOT (INT= 1 (LENGTH (CDR X))))
                  (ER SOFT (X) QUOTE |must| |be| |given| |exactly| |one|
                      |argument| |.| |In| (!PPR X NIL) |it| |is| |given| |the|
                      |wrong| |number| |of| |arguments| |.|))
                 ((NOT (EVG (CADR X)))
                  (ER SOFT (X) |the| |object| |QUOTEd| |in| |the| |expression|
                      (!PPR X NIL) |does| |not| |represent| |an| |explicit|
                      |value| |term| |.|))
                 (T X)))
          ((MEMBER-EQ (CAR X) (QUOTE (NIL T F)))
           (ER SOFT (X) (!PPR (CAR X) NIL) |is| |an| |illegal| |function|
               |symbol| |.|))
          ((EQ (CAR X) (QUOTE LET))
           (COND ((NOT (INT= 2 (LENGTH (CDR X))))
                  (ER SOFT (X) LET |must| |be| |given| |exactly| |two|
                      |arguments| |.| |In| (!PPR X NIL) |it| |is| |given|
                      |the| |wrong| |number| |of| |arguments| |.|))
                 ((OR (AND (CADR X) (ATOM (CADR X)))
                      (CDR (OUR-LAST (CADR X)))
                      (NOT (ITERATE FOR PAIR IN (CADR X)
                                    ALWAYS
                                    (AND (CONSP PAIR)
                                         (NULL (CDR (OUR-LAST PAIR)))
                                         (INT= 2 (LENGTH PAIR)))))
                      (NOT (NO-DUPLICATESP (ITERATE FOR PAIR IN (CADR X)
                                                    COLLECT (CAR PAIR)))))
                  (ER SOFT (X) |The| |first| |argument| |of| |a| LET |must|
                      |be| |a| |proper| |list| |of| |doublets| |,| |i.e.,|
                      |lists| |of| |the| |form| |(var term),| |in| |which|
                      |no| |var| |occurs| |twice| |.|  (!PPR X NIL) |is|
                      |illegal| |.|))
                 (T (SUBLIS-VAR
                     (ITERATE FOR PAIR IN (CADR X)
                              COLLECT
                              (COND ((NOT (VARIABLEP (TRANSLATE (CAR PAIR))))
                                     (ER SOFT ((VAR (CAR PAIR))
                                               X)
                                         |In| |the| |first| |argument| |to|
                                         |the| LET |statement| (!PPR X NIL)
                                         |there| |is| |an| |attempt| |to|
                                         |bind| |the| |non-variable|
                                         (!PPR VAR '|.|)))
                                    (T (CONS (CAR PAIR)
                                             (TRANSLATE (CADR PAIR))))))
                                (TRANSLATE (CADDR X))))))
          ((EQ (CAR X) (QUOTE CASE))
           (COND ((NOT (AND (>= (LENGTH (CDR X)) 2)
                            (ITERATE FOR PAIR IN (CDDR X)
                                     ALWAYS
                                     (AND (CONSP PAIR)
                                          (NULL (CDR (OUR-LAST PAIR)))
                                          (INT= (LENGTH PAIR) 2)))
                            (EQ (CAAR (OUR-LAST (CDR X))) 'OTHERWISE)
                            (ITERATE FOR TL ON (CDDR X) UNTIL (NULL (CDR TL))
                                     NEVER (EQ (CAAR TL) 'OTHERWISE))))
                  (ER SOFT (X) |The| CASE |expression| |must| |have| |at|
                      |least| |two| |arguments,| |all| |but| |the| |first|
                      |must| |be| |proper| |lists| |of| |length| |two,|
                      |the| |last| |must| |start| |with| |the|
                      |symbol| |OTHERWISE,| |and| |none| |but| |the|
                      |last| |may| |start| |with| |that| |symbol| |.| |These|
                      |rules| |are| |violated| |in| (!PPR X '|.|))))
           (FIX-CASE (TRANSLATE (CADR X))
                     (ITERATE FOR PAIR IN (CDDR X)
                              COLLECT
                              (COND ((EQ (CAR PAIR) 'OTHERWISE)
                                     (CONS 'OTHERWISE (TRANSLATE (CADR PAIR))))
                                    (T (CONS (TRANSLATE (LIST 'QUOTE
                                                              (CAR PAIR)))
                                             (TRANSLATE (CADR PAIR))))))))
          ((EQ (CAR X) (QUOTE COND))
           (COND ((NOT (AND (>= (LENGTH (CDR X)) 1)
                            (ITERATE FOR PAIR IN (CDR X)
                                     ALWAYS
                                     (AND (CONSP PAIR)
                                          (NULL (CDR (OUR-LAST PAIR)))
                                          (INT= (LENGTH PAIR) 2)))
                            (EQ (CAAR (OUR-LAST (CDR X))) 'T)
                            (ITERATE FOR TL ON (CDR X) UNTIL (NULL (CDR TL))
                                     NEVER (EQ (CAAR TL) 'T))))
                  (ER SOFT (X) |The| COND |expression| |must| |have| |at|
                      |least| |one| |argument,| |all|
                      |must| |be| |proper| |lists| |of| |length| |two,|
                      |the| |last| |must| |start| |with| |the|
                      |symbol| |T,| |and| |none| |but| |the|
                      |last| |may| |start| |with| |that| |symbol| |.| |These|
                      |rules| |are| |violated| |in| (!PPR X '|.|))))
           (FIX-COND (ITERATE FOR PAIR IN (CDR X)
                              COLLECT
                              (CONS (TRANSLATE (CAR PAIR))
                                    (TRANSLATE (CADR PAIR))))))
                           
          ((EQ (CAR X) (QUOTE LIST))
           (COND ((NULL (CDR X)) (TRANSLATE NIL))
                 (T (XXXJOIN (QUOTE CONS)
                             (NCONC1 (ITERATE FOR ARG IN (CDR X)
                                              COLLECT (TRANSLATE ARG))
                                     (TRANSLATE NIL))))))
          ((EQ (CAR X) (QUOTE LIST*))
           (COND ((NULL (CDR X))
                  (ER SOFT NIL |LIST*| |requires| |at| |least| |one|
                      |argument| |.|))
                 ((NULL (CDDR X))
                  (TRANSLATE (CADR X)))
                 (T (XXXJOIN (QUOTE CONS)
                             (ITERATE FOR ARG IN (CDR X)
                                      COLLECT (TRANSLATE ARG))))))
          ((CAR-CDRP (CAR X))
           (COND ((INT= 1 (LENGTH (CDR X)))
                  (FIXCAR-CDR (LIST (CAR X) (TRANSLATE (CADR X)))))
                 (T (ER SOFT (X) (!PPR (CAR X) NIL) |is| |a| |reserved|
                        |abbreviation| |for| |a| CAR-CDR |nest| |and| |must|
                        |be| |given| |exactly| |one| |argument| |.|))))
          ((ASSOC-EQ (CAR X) *EXTRA-PROPERTYLESS-SYMBOLS-ALIST*)
           (ERROR1 (CONS 'PROGN
                         (CDR (ASSOC-EQ (CAR X)
                                        *EXTRA-PROPERTYLESS-SYMBOLS-ALIST*)))
                   (LIST (CONS 'X X))
                   'SOFT))
          (T (ER HARD (X) PROPERTYLESS-SYMBOLP |and| TRANSLATE |do| |not|
                 |agree| |on| (!PPR (CAR X) (QUOTE |.|))))))
   ((NULL (ARITY (CAR X)))
    (COND (IN-BOOT-STRAP-FLG
           (ER WARNING (X) (!PPR (CAR X) NIL) |has| |been| |encountered| |as|
               |an| |undefined| |function| |by| TRANSLATE |.| |You| |should|
               |add| |it| |to| |the| |binding| |of| ARITY-ALIST |in| BOOT-STRAP
               |if| |you| |wish| |to| |suppress| |this| |message| EXCL))
          (T (ER SOFT (X) |the| |function| (!PPR (CAR X) NIL) |is| |unknown|
                 |.| |Please| |delete| |all| |references| |to| |it| |,|
                 |define| |it| |or| |declare| |it| |as| |an| |undefined|
                 |function| |.|))))
   ((MEMBER-EQ (CAR X) (QUOTE (AND OR PLUS TIMES)))
    (COND ((<= 2 (LENGTH (CDR X)))
           (XXXJOIN (CAR X) (ITERATE FOR ARG IN (CDR X)
                                     COLLECT (TRANSLATE ARG))))
          (T (ER SOFT (X) |the| |function| |symbol| (!PPR (CAR X) NIL) |must|
                 |be| |given| |at| |least| |two| |arguments| |.| (!PPR x nil)
                 |is| |illegal| |.|))))
   ((AND (EQ *1*THM-MODE$ (QUOTE NQTHM))
         (OR (MATCH X (FOR & (QUOTE IN) & (QUOTE WHEN) & & &))
             (MATCH X (FOR & (QUOTE IN) & & &))))
    (LET (V C R O B)
      (COND ((NOT (MATCH X (FOR V (QUOTE IN) R (QUOTE WHEN) C O B)))
             (SETQ C T) (MATCH X (FOR V (QUOTE IN) R O B))))
      (OR (AND (SYMBOLP V) (EQ V (TRANSLATE V)))
          (ER SOFT (V) FOR |didn't| |like| (!PPR V NIL) |as| |its| |first|
              |argument| |.|))
      (OR (MEMBER-EQ O FOR-OPS)
          (ER SOFT (FOR-OPS O) |A| |quantifier| |operation| |must| |be| |one|
              |of| (!PPR-LIST FOR-OPS (QUOTE  |.|))  (!PPR O NIL)
              |is| |not| |.|))
      (FCONS-TERM (QUOTE FOR)
                  (LIST (KWOTE V)
                        (TRANSLATE R)
                        (KWOTE (SETQ C (TRANSLATE C)))
                        (KWOTE O)
                        (KWOTE (SETQ B (TRANSLATE B)))
                        (MAKE-ALIST V C B)))))
   ((NOT (INT= (LENGTH (CDR X)) (ARITY (CAR X))))
    (ER SOFT (X (N (ARITY (CAR X)))) |the| |function| |symbol|
        (!PPR (CAR X) NIL) |takes| |exactly| (@ N)
        (PLURAL? N |arguments| |argument|) |.| |In| (!PPR X NIL) |it| |is|
        |given| |the| |wrong| |number| |of| |arguments| |.|))
   ((MEMBER-EQ (CAR X) BOOT-STRAP-MACRO-FNS)
    (SUB-PAIR-VAR (CADR (GET (CAR X) (QUOTE SDEFN)))
                  (ITERATE FOR ARG IN (CDR X) COLLECT (TRANSLATE ARG))
                  (CADDR (GET (CAR X) (QUOTE SDEFN)))))
   (T (CONS-TERM (CAR X)
                 (ITERATE FOR ARG IN (CDR X) COLLECT (TRANSLATE ARG))))))

(DEFUN TRANSLATE-AND-CHK (X)

;   This function is equivalent to TRANSLATE but comments upon the
;   the translated text before returning it.

  (SETQ X (TRANSLATE X))
  (QUOTATIONS-CHK X)
  X)

(DEFUN TRANSLATE-TO-LISP (X)
  (SETQ ALL-LEMMAS-USED NIL)
  (PRETTYIFY-LISP (OPTIMIZE-COMMON-SUBTERMS
                   (ONEIFY (ELIMINATE-SOME-EVAL$S X) NIL))))

(DEFUN TREE-DEPENDENTS (NAME)
  (CONS NAME (ITERATE FOR X IN (GET NAME (QUOTE IMMEDIATE-DEPENDENTS0))
                      WITH ITERATE-ANS
                      DO (SETQ ITERATE-ANS
                               (UNION-EQ (TREE-DEPENDENTS X) ITERATE-ANS))
                      FINALLY (RETURN ITERATE-ANS))))

(DEFUN TRIVIAL-POLYP (POLY)
  (OR (TRIVIAL-POLYP1 POLY (QUOTE POSITIVE))
      (TRIVIAL-POLYP1 POLY (QUOTE NEGATIVE))))

(DEFUN TRIVIAL-POLYP1 (POLY PARITY)
  (PROG (WINNING-PAIR COEF)
        (COND ((EQ PARITY (QUOTE POSITIVE))
               (COND ((AND (> 1 (ACCESS POLY CONSTANT POLY))
                           (INT= 1 (ITERATE FOR PAIR IN (ACCESS POLY ALIST
                                                                POLY)
                                            COUNT (> (CDR PAIR) 0))))
                      (SETQ WINNING-PAIR
                            (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                                     WHEN (> (CDR PAIR) 0)
                                     DO (RETURN PAIR)))
                      (SETQ COEF (CDR WINNING-PAIR)))
                     (T (RETURN NIL))))
              ((AND (> (ACCESS POLY CONSTANT POLY) -1)
                    (INT= 1 (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                                     COUNT (< (CDR PAIR) 0))))
               (SETQ WINNING-PAIR (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                                           WHEN (< (CDR PAIR) 0)
                                           DO (RETURN PAIR)))
               (SETQ COEF (- (CDR WINNING-PAIR))))
              (T (RETURN NIL)))
        (COND ((AND (NOT (MATCH (ACCESS POLY LITERALS POLY)
                                (LIST (NOT (EQUAL & &)))))
                    (EQUAL 0 (OUR-REMAINDER (ACCESS POLY CONSTANT POLY) COEF))
                    (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                             ALWAYS (EQUAL 0 (OUR-REMAINDER (CDR PAIR) COEF))))

;   We know that the polys in this pot list were formed from the current CL
;   with the ADD-TERMS-TO-POT-LST FLG=NIL.  That is, the literals of the clause
;   were stored by LINEARIZE with their original parities, even though the poly
;   was generated from their negations.

               (RETURN (CONS (CONS (CAR WINNING-PAIR)
                                   (COND ((EQ PARITY (QUOTE POSITIVE)) 1)
                                         (T -1)))
                             (MAKE POLY (OUR-QUOTIENT (ACCESS POLY
                                                              CONSTANT POLY)
                                                      COEF)
                                   (ITERATE
                                    FOR PAIR IN (ACCESS POLY ALIST POLY)
                                    COLLECT
                                    (CONS (CAR PAIR)
                                          (OUR-QUOTIENT (CDR PAIR) COEF)))
                                   (ACCESS POLY ASSUMPTIONS POLY)
                                   (ACCESS POLY LITERALS POLY)
                                   (ACCESS POLY LEMMAS POLY)))))
              (T (RETURN NIL)))))

(DEFUN TRUE-POLYP (POLY)
  (AND (<= (ACCESS POLY CONSTANT POLY)
           0)
       (ITERATE FOR PAIR IN (ACCESS POLY ALIST POLY)
                ALWAYS (<= (CDR PAIR) 0))))

(DEFUN TYPE-ALIST-CLAUSE (CL)
  (LET ((TYPE-ALIST TYPE-ALIST))
    (ITERATE FOR LIT IN CL
             WHILE (NOT (EQ TYPE-ALIST (QUOTE CONTRADICTION))) DO
             (PROGN (SMART-ASSUME-TRUE-FALSE LIT)
                    (COND (MUST-BE-TRUE
                           (SETQ TYPE-ALIST (QUOTE CONTRADICTION)))
                          (MUST-BE-FALSE NIL)
                          (T (SETQ TYPE-ALIST FALSE-TYPE-ALIST)))))
    TYPE-ALIST))

(DEFUN TYPE-PRESCRIPTION-LEMMAP (NAME)
  (LET (ATM)
    (COND ((ITERATE FOR TUPLE IN (GET NAME (QUOTE LOCAL-UNDO-TUPLES))
                    THEREIS (MATCH TUPLE
                                   (CONS (QUOTE TYPE-PRESCRIPTION-LST)
                                         (CONS ATM &))))
           ATM)
          (T NIL))))

(DEFUN TYPE-SET (TERM)
  (LET (PAIR TYPE-ARG1 TYPE-ARG2 ARG1 ARG2)
    (COND ((SETQ TEMP-TEMP (ASSOC-EQUAL TERM TYPE-ALIST))
           (CDR TEMP-TEMP))
          ((VARIABLEP TERM)
           TYPE-SET-UNKNOWN)
          ((FQUOTEP TERM)
           (CAR (TYPE-PRESCRIPTION (FN-SYMB0 (CADR TERM)))))
          ((SETQ PAIR (ASSOC-EQ (FFN-SYMB TERM)
                                RECOGNIZER-ALIST))
           (SETQ TYPE-ARG1 (TYPE-SET (FARGN TERM 1)))
           (COND ((TS= 0 (TSLOGAND TYPE-ARG1 (CDR PAIR)))
                  TYPE-SET-FALSE)
                 ((TSLOGSUBSETP TYPE-ARG1 (CDR PAIR))
                  TYPE-SET-TRUE)
                 (T TYPE-SET-BOOLEAN)))
          ((MATCH TERM (EQUAL ARG1 ARG2))
           (SETQ TYPE-ARG1 (TYPE-SET ARG1))
           (SETQ TYPE-ARG2 (TYPE-SET ARG2))
           (COND ((TS= 0 (TSLOGAND TYPE-ARG1 TYPE-ARG2))
                  TYPE-SET-FALSE)
                 ((AND (TS= TYPE-ARG1 TYPE-ARG2)
                       (MEMBER-EQUAL TYPE-ARG1 SINGLETON-TYPE-SETS))
                  TYPE-SET-TRUE)
                 (T TYPE-SET-BOOLEAN)))
          ((MATCH TERM (NOT ARG1))
           (SETQ TYPE-ARG1 (TYPE-SET ARG1))
           (COND ((TS= TYPE-ARG1 TYPE-SET-FALSE)
                  TYPE-SET-TRUE)
                 ((NOT (TSLOGSUBSETP TYPE-SET-FALSE TYPE-ARG1))
                  TYPE-SET-FALSE)
                 (T TYPE-SET-BOOLEAN)))
          ((EQ (FFN-SYMB TERM)
               (QUOTE IF))
           (ASSUME-TRUE-FALSE (FARGN TERM 1))
           (COND (MUST-BE-TRUE (TYPE-SET (FARGN TERM 2)))
                 (MUST-BE-FALSE (TYPE-SET (FARGN TERM 3)))
                 (T (TSLOGIOR (TYPE-SET2 (FARGN TERM 2)
                                         TRUE-TYPE-ALIST)
                              (TYPE-SET2 (FARGN TERM 3)
                                         FALSE-TYPE-ALIST)))))
          ((SETQ TEMP-TEMP (TYPE-PRESCRIPTION
                            (FFN-SYMB TERM)))
           (LET ((TEMP (CAR TEMP-TEMP)))
             (TSLOGIOR TEMP
                       (ITERATE FOR ARG IN (FARGS TERM) AS FLG
                                IN (CDR TEMP-TEMP)
                                WITH ITERATE-ANS = 0
                                WHEN FLG
                                DO
                                (SETQ ITERATE-ANS
                                      (TSLOGIOR ITERATE-ANS
                                                (TYPE-SET ARG)))
                                FINALLY (RETURN ITERATE-ANS)))))
          (T TYPE-SET-UNKNOWN))))

(DEFUN TYPE-SET2 (TERM TYPE-ALIST)

;   This is like TYPE-SET, only it lets you specify the local TYPE-ALIST and
;   protects the FALSE-TYPE-ALIST for you.

  (LET (FALSE-TYPE-ALIST) (TYPE-SET TERM)))

(DEFUN TYPE-SET-TERMP (TERM)

;   A type set term is a term of the form (OR (r1 a) ... (rn a)) or
;   of the form (AND (NOT (r1 a)) ... (NOT (rn a))), where each ri is
;   a recognizer and a is any term.  If TERM is a type set term, we
;   return a pair <a, type-set>, where type-set is the bit mask
;   corresponding to the type set of a described by the term.  Otherwise,
;   we return NIL.

  (LET (LST) 
    (COND ((AND (ITERATE FOR X IN (SETQ LST (FLATTEN-TERM TERM (QUOTE OR)))
                         ALWAYS (RECOGNIZER-TERMP X))
                (ITERATE FOR X IN (CDR LST)
                         WITH A = (FARGN (CAR LST) 1)
                         ALWAYS (EQUAL A (FARGN X 1))))
           (CONS (FARGN (CAR LST) 1)
                 (ITERATE FOR X IN LST WITH ITERATE-ANS = 0
                          DO 
                          (SETQ ITERATE-ANS (TSLOGIOR ITERATE-ANS
                                                      (RECOGNIZER-TERMP X)))
                          FINALLY (RETURN ITERATE-ANS))))
          ((AND (ITERATE FOR X IN (SETQ LST (FLATTEN-TERM TERM (QUOTE AND)))
                         ALWAYS (AND (MATCH X (NOT X))
                                     (RECOGNIZER-TERMP X)))
                (ITERATE FOR X IN (CDR LST)
                         WITH A = (FARGN (FARGN (CAR LST) 1) 1)
                         ALWAYS (EQUAL A (FARGN (FARGN X 1) 1))))
           (CONS (FARGN (FARGN (CAR LST) 1) 1)
                 (ITERATE FOR X IN LST WITH ITERATE-ANS = -1
                          DO
                          (SETQ ITERATE-ANS (TSLOGAND ITERATE-ANS
                                                      (TSLOGNOT
                                                       (RECOGNIZER-TERMP
                                                        (FARGN X 1)))))
                          FINALLY (RETURN ITERATE-ANS))))
          (T NIL))))

(DEFUN UGLYP (EVG)
 
;   Answers the question:  Does the representation of EVG have
;   *1*'s in it?
 
  (COND ((ATOM EVG)
         (OR (EQ EVG *1*T)
             (EQ EVG *1*F)))
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK)
         T)
        (T (OR (UGLYP (CAR EVG))
               (UGLYP (CDR EVG))))))

(DEFUN UNBREAK-LEMMA (&OPTIONAL NAME)
  (COND ((NULL NAME)
         (SETQ BROKEN-LEMMAS NIL))
        ((MEMBER-EQ NAME BROKEN-LEMMAS)
         (SETQ BROKEN-LEMMAS
               (REMOVE1 NAME BROKEN-LEMMAS))))
  (COND ((AND (NULL BROKEN-LEMMAS)
              REWRITE-PATH-STK-PTR)
         (ER WARNING NIL |No| |lemmas| |remain| |broken| |.|
             |However| |,| |rewrite| |path| |maintenance|
             |is| |still| |enabled| |.| |To| |disable| |it|
             |execute| (!PPR '(MAINTAIN-REWRITE-PATH NIL) '|.|))))
  NAME)

(DEFUN UNCHANGING-VARS (TERM)
  (LET (ANS)
    (UNCHANGING-VARS1 (EXPAND-NON-REC-FNS TERM))
    ANS))

(DEFUN UNCHANGING-VARS1 (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM) DO (UNCHANGING-VARS1 ARG))
           (COND ((OR (MEMBER-EQ (FFN-SYMB TERM) *1*BTM-OBJECTS)
                      (ASSOC-EQ (FFN-SYMB TERM) RECOGNIZER-ALIST)
                      (ITERATE FOR X IN SHELL-POCKETS
                               THEREIS (MEMBER-EQ (FFN-SYMB TERM) X))
                      (MEMBER-EQ (FFN-SYMB TERM) (QUOTE (IF EQUAL))))
                  NIL)
                 ((AND (GET (FFN-SYMB TERM) (QUOTE SDEFN))
                       (NOT (DISABLEDP (FFN-SYMB TERM))))
                  NIL)
                 (T (ITERATE FOR ARG IN (FARGS TERM) WHEN (VARIABLEP ARG)
                             DO (SETQ ANS (ADD-TO-SET ARG ANS))))))))

(DEFUN UNDO-BACK-THROUGH (NAME)
  (CHK-COMMAND-STATUS NIL)
  (LET ((COMMAND-STATUS-FLG T))
       (UNDO-BACK-THROUGH-FN NAME)))

(DEFUN UNDO-BACK-THROUGH-FN (NAME)
  (COND ((OR (NOT (SYMBOLP NAME))
             (NOT (GET NAME (QUOTE EVENT))))
         (ER SOFT (NAME) |Attempt| |to| |undo| |a| |nonevent| |,|
             (!PPR NAME (QUOTE |.|))))
        (T (NREVERSE (ITERATE WHILE (AND (BOUNDP (QUOTE CHRONOLOGY))
                                         (MEMBER-EQ NAME CHRONOLOGY))
                              APPEND (UNDO-NAME-FN (CAR CHRONOLOGY)))))))

(DEFUN UNDO-NAME (NAME)
  (CHK-COMMAND-STATUS NIL)
  (LET ((COMMAND-STATUS-FLG T))
       (UNDO-NAME-FN NAME)))

(DEFUN UNDO-NAME-FN (NAME)

;   This function is difficult to implement correctly because one does
;   not want to slow down things like TYPE-SET.  To our disgust, we
;   discovered several years after we wrote the meta-paper that F
;   could be proved by undoing a function definition and redefining
;   it with a different number of args.  We have decided to abandon
;   any pretense that undoing (except undoing back through) is sound;
;   we leave it only for convenience.  If we ever try to do this
;   right, we must visit SUBRP, BODY, FORMALS, not to mention the
;   places where we rewrite EVALs, FORs, etc.

  (LET (EVENTS)
    (COND ((OR (NOT (SYMBOLP NAME))
               (NOT (GET NAME (QUOTE EVENT))))
           (ER SOFT (NAME) |Attempt| |to| |undo| |a| |nonevent| |,|
               (!PPR NAME (QUOTE |.|))))
          ((EQ NAME (QUOTE GROUND-ZERO))
           (SETQ EVENTS (NREVERSE (ITERATE FOR X IN CHRONOLOGY
                                           COLLECT (GET X (QUOTE EVENT)))))
           (KILL-LIB)
           EVENTS)
          (T (SETQ EVENTS (REVERSE (DEPENDENTS-OF NAME)))
             (COND ((AND (NOT (EQ NAME (CAR CHRONOLOGY)))
                         (NOT *THM-SUPPRESS-UNDO-NAME-WARNING-FLG*)
                         (ER WARNING NIL |Undoing| |events| |except| |in|
                             |reverse| |order| |,| |i.e.,| |most| |recent|
                             |first| |,| |is| |dangerous| |because| |not|
                             |all| |dependencies| |are| |correctly|
                             |tracked| |.| |it| |is| |possible| |to|
                             |derive| |inconsistencies| |by| |appropriate|
                             |use| |of| |UNDO-NAME| |.| |use| |it| |at| |your|
                             |own| |risk| |.|  |to| |suppress| |repetition|
                             |of| |this| |message|
                             (!PPR
                              '(SETQ *THM-SUPPRESS-UNDO-NAME-WARNING-FLG* T)
                              '|.|)))))
             (NREVERSE
              (ITERATE FOR X IN EVENTS COLLECT
                       (PROG1 (GET X (QUOTE EVENT)) (KILL-EVENT X))))))))

(DEFUN UNION-EQ (X Y)
  (NCONC (ITERATE FOR X1 IN X UNLESS (MEMBER-EQ X1 Y) COLLECT X1) Y))

(DEFUN UNION-EQUAL (X Y)

;   When we moved to the 3600 we replaced calls of INTERLISP's UNION -- which
;   uses EQUAL -- with our own UNION-EQUAL because Zetalisp's UNION uses EQ.
;   Some calls of INTERLISP's UNION were allowed to remain UNIONs because we
;   could convince ourselves that only atoms were involved.  However, on
;   questionable cases we went ahead and used UNION-EQUAL.  Thus, some calls of
;   UNION-EQUAL could be replaced by UNION.  The main place is when dealing
;   with lemmas used, where inside the simpblock we permit listp names.  Seeing
;   a call of UNION-EQUAL in such a situation is not to be taken as a claim
;   that listp names are present; we just didn't trace it out.

  (NCONC (ITERATE FOR Z IN X UNLESS (MEMBER-EQUAL Z Y) COLLECT Z) Y))

(DEFUN UNPRETTYIFY (TERM)

;   This function returns a list of pairs (hyps . concl) such that the
;   conjunction of all (IMPLIES hyps concl) is equivalent to TERM.  hyps is a
;   list of hypotheses, implicitly conjoined.  concl does not begin with an AND
;   or IMPLIES.

  (LET (C1 C2 HYP CONCL)
    (COND ((MATCH TERM (AND C1 C2))
           (APPEND (UNPRETTYIFY C1) (UNPRETTYIFY C2)))
          ((MATCH TERM (IMPLIES HYP CONCL))
           (SETQ HYP (FLATTEN-ANDS-IN-LIT HYP))
           (ITERATE FOR PAIR IN (UNPRETTYIFY CONCL)
                    COLLECT (CONS (APPEND HYP (CAR PAIR)) (CDR PAIR))))
          (T (LIST (CONS NIL TERM))))))

(DEFUN UNSTABLE-SORT (X Y) 
  (OUR-STABLE-SORT (REVERSE X) Y))

(DEFUN UNTRANSLATE (TERM)
  
;   Copies TERM, introducing abbreviations.  That is,
;   (TRANSLATE (UNTRANSLATE TERM)) = TERM.
  
  (COND ((VARIABLEP TERM) TERM)
        ((QUOTEP TERM) (UNTRANSLATE-QUOTE (CADR TERM)))
        (T (CASE (FFN-SYMB TERM)
                 (IF
                     (COND ((CASE-FORMP TERM)
                            (CASE-FORM TERM))
                           ((COND-FORMP TERM)
                            (COND-FORM TERM))
                           (T (CONS 'IF
                                    (ITERATE FOR ARG IN (FARGS TERM)
                                             COLLECT (UNTRANSLATE ARG))))))
                 ((CAR CDR)
                  (ITERATE WITH L DO
                           (COND ((MATCH TERM (CAR &))
                                  (PUSH (QUOTE A) L)
                                  (SETQ TERM (FARGN TERM 1)))
                                 ((MATCH TERM (CDR &))
                                  (PUSH (QUOTE D) L)
                                  (SETQ TERM (FARGN TERM 1)))
                                 (T (RETURN
                                     `(,(PACK
                                         (CONS (QUOTE C)
                                               (NRECONC L (QUOTE (R)))))
                                       ,(UNTRANSLATE TERM)))))))
                 (CONS
                  (LET ((R (UNTRANSLATE (FARGN TERM 2))))
                    (COND ((NULL R) `(LIST ,(UNTRANSLATE (FARGN TERM 1))))
                          ((AND (CONSP R) (EQ (CAR R) (QUOTE LIST)))
                           `(LIST ,(UNTRANSLATE (FARGN TERM 1)) ,@(CDR R)))
                          (T `(CONS ,(UNTRANSLATE (FARGN TERM 1)) ,R)))))
                 ((AND OR PLUS TIMES)
                  (LET ((R (UNTRANSLATE (FARGN TERM 2))))
                    (COND ((AND (CONSP R) (EQ (CAR R) (FFN-SYMB TERM)))
                           `(,(CAR R) ,(UNTRANSLATE (FARGN TERM 1)) ,@(CDR R)))
                          (T `(,(FFN-SYMB TERM)
                               ,(UNTRANSLATE (FARGN TERM 1)) ,R)))))
                 (FOR
                  (COND
                   ((EQ *1*THM-MODE$ (QUOTE NQTHM))
                    (LET (V R C O B A)
                      (COND ((AND (MATCH TERM (FOR (LIST (QUOTE QUOTE) V)
                                                   R (LIST (QUOTE QUOTE) C)
                                                   (LIST (QUOTE QUOTE) O)
                                                   (LIST (QUOTE QUOTE) B) A))
                                  (TERMP V)
                                  (VARIABLEP V)
                                  (TERMP C)
                                  (MEMBER-EQ O FOR-OPS)
                                  (TERMP B)
                                  (EQUAL A (MAKE-ALIST V C B)))
                             (COND ((EQUAL C TRUE)
                                    (LIST (QUOTE FOR) V (QUOTE IN)
                                          (UNTRANSLATE R)
                                          O (UNTRANSLATE B)))
                                   (T (LIST (QUOTE FOR) V (QUOTE IN)
                                            (UNTRANSLATE R)
                                            (QUOTE WHEN) (UNTRANSLATE C)
                                            O (UNTRANSLATE B)))))
                            (T (CONS (QUOTE FOR)
                                     (ITERATE FOR ARG IN (FARGS TERM)
                                              COLLECT (UNTRANSLATE ARG)))))))
                   (T (CONS (FFN-SYMB TERM)
                            (ITERATE FOR ARG IN (FARGS TERM)
                                     COLLECT (UNTRANSLATE ARG))))))
                 (OTHERWISE (CONS (FFN-SYMB TERM)
                                  (ITERATE FOR ARG IN (FARGS TERM)
                                           COLLECT (UNTRANSLATE ARG))))))))

(DEFUN UNTRANSLATE-EVENT (EVENT)
  (LET (NAME TYPES TERM ARGS BODY HINTS OLD-NAME-OR-LIST FS)
    (CASE (CAR EVENT)
          (ADD-AXIOM (MATCH! EVENT (ADD-AXIOM NAME TYPES TERM))
                     (LIST (QUOTE ADD-AXIOM)
                           NAME TYPES (UNTRANSLATE TERM)))
          ((ADD-SHELL BOOT-STRAP DCL TOGGLE TOGGLE-DEFINED-FUNCTIONS
                      DEFTHEORY SET-STATUS)
           EVENT)
          (DEFN (COND ((INT= (LENGTH EVENT) 4)
                       (MATCH! EVENT (DEFN NAME ARGS BODY))
                       (LIST (QUOTE DEFN) NAME ARGS (UNTRANSLATE BODY)))
                      (T (MATCH! EVENT (DEFN NAME ARGS BODY HINTS))
                         (LIST (QUOTE DEFN) NAME ARGS (UNTRANSLATE BODY)
                               (ITERATE FOR X IN HINTS COLLECT
                                        (LIST (CAR X)
                                              (UNTRANSLATE (CADR X))))))))
          (PROVE-LEMMA (COND ((INT= (LENGTH EVENT) 4)
                              (MATCH! EVENT (PROVE-LEMMA NAME TYPES TERM))
                              (LIST (QUOTE PROVE-LEMMA)
                                    NAME TYPES (UNTRANSLATE TERM)))
                             (T (MATCH! EVENT
                                        (PROVE-LEMMA NAME TYPES TERM HINTS))
                                (LIST (QUOTE PROVE-LEMMA)
                                      NAME TYPES (UNTRANSLATE TERM)
                                      (UNTRANSLATE-HINTS HINTS)))))
          (FUNCTIONALLY-INSTANTIATE
           (MATCH! EVENT
                   (FUNCTIONALLY-INSTANTIATE NAME TYPES TERM
                                             OLD-NAME-OR-LIST FS HINTS))
           (LIST (QUOTE FUNCTIONALLY-INSTANTIATE) NAME TYPES
                 (UNTRANSLATE TERM)
                 OLD-NAME-OR-LIST
                 (UNTRANSLATE-FS FS)
                 (UNTRANSLATE-HINTS HINTS)))
          (CONSTRAIN
           (MATCH! EVENT (CONSTRAIN NAME TYPES TERM FS HINTS))
           (LIST (QUOTE CONSTRAIN) NAME TYPES (UNTRANSLATE TERM)
                 (UNTRANSLATE-FS FS)
                 (UNTRANSLATE-HINTS HINTS)))
          (OTHERWISE (ER HARD (EVENT) |The| |following| |event| |was| |not|
                         |recognized| |by|
                         UNTRANSLATE-EVENT |,| (!PPR EVENT (QUOTE |.|)))))))

(DEFUN UNTRANSLATE-FS (SUBST)
  (ITERATE FOR PAIR IN SUBST WITH ARGS AND BODY COLLECT
           (LIST (CAR PAIR)
                 (COND ((SYMBOLP (CADR PAIR)) (CADR PAIR))
                       (T (MATCH! (CADR PAIR) (LAMBDA ARGS BODY))
                          (LIST 'LAMBDA ARGS
                                (UNTRANSLATE BODY)))))))

(DEFUN UNTRANSLATE-HINTS (HINTS)
  (ITERATE
   FOR X IN HINTS
   COLLECT
   (CASE (CAR X)
         (USE
          (CONS (QUOTE USE)
                (ITERATE
                 FOR PAIR IN (CDR X)
                 COLLECT (CONS (CAR PAIR)
                               (ITERATE
                                FOR SUB-PAIR
                                IN (CDR PAIR)
                                COLLECT
                                (LIST (CAR SUB-PAIR)
                                      (UNTRANSLATE (CADR SUB-PAIR))))))))
         (EXPAND
          (CONS (QUOTE EXPAND)
                (ITERATE FOR X IN (CDR X)
                         COLLECT (UNTRANSLATE X))))
         ((DISABLE ENABLE) X)
         (INDUCT
          (LIST (QUOTE INDUCT) (UNTRANSLATE (CADR X))))
         (OTHERWISE
          (COND ((CADDR (ASSOC-EQ (CAR X) HINT-VARIABLE-ALIST))
                 (CONS (CAR X)
                       (ITERATE FOR Y IN (CDR X)
                                COLLECT (UNTRANSLATE Y))))
                (T X))))))


(DEFUN UNTRANSLATE-QUOTE (EVG) 

;   UNTRANSLATE-QUOTE eliminates UGLYP evgs by printing T and F in place 
;   of *1*T and *1*F and (const 'a1 ... 'an) in place of (*1*SQM const ...). 
;   This means digging into the evg to see if ugly things are hidden inside
;   the CONS structure.  If so, we introduce CONS or LIST to expose the 
;   the ugly terms. 

  (COND ((ATOM EVG) 
         (COND ((EQ EVG *1*T) T) 
               ((EQ EVG *1*F) (QUOTE F)) 
               ((EQ EVG NIL) NIL) 
               ((INTEGERP EVG) EVG) 
               (T (LIST (QUOTE QUOTE) EVG)))) 
        ((EQ (CAR EVG) *1*SHELL-QUOTE-MARK) 
         (CONS (CADR EVG) 
               (ITERATE FOR ARG IN (CDDR EVG) 
                        COLLECT (UNTRANSLATE-QUOTE ARG)))) 
        ((UGLYP EVG) 
         (COND ((SETQ TEMP-TEMP (LISTABLE-EVG-PAIRS EVG)) 
                (CONS (QUOTE LIST)
                      (ITERATE FOR X IN TEMP-TEMP
                               COLLECT (UNTRANSLATE-QUOTE X))))
               (T (LIST (QUOTE CONS)
                        (UNTRANSLATE-QUOTE (CAR EVG))
                        (UNTRANSLATE-QUOTE (CDR EVG))))))
        (T (LIST (QUOTE QUOTE) EVG))))

(DEFUN UPDATE-PERSISTENCE-ALIST (NAME CNT)
  (COND ((SETQ TEMP-TEMP
               (ASSOC-EQ NAME REWRITE-PATH-PERSISTENCE-ALIST))
         (SETF (CDR TEMP-TEMP) (+ CNT (CDR TEMP-TEMP))))
        (T (SETQ REWRITE-PATH-PERSISTENCE-ALIST
                 (CONS (CONS NAME CNT) REWRITE-PATH-PERSISTENCE-ALIST)))))

(DEFUN VARIANTP (TERM1 TERM2)
  (AND (ONE-WAY-UNIFY TERM1 TERM2)
       (ITERATE FOR PAIR IN UNIFY-SUBST ALWAYS (VARIABLEP (CDR PAIR)))
       (NO-DUPLICATESP (ITERATE FOR PAIR IN UNIFY-SUBST COLLECT (CDR PAIR)))))

(DEFUN VVV- (INT)
  (CASE INT
        (0 'VVV-0)
        (1 'VVV-1)
        (2 'VVV-2)
        (3 'VVV-3)
        (OTHERWISE (PACK (LIST 'VVV- INT)))))

(DEFUN WORSE-THAN (TERM1 TERM2)
  (COND ((QUICK-WORSE-THAN TERM1 TERM2) T)
        ((VARIABLEP TERM1) NIL)
        ((FQUOTEP TERM1) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM1)
                    THEREIS (SOME-SUBTERM-WORSE-THAN-OR-EQUAL ARG TERM2)))))

(DEFUN WORSE-THAN-OR-EQUAL (TERM1 TERM2)
  (OR (EQUAL TERM1 TERM2) (WORSE-THAN TERM1 TERM2)))

(DEFUN WRAPUP (WON-FLG)
  (COND ((NOT (EQ LEMMA-STACK ORIG-LEMMA-STACK))
         (ITERPRI T)
         (ER HARD NIL WRAPUP |found| |a| |non-trivial| LEMMA-STACK EXCL)))
  (COND ((NOT (EQ LINEARIZE-ASSUMPTIONS-STACK
                  ORIG-LINEARIZE-ASSUMPTIONS-STACK))
         (ITERPRI T)
         (ER HARD NIL WRAPUP |found| |a| |non-trivial|
             LINEARIZE-ASSUMPTIONS-STACK EXCL)))
  (IO (QUOTE FINISHED)
      NIL NIL NIL (LIST WON-FLG))
  (THROW (QUOTE PROVE)
         (COND (WON-FLG (QUOTE PROVED))
               (T NIL))))

(DEFUN XXXJOIN (FN X)
  (COND ((OR (ATOM X) (ATOM (CDR X)))
         (ER HARD NIL XXXJOIN |must| |not| |be| |called| |on| |a| |list| |with|
             |less| |than| 2 |elements| |.|))
        ((ATOM (CDDR X)) (CONS-TERM FN X))
        (T (CONS-TERM FN (LIST (CAR X) (XXXJOIN FN (CDR X)))))))

(DEFUN ZERO-POLY (LIT)
  (MAKE POLY 0 NIL NIL (LIST LIT) NIL))

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

(DEFUN BACKQUOTE (X)

; See the file remarks.text for some historical information regarding
; our implementation of backquote.

  (COND ((SIMPLE-VECTOR-P X)
         (LIST 'APPLY '(FUNCTION VECTOR)
               (BACKQUOTE (COERCE X 'LIST))))
        ((ATOM X) (LIST 'QUOTE X))
        ((EQ (CAR X) *COMMA*) (CADR X))
        ((EQ (CAR X) *COMMA-ATSIGN*)
         (ER SOFT NIL |`,@| |is| |an| |error| |.|))
        (T (BACKQUOTE-LST X))))

(DEFUN BACKQUOTE-LST (L)
  (COND ((ATOM L)
         (LIST 'QUOTE L))
        ((EQ (CAR L) *COMMA*)
         (CADR L))
        ((EQ (CAR L) *COMMA-ATSIGN*)
         (ER SOFT NIL |. ,@| |is| |illegal| |.|))
        ((AND (CONSP (CAR L))
              (EQ (CAAR L) *COMMA*))
         (LIST 'CONS
               (CADR (CAR L))
               (BACKQUOTE-LST (CDR L))))
        ((AND (CONSP (CAR L))
              (EQ (CAAR L) *COMMA-ATSIGN*))
         (LIST 'APPEND (CADR (CAR L)) (BACKQUOTE-LST (CDR L))))
        (T (LIST 'CONS
                 (BACKQUOTE (CAR L))
                 (BACKQUOTE-LST (CDR L))))))

(DEFUN BACKQUOTE-SETTING (ARG)

; BACKQUOTE-SETTING is to be used to set the comma and backquote functions in
; *READTABLE*.  If ARG is 'ORIG, then we revert to the original setting.  If
; arg is 'NQTHM, then we use the Nqthm definitions.

; We use the Nqthm definitions in PROVE-FILE, and we recommend that any Nqthm
; user who wants to use backquote in Nqthm forms establish the Nqthm settings
; in the default top level reader by invoking (BACKQUOTE-SETTINGS 'NQTHM) at
; the top level of Lisp.

  (COND ((NOT (MEMBER ARG '(ORIG NQTHM)))
         (ER SOFT (ARG) |the| |argument| |to| BACKQUOTE-SETTING |must|
             |be| |the| |symbol| NQTHM |or| |the| |symbol| ORIG |but|
             (!PPR ARG NIL) |is| |neither| |.|)))
  (SET-MACRO-CHARACTER
   #\`
   (COND ((EQ ARG 'NQTHM)
          #'(LAMBDA (STREAM CHAR)
              (DECLARE (IGNORE CHAR))
              (LET ((*BACKQUOTE-COUNTER* (1+ *BACKQUOTE-COUNTER*)))
                (BACKQUOTE (READ STREAM T NIL T)))))
         (T (GET-MACRO-CHARACTER #\` (COPY-READTABLE NIL)))))
  (SET-MACRO-CHARACTER
   #\,
   (COND ((EQ ARG 'NQTHM)
          #'(LAMBDA (STREAM CHAR)
              (DECLARE (IGNORE CHAR))
              (LET ((*BACKQUOTE-COUNTER* (1- *BACKQUOTE-COUNTER*)))
                (COND ((< *BACKQUOTE-COUNTER* 0)
                       (ER SOFT NIL |illegal| |comma| |encountered| |by|
                           READ |.|)))
                (CASE (PEEK-CHAR NIL STREAM T NIL T)
                      ((#\@ #\.) (READ-CHAR STREAM T NIL T)
                       (LIST *COMMA-ATSIGN* (READ STREAM T NIL T)))
                      (OTHERWISE (LIST *COMMA* (READ STREAM T NIL T)))))))
         (T (GET-MACRO-CHARACTER #\, (COPY-READTABLE NIL))))))

(DEFUN BEVIER-MODE (HINTS)
; It is illegal in Common Lisp to smash a top-level form in a file.
  (SETQ HINTS (COPY-TREE HINTS))
  (LET ((ENABLE-THEORY-HINT  (ASSOC 'ENABLE-THEORY HINTS))
        (DISABLE-THEORY-HINT (ASSOC 'DISABLE-THEORY HINTS)))
       (COND (DISABLE-THEORY-HINT HINTS)
             (ENABLE-THEORY-HINT
              (COND ((MEMBER T ENABLE-THEORY-HINT) HINTS)
                    ((MEMBER 'GROUND-ZERO ENABLE-THEORY-HINT)
                     (RPLACD (LAST HINTS) (LIST '(DISABLE-THEORY T)))
                     HINTS)
                    (T (RPLACD (LAST ENABLE-THEORY-HINT)
                               (CONS 'GROUND-ZERO NIL))
                       (RPLACD (LAST HINTS) (CONS '(DISABLE-THEORY T) NIL))
                       HINTS)))
             ((CONSP HINTS)
              (RPLACD (LAST HINTS) 
                      (LIST '(ENABLE-THEORY GROUND-ZERO) '(DISABLE-THEORY T)))
              HINTS)
             (T (LIST '(ENABLE-THEORY GROUND-ZERO)
                      '(DISABLE-THEORY T))))))

(DEFUN OUR-BOOLEAN (TERM) (TSLOGSUBSETP (TYPE-SET TERM) TYPE-SET-BOOLEAN))

(DEFUN BOOT-STRAP0 (MODE)
  (COND ((NOT (OR (NULL MODE)
                  (EQ MODE (QUOTE NQTHM))
                  (EQ MODE (QUOTE THM))))
         (ER SOFT (MODE) BOOT-STRAP |expects| |its| |argument| |to| |be|
             |NIL,| THM |,| |or| NQTHM |and| (!PPR MODE NIL) |is| |none|
             |of| |these| |.|)))
  (ADD-SUB-FACT NIL NIL NIL NIL T)
  (ADD-FACT NIL (QUOTE *1*THM-MODE$)
            (COND ((EQ MODE (QUOTE NQTHM))
                   (QUOTE NQTHM))
                  (T (QUOTE THM)))))

(DEFUN BREAK-AFTER-RELIEVE-HYPS (NAME LEMMA TARGET RELIEVE-HYPS-ANS)

;   See the comment in BREAK-BEFORE-RELIEVE-HYPS.

;   This function is called both from under the term rewriter and under
;   linear arithmetic.  When under the first, the next major act will
;   be to rewrite the rhs of the concl of the lemma, provided the
;   hyps were relieved.  When under the second, the next major act will
;   be to rewrite the entire conclusion and then linearize it.  This
;   function uses the type of LEMMA, REWRITE-RULE or LINEAR-LEMMA, to
;   decide what the command options should be.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   We know we have just exited the BREAK-BEFORE... routine.  If the cmd
;   in the BREAK-REWRITE-COMMAND-HANDLER-STATE is GO and the hyps were not
;   relieved, we should print the exit message and quit because no other
;   time will be spent on this lemma.  If the command was GO but we did
;   relieve the hyps, we should just get out of this break and await the
;   final one (In rewriting the concl we may experience further breaks
;   that are under this one, so it would be misleading to print the exit
;   message now.)  Otherwise, we left BREAK-BEFORE-RELIEVE-HYPS with the
;   message that the hypotheses were being attempted.  So we should
;   complete that interaction: 
            
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (COND ((NULL RELIEVE-HYPS-ANS)
                          (BREAK-EXIT-MSG LEMMA NIL)))
                   (RETURN NIL)))

            REPEAT
            (COND (RELIEVE-HYPS-ANS
                   (FORMAT *STANDARD-OUTPUT*
                           "Established hypotheses of ~A."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*))
                  (T (FORMAT *STANDARD-OUTPUT*
                             "Failed to establish the ~:R hypothesis of ~A:~%"
                             (ITERATE FOR I FROM 1
                                      AS HYP IN
                                      (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
                                             (ACCESS REWRITE-RULE HYPS LEMMA))
                                            (T (ACCESS
                                                LINEAR-LEMMA HYPS LEMMA)))
                                      WHEN (EQ LAST-HYP HYP)
                                      DO (RETURN I))
                             NAME)
                     (PPR-TERM LAST-HYP *STANDARD-OUTPUT*)
                     (TERPRI *STANDARD-OUTPUT*)
                     (PRINC "under the substitution" *STANDARD-OUTPUT*)
                     (TERPRI *STANDARD-OUTPUT*)
                     (PRINT-SUBSTITUTION NIL UNIFY-SUBST *STANDARD-OUTPUT*)
                     (COND ((EQ LAST-EXIT 'FREE-VARSP)
                            (FORMAT *STANDARD-OUTPUT*
                                    "because it has free variables in it."))
                           ((EQ LAST-EXIT 'RELIEVE-HYPS-NOT-OK)
                            (FORMAT *STANDARD-OUTPUT*
                                    "because it appears worse than an ~
                                     ancestor."))
                           ((EQ LAST-EXIT 'FALSE-NONFALSEP)
                            (FORMAT *STANDARD-OUTPUT*
                                    "because the instantiated hypothesis is ~
                                     assumed false."))
                           ((EQ LAST-EXIT 'LITS-THAT-MAY-BE-ASSUMED-FALSE)
                            (FORMAT *STANDARD-OUTPUT*
                                    "because the instantiated hypothesis is ~
                                     on LITS-THAT-MAY-BE-ASSUMED-FALSE."))
                           (T (FORMAT *STANDARD-OUTPUT*
                                      "because the hypothesis rewrote to:~%")
                              (PPR-TERM (COND ((MATCH LAST-HYP (NOT &))
                                               (LIST 'NOT LAST-EXIT))
                                              (T LAST-EXIT))
                                        *STANDARD-OUTPUT*)))
                     (TERPRI *STANDARD-OUTPUT*)))

;   We soon call the general purpose BREAK-REWRITE-COMMAND-HANDLER.  If the
;   attempt to relieve the hypotheses failed, all we can do is quit,
;   with the command OK.  If the attempt succeeded, we can either
;   watch the rewriting of the RHS or not.  In both cases, we permit
;   the standard break-lemma commands.

            (SETQ EXPORT-CMD-ALIST
                  (COND (RELIEVE-HYPS-ANS
                         (APPEND
                          (COND
                           ((EQ (CAR LEMMA) 'REWRITE-RULE)
                            '((OK . "Rewrite rhs of conclusion and break.")
                              (GO . "Rewrite rhs of conclusion and proceed.")))
                           (T
                            '((OK . "Rewrite the conclusion and break.")
                              (GO . "Rewrite the conclusion and proceed."))))
                          BREAK-LEMMA-COMMAND-HANDLER-ALIST))
                        (T (APPEND '((FAILED-HYP .
                                      "Repeat the explanation of failure.")
                                     (OK . "Proceed.")
                                     (GO . "Proceed."))
                                   BREAK-LEMMA-COMMAND-HANDLER-ALIST))))
                                 
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))
            (COND ((AND (EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                        (NULL RELIEVE-HYPS-ANS))
                   (SETF (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)))
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                   (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
                          (FORMAT
                           *STANDARD-OUTPUT*
                           "Rewriting the rhs of the conclusion of ~A..."
                           NAME))
                         (T
                          (FORMAT *STANDARD-OUTPUT*
                                  "Rewriting the conclusion of ~A..."
                                  NAME)))
                   (TERPRI NIL)
                   (RETURN NIL))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (COND ((NULL RELIEVE-HYPS-ANS)
                          (BREAK-EXIT-MSG LEMMA NIL)))
                   (RETURN NIL))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                       'FAILED-HYP)
                   (GO REPEAT))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-AFTER-REWRITE-RHS (NAME LEMMA TARGET REWRITTEN-TERM)

;   See the comment in BREAK-BEFORE-RELIEVE-HYPS.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   We know we have just exited the BREAK-AFTER-RELIEVE-HYPS routine.
;   If the CAR of the BREAK-REWRITE-COMMAND-HANDLER-STATE is GO we
;   should print the exit message and get out.  Otherwise, we left
;   BREAK-AFTER-RELIEVE-HYPS with a message that the rhs was being
;   rewritten and we should complete that interaction and enter
;   a break.

            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (BREAK-EXIT-MSG LEMMA T)
                   (RETURN NIL)))

            (FORMAT *STANDARD-OUTPUT*
                    "Rhs of conclusion of ~A rewritten.  RHS ="
                    NAME)
            (TERPRI *STANDARD-OUTPUT*)
            (PPR-TERM REWRITTEN-TERM *STANDARD-OUTPUT*)
            (TERPRI *STANDARD-OUTPUT*)

            (SETQ EXPORT-CMD-ALIST
                  (APPEND '((RHS .
                             "Print the rewritten rhs of the conclusion.")
                            (OK . "Proceed.")
                            (GO . "Proceed."))
                          BREAK-LEMMA-COMMAND-HANDLER-ALIST))
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'RHS)
                   (PPR-TERM REWRITTEN-TERM *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((OR (EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                       (EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO))
                   (BREAK-EXIT-MSG LEMMA T)
                   (RETURN NIL))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-AFTER-REWRITE-LINEAR-CONCL (NAME LEMMA TARGET REWRITTEN-CONCL)

;   See the comment in BREAK-BEFORE-RELIEVE-HYPS.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   We know we have just exited the BREAK-AFTER-RELIEVE-HYPS routine and
;   we have rewritten the conclusion of the lemma.  If the CAR of the
;   BREAK-REWRITE-COMMAND-HANDLER-STATE is GO we should just get out of
;   this break and await the final function in the sequence.  Otherwise,
;   we left BREAK-AFTER-RELIEVE-HYPS with a message that the concl was
;   being rewritten and we should complete that interaction and continue a
;   break.

            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (RETURN NIL)))

            (FORMAT *STANDARD-OUTPUT*
                    "Conclusion of ~A rewritten.  REWRITTEN-CONCL ="
                    NAME)
            (TERPRI *STANDARD-OUTPUT*)
            (PPR-TERM REWRITTEN-CONCL *STANDARD-OUTPUT*)
            (TERPRI *STANDARD-OUTPUT*)

            (SETQ EXPORT-CMD-ALIST
                  (APPEND '((REWRITTEN-CONCL .
                             "Print the rewritten conclusion.")
                            (OK . "Linearize rewritten conclusion and break.")
                            (GO . "Proceed."))
                          BREAK-LEMMA-COMMAND-HANDLER-ALIST))
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                       'REWRITTEN-CONCL)
                   (PPR-TERM REWRITTEN-CONCL *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                   (FORMAT *STANDARD-OUTPUT*
                           "Linearizing the rewritten conclusion of ~A..."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*)
                   (RETURN NIL))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (RETURN NIL))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-AFTER-LINEARIZE-REWRITTEN-CONCL
  (NAME LEMMA TARGET REWRITTEN-CONCL POLY-LST)

;   See the comment in BREAK-BEFORE-RELIEVE-HYPS.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   We know we have just exited the BREAK-AFTER-REWRITE-LINEAR-CONCL
;   routine and linearized the conclusion.  The result is POLY-LST.
;   If POLY-LST has a non-NIL CDR then the attempt to apply this lemma
;   failed.

;   If the CAR of the BREAK-REWRITE-COMMAND-HANDLER-STATE is GO
;   and POLY-LST has a non-NIL CDR then we should print the exit message
;   and quit.  Otherwise, we should complete the interaction started
;   in BREAK-AFTER-REWRITE-LINEAR-CONCL and then continue the break.

            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (COND ((CDR POLY-LST)
                          (BREAK-EXIT-MSG LEMMA NIL)))
                   (RETURN NIL)))

            (FORMAT *STANDARD-OUTPUT*
                    "Conclusion of ~A linearized."
                    NAME)
            (TERPRI *STANDARD-OUTPUT*)
            (FORMAT *STANDARD-OUTPUT*
                    "POLY-LST will print the result.")
            (TERPRI *STANDARD-OUTPUT*)
            (COND ((CDR POLY-LST)
                   (FORMAT *STANDARD-OUTPUT*
                           "The result is a disjunction of polynomials and~@
                           is thus ineligible for addition to the linear~@
                           data base.  The application of ~A~@
                           therefore fails."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*)))

            (SETQ EXPORT-CMD-ALIST
                  (APPEND '((REWRITTEN-CONCL .
                             "Print the rewritten conclusion.")
                            (POLY-LST .
                             "Print the linearized rewritten conclusion.")
                            (OK . "Test appropriateness of polys and break.")
                            (GO . "Proceed."))
                          BREAK-LEMMA-COMMAND-HANDLER-ALIST))
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                       'REWRITTEN-CONCL)
                   (PPR-TERM REWRITTEN-CONCL *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'POLY-LST)
                   (PPR POLY-LST *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                   (FORMAT *STANDARD-OUTPUT*
                           "Testing appropriateness of adding polys from ~A..."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*)
                   (RETURN NIL))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (COND ((CDR POLY-LST)
                          (BREAK-EXIT-MSG LEMMA NIL)))
                   (RETURN NIL))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-AFTER-LINEAR-WORSE-THAN
  (NAME LEMMA TARGET REWRITTEN-CONCL POLY-LST WORSE-THAN-FLG)

;   See the comment in BREAK-BEFORE-RELIEVE-HYPS.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   We know we have just exited the BREAK-AFTER-LINEARIZE-REWRITTEN-CONCL
;   routine and done the worse-than check.  The result is WORSE-THAN-FLG.
;   If the flag is NIL the application of the lemma has failed.  In any
;   case, this is the last function in the break sequence.

            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (BREAK-EXIT-MSG LEMMA WORSE-THAN-FLG)
                   (RETURN NIL)))

            (COND (WORSE-THAN-FLG
                   (FORMAT *STANDARD-OUTPUT*
                           "Polys from ~A are appropriate and~@
                            will be added to the linear data base."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*))
                  (T (FORMAT *STANDARD-OUTPUT*
                             "Polys from ~A are inappropriate.~@
                             Some poly in POLY-LST contains an addend~@
                             that is worse than every addend in the~@
                             current linear data base.  The polys will~@
                             not be added and so the application of~@
                             ~A fails."
                             NAME NAME)
                     (TERPRI *STANDARD-OUTPUT*)))

            (SETQ EXPORT-CMD-ALIST
                  (APPEND '((REWRITTEN-CONCL .
                             "Print the rewritten conclusion.")
                            (POLY-LST .
                             "Print the linearized rewritten conclusion.")
                            (OK . "Proceed.")
                            (GO . "Proceed."))
                          BREAK-LEMMA-COMMAND-HANDLER-ALIST))
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))
            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                       'REWRITTEN-CONCL)
                   (PPR-TERM REWRITTEN-CONCL *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'POLY-LST)
                   (PPR POLY-LST *STANDARD-OUTPUT*)
                   (TERPRI *STANDARD-OUTPUT*))
                  ((OR (EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                       (EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO))
                   (BREAK-EXIT-MSG LEMMA WORSE-THAN-FLG)
                   (RETURN NIL))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-BEFORE-RELIEVE-HYPS (NAME LEMMA TARGET)

;   The break facility for rewrite and linear lemmas is implemented
;   across many different functions.  A standard sequence of them is
;      BREAK-BEFORE-RELIEVE-HYPS,
;      BREAK-AFTER-RELIEVE-HYPS,
;      BREAK-AFTER-REWRITE-RHS.
;   They are always called in turn if the BROKEN-LEMMAS list is
;   non-NIL.  This function handles the initial entry message for all
;   the sequences.  But many of the subsequent functions may print the
;   exit message, since control may not always reach the final function.
;   For example, if relieve-hyps fails, BREAK-AFTER-RELIEVE-HYPS is the
;   last chance we have to print an exit message.  Each function
;   uses the general purpose BREAK-REWRITE-COMMAND-HANDLER to interact
;   with the user and field queries about the general state.  That
;   command loop function passes back to its caller any command it
;   has been told to export by the caller.  Each function
;   has the command loop export certain commands to it for
;   processing in the given situation.
   
;   This function is passed both the NAME of the LEMMA and the LEMMA
;   itself, even though the name is in the LEMMA.  The reason is for
;   efficiency.  LEMMA may be a LINEAR-LEMMA or a REWRITE-RULE.  To
;   determine whether the lemma is broken we must find its NAME in
;   BROKEN-LEMMAS, but first we must determine the type of lemma
;   we have so we can get its name.  But the caller of this function
;   knows what kind of lemma it is dealing with and so we have it
;   supply the name.  We dig out the rest of what we need from LEMMA
;   when we need it, after deciding to break.

  (OR (NOT (MEMBER-EQ NAME BROKEN-LEMMAS))
      (PROG (EXPORT-CMD-ALIST)
            
;   Print the entry message
            
            (BREAK-ENTRY-MSG LEMMA)
            
;   Now call the general purpose BREAK-REWRITE-COMMAND-HANDLER, telling it
;   to export back to us the OK and GO commands plus the standard commands
;   handled by all three of the break lemma functions.

            (SETQ EXPORT-CMD-ALIST
                  (APPEND
                   '((OK . "Attempt to relieve the hypotheses and then break.")
                     (GO . "Proceed without further interaction."))
                   BREAK-LEMMA-COMMAND-HANDLER-ALIST))
            LOOP
            (SETQ BREAK-REWRITE-COMMAND-HANDLER-STATE
                  (BREAK-REWRITE-COMMAND-HANDLER EXPORT-CMD-ALIST NIL))

;   The CAR of the returned state is the exported command.  The
;   CDR of the state is known only to BREAK-REWRITE-COMMAND-HANDLER, which
;   expects to get that same state passed to it later during the
;   processing of this rule.

            (COND ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'OK)
                   (FORMAT *STANDARD-OUTPUT*
                           "Attempting to relieve the hypotheses of ~A..."
                           NAME)
                   (TERPRI *STANDARD-OUTPUT*)
                   (RETURN NIL))
                  ((EQ (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE) 'GO)
                   (RETURN NIL))
                  (T (BREAK-LEMMA-COMMAND-HANDLER
                      (CAR BREAK-REWRITE-COMMAND-HANDLER-STATE)
                      NAME LEMMA TARGET)))
            (GO LOOP))))

(DEFUN BREAK-ENTRY-MSG (LEMMA)
  (TERPRI *STANDARD-OUTPUT*)
  (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
         (FORMAT *STANDARD-OUTPUT*
                 "(Entering break on replacement rule ~A"
                 (ACCESS REWRITE-RULE NAME LEMMA)))
        (T (FORMAT *STANDARD-OUTPUT*
                   "(Entering break on linear rule ~A"
                   (ACCESS LINEAR-LEMMA NAME LEMMA))))
  (TERPRI *STANDARD-OUTPUT*))

(DEFUN BREAK-EXIT-MSG (LEMMA FLG)
  (LET ((NAME (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
                     (ACCESS REWRITE-RULE NAME LEMMA))
                    (T (ACCESS LINEAR-LEMMA NAME LEMMA)))))
    (COND (FLG
           (FORMAT *STANDARD-OUTPUT*
                   "Application of ~A succeeded."
                   NAME))
          (T (FORMAT *STANDARD-OUTPUT*
                     "Application of ~A failed."
                     NAME)))
    (TERPRI *STANDARD-OUTPUT*)
    (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
           (FORMAT *STANDARD-OUTPUT*
                   "Exiting break on replacement rule ~A.)"
                   NAME))
          (T (FORMAT *STANDARD-OUTPUT*
                     "Exiting break on linear rule ~A.)"
                     NAME)))
    (TERPRI *STANDARD-OUTPUT*)))

(DEFUN BREAK-LEMMA (NAME)
  (LET ((EVENT-FORM (DATA-BASE 'EVENT-FORM NAME)))
    (SETQ BROKEN-LEMMAS (ADD-TO-SET NAME BROKEN-LEMMAS))
    (MAINTAIN-REWRITE-PATH T)
    (COND ((NOT (AND EVENT-FORM
                     (MEMBER-EQ (CAR EVENT-FORM)
                                '(ADD-AXIOM
                                  PROVE-LEMMA
                                  CONSTRAIN
                                  FUNCTIONALLY-INSTANTIATE))
                     (MEMBER-EQ 'REWRITE
                                (CADDR EVENT-FORM))))
           (ER WARNING (NAME) (!PPR NAME NIL) |has| |been| |broken|
               |but| |it| |is| |not| |an| ADD-AXIOM |,| CONSTRAIN |,|
               FUNCTIONALLY-INSTANTIATE |,| |or| PROVE-LEMMA
               |event| |with| |lemma| |type|
               REWRITE |.|  |Nevertheless| |,| |a| |break| |will|
               |occur| |if| |a| |replacement| |rule| |of| |that|
               |name| |is| |applied| |.| )))
    (COND ((DISABLEDP NAME)
           (ER WARNING (NAME) (!PPR NAME NIL) |has| |been| |broken|
               |but| |is| |currently| |disabled| |and| |won't|
               |be| |considered| |until| |it| |is| |enabled| |.|)))
    
    NAME))

(DEFUN BREAK-LEMMA-COMMAND-HANDLER (CMD NAME LEMMA TARGET)
  (CASE CMD
        (NAME (PRINC NAME *STANDARD-OUTPUT*)
              (TERPRI *STANDARD-OUTPUT*))
        (HYPS  (ITERATE FOR HYP IN
                        (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
                               (ACCESS REWRITE-RULE HYPS LEMMA))
                              (T (ACCESS LINEAR-LEMMA HYPS LEMMA)))
                        AS I FROM 1
                        DO
                        (PRINC I *STANDARD-OUTPUT*)
                        (PRINC ".  " *STANDARD-OUTPUT*)
                        (PPRIND (UNTRANSLATE HYP) 4 0 *STANDARD-OUTPUT*)
                        (TERPRI *STANDARD-OUTPUT*)))
        (CONCL (PPR-TERM (COND ((EQ (CAR LEMMA) 'REWRITE-RULE)
                                (ACCESS REWRITE-RULE CONCL LEMMA))
                               (T (ACCESS LINEAR-LEMMA CONCL LEMMA)))
                         *STANDARD-OUTPUT*)
               (TERPRI *STANDARD-OUTPUT*))
        (SUBST (PRINT-SUBSTITUTION NIL UNIFY-SUBST *STANDARD-OUTPUT*))
        (TARGET (PPR-TERM TARGET *STANDARD-OUTPUT*)
                (TERPRI *STANDARD-OUTPUT*))
        (OTHERWISE (ER HARD (CMD) BREAK-LEMMA-COMMAND-HANDLER |and|
                       BREAK-LEMMA-COMMAND-HANDLER-ALIST |do| |not| |agree|
                       |on|
                       (!PPR CMD NIL) |or| |else| |some| |function| |is|
                       |not| |checking| |the| |alist| |before| |invoking|
                       |the| |handler| |.|))))

(DEFUN BREAK-REWRITE NIL
  (FORMAT *STANDARD-OUTPUT* "~&")  
  (COND ((NULL REWRITE-PATH-STK-PTR)
         (FORMAT *STANDARD-OUTPUT*
                 "The REWRITE-PATH is not being maintained.~%"))
        ((INT= REWRITE-PATH-STK-PTR -1)
         (FORMAT *STANDARD-OUTPUT*
                 "The theorem prover is not in the simplifier right now.~%"))
        (T
         (BREAK-REWRITE-COMMAND-HANDLER
          '((OK . "Return to Common Lisp")) NIL)))
  NIL)

(DEFUN BREAK-REWRITE-COMMAND-HANDLER (EXPORT-CMD-ALIST STATE)
  (PROG (CURRENT-REWRITE-PATH-FRAME-PTR
         CMD
         (CMD-ALIST
          '((PATH . "Highlight the REWRITE path.")
            (FRAME . "Print the current frame, pruning deep terms.")
            (PATH! . "Print every frame in the path, pruning deep terms.")
            (FRAME! . "Print the current frame, with no pruning.")
            (PATH!! . "Print the path, with no pruning.")
            (ASSUMPTIONS . "Print the governing assumptions.")
            (ANCESTORS . "Print the negations of backchaining hypotheses.")
            (ACCUMULATED-PERSISTENCE .
             "Print the accumulated persistence totals.")
            (BK . "Move one frame towards the top-level SIMPLIFY.")
            (NX . "Move one frame away from the top-level SIMPLIFY.")
            (TOP . "Go to the top-level SIMPLIFY frame.")
            (BTM . "Go to the frame farthest from the top-level SIMPLIFY.")
            ("n (a natural number)" . "Go to frame number n.")
            ("s-expr (a list expression)" . "Evaluate Common Lisp s-expr"))))
        (COND ((NULL STATE)
               (SETQ CURRENT-REWRITE-PATH-FRAME-PTR REWRITE-PATH-STK-PTR))
              (T
               (SETQ CURRENT-REWRITE-PATH-FRAME-PTR (CADR STATE))))
        LOOP
        (IPRINC ": " *STANDARD-OUTPUT*)
        (SETQ CMD (READ *STANDARD-INPUT*))
        (FORMAT *STANDARD-OUTPUT* "~&")
        (COND ((CONSP CMD)
               (PRIN1 (EVAL CMD) *STANDARD-OUTPUT*)
               (TERPRI *STANDARD-OUTPUT*))
              ((ASSOC-EQ CMD EXPORT-CMD-ALIST)
               (RETURN (LIST CMD CURRENT-REWRITE-PATH-FRAME-PTR)))
              (T
               (CASE CMD
                     (ASSUMPTIONS
                      (COND ((NULL TYPE-ALIST)
                             (PRINC "none" *STANDARD-OUTPUT*)
                             (TERPRI *STANDARD-OUTPUT*))
                            (T
                             (ITERATE FOR X IN
                                      (PRETTYIFY-TYPE-ALIST TYPE-ALIST)
                                      DO
                                      (PPR X *STANDARD-OUTPUT*)
                                      (TERPRI *STANDARD-OUTPUT*)))))
                     (ANCESTORS
                      (COND ((NULL ANCESTORS)
                             (PRINC "none" *STANDARD-OUTPUT*)
                             (TERPRI *STANDARD-OUTPUT*))
                            (T
                             (ITERATE FOR X IN ANCESTORS DO
                                      (PPR-TERM X *STANDARD-OUTPUT*)
                                      (TERPRI *STANDARD-OUTPUT*)))))
                     (PATH     (PRINT-REWRITE-PATH 'HIGHLIGHT
                                                   *STANDARD-OUTPUT*))
                     (PATH!    (PRINT-REWRITE-PATH T *STANDARD-OUTPUT*))
                     (PATH!!   (PRINT-REWRITE-PATH NIL *STANDARD-OUTPUT*))
                     (FRAME    (PRINT-REWRITE-PATH-FRAME
                                CURRENT-REWRITE-PATH-FRAME-PTR
                                T *STANDARD-OUTPUT*))
                     (FRAME!   (PRINT-REWRITE-PATH-FRAME
                                CURRENT-REWRITE-PATH-FRAME-PTR
                                NIL *STANDARD-OUTPUT*))
                     (BK       (COND ((NOT (ZEROP
                                            CURRENT-REWRITE-PATH-FRAME-PTR))
                                      (SETQ
                                       CURRENT-REWRITE-PATH-FRAME-PTR
                                       (1- CURRENT-REWRITE-PATH-FRAME-PTR))))
                               (GO PRINT-FRAME))
                     (NX     (COND ((NOT (INT= CURRENT-REWRITE-PATH-FRAME-PTR
                                               REWRITE-PATH-STK-PTR))
                                    (SETQ
                                     CURRENT-REWRITE-PATH-FRAME-PTR
                                     (1+ CURRENT-REWRITE-PATH-FRAME-PTR))))
                             (GO PRINT-FRAME))
                     (TOP    (SETQ CURRENT-REWRITE-PATH-FRAME-PTR 0)
                             (GO PRINT-FRAME))
                     (BTM    (SETQ CURRENT-REWRITE-PATH-FRAME-PTR
                                   REWRITE-PATH-STK-PTR)
                             (GO PRINT-FRAME))
                     (BREAK (BREAK "~A" NAME)
                            (TERPRI *STANDARD-OUTPUT*))
                     (ACCUMULATED-PERSISTENCE
                      (ACCUMULATED-PERSISTENCE))
                     (? (FORMAT
                         *STANDARD-OUTPUT*
                         "You are in the BREAK-REWRITE command interpreter.~@
                       The commands specific to this break are:")
                        (TERPRI *STANDARD-OUTPUT*)
                        (PRINT-TWO-COLUMN-TABLE
                         "   cmd              effect"  2 20
                         (APPEND EXPORT-CMD-ALIST
                                 '((?? . "General purpose commands.")))
                         *STANDARD-OUTPUT*))
                     (??
                      (FORMAT
                       *STANDARD-OUTPUT*
                       "You are in the BREAK-REWRITE command interpreter.~@
                       The general purpose commands are:")
                      (TERPRI *STANDARD-OUTPUT*)
                      (PRINT-TWO-COLUMN-TABLE
                       "   cmd              effect"  2 20
                       (APPEND CMD-ALIST
                               '((? . "Special purpose commands.")))
                       *STANDARD-OUTPUT*))
                     (OTHERWISE
                      (COND
                       ((AND (INTEGERP CMD)
                             (<= 0 CMD)
                             (<= CMD REWRITE-PATH-STK-PTR))
                        (SETQ CURRENT-REWRITE-PATH-FRAME-PTR CMD)
                        (GO PRINT-FRAME))
                       (T (GO UNREC)))))))
        (GO LOOP)
        PRINT-FRAME
        (PRINT-REWRITE-PATH-FRAME CURRENT-REWRITE-PATH-FRAME-PTR
                                  T *STANDARD-OUTPUT*)
        (GO LOOP)
        UNREC
        (PRINC "Unrecognized command.  Type ? for help."
               *STANDARD-OUTPUT*)
        (TERPRI *STANDARD-OUTPUT*)
        (GO LOOP)))

(DEFUN BTM-OBJECT (CONST)

;   If the shell for which CONST is the constructor has a bottom object return
;   the term that is that bottom object.  Else, return NIL.

  (LET (TYPE-SET ANS)
    (SETQ TYPE-SET (TSLOGBIT (CDR (ASSOC-EQ CONST SHELL-ALIST))))
    (COND ((ITERATE FOR FN IN *1*BTM-OBJECTS
                    THEREIS (TS= (TYPE-SET (SETQ ANS (CONS-TERM FN NIL)))
                                 TYPE-SET))
           ANS)
          (T NIL))))

(DEFUN BTM-OBJECT-OF-TYPE-SET (TYPE-SET)

;   Returns the btm object fn symb with the specified type set, or NIL if no
;   such btm object exists.

  (COND ((NULL (CDR *1*BTM-OBJECTS))
         (COND ((TS= TYPE-SET TYPE-SET-NUMBERS)
                (QUOTE ZERO))
               (T NIL)))
        (T (ITERATE FOR X IN *1*BTM-OBJECTS
                    WHEN (TS= TYPE-SET (CAR (TYPE-PRESCRIPTION X)))
                    DO (RETURN X)))))

(DEFUN BTM-OBJECTP (TERM)
  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM)
         (COND ((ATOM (CADR TERM))
                (EQUAL 0 (CADR TERM)))
               (T (AND (EQ *1*SHELL-QUOTE-MARK (CAR (CADR TERM)))
                       (MEMBER-EQ (CADR (CADR TERM)) *1*BTM-OBJECTS)))))
        (T (MEMBER-EQ (FFN-SYMB TERM) *1*BTM-OBJECTS))))

(DEFUN BUILD-SUM (WINNING-PAIR ALIST)
  (COND ((ATOM ALIST) ZERO)
        ((EQUAL WINNING-PAIR (CAR ALIST))
         (BUILD-SUM WINNING-PAIR (CDR ALIST)))
        (T (CONS-PLUS (COND ((EQUAL 1 (ABS (CDAR ALIST)))
                             (CAAR ALIST))
                            (T (FCONS-TERM* (QUOTE TIMES)
                                            (LIST (QUOTE QUOTE)
                                                  (ABS (CDAR ALIST)))
                                            (CAAR ALIST))))
                      (BUILD-SUM WINNING-PAIR (CDR ALIST))))))

(DEFUN CANCEL-POLYS (EQ1 EQ2)

; Once upon a time, this function was named simply CANCEL.  But
; Coral Common Lisp illegally used that name and we have renamed
; our function out of courtesy.

  (LET (CO1 CO2 POLY)
    (SETQ CO1 (ABS (FIRST-COEFFICIENT EQ1)))
    (SETQ CO2 (ABS (FIRST-COEFFICIENT EQ2)))

;   See ADD-TERMS-TO-POT-LST for an explanation of why we UNION rather than
;   UNION-EQUAL the LITERALS and LEMMAS.

    (SETQ POLY (MAKE POLY (+ (* CO2
                                (ACCESS POLY CONSTANT EQ1))
                             (* CO1
                                (ACCESS POLY CONSTANT EQ2)))
                     (CANCEL1 CO2 (CDR (ACCESS POLY ALIST EQ1))
                              CO1
                              (CDR (ACCESS POLY ALIST EQ2)))
                     (UNION-EQUAL (ACCESS POLY ASSUMPTIONS EQ1)
                                  (ACCESS POLY ASSUMPTIONS EQ2))
                     (UNION-EQ (ACCESS POLY LITERALS EQ1)
                               (ACCESS POLY LITERALS EQ2))
                     (UNION-EQ (ACCESS POLY LEMMAS EQ1)
                               (ACCESS POLY LEMMAS EQ2))))
    (COND ((IMPOSSIBLE-POLYP POLY)
           (SETQ LINEAR-ASSUMPTIONS (ACCESS POLY ASSUMPTIONS POLY))
           (SETQ LEMMAS-USED-BY-LINEAR (UNION-EQ (ACCESS POLY LEMMAS POLY)
                                                 (ACCESS POLY LITERALS
                                                         POLY)))
           (THROW (QUOTE ADD-EQUATIONS)
                  (QUOTE CONTRADICTION)))
          ((TRUE-POLYP POLY) NIL)
          (T POLY))))

(DEFUN CANCEL-POSITIVE (EQUATION)
  (COND ((> (FIRST-COEFFICIENT EQUATION) 0)
         (SETQ EQUATION (MAKE POLY (ACCESS POLY CONSTANT EQUATION)
                              (CDR (ACCESS POLY ALIST EQUATION))
                              (ACCESS POLY ASSUMPTIONS EQUATION)
                              (ACCESS POLY LITERALS EQUATION)
                              (ACCESS POLY LEMMAS EQUATION)))
         (COND ((IMPOSSIBLE-POLYP EQUATION)
                (SETQ LINEAR-ASSUMPTIONS (ACCESS POLY ASSUMPTIONS EQUATION))
                (SETQ LEMMAS-USED-BY-LINEAR
                      (UNION-EQ (ACCESS POLY LEMMAS EQUATION)
                                (ACCESS POLY LITERALS EQUATION)))
                (THROW (QUOTE ADD-EQUATIONS)
                       (QUOTE CONTRADICTION)))
               ((TRUE-POLYP EQUATION) NIL)
               (T EQUATION)))
        (T NIL)))

(DEFUN CANCEL1 (CO1 AL1 CO2 AL2)
  (LET (TEMP)
    (COND ((NULL AL1)
           (ITERATE FOR PAIR IN AL2 COLLECT
                    (CONS (CAR PAIR) (* (CDR PAIR) CO2))))
          ((NULL AL2)
           (ITERATE FOR PAIR IN AL1 COLLECT
                    (CONS (CAR PAIR)
                          (* (CDR PAIR) CO1))))
          ((NOT (TERM-ORDER (CAAR AL1) (CAAR AL2)))
           (CONS (CONS (CAAR AL1)
                       (* (CDAR AL1) CO1))
                 (CANCEL1 CO1 (CDR AL1) CO2 AL2)))
          ((EQUAL (CAAR AL1) (CAAR AL2))
           (SETQ TEMP (+ (* CO1 (CDAR AL1))
                         (* CO2 (CDAR AL2))))
           (COND ((EQUAL TEMP 0)
                  (CANCEL1 CO1 (CDR AL1) CO2 (CDR AL2)))
                 (T (CONS (CONS (CAAR AL1) TEMP)
                          (CANCEL1 CO1 (CDR AL1) CO2 (CDR AL2))))))
          (T (CONS (CONS (CAAR AL2) (* (CDAR AL2) CO2))
                   (CANCEL1 CO1 AL1 CO2 (CDR AL2)))))))

(DEFUN CAR-CDRP (X)
  (LET ((STR (SYMBOL-NAME X)))
    (COND ((AND (> (LENGTH STR) 2)
                (EQL (AREF STR 0) #\C)
                (EQL (AREF STR (1- (LENGTH STR))) #\R)
                (ITERATE FOR I FROM 1 TO  (- (LENGTH STR) 2)
                         ALWAYS (OR (EQL (AREF STR I) #\A)
                                    (EQL (AREF STR I) #\D))))
           (ITERATE FOR I DOWNFROM (- (LENGTH STR) 2) TO 1 COLLECT
                    (AREF STR I)))
          (T NIL))))

(DEFUN CASE-FORMP (TERM)
 (LET (LHS)
  (AND (MATCH TERM (IF (EQUAL LHS &) & &))
       (>= (CASE-LENGTH LHS TERM) 3))))

(DEFUN CASE-FORM (TERM)
  (LET (LHS)
    (MATCH TERM (IF (EQUAL LHS &) & &))
    (CONS 'CASE
          (CONS (UNTRANSLATE LHS)
                (CASE-FORM1 LHS TERM)))))

(DEFUN CASE-FORM1 (X TERM)
  (LET (Y C U V)
    (COND ((AND (MATCH TERM (IF (EQUAL Y C) U V))
                (EQUAL X Y)
                (QUOTEP C)
                (NOT (UGLYP (CADR C)))
                (NOT (EQ (CADR C) 'OTHERWISE)))
           (CONS (LIST (CADR C) (UNTRANSLATE U))
                 (CASE-FORM1 X V)))
          (T (LIST (LIST 'OTHERWISE (UNTRANSLATE TERM)))))))

(DEFUN CASE-LENGTH (X TERM)

; TERM is an IF.  We are imagining printing it as a CASE on X.
; If the test of TERM is (EQUAL X const) then we can extend the
; length of the CASE statement by 1.  Otherwise, this term is
; the otherwise clause.  Note that every term can be printed
; as a (CASE any (otherwise term)).  

; Larry Smith caught a bug in the original version of this function
; which caused the untranslate of (if (equal key 'otherwise) 1 2)
; to be the un-translatable (case key (otherwise 1) (otherwise 2)).

  (LET (Y C REST)
    (COND ((AND (MATCH TERM (IF (EQUAL Y C) & REST))
                (EQUAL X Y)
                (QUOTEP C)
                (NOT (UGLYP (CADR C)))
                (NOT (EQ (CADR C) 'OTHERWISE)))
           (1+ (CASE-LENGTH X REST)))
          (T 1))))

(DEFUN COND-FORMP (TERM)
 (>= (COND-LENGTH TERM) 3))

(DEFUN COND-FORM (TERM)
 (CONS 'COND (COND-FORM1 TERM)))

(DEFUN COND-FORM1 (TERM)
 (LET (X U V)
   (COND ((MATCH TERM (IF X U V))
          (CONS (LIST (UNTRANSLATE X) (UNTRANSLATE U))
                (COND-FORM1 V)))
         (T (LIST (LIST 'T (UNTRANSLATE TERM)))))))

(DEFUN COND-LENGTH (TERM)

; TERM is an IF.  We are imagining printing it as a COND.
; How many clauses will that COND have?  Note that every
; term can be printed as (COND (T term)).

 (LET (REST)
   (COND ((MATCH TERM (IF & & REST))
          (1+ (COND-LENGTH REST)))
         (T 1))))

(DEFUN CDR-ALL (X) (ITERATE FOR X1 IN X COLLECT (CDR X1)))

(DEFUN CH (&OPTIONAL (N (1- (LENGTH CHRONOLOGY))) M)
  (LET (EVENT (*PRINT-PRETTY* NIL))
    (COND ((NULL M)
           (COND ((SYMBOLP N)
                  (SETQ M (ITERATE FOR X IN CHRONOLOGY AS I FROM 0
                                   WHEN (EQ X N)
                                   DO (RETURN I)))
                  (SETQ N 0))
                 (T (SETQ M N)
                    (SETQ N 0))))
          (T (COND ((SYMBOLP M)
                    (SETQ M (ITERATE FOR X IN CHRONOLOGY AS I FROM 0
                                     WHEN (EQ X M)
                                     DO (RETURN I)))))
             (COND ((SYMBOLP N)
                    (SETQ N (ITERATE FOR X IN CHRONOLOGY AS I FROM 0
                                     WHEN (EQ X N)
                                     DO (RETURN I)))))))
    (COND ((NOT (AND (INTEGERP N)
                     (INTEGERP M)
                     (<= 0 N)
                     (<= N M)
                     (< M (LENGTH CHRONOLOGY))))
           (FORMAT T "~%Inappropriate args to CH.")
           NIL)
          (T
           (TERPRI)
           (ITERATE FOR I FROM 0 TO M
                    AS NAME IN CHRONOLOGY
                    WHEN (<= N I)
                    DO
                    (FORMAT T "~4D " I)
                    (SETQ EVENT (DATA-BASE 'EVENT-FORM NAME))
                    (COND ((DISABLEDP NAME)
                           (PRINC "D " T))
                          (T (PRINC "  " T)))
                    (PRINC (IF (> (LENGTH EVENT) 2)
                               (LIST (CAR EVENT)
                                     (CADR EVENT)
                                     '|...|)
                               EVENT)
                           T)
                    (TERPRI T))))))

(DEFUN CHK-ACCEPTABLE-CONSTRAIN (NAME TYPES TERM WITNESS-ALIST)

;   It is important that the function symbols being witnessed, i.e.,
;   the new function symbols, not occur in the terms in the range of
;   the substitution.  This is insured by our not binding ARITY-ALIST
;   until after the TRANSLATE on the range terms.

  (MATCH! (CHK-ACCEPTABLE-FUNCTIONAL-SUBSTITUTION WITNESS-ALIST T)
          (LIST WITNESS-ALIST))
  (LET ((ARITY-ALIST (APPEND
                      (ITERATE FOR DOUBLET IN WITNESS-ALIST
                               COLLECT
                               (CONS (CAR DOUBLET)
                                     (COND ((SYMBOLP (CADR DOUBLET))
                                            (ARITY (CADR DOUBLET)))
                                           (T (LENGTH
                                               (CADR (CADR DOUBLET)))))))
                      ARITY-ALIST)))
       (MATCH! (CHK-ACCEPTABLE-LEMMA NAME TYPES TERM)
               (LIST NAME TYPES TERM)))
  (OR (NO-DUPLICATESP (CONS NAME (ITERATE FOR DOUBLET IN WITNESS-ALIST
                                          COLLECT (CAR DOUBLET))))
      (ER SOFT NIL
          |it| |is| |illegal| |to| |use| |the| |name| |of| |a| |newly|
          |introduced| |function| |for| |the| |name| |of| |the| CONSTRAIN
          |event| |or| |to| |duplicate| |a| |new| |function| |in| |the|
          |witness| |alist| |of| |the| |constraint| |.|))
  (LIST NAME TYPES TERM WITNESS-ALIST))

(DEFUN CHK-ACCEPTABLE-DEFN (NAME ARGS BODY RELATION-MEASURE-LST)
  (LET ((ARITY-ALIST (CONS (CONS NAME (LENGTH-TO-ATOM ARGS)) ARITY-ALIST))
        FNS)
    (CHK-NEW-NAME NAME NIL)
    (CHK-NEW-*1*NAME NAME)
    (CHK-ARGLIST NAME ARGS)
    (COND ((> (LENGTH ARGS) 32)
           (ER SOFT (NAME) |Too| |many| |args| EXCL |because| |of| |our| |use|
               |of| |32-bit| |words| |to| |encode| |sets| |of| |recursion|
               |controllers| |we| |cannot| |accept| |functions| |,| |such| |as|
               (!PPR NAME (QUOTE |,|)) |with| |more| |than| 32 |arguments|
               |.|)))
    (SETQ BODY (TRANSLATE-AND-CHK BODY))
    (FREE-VAR-CHK NAME ARGS BODY)
    (COND ((EQ *1*THM-MODE$ (QUOTE THM))
           (SETQ FNS (INTERSECTION (QUOTE (APPLY$ EVAL$))
                                   (ALL-FNNAMES BODY)))
           (COND (FNS
                  (ER SOFT (FNS) |When| |not| |in| NQTHM |mode|
                      |it| |is| |prohibited|
                      |to| |use| |the| (PLURAL? FNS |functions| |function|)
                      (!LIST FNS) |in| |a| |definition| |.|)))))
    (SETQ RELATION-MEASURE-LST
          (ITERATE
           FOR X IN RELATION-MEASURE-LST
           WITH MEASURE
           COLLECT
           (COND ((NOT (AND (CONSP X)
                            (MEMBER-EQ (CAR X)
                                       (COND ((EQ *1*THM-MODE$ (QUOTE NQTHM))
                                              (QUOTE (LESSP ORD-LESSP)))
                                             (T (QUOTE (LESSP LEX2 LEX3)))))
                            (CONSP (CDR X))
                            (NULL (CDDR X))
                            (PROGN
                              (SETQ MEASURE (TRANSLATE-AND-CHK (CADR X)))
                              T)
                            (NVARIABLEP MEASURE)
                            (NOT (FQUOTEP MEASURE))
                            (SUBSETP-EQ (ALL-VARS MEASURE)
                                        ARGS)))
                  (ER SOFT NIL |Each| |member| |of| |the| |fourth| |argument|
                      |to| DEFN |must| |be| |of| |the| |form|
                      (!PPR (QUOTE (|rel| |term|)) (QUOTE |,|)) |where|
                      |rel| |is| |the| |name| |of| |a| |well-founded|
                      |relation| |and| |term| |is| |a| |non-variable| |,|
                      |non-QUOTE| |term| |all| |of|
                      |whose| |variables| |are| |among| |the| |formals| |of|
                      |the| |function| |being| |defined| |.|))
                 (T (LIST (CAR X) MEASURE)))))
    (LIST NAME ARGS BODY RELATION-MEASURE-LST)))

(DEFUN CHK-ACCEPTABLE-DCL (NAME ARGS)
  (CHK-ARGLIST NAME ARGS)
  (CHK-NEW-NAME NAME NIL)
  (CHK-NEW-*1*NAME NAME)
  (COND ((> (LENGTH ARGS) 32)
         (ER SOFT (NAME) |Too| |many| |args| EXCL
             |because| |of| |our| |use| |of|
             |32-bit| |words| |to| |encode| |sets| |of| |recursion|
             |controllers| |we| |cannot| |accept| |functions| |,| |such| |as|
             (!PPR NAME (QUOTE |,|)) |with| |more| |than| 32 |arguments|
             |.|)))
  (LIST NAME ARGS))

(DEFUN CHK-ACCEPTABLE-DEFTHEORY (NAME EVENTNAMES)
  (CHK-NEW-NAME NAME NIL)
  (COND
   ((NOT (AND (CONSP EVENTNAMES)
              (NULL (CDR (OUR-LAST EVENTNAMES)))))
    (ER SOFT (EVENTNAMES) |The| |second| |argument| |to| DEFTHEORY |should|
        |be| |a| |non-empty| |proper| |list| |,| |but| (!PPR EVENTNAMES NIL)
        |is| |not| |.|)))
  (ITERATE FOR EVENTNAME IN EVENTNAMES DO (CHK-DISABLEABLE EVENTNAME))
  (LIST NAME EVENTNAMES))

(DEFUN CHK-ACCEPTABLE-ELIM-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  TYPE
  (LET (LST ALLVARS LHS RHS DESTS)
    (SETQ LST (UNPRETTYIFY TERM))
    (COND ((NOT (AND LST (NULL (CDR LST))
                     (MATCH (CDAR LST) (EQUAL LHS RHS))
                     (VARIABLEP RHS)
                     (NVARIABLEP LHS)
                     (ITERATE FOR ARG IN (SARGS LHS)
                              THEREIS (NVARIABLEP ARG))))
           (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |unacceptable| ELIM
               |lemma| |because| |its| |conclusion| |is| |not| |an| |equality|
               |of| |the| |form| |(| EQUAL |term| |var)| |where| |term|
               |contains| |some| |non-variable| |arguments| |and| |var| |is|
               |a| |variable| |.|)))
    (SETQ ALLVARS (ALL-VARS TERM))
    (COND ((NOT (SETQ DESTS (DESTRUCTORS (LIST LHS))))
           (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |unacceptable| ELIM
               |lemma| |because| |the| |left| |hand| |side| |of| |the|
               |conclusion| |does| |not| |contain| |any| |terms| |of| |the|
               |form| |(| |fn| |var1| |var2| |...| |varn)| |where| |fn| |is|
               |a| |recursive| |function| |and| |the| |vari| |are| |all|
               |distinct| |variables| |.|))
          ((NOT (NO-DUPLICATESP (ITERATE FOR X IN DESTS COLLECT (FN-SYMB X))))
           (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |unacceptable| ELIM
               |lemma| |because| |the| |left| |hand| |side| |of| |the|
               |conclusion| |contains| |two| |or| |more| |destructor| |terms|
               |with| |the| |same| |function| |symbol| |.|))
          ((NOT (ITERATE FOR X IN DESTS ALWAYS (SUBSETP-EQ ALLVARS (SARGS X))))
           (ER SOFT (NAME) (!PPR NAME NIL) |is| |not| |an| |acceptable| ELIM
               |lemma| |because| |some| |of| |the| |destructor| |nests| |do|
               |not| |mention| |all| |of| |the| |variables| |in| |the| |lemma|
               |.|))
          ((OCCUR RHS (SUB-PAIR-EXPR
                       DESTS
                       (MAKE-LIST (LENGTH DESTS) :INITIAL-ELEMENT TRUE)
                       LHS))
           (ER SOFT (NAME RHS DESTS) (!PPR NAME NIL) |is| |an| |unacceptable|
               ELIM |lemma| |because| |the| |right-hand| |side| |of| |the|
               |conclusion| |,| (!TERM RHS (QUOTE |,|)) |occurs| |in| |the|
               |left-hand| |side| |in| |places| |other| |than| |the|
               |destructor| (PLURAL? DESTS |terms| |term|)
               (!TERM-LIST DESTS (QUOTE |.|))))
          (T (ITERATE
              FOR X IN DESTS
              WHEN (GET (CAR X) (QUOTE ELIMINATE-DESTRUCTORS-DESTS))
              DO (ER SOFT (X) |We| |do| |not| |know| |how| |to| |handle|
                     |multiple| |elimination| |lemmas| |for| |the| |same|
                     |function| |symbol| |,| |e.g.,|
                     (!PPR (CAR X) (QUOTE |.|))))))
    NIL))

(DEFUN CHK-ACCEPTABLE-FUNCTIONAL-SUBSTITUTION (WITNESS-ALIST FLG)

;   If FLG is T we additionally check that symbols in the domain are
;   all new and that the LAMBDA expressions in the range contain no
;   free vars.

;   If FLG in NIL we additionally check that the symbols in the domain
;   are not introduced by BOOT-STRAP and that the arities of the
;   symbols in the domain are the arities of the corresponding symbols
;   in the range.

  (LET (ARGS BODY FN1 FN2)
       (COND ((CDR (OUR-LAST WITNESS-ALIST))
              (ER SOFT (WITNESS-ALIST) |witness| |alists| |must| |be| |proper|
                  |and| (!PPR WITNESS-ALIST NIL) |is| |not| |.|)))
       (LIST
        (ITERATE FOR DOUBLET IN WITNESS-ALIST
                 COLLECT
                 (PROGN
                  (OR (MATCH DOUBLET (LIST FN1 FN2))
                      (ER SOFT (DOUBLET) |each| |element| |of| |a| |witness|
                          |alist| |must| |be| |a| |doublet| |and|
                          (!PPR DOUBLET NIL) |is| |not| |.|))
                  (COND ((SYMBOLP FN2)
                         (OR (ARITY FN2)
                             (ER SOFT (DOUBLET) |the| |second| |component| |of|
                                 |the| |doublet| (!PPR DOUBLET NIL) |is| |not|
                                 |an| |old| |function| |symbol| |.|)))
                        ((MATCH FN2 (LAMBDA ARGS BODY))
                         (CHK-ARGLIST FN2 ARGS)
                         (SETQ BODY (TRANSLATE-AND-CHK BODY))
                         (OR (NULL FLG)
                             (SUBSETP-EQ (ALL-VARS BODY) ARGS)
                             (ER SOFT (FN2) |the| |body| |of| |the| LAMBDA
                                 |expression| (!PPR FN2 NIL) |contains|
                                 |variables| |other| |than| |the| |formals|
                                 |.|)))
                        (T (ER SOFT (FN2) (!PPR FN2 NIL) |is| |neither| |an|
                               |old| |function| |symbol| |nor| |a| LAMBDA
                               |expression| |.|)))
                  (COND (FLG (CHK-NEW-NAME FN1 NIL)
                             (CHK-NEW-*1*NAME FN1))
                        (T (OR (SYMBOLP FN1)
                               (ER SOFT (FN1) |functional| |substitutions|
                                   |must| |hit| |only| |function| |symbols|
                                   |and| (!PPR FN1 NIL) |is| |not| |one| |.|))
                           (OR (NOT
                                (OR (EQ (MAIN-EVENT-OF FN1) 'GROUND-ZERO)
                                    (EQ (CAR (GET (MAIN-EVENT-OF FN1) 'EVENT))
                                        'ADD-SHELL)))
                               (ER SOFT (FN1) |It| |is| |intolerable| |to|
                                   |substitute| |for| |a| |primitive|
                                   |function| |symbol| |such| |as|
                                   (!PPR FN1 '|.|)))
                           (OR (EQUAL (ARITY FN1)
                                      (COND ((SYMBOLP FN2) (ARITY FN2))
                                            (T (LENGTH (CADR FN2)))))
                               (ER SOFT (FN1 FN2) |The| |arity| |of|
                                   |each| |function| |in| |the| |domain|
                                   |of| |a| |functional| |substitution|
                                   |must| |be| |the| |same| |as| |the|
                                   |arity| |of| |the| |corresponding|
                                   |member| |of| |the| |range| |,| |but|
                                   |the| |arity| |of| (!PPR FN1 NIL)
                                   |is| |not| |that| |of| 
                                   (!PPR FN2 '|.|)))))
                  (COND ((SYMBOLP FN2)
                         DOUBLET)
                        (T (LIST FN1 (LIST 'LAMBDA ARGS BODY)))))))))

(DEFUN CHK-ACCEPTABLE-FUNCTIONALLY-INSTANTIATE
  (NAME TYPES TERM OLD-NAME-OR-LIST FS)

; This checker returns more than just the translated args:  it returns
; the uninstantiated constraints to be satisfied.  We have to look at the
; constraints to guarantee that the free-vars in the FS do not occur
; in the uninstantiated constraints.  The reason for this bizarre requirement
; is that it is a condition on the theorem that the functional instantiation
; of an instance of a formula thm is a theorem provided the functional
; instantiation of thm is a theorem.  For example, let thm be (EQUAL X (BAR)).
; Let FS be {(BAR (LAMBDA () X))}.  Then thm\FS is a theorem, namely 
; (EQUAL X X).  But thm/{(x 2)}\FS is not a theorem, (EQUAL 2 X).

; See definition of AVAILABLE-EVENT-FS-PAIRS-ALIST for the form of 
; old-name-or-list.

  (LET (CONSTRAINT FREE-VARS INST
                   CONSTRAINT-NAMES CONSTRAINT-LIST EVENT-FS-ALIST FS-1
                   PRECEDING-FI-EVENTS
                   (OLD-NAME (IF (CONSP OLD-NAME-OR-LIST)
                                 (CAR OLD-NAME-OR-LIST)
                                 OLD-NAME-OR-LIST)))
       (OR (SYMBOLP OLD-NAME-OR-LIST)
           (AND (CONSP OLD-NAME-OR-LIST)
                (NULL (CDR (OUR-LAST OLD-NAME-OR-LIST)))
                (ITERATE FOR X IN (CDR OLD-NAME-OR-LIST)
                         ALWAYS (OR (AND (SYMBOLP X)
                                         (EQ (CAR (GET X 'EVENT))
                                             'FUNCTIONALLY-INSTANTIATE))
                                    (ER SOFT (X) |When| |the| |fourth|
                                        |argument| |to|
                                        FUNCTIONALLY-INSTANTIATE |is|
                                        |a| |list| |,| |all| |but| |the|
                                        |first| |member| |must| |be| |names|
                                        |of| FUNCTIONALLY-INSTANTIATE |events|
                                        |,| |but| (!PPR X NIL) |is| |not|
                                        |.|))))
           (ER SOFT (OLD-NAME-OR-LIST) |The| |fourth| |argument| |to|
               FUNCTIONALLY-INSTANTIATE |must| |be| |either| |a| |symbol|
               |(which| |names| |a| |previous| |event)| |or| |else| |a|
               |list| |of| |names| |,| |the| |first| |of| |which| |is|
               |the| |name| |of| |a| |previous| |event| |and| |the|
               |rest| |of| |which| |are| |previous| FUNCTIONALLY-INSTANTIATE
               |events| |,| |but| (!PPR OLD-NAME-OR-LIST NIL) |is| |not| |.|))
       (OR (AND (SYMBOLP OLD-NAME)
                (FORMULA-OF OLD-NAME))
           (ER SOFT (OLD-NAME) |The| |reference| |for|
               |a| FUNCTIONALLY-INSTANTIATE |event| |must| |be| |an|
               |event| |with| |a| |formula| |.|
               (!PPR OLD-NAME NIL) |is| |not| |.|))
       (MATCH (CHK-ACCEPTABLE-FUNCTIONAL-SUBSTITUTION FS NIL)
              (LIST FS))
       (SETQ FS-1
             (ITERATE FOR DOUBLET IN FS COLLECT
                      (CONS (CAR DOUBLET) (CADR DOUBLET))))
       (SETQ INST (SUBLIS-FN FS-1 (FORMULA-OF OLD-NAME)))
       (COND ((EQ TERM '*AUTO*) (SETQ TERM INST)))
       (MATCH! (CHK-ACCEPTABLE-LEMMA NAME TYPES TERM)
               (LIST NAME TYPES TERM))
       (OR (EQUAL TERM INST)
           (ER SOFT (TERM INST)
               |The| |formula| |of| |a| FUNCTIONALLY-INSTANTIATE
               |must| |be| |identical| |to| |the| |formula| |of| |the|
               |conclusion| |referenced| |after| |the| |substitution|
               |has| |been| |applied|  |.| |However| |,| |in| |this|
               |case| |the| |instantiated| |conclusion| |referenced| |is|
               (!TERM INST NIL) |,| |which| |is| |not| |the| |same| |as|
               |the| |given| |term| (!TERM TERM NIL) |.|))
       (SETQ CONSTRAINT-NAMES (RELEVANT-EVENTS (FORMULA-OF OLD-NAME) FS))
       (SETQ CONSTRAINT-LIST
             (ITERATE FOR X IN CONSTRAINT-NAMES
                      COLLECT
                      (HITABLE-AXIOM-INTRODUCED-BY X)))
       (ITERATE FOR DOUBLET IN FS
                WHEN (NOT (SYMBOLP (CADR DOUBLET)))
                DO
                (SETQ FREE-VARS
                      (UNION-EQ
                       (SET-DIFF (ALL-VARS (CADDR (CADR DOUBLET)))
                                 (CADR (CADR DOUBLET)))
                       FREE-VARS)))
       (OR (NOT (INTERSECTP FREE-VARS (ALL-VARS-lst CONSTRAINT-list)))
           (ER SOFT ((C (DUMB-CONJOIN CONSTRAINT-LIST))
                     (INT (INTERSECTION-EQ FREE-VARS
                                           (ALL-VARS CONSTRAINT))))
               |It| |is| |not| |permitted| |for| |the| |free|
               |variables| |in| |the| LAMBDA |expressions|
               |of| |a| |substitution| |to| |occur| |in| |the|
               |contraints| |,| |but| |the| |free|
               (PLURAL? INT |variables| |variable|) (!LIST INT)
               (PLURAL? INT |occur| |occurs|) |in| |the|
               |constraint| (!TERM C '|.|)))
       (SETQ CONSTRAINT
             (DUMB-CONJOIN
              (ITERATE
               FOR NAME IN CONSTRAINT-NAMES
               AS TERM IN CONSTRAINT-LIST
               FOR LOCAL-FS = (MAKE-LOCAL-FS FS TERM)
               WITH FI-EVENT AND
               AVAILABLE-EVENT-FS-PAIRS-ALIST =
               (AVAILABLE-EVENT-FS-PAIRS-ALIST OLD-NAME-OR-LIST)
               DO
               (IF (SETQ FI-EVENT
                         (EVENT-THAT-PROVED-CONSTRAINT
                          NAME LOCAL-FS AVAILABLE-EVENT-FS-PAIRS-ALIST))
                   (SETQ PRECEDING-FI-EVENTS
                         (ADD-TO-SET-EQ FI-EVENT PRECEDING-FI-EVENTS))
                   (PUSH (CONS NAME LOCAL-FS) EVENT-FS-ALIST))
               WHEN (NULL FI-EVENT)
               COLLECT (SUBLIS-FN FS-1 TERM))))
       (LIST NAME TYPES TERM OLD-NAME FS CONSTRAINT EVENT-FS-ALIST
             PRECEDING-FI-EVENTS)))

(DEFUN CHK-ACCEPTABLE-GENERALIZE-LEMMA

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (NAME TYPE TERM) NAME TYPE TERM T)

(DEFUN CHK-ACCEPTABLE-HINTS (HINTS)
  (COND ((OR (AND (ATOM HINTS)
                  HINTS)
             (CDR (OUR-LAST HINTS)))
         (ER SOFT (HINTS) |The| HINTS |argument| |must|
             |be| |a| |proper| |list| |but| (!PPR HINTS NIL) |is| |not| |.|)))
  (ITERATE FOR X IN HINTS
           WITH HINT-NAMES
           DO
           (COND
            ((OR (ATOM X)
                 (CDR (OUR-LAST X)))
             (ER SOFT (X) |each| |element| |of| |the| HINTS |argument| 
                 |must| |be| |a| |non-NIL| |proper| |list| |but|
                 (!PPR X NIL) |is| |not| |.|))
            ((MEMBER-EQ (CAR X) HINT-NAMES)
             (ER SOFT ((Y (CAR X))) |There| |are| |two| (!PPR Y NIL) |hints|
                 EXCL))
            (T (SETQ HINT-NAMES (CONS (CAR X) HINT-NAMES)))))
  (COND
   ((AND (EQUAL (ASSOC-EQ (QUOTE ENABLE-THEORY) HINTS)
                (QUOTE (ENABLE-THEORY T)))
         (EQUAL (ASSOC-EQ (QUOTE DISABLE-THEORY) HINTS)
                (QUOTE (DISABLE-THEORY T))))
    (ER SOFT NIL |It| |does| |not| |make| |sense| |both| |to| |enable|
        |everything| |and| |to| |disable| |everything| |,| |as| |you| |have|
        |done| |with| |the| |hints| |(ENABLE-THEORY T)| |and|
        |(DISABLE-THEORY T)| EXCL)))
  (LIST
   (ITERATE
    FOR X IN HINTS WITH TERM
    COLLECT
      (CASE
       (CAR X)
       (USE
        (CONS (QUOTE USE)
              (ITERATE FOR PAIR IN (CDR X)
                       WITH ALIST
                       COLLECT
                       (COND
                        ((AND (CONSP PAIR)
                              (SYMBOLP (CAR PAIR))
                              (FORMULA-OF (CAR PAIR))
                              (NULL (CDR (OUR-LAST PAIR)))
                              (PROGN
                                (SETQ ALIST
                                      (ITERATE FOR X IN (CDR PAIR)
                                               COLLECT
                                               (COND ((AND (CONSP X)
                                                           (CONSP (CDR X))
                                                           (NULL (CDDR X)))
                                                      (LIST
                                                       (TRANSLATE (CAR X))
                                                       (TRANSLATE-AND-CHK
                                                        (CADR X))))
                                                     (T X))))
                               T)
                              (ITERATE FOR X IN ALIST
                                       ALWAYS
                                       (AND (CONSP X)
                                            (CONSP (CDR X))
                                            (NULL (CDDR X))
                                            (VARIABLEP (CAR X))))
                              (NO-DUPLICATESP
                               (ITERATE FOR X IN ALIST COLLECT (CAR X))))
                         (CONS (CAR PAIR) ALIST))
                        (T (ER SOFT
                               ((H (QUOTE
                                    (USE (|event1| (|v1| |t1|) |...|
                                          (|vn| |tn|))
                                         |...|
                                         (|eventk| (|vk| |tk|) |...|
                                          (|vm| |tm|)))))
                                PAIR)
                               |the| USE |hint| |must| |have| |the| |form|
                               (!PPR H NIL) |where| |each| |eventi| |is| |the|
                               |name| |of| |an| ADD-AXIOM |,| CONSTRAIN |,|
                               DEFN |,| FUNCTIONALLY-INSTANTIATE |,| |or|
                               PROVE-LEMMA |event| |,| |each| |vi| |is| |a|
                               |variable| |name| |,| |no| |vi| |occurs| |twice|
                               |,| |and| |each| |ti| |is|
                               |a| |term| |.| |the| |entry|
                               (!PPR PAIR NIL) |is| |thus| |unacceptable|
                               |.|))))))
       (EXPAND
        (CONS (QUOTE EXPAND)
              (ITERATE FOR X IN (CDR X)
                       APPEND
                       (PROGN (SETQ X (TRANSLATE-AND-CHK X))
                              (COND ((AND (NVARIABLEP X)
                                          (NOT (FQUOTEP X))
                                          (GET (FFN-SYMB X) (QUOTE SDEFN)))
                                     (COND
                                      ((FNNAMEP 'IDENTITY X)
                                       (LET ((XR (REMOVE-IDENTITY X T)))
                                         (IF (AND (NOT (EQUAL XR X))
                                                  (NVARIABLEP XR)
                                                  (NOT (FQUOTEP XR))
                                                  (GET (FFN-SYMB XR)
                                                       (QUOTE SDEFN)))
                                             (LIST X XR)
                                           (LIST X))))
                                      (T (LIST X))))
                                    (T (ER SOFT (X) |every| |element| |of| |an|
                                           EXPAND |hint| |must| |be| |an|
                                           |application| |of| |a| |defined|
                                           |function| |to| |some|
                                           |arguments| |and|
                                           (!TERM X NIL) |is| |not| |.|)))))))
       ((DISABLE ENABLE)
        (ITERATE FOR X IN (CDR X) DO (CHK-DISABLEABLE X))
        X)
       (HANDS-OFF
        (ITERATE FOR X IN (CDR X) DO
                 (OR (AND (SYMBOLP X)
                          (GET X 'TYPE-PRESCRIPTION-LST))
                     (ER SOFT (X) |every| |element| |of| |a|
                         HANDS-OFF |hint| |must| |be| |a|
                         |known| |function| |symbol| |and|
                         (!TERM X NIL) |is| |not| |.|)))
        X)
       ((DISABLE-THEORY ENABLE-THEORY)
        (COND ((NULL (CDR X))
               (ER SOFT ((Y (CAR X))) |The| (!PPR Y NIL) |hint| |must| |take|
                   |at| |least| |one| |argument| |.|))
              ((MEMBER-EQ T (CDR X))
               (OR (NULL (CDDR X))
                   (ER SOFT ((Y (CAR X))) |The| (!PPR Y NIL) |hint| |must|
                       |take| |either| |the| |single| |argument| |T| |or|
                       |else| |a| |list| |of| |names| |.|)))
              (T
               (ITERATE FOR NAME IN (CDR X) DO
                        (OR (THEORYP NAME)
                            (ER SOFT (NAME) (!PPR NAME NIL) |is| |neither|
                                |GROUND-ZERO| |nor| |the| |name| |of|
                                |a| DEFTHEORY |event| |.|)))))
        X)
       (INDUCT
        (COND ((AND (CONSP (CDR X))
                    (NULL (CDDR X))
                    (PROGN (SETQ TERM (TRANSLATE (CADR X))) T)
                    (NVARIABLEP TERM)
                    (NOT (FQUOTEP TERM))
                    (GET (FFN-SYMB TERM) (QUOTE JUSTIFICATIONS))
                    (GET (FFN-SYMB TERM) (QUOTE INDUCTION-MACHINE))
                    (GET (FFN-SYMB TERM) (QUOTE SDEFN))
                    (ITERATE FOR X IN (FARGS TERM) ALWAYS (VARIABLEP X))
                    (NO-DUPLICATESP (FARGS TERM)))
               (LIST (QUOTE INDUCT) TERM))
              (T (ER SOFT
                     ((H (QUOTE (INDUCT (|fn| |v1| |...| |vn|))))
                      X)
                     |The| INDUCT |hint| |must| |have| |the| |form|
                     (!PPR H NIL) |where| |fn| |is| |a| |recursively|
                     |defined| |function| |and| |the| |vi| |are|
                     |distinct| |variables| |.| |Thus| |,| (!PPR X NIL)
                     |is| |an| |inappropriate| INDUCT |hint| |.|))))
       (OTHERWISE
        (COND ((ASSOC-EQ (CAR X) HINT-VARIABLE-ALIST)
               (COND ((CADDR (ASSOC-EQ (CAR X) HINT-VARIABLE-ALIST))
                      (CONS (CAR X)
                            (ITERATE FOR Y IN (CDR X)
                                     COLLECT (TRANSLATE-AND-CHK Y))))
                     (T X)))
              (T
               (ER SOFT (X
                         (Y (NCONC (ITERATE FOR X IN HINT-VARIABLE-ALIST
                                            COLLECT (CAR X))
                                   '(ENABLE-THEORY DISABLE-THEORY
                                                   USE INDUCT))))
                   (!PPR X NIL) |is| |an| |unrecognized|
                   |hint| |.| |the| |recognized| |hints|
                   |are| (!LIST Y) |.|))))))))

(DEFUN CHK-ACCEPTABLE-LEMMA (NAME TYPES TERM)
  (CHK-NEW-NAME NAME NIL)
  (SETQ TERM (TRANSLATE-AND-CHK TERM))
  (COND ((OR (AND (ATOM TYPES) TYPES)
             (CDR (OUR-LAST TYPES)))
         (ER SOFT (TYPES) |The| |lemma| |types| |argument| |must| |be|
             |a| |proper| |list| |and| (!PPR TYPES NIL) |is| |not| |.|)))
  (ITERATE FOR TYPE IN TYPES
           DO (COND ((MEMBER-EQ (COND ((CONSP TYPE) (CAR TYPE))
                                      (T TYPE))
                                LEMMA-TYPES)
                     (FUNCALL (PACK (LIST (QUOTE CHK-ACCEPTABLE-)
                                          (COND ((CONSP TYPE) (CAR TYPE))
                                                (T TYPE))
                                          (QUOTE -)
                                          (QUOTE LEMMA)))
                              NAME TYPE TERM))
                    (T (ER SOFT (TYPE LEMMA-TYPES) (!PPR TYPE NIL) |is| |not|
                           |among| |the| |legal| |types| |,| |viz.| |,|
                           (!LIST LEMMA-TYPES) |.|))))
  (LIST NAME TYPES TERM))

(DEFUN CHK-ACCEPTABLE-META-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  (LET (FLG1 FLG2 FN1 A1 V2 A2 V1)
    (COND ((AND (NOT IN-ADD-AXIOM-FLG) NONCONSTRUCTIVE-AXIOM-NAMES)
           (ER WARNING ((LST NONCONSTRUCTIVE-AXIOM-NAMES)) META |lemmas| |must|
               |be| |proved| |in| |a| |constructive| |history| |.| |The|
               |current| |history| |contains| |the| |nonconstructive|
               (PLURAL? LST |axioms| |axiom|) (!LIST LST) |.| |If| |this|
               |metalemma| |is| |proved| |using| |unsound| |axioms| |you| |may|
               |get| |wiped| |out| |by| |the| |application| |of| |the|
               |metafunction| |.|)))
    (COND
     ((NOT
       (AND (MATCH TERM
                   (EQUAL (EVAL$ FLG2 V2 A2)
                          (EVAL$ FLG1 (LIST FN1 V1) A1)))
            (EQUAL FLG2 FLG1)
            (QUOTEP FLG1)
            (NOT (EQ (CADR FLG1) (QUOTE LIST)))
            (NOT (EQ FN1 (QUOTE QUOTE)))
            (TOTALP FN1)
            (VARIABLEP V1)
            (EQ V1 V2)
            (VARIABLEP A1)
            (EQ A1 A2)
            (NOT (EQ V1 A1))))
      (ER SOFT
          ((X (QUOTE (EQUAL (EVAL$ T |v| |a|) (EVAL$ T (|fn| |v|) |a|))))
           NAME)
          META |lemmas| |have| |to| |have| |the| |form| (!PPR X NIL) |where|
          |v| |and| |a| |are| |distinct| |variables| |and| |fn| |is| |a|
          |total| |function| |.| (!PPR NAME NIL) |does| |not| |have| |this|
          |form| |.|))
     ((NOT (AND (MATCH TYPE (CONS (QUOTE META) FNS))
                (ITERATE FOR FN IN FNS
                         ALWAYS (AND (SYMBOLP FN)
                                     (GET FN
                                          (QUOTE
                                           TYPE-PRESCRIPTION-LST))))))
      (ER SOFT
          ((X (QUOTE (META |fn1| |fn2| |...| |fnn|)))
           TYPE)
          META |lemmas| |must| |be| |stored| |under| |one| |or| |more|
          |functions| |named| |by| |the| |user| |in| |a| |lemma| |type|
          |of| |the| |form| (!PPR X NIL) |where| |the| |fni| |are|
          |function| |names| |.| (!PPR TYPE NIL) |is| |not| |of| |this|
          |form| |.|)))
    T))

(DEFUN CHK-ACCEPTABLE-REWRITE-LEMMA (NAME TYPE TERM)

;   This function is FUNCALLed and therefore may not be made a MACRO.

  TYPE
  (LET ((TYPE-COUNT 0)
        (COMPOUND-COUNT 0)
        (LINEAR-COUNT 0)
        (REPLACEMENT-COUNT 0))
       (ITERATE
        FOR X IN (UNPRETTYIFY (REMOVE-IDENTITY TERM T))
        WITH (TOP-FNNAME-VAR REWRITE-RULE LHS ALL-VARS-HYPS ALL-VARS-CONCL
                             MAX-TERMS LST HYPS CONCL)
        DO
        (PROGN
         (SETQ HYPS (CAR X))
         (SETQ CONCL (CDR X))
         (SETQ TOP-FNNAME-VAR (TOP-FNNAME CONCL))
         (COND ((ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP HYPS CONCL)
                (INCF TYPE-COUNT)
                T)
               ((ACCEPTABLE-COMPOUND-RECOGNIZER-LEMMAP HYPS CONCL)
                (INCF COMPOUND-COUNT)
                T)
               ((NULL TOP-FNNAME-VAR)
                (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |unacceptable|
                    REWRITE |lemma| |because| |it| |rewrites| |a| |variable|
                    |.|))
               ((EQ TOP-FNNAME-VAR (QUOTE IF))
                (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |unacceptable|
                    REWRITE |lemma| |because| |it| |rewrites| |an|
                    |IF-expression| |.|))
               ((FQUOTEP CONCL) NIL)
               ((AND (NOT NO-BUILT-IN-ARITH-FLG)
                     (OR (MATCH CONCL (NOT (LESSP & &)))
                         (MATCH CONCL (LESSP & &))))
                (SETQ LST (EXTERNAL-LINEARIZE CONCL T))
                (COND ((OR (NOT (AND LST (NULL (CDR LST))))
                           (NOT (AND (CAR LST) (NULL (CDAR LST)))))
                       (ER HARD NIL LINEARIZE |returned| |a| |list| |of| |more|
                           |than| |one| |thing| |,| |even| |though| |called|
                           |on| |a| LESSP |atom| EXCL)))
                (SETQ ALL-VARS-HYPS (ALL-VARS-LST HYPS))
                (SETQ ALL-VARS-CONCL (ALL-VARS CONCL))
                (SETQ MAX-TERMS
                      (ITERATE FOR PAIR IN (ACCESS POLY ALIST (CAR (CAR LST)))
                               WHEN
                               (AND (NVARIABLEP (CAR PAIR))
                                    (SUBSETP-EQ ALL-VARS-CONCL
                                                (UNION-EQ (ALL-VARS (CAR PAIR))
                                                          ALL-VARS-HYPS))
                                    (ITERATE FOR PAIR2 IN
                                             (ACCESS POLY ALIST
                                                     (CAR (CAR LST)))
                                             WHEN (NOT (EQ PAIR2 PAIR))
                                             NEVER
                                             (AND (< (FORM-COUNT (CAR PAIR))
                                                     (FORM-COUNT (CAR PAIR2)))
                                                  (SUBBAGP
                                                   (ALL-VARS-BAG (CAR PAIR))
                                                   (ALL-VARS-BAG
                                                    (CAR PAIR2))))))
                               COLLECT (CAR PAIR)))
                (COND ((NULL MAX-TERMS)
                       (ER SOFT (NAME) (!PPR NAME NIL) |is| |an|
                           |unacceptable| REWRITE |lemma| |because| |the|
                           |atom| |of| |its| |conclusion| |is| |a| LESSP |and|
                           |it| |cannot| |be| |handled| |by| |our| |linear|
                           |arithmetic| |package| |.| |to| |be| |acceptable|
                           |,| |at| |least| |one| |nonvariable| |addend| |of|
                           |the| |conclusion| |must| |satisfy| |two|
                           |properties.| |First| |,| |it| |must|
                           |contain| |all| |the| |variables| |of| |the| |lemma|
                           |that| |are| |not| |in| |the| |hypotheses| |.|
                           |Second| |,| |it| |must| |not| |be| |the| |case|
                           |that| |under| |every| |substitution| |,| |the|
                           |term| |is| |smaller| |than| |another| |addend| |of|
                           |the| |conclusion.| |.|)))
                (ITERATE FOR X IN MAX-TERMS
                         WHEN (NON-RECURSIVE-DEFNP (FFN-SYMB X))
                         DO (ER WARNING (NAME X (FN (FFN-SYMB X)))
                                |Note| |that| |the| |linear| |lemma|
                                (!PPR NAME NIL) |is| |being| |stored| |under|
                                |the| |term| (!TERM X (QUOTE |,|)) |which| |is|
                                |unusual| |because| (!PPR FN NIL) |is| |a|
                                |nonrecursive| |function| |symbol| |.|))
                (ITERATE
                 FOR X IN MAX-TERMS WHEN (NOT (SUBSETP-EQ ALL-VARS-HYPS
                                                          (ALL-VARS X)))
                 DO
                 (ER WARNING
                     (X NAME
                        (VARS (SET-DIFF ALL-VARS-HYPS (ALL-VARS X)))
                        (LST (ITERATE FOR HYP IN HYPS
                                      WITH VARS = (SET-DIFF ALL-VARS-HYPS
                                                            (ALL-VARS X))
                                      WHEN (INTERSECTP VARS (ALL-VARS HYP))
                                      COLLECT
                                      (PROGN (SETQ VARS
                                                   (SET-DIFF VARS
                                                             (ALL-VARS HYP)))
                                             HYP))))
                     |When| |the| |linear| |lemma| (!PPR NAME NIL) |is|
                     |stored| |under| (!TERM X NIL) |it|
                     |contains| |the| |free|
                     (PLURAL? VARS |variables| |variable|)
                     (!LIST VARS) |which| |will| |be| |chosen| |by|
                     |instantiating| |the|
                     (PLURAL? LST |hypotheses| |hypothesis|)
                     (!TERM-LIST LST (QUOTE |.|))))
                (INCF LINEAR-COUNT (LENGTH MAX-TERMS))
                T)
               (T (SETQ REWRITE-RULE (CREATE-REWRITE-RULE NAME HYPS CONCL NIL))
                  (SETQ ALL-VARS-HYPS (ALL-VARS-LST HYPS))
                  (SETQ ALL-VARS-CONCL (ALL-VARS (COND ((MATCH CONCL
                                                               (EQUAL LHS &))
                                                        LHS)
                                                       (T CONCL))))
                  (COND ((NON-RECURSIVE-DEFNP (TOP-FNNAME CONCL))
                         (ER WARNING (NAME (FN (TOP-FNNAME CONCL)))
                             |Note| |that| |the| |rewrite| |rule|
                             (!PPR NAME NIL) |will| |be| |stored| |so| |as|
                             |to| |apply| |only| |to| |terms| |with| |the|
                             |nonrecursive| |function| |symbol|
                             (!PPR FN (QUOTE |.|)))))
                  (COND ((NOT (SUBSETP-EQ ALL-VARS-HYPS ALL-VARS-CONCL))
                         (ER WARNING
                             (NAME
                              (VARS (SET-DIFF ALL-VARS-HYPS ALL-VARS-CONCL))
                              (LST  (ITERATE FOR HYP IN HYPS
                                             WITH VARS =
                                             (SET-DIFF ALL-VARS-HYPS
                                                       ALL-VARS-CONCL)
                                             WHEN (INTERSECTP VARS
                                                              (ALL-VARS HYP))
                                             COLLECT
                                             (PROGN
                                              (SETQ VARS
                                                    (SET-DIFF VARS
                                                              (ALL-VARS HYP)))
                                              HYP))))
                             |Note| |that| (!PPR NAME NIL) |contains| |the|
                             |free| (PLURAL? VARS |variables| |variable|)
                             (!LIST VARS) |which| |will| |be| |chosen| |by|
                             |instantiating| |the|
                             (PLURAL? LST |hypotheses| |hypothesis|)
                             (!TERM-LIST LST (QUOTE |.|))))
                        ((AND (ATTEMPT-TO-REWRITE-RECOGNIZER CONCL) HYPS)
                         (ER WARNING (NAME) (!PPR NAME NIL) |will| |slow|
                             |down| |the| |theorem-prover| |because| |it|
                             |will| |cause| |backward| |chaining| |on| |every|
                             |instance| |of| |a| |primitive| |type|
                             |expression| |.|)))
                  (ITERATE FOR OLD-RULE IN (GET (TOP-FNNAME CONCL)
                                                (QUOTE LEMMAS))
                           UNLESS (OR (DISABLEDP
                                       (ACCESS REWRITE-RULE NAME OLD-RULE))
                                      (META-LEMMAP OLD-RULE))
                           DO (COND ((SUBSUMES-REWRITE-RULE OLD-RULE
                                                            REWRITE-RULE)
                                     (ER WARNING
                                         (NAME (OLDNAME (ACCESS REWRITE-RULE
                                                                NAME
                                                                OLD-RULE)))
                                         |the| |previously| |added| |lemma| |,|
                                         (!PPR OLDNAME (QUOTE |,|)) |could|
                                         |be| |applied| |whenever| |the|
                                         |newly| |proposed| (!PPR NAME NIL)
                                         |could| EXCL))
                                    ((SUBSUMES-REWRITE-RULE REWRITE-RULE
                                                            OLD-RULE)
                                     (ER WARNING
                                         (NAME (OLDNAME (ACCESS REWRITE-RULE
                                                                NAME
                                                                OLD-RULE)))
                                         |the| |newly| |proposed| |lemma| |,|
                                         (!PPR NAME (QUOTE |,|))
                                         |could| |be| |applied| |whenever|
                                         |the| |previously| |added| |lemma|
                                         (!PPR OLDNAME NIL) |could| |.| CR
                                         CR))))
                  (INCF REPLACEMENT-COUNT)
                  T))))
       (IF (AND (NOT IN-ADD-SHELL0)
                (NOT IN-BOOT-STRAP-FLG)
                (NOT (AND (= REPLACEMENT-COUNT 1)
                          (= TYPE-COUNT 0)
                          (= COMPOUND-COUNT 0)
                          (= LINEAR-COUNT 0))))
           (ER WARNING
               (NAME REPLACEMENT-COUNT TYPE-COUNT COMPOUND-COUNT LINEAR-COUNT)
               |Note| |that| |the| |proposed| |lemma|
               (!PPR NAME NIL) |is| |to| |be| |stored| |as|
               (@ TYPE-COUNT) |type| |prescription|
               (PLURAL? TYPE-COUNT |rules| |rule|) |,|
               (@ COMPOUND-COUNT) |compound| |recognizer|
               (PLURAL? COMPOUND-COUNT |rules| |rule|) |,|
               (@ LINEAR-COUNT) |linear|
               (PLURAL? LINEAR-COUNT |rules| |rule|) |,| |and|
               (@ REPLACEMENT-COUNT) |replacement|
               (PLURAL? REPLACEMENT-COUNT |rules| |rule|) |.|))))

(DEFUN CHK-ACCEPTABLE-SET-STATUS (NAME NAMES ALIST)
  (CHK-NEW-NAME NAME NIL)
  (COND ((OR (EQ NAMES T)
             (THEORYP NAMES)
             (NULL NAMES)
             (AND (CONSP NAMES)
                  (NULL (CDR (OUR-LAST NAMES)))
                  (PROGN (ITERATE FOR X IN NAMES DO (CHK-DISABLEABLE X))
                         T))
             (AND (CONSP NAMES)
                  (SYMBOLP (CAR NAMES))
                  (GET (CAR NAMES) 'EVENT)
                  (SYMBOLP (CDR NAMES))
                  (GET (CDR NAMES) 'EVENT)))
         NIL)
        (T (ER SOFT (NAMES)
               |the| |second| |argument| |to| SET-STATUS |must| |be|
               T |,| |the| |name| |of| |a| |theory| |,| |a| |list| |of|
               |citizen| |names| |,| |or| |a| |pair| |,| |(name1 . name2)|
               |,| |of| |two| |event| |names| |.| (!PPR NAMES NIL) |is|
               |none| |of| |these| |.|)))
  (CHK-STATUS-ALIST ALIST)
  (LIST NAME NAMES ALIST))

(DEFUN CHK-ACCEPTABLE-SHELL
  (SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)
  (LET (DESTRUCTOR-NAMES NAMES AXIOM-NAMES AC DV TR L FLG)

;   Check that there is a type no available.

    (NEXT-AVAILABLE-TYPE-NO)
    (ITERATE FOR TUPLE IN DESTRUCTOR-TUPLES
             UNLESS (MATCH TUPLE (LIST & & &))
             DO (ER SOFT NIL |The| DESTRUCTOR-TUPLES |argument| |to| ADD-SHELL
                    |must| |be| |a| |list| |of| |triples| |of| |the| |form|
                    (!PPR (QUOTE (|name| (|flg| |recognizer| |...|)
                                         |default-fn-symb|))
                          NIL)
                    |where| |name| |is| |the| |name| |of| |the| |accessor| |,|
                    |flg| |is| |either| ONE-OF |or| NONE-OF |,| |and|
                    |default-fn-symb| |is| |the| |function| |symbol| |for|
                    |the|
                    |default| |value| |.|))
    (SETQ DESTRUCTOR-NAMES (ITERATE FOR TUPLE IN DESTRUCTOR-TUPLES
                                    COLLECT (CAR TUPLE)))
    (SETQ NAMES (CONS SHELL-NAME
                      (CONS RECOGNIZER DESTRUCTOR-NAMES)))
    (COND (BTM-FN-SYMB (SETQ NAMES (CONS BTM-FN-SYMB NAMES))))
    (ITERATE
     FOR NAME IN NAMES DO
     (PROGN
       (CHK-NEW-NAME NAME NIL)
       (CHK-NEW-*1*NAME NAME)
       (COND ((EQL #\- (CHAR (STRING NAME)
                             (1- (LENGTH (STRING NAME)))))
              (ER SOFT (NAME) |Hyphen| |,| |as| |in|
                  (!PPR NAME (QUOTE |,|)) |is| |not| |allowed| |as| |the|
                  |last| |character| |in| |a| |shell| |name| EXCL)))))
    (COND ((NOT (NO-DUPLICATESP NAMES))
           (ER SOFT NIL |Multiple| |use| |of| |the| |same| |name| EXCL)))
    (ITERATE
     FOR TUPLE IN DESTRUCTOR-TUPLES
     DO
     (PROGN (MATCH TUPLE (LIST AC TR DV))
            (COND ((AND (NOT (EQ DV (QUOTE TRUE)))
                        (NOT (EQ DV (QUOTE FALSE)))
                        (NOT (MEMBER-EQ DV *1*BTM-OBJECTS))
                        (OR (NULL BTM-FN-SYMB)
                            (NOT (EQ DV BTM-FN-SYMB))))
                   (ER SOFT (DV) |The| |default| |object| |for| |a|
                       |type-restricted| |shell| |component| |must| |be|
                       |a| |bottom| |object| |function| |symbol| |or|
                       |else| |must| |be| TRUE |or| FALSE EXCL
                       (!PPR DV NIL) |is| |not| |such| |an| |object|
                       |.|)))
            (COND ((NOT (AND (MATCH TR (CONS FLG L))
                             (OR (EQ FLG (QUOTE ONE-OF))
                                 (EQ FLG (QUOTE NONE-OF)))
                             (ITERATE FOR X IN L
                                      ALWAYS
                                      (ASSOC-EQ X
                                                (CONS (CONS RECOGNIZER
                                                            0)
                                                      RECOGNIZER-ALIST)))))
                   (ER SOFT NIL |the| |type| |restriction| |term| |for|
                       |a| |shell| |component| |must| |be| |a| |list|
                       |of| |the| |form|
                       (!PPR (QUOTE (ONE-OF |...|)) NIL) |or|
                       (!PPR (QUOTE (NONE-OF |...|)) NIL) |where|
                       |...| |is| |a| |list| |of| |recognizer| |names|
                       |.|)))
            (COND ((NOT
                    (OR (AND (EQ DV BTM-FN-SYMB)
                             (OR (AND (EQ FLG (QUOTE ONE-OF))
                                      (MEMBER-EQ RECOGNIZER L))
                                 (AND (EQ FLG (QUOTE NONE-OF))
                                      (NOT (MEMBER-EQ RECOGNIZER L)))))
                        (AND
                         (NOT (EQ DV BTM-FN-SYMB))
                         (EQUAL (EQUAL FLG (QUOTE ONE-OF))
                                (TSLOGSUBSETP
                                 (CAR (TYPE-PRESCRIPTION DV))
                                 (ITERATE FOR X IN L
                                          WITH ITERATE-ANS = 0
                                          WHEN (NOT (EQ X RECOGNIZER))
                                          DO
                                          (SETQ
                                           ITERATE-ANS
                                           (TSLOGIOR
                                            ITERATE-ANS
                                            (CDR (ASSOC-EQ X
                                                           RECOGNIZER-ALIST))))
                                          FINALLY (RETURN ITERATE-ANS)))))))
                   (ER SOFT (TR DV AC)
                       |the| |default| |value| (!PPR DV NIL) |does| |not|
                       |satisfy| |the| |type| |restriction| (!PPR TR NIL)
                       |specified| |for| |the| (!PPR AC NIL) |component|
                       |.|)))))
    (COND (DESTRUCTOR-NAMES
           (ITERATE
            FOR TUPLE IN DESTRUCTOR-TUPLES DO
            (PROGN
              (MATCH TUPLE (LIST AC TR DV))
              (SETQ AXIOM-NAMES (CONS (PACK (LIST AC (QUOTE -) SHELL-NAME))
                                      AXIOM-NAMES))
              (SETQ AXIOM-NAMES (CONS (PACK (LIST AC (QUOTE -N)
                                                  RECOGNIZER))
                                      AXIOM-NAMES))
              (AND (NOT (EQUAL TR (QUOTE (NONE-OF))))
                   (SETQ AXIOM-NAMES
                         (CONS (PACK (LIST AC (QUOTE -TYPE-RESTRICTION)))
                               AXIOM-NAMES)))
              (SETQ AXIOM-NAMES (CONS (PACK (LIST AC (QUOTE -LESSP)))
                                      AXIOM-NAMES))
              (SETQ AXIOM-NAMES (CONS (PACK (LIST AC (QUOTE -LESSEQP)))
                                      AXIOM-NAMES))))
           (SETQ AXIOM-NAMES (CONS (PACK (LIST SHELL-NAME (QUOTE -EQUAL)))
                                   AXIOM-NAMES))
           (SETQ AXIOM-NAMES
                 (CONS (PACK (CONS SHELL-NAME
                                   (ITERATE FOR AC IN DESTRUCTOR-NAMES
                                            NCONC (LIST (QUOTE -) AC))))
                       AXIOM-NAMES))
           (SETQ AXIOM-NAMES
                 (CONS (PACK (NCONC1 (CDR (ITERATE FOR AC IN DESTRUCTOR-NAMES
                                                   NCONC (LIST (QUOTE -) AC)))
                                     (QUOTE -ELIM)))
                       AXIOM-NAMES))
           (SETQ AXIOM-NAMES (CONS (PACK (LIST (QUOTE COUNT-) SHELL-NAME))
                                   AXIOM-NAMES)))
          (BTM-FN-SYMB (SETQ AXIOM-NAMES
                             (CONS (PACK (LIST RECOGNIZER
                                               (QUOTE -ELIMINATOR)))
                                   AXIOM-NAMES))))
    (COND ((NOT (NO-DUPLICATESP (APPEND NAMES AXIOM-NAMES)))
           (ER SOFT (AXIOM-NAMES) |The| |addition| |of| |a| |shell|
               |introduces| |many| |new| |axiom| |names| |.| |The| |new|
               |names| |are| |created| |from| |the| |shell| |name| |,|
               |recognizer| |,| |bottom| |object| |,| |and| |destructor|
               |names| |supplied| |in| |the| ADD-SHELL |command| |.| |The|
               |names| |supplied| |in| |this| |instance| |of| |the|
               ADD-SHELL |command| |do| |not| |lead| |to| |distinct| |axiom|
               |names| |.| |the| |axiom| |names| |generated| |are| |:|
               (!LIST AXIOM-NAMES) |.|)))
    (ITERATE FOR X IN AXIOM-NAMES DO (CHK-NEW-NAME X NIL))
    (LIST SHELL-NAME BTM-FN-SYMB RECOGNIZER DESTRUCTOR-TUPLES)))

(DEFUN CHK-ACCEPTABLE-TOGGLE (NAME OLDNAME FLG)
  (CHK-NEW-NAME NAME NIL)
  (CHK-DISABLEABLE OLDNAME)
  (OR (EQ FLG T)
      (EQ FLG NIL)
      (ER SOFT (FLG) |The| |third| |argument| |of| TOGGLE |must| |be| T |or|
          NIL |and| (!PPR FLG NIL) |is| |not| |.|))
  (LIST NAME OLDNAME FLG))

(DEFUN CHK-ACCEPTABLE-TOGGLE-DEFINED-FUNCTIONS (NAME FLG)
  (CHK-NEW-NAME NAME NIL)
  (OR (EQ FLG T)
      (EQ FLG NIL)
      (ER SOFT (FLG)
          |The| |third| |argument| |of| TOGGLE-DEFINED-FUNCTIONS |must|
          |be| T |or| NIL |and| (!PPR FLG NIL) |is| |not| |.|))
  (LIST NAME FLG))

(DEFUN CHK-ARGLIST (NAME ARGS)
  (COND ((OR (COND ((CONSP ARGS)
                    (CDR (OUR-LAST ARGS)))
                   (T ARGS))
             (NOT (NO-DUPLICATESP ARGS))
             (ITERATE FOR ARG IN ARGS
                      THEREIS (OR (ILLEGAL-NAME ARG)
                                  (MEMBER-EQ ARG (QUOTE (T F NIL))))))

;   T and F are merely confusing, not illegal.

         (ER SOFT (ARGS NAME) |The| |argument| |list| |to|
             (!PPR NAME (QUOTE |,|))  |i.e.,| (!PPR ARGS (QUOTE |,|)) |is|
             |not| |a| |list| |of| |distinct| |variable| |names| |.|))))

(DEFUN CHK-COMMAND-STATUS (BOOT-FLG)

;  This function is called by all of the event commands prior to getting
;  started.

  (OR BOOT-FLG (CHK-INIT))
  (COND (COMMAND-STATUS-FLG
         (ER SOFT NIL |It| |is| |illegal| |to| |enter| |a| |theorem| |prover|
             |function| |while| |you| |are| |recursively| |under| |another|
             |theorem| |prover| |function| |.|)))

;  If we aren't under PROVEALL and the theorem prover's output files are
;  still directed off-terminal, then close them and direct them to the
;  terminal.  This would not be necessary if we could unwind protect
;  proveall from user aborts in all our Lisps.

  (COND ((AND (NOT PROVEALL-FLG)
              (OR (NOT PROVE-FILE)
                  (NOT ERR-FILE)))
         (CLOSE-THM-FILES))))

(DEFUN CHK-DISABLEABLE (NAME) 

;   We permit you to disable or enable events (e.g., REVERSE and
;   APP-IS-ASSOC) satellites (e.g., PLUS and CAR-NLISTP) and
;   *1*-functions (e.g., *1*PLUS and *1*REVERSE).  We permit you to
;   disable the *1*-functions for shell constructors or bottom objects
;   but in fact it has no effect: we will run those functions from
;   within CONS-TERM without checking DISABLEDP.

  (OR (AND (SYMBOLP NAME)
           (OR (GET NAME (QUOTE EVENT))
               (GET NAME (QUOTE MAIN-EVENT))))
      (ER SOFT (NAME) |A| |name| |can| |be| |disabled| |or| |enabled|
          |only| |if| |it| |is| |the| |name| |of| |an|
          |event| |or| |the| |name| |of| |a| |satellite| 
          |.| |thus| (!PPR NAME NIL) |is| |illegal| |here|
          |.|)))

(DEFUN CHK-INIT ()
  (COND ((NOT (BOUNDP (QUOTE LIB-PROPS)))
         (ER HARD NIL |the| |theorem-prover's| |database| |has| |not| |been|
             |initialized| |.|  |you| |should| |either| |call| BOOT-STRAP |or|
             NOTE-LIB |.|))))

(DEFUN CHK-NEW-*1*NAME (NAME)
  (COND ((OR (NOT (SYMBOLP (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))))
             (AND (NOT IN-BOOT-STRAP-FLG)
                  (OR (FBOUNDP (PACK (LIST PREFIX-FOR-FUNCTIONS NAME)))
                      (HAS-LIB-PROPS
                       (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))))))
         (ER SOFT (NAME (FN (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))))
             |the| |atom| (!PPR FN (QUOTE |,|)) |which| |is| |derived| |from|
             (!PPR NAME NIL) |and| |used| |for| |internal| |purposes| |,|
             |is| |not| |a| |literal| |atom,| |has| |a| LISP |function|
             |definition| |or| LIB-PROP |properties| |.| |You| |should|
             |change| |the| |name| |of| |your| |function| |to| |avoid|
             |clashes| |of| |this| |sort| |.|))))

(DEFUN CHK-NEW-NAME (NAME QUIET-FLG)

;   Checks that NAME has the correct syntax for use as a symbol in the theory
;   (and hence as an event name).  Further checks that the name has no
;   properties and is not one of the symbols about which there are syntactic
;   conventions (e.g., LIST, CADR, NIL, QUOTE).  Thus there are no axioms about
;   NAME.

  (COND ((ILLEGAL-NAME NAME)
         (COND (QUIET-FLG NIL)
               (T (ER SOFT (NAME) (!PPR NAME NIL) |is| |an| |illegal| |object|
                      |to| |use| |for| |a| |name| EXCL))))
        ((PROPERTYLESS-SYMBOLP NAME)
         (COND (QUIET-FLG NIL)
               (T (ER SOFT (NAME) |The| |name| (!PPR NAME NIL) |is| |a|
                      |reserved| |symbol| |and| |cannot| |be| |used| |as| |a|
                      |user| |name| |.|))))
        ((HAS-LIB-PROPS NAME)
         (COND (QUIET-FLG NIL)
               (T (ERROR1 (PQUOTE (PROGN |Name| |currently| |in| |use| |:|
                                         (!PPR NAME (QUOTE |.|))))
                          `((NAME . ,NAME))
                          (COND (IN-BOOT-STRAP-FLG (QUOTE WARNING))
                                (T (QUOTE SOFT)))))))
        (T T)))

(DEFUN CHK-NQTHM-MODE$-ERR (FN)
  (ER HARD (FN) |An| NQTHM |mode| |function| |,| (!PPR FN (QUOTE |,|))
      |has| |been| |executed| |while| |not| |in| NQTHM |mode| EXCL  |This|
      |is| |a| HARD |error| |unless| |the| |user| |has| |reset| |the|
      |mode| |flag| |without| |doing| |a| BOOT-STRAP |or| NOTE-LIB |.|))

(DEFUN CHK-STATUS-ALIST (ALIST)

; We check that ALIST is a proper status alist, as described in the
; error message below.  This function is either a no-op or causes
; an error.

  (LET ((KEYS '(BOOT-STRAP
                DEFN
                *1*DEFN
                ADD-AXIOM
                ADD-SHELL
                PROVE-LEMMA
                CONSTRAIN
                FUNCTIONALLY-INSTANTIATE))
        (VALS '(ENABLE DISABLE AS-IS)))
  (COND
   ((AND (CONSP ALIST)
         (NULL (CDR (OUR-LAST ALIST)))
         (ITERATE FOR X IN ALIST
                  ALWAYS
                  (AND (CONSP X)
                       (OR (EQ (CAR X) 'OTHERWISE)
                           (MEMBER-EQ (CAR X) KEYS)
                           (AND (CONSP (CAR X))
                                (NULL (CDR (OUR-LAST (CAR X))))
                                (SUBSETP-EQ (CAR X) KEYS)))
                       (CONSP (CDR X))
                       (OR (MEMBER-EQ (CADR X) VALS)
                           (AND (EQ (CAR X) 'BOOT-STRAP)
                                (EQ (CADR X) 'INITIAL)))
                       (NULL (CDDR X))))
         (NO-DUPLICATESP
          (ITERATE FOR X IN ALIST
                   APPEND
                   (COND ((SYMBOLP (CAR X)) (LIST (CAR X)))
                         (T (CAR X)))))
         (EQ (CAR (CAR (OUR-LAST ALIST))) 'OTHERWISE))
    NIL)
   (T (ER SOFT (ALIST)
          |The| |third| |argument| |to| SET-STATUS |must| |be|
          |a| |non-NIL| |proper| |list| |with| |the| |following| |three|
          |properties| |.|  |First| |,| |each| |element| 
          |must| |be| |of| |the| |form| |(key val)| |where| |key|
          |is| |either| |one| |of| |the| |symbols| BOOT-STRAP |,| DEFN |,|
          *1*DEFN |,| ADD-AXIOM |,| ADD-SHELL |,| PROVE-LEMMA |,|
          CONSTRAIN |,| FUNCTIONALLY-INSTANTIATE |,| |or| OTHERWISE |or|
          |else| |key| |is| |a| |non-NIL| |proper| |list| |of| |these|
          |symbols| |,| |and| |val| |is| |one| |of| |the| |symbols| ENABLE
          |,| DISABLE |,| AS-IS |,| |or| INITIAL |(the| |last| |being|
          |allowed| |only| |if| |the| |corresponding| |key| |is|
          |BOOT-STRAP)| |.| |Second| |,| |none| |of| |the| |key| |symbols|
          |may| |appear| |more| |than| |once| |.| |Third| |,| |the| |last|
          |element| |of| |the| |list| |must| |be| |of| |the| |form|
          |(OTHERWISE val)| |.|  |The| |argument| (!PPR alist nil) |is|
          |thus| |illegal| |.|)))))
         
(DEFUN CLAUSIFY (TERM)
  (COND ((EQUAL TERM TRUE) NIL)
        ((EQUAL TERM FALSE) (LIST NIL))
        ((FNNAMEP-IF TERM)
         (CLEAN-UP-BRANCHES (STRIP-BRANCHES TERM)))
        (T (LIST (LIST TERM)))))

(DEFUN CLAUSIFY-INPUT (TERM)

;   In addition to clausifying TERM, we expand ANDs in the hyps and ORs in the
;   concl, adding entries to ABBREVIATIONS-USED.

  (ITERATE FOR TERM1 IN (CLAUSIFY-INPUT1 TERM FALSE)
           COLLECT (CLAUSIFY-INPUT1 (DUMB-NEGATE-LIT TERM1) TRUE)))

(DEFUN CLAUSIFY-INPUT1 (TERM BOOL)

;   If BOOL is TRUE, returns a list of terms whose disjunction is equivalent to
;   TERM.  IF BOOL is FALSE, returns a list of terms whose disjunction is
;   equivalent to the negation of TERM.  Opens up some nonrec fns and applies
;   some unconditional rewrite rules -- according to BOOL -- and side-effects
;   ABBREVIATIONS-USED.

  (LET (C1 C2 C3)
    (COND ((EQUAL TERM (NEGATE BOOL)) NIL)
          ((MATCH TERM (IF C1 C2 C3))
           (COND ((EQUAL BOOL TRUE)
                  (COND ((EQUAL C3 TRUE)
                         (DISJOIN-CLAUSES (CLAUSIFY-INPUT1 C1 FALSE)
                                          (CLAUSIFY-INPUT1 C2 TRUE)))
                        ((EQUAL C2 TRUE)
                         (DISJOIN-CLAUSES (CLAUSIFY-INPUT1 C1 TRUE)
                                          (CLAUSIFY-INPUT1 C3 TRUE)))
                        (T (LIST TERM))))
                 (T (COND ((EQUAL C3 FALSE)
                           (DISJOIN-CLAUSES (CLAUSIFY-INPUT1 C1 FALSE)
                                            (CLAUSIFY-INPUT1 C2 FALSE)))
                          ((EQUAL C2 FALSE)
                           (DISJOIN-CLAUSES (CLAUSIFY-INPUT1 C1 TRUE)
                                            (CLAUSIFY-INPUT1 C3 FALSE)))
                          (T (LIST (DUMB-NEGATE-LIT TERM)))))))
          ((SETQ C1 (EXPAND-AND-ORS TERM BOOL))
           (CLAUSIFY-INPUT1 C1 BOOL))
          ((EQUAL BOOL FALSE)
           (LIST (DUMB-NEGATE-LIT TERM)))
          (T (LIST TERM)))))

(DEFUN CLEAN-UP-BRANCHES (LST)
  (LET (PARTITIONS)
    (SETQ PARTITIONS (PARTITION-CLAUSES LST))
    (SETQ TEMP-TEMP (ITERATE FOR POCKET IN PARTITIONS
                             NCONC (ALMOST-SUBSUMES-LOOP POCKET)))
    (COND ((NULL (CDR PARTITIONS))
           TEMP-TEMP)
          (T (ALMOST-SUBSUMES-LOOP TEMP-TEMP)))))

(DEFUN CLEARLY-NOT-ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP (TERM)

; This short-circuit can cause a drastic speed-up in ADD-SHELL.  When this
; returns T, we can be sure that it's OK to give up in
; ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP.  The original input is the term that we
; have built in ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP.

  (COND
   ((VARIABLEP TERM)
    NIL)
   ((FQUOTEP TERM)
    NIL)
   ((AND (ASSOC-EQ (FFN-SYMB TERM) RECOGNIZER-ALIST)
         (VARIABLEP (FARGN TERM 1)))
    T)
   (T (ITERATE FOR ARG IN (FARGS TERM)
               THEREIS
               (CLEARLY-NOT-ACCEPTABLE-TYPE-PRESCRIPTION-LEMMAP ARG)))))

(DEFUN CLOSE-THM-FILES NIL
  
;  Close PROVE-FILE and ERR-FILE and set them to NIL.  Print advisory
;  to user.
  
  (COND ((NOT (EQ PROVE-FILE NIL))
         (CLOSE PROVE-FILE)
         (PRINEVAL (PQUOTE (PROGN |Closed| PROVE-FILE |,|
                                  (!PPR X (QUOTE |.|)) |Subsequent|
                                  |proof| |output| |will| |go| |to|
                                  |the| |terminal| |.| CR))
                   (LIST (CONS (QUOTE X) PROVE-FILE))
                   0 NIL)
         (SETQ PROVE-FILE NIL)))
  (COND ((AND (NOT (EQ ERR-FILE NIL))
              (NOT (EQ ERR-FILE PROVE-FILE)))
         (CLOSE ERR-FILE)
         (PRINEVAL (PQUOTE (PROGN |Closed| ERR-FILE |,|
                                  (!PPR X (QUOTE |.|)) |Subsequent|
                                  |error| |messages| |will| |go| |to|
                                  |the| |terminal| |.| CR))
                   (LIST (CONS (QUOTE X) ERR-FILE))
                   0 NIL)                
         (SETQ ERR-FILE NIL))))


(DEFUN CNF-DNF (TERM FLG)

;   If FLG is (QUOTE C), returns a list of lists, say:

;   ((p11 p12 ...) (p21 p22  ...) ...  (pn1 pn2 ...))

;   such that TERM is not equal to F iff

;   (AND (OR p11 p12 ...) (OR p21 p22 ...) ... (OR pn1 pn2 ...))

;   is not equal to F.  The latter term is the "conjunctive normal form" of
;   TERM.  If FLG is (QUOTE D) computes the disjunctive normal form.

  (LET (P Q NF-Q)
    (COND ((OR (AND (EQ FLG (QUOTE C))
                    (MATCH TERM (AND P Q)))
               (AND (EQ FLG (QUOTE D))
                    (MATCH TERM (OR P Q))))
           (APPEND (CNF-DNF P FLG)
                   (CNF-DNF Q FLG)))
          ((OR (AND (EQ FLG (QUOTE C))
                    (MATCH TERM (OR P Q)))
               (AND (EQ FLG (QUOTE D))
                    (MATCH TERM (AND P Q))))
           (SETQ NF-Q (CNF-DNF Q FLG))
           (ITERATE FOR L1 IN (CNF-DNF P FLG)
                    WITH ITERATE-ANS
                    DO (SETQ ITERATE-ANS
                             (UNION-EQUAL (ITERATE FOR L2 IN NF-Q
                                                   COLLECT (UNION-EQUAL L1 L2))
                                          ITERATE-ANS))
                    FINALLY (RETURN ITERATE-ANS)))
          ((MATCH TERM (NOT P))
           (ITERATE FOR L1 IN (CNF-DNF P (CASE FLG
                                               (D (QUOTE C))
                                               (OTHERWISE (QUOTE D))))
                    COLLECT (ITERATE FOR TERM IN L1
                                     COLLECT (DUMB-NEGATE-LIT TERM))))
          ((MATCH TERM (IMPLIES P Q))
           (CNF-DNF (FCONS-TERM* (QUOTE OR) (DUMB-NEGATE-LIT P) Q)
                    FLG))
          (T (LIST (LIST TERM))))))

(DEFUN COMMON-SWEEP (FORM)
  (LET (VAR DECISION)
    (COND ((OR (ATOM FORM) (EQ (CAR FORM) (QUOTE QUOTE))) FORM)
          ((SETQ DECISION (ASSOC-EQ FORM DECISIONS))
           (SETQ VAR (CDR (ASSOC-EQUAL FORM VAR-ALIST)))
           (SUBLIS (LIST (CONS (QUOTE VAR) VAR)
                         (CONS (QUOTE FORM)
                               (CONS
                                (CAR FORM)
                                (ITERATE FOR ARG IN (CDR FORM)
                                         COLLECT (COMMON-SWEEP ARG)))))
                   (CASE (CDR DECISION)
                         (TEST-AND-SET
                          (QUOTE (*2*IF (NOT (EQ VAR (QUOTE *1*X)))
                                        VAR
                                        (SETQ VAR FORM))))
                         (SET (QUOTE (SETQ VAR FORM)))
                         (TEST (QUOTE (*2*IF (NOT (EQ VAR (QUOTE *1*X)))
                                             VAR
                                             FORM)))
                         (VAR (QUOTE VAR))
                         (OTHERWISE
                          (ER HARD ((X (CDR DECISION)))
                              COMMON-SWEEP |has| |encountered| |the|
                              |impossible| (!PPR X '|.|))))))
          (T (CONS (CAR FORM)
                   (ITERATE FOR ARG IN (CDR FORM)
                            COLLECT (COMMON-SWEEP ARG)))))))

(DEFUN COMMUTE-EQUALITIES (TERM)
  (COND ((VARIABLEP TERM) TERM)
        ((FQUOTEP TERM) TERM)
        ((EQ (FFN-SYMB TERM) (QUOTE EQUAL))
         (FCONS-TERM* (QUOTE EQUAL) (FARGN TERM 2) (FARGN TERM 1)))
        (T (CONS-TERM (CAR TERM)
                      (ITERATE FOR ARG IN (FARGS TERM)
                               COLLECT (COMMUTE-EQUALITIES ARG))))))

(DEFUN COMPILE-UNCOMPILED-DEFNS (FILE)
  (CHK-COMMAND-STATUS NIL)
  (COND (PETITIO-PRINCIPII (RETURN-FROM COMPILE-UNCOMPILED-DEFNS T)))
  (LET ((*READ-BASE* 10)
        (*PRINT-BASE* 10)
        (*PRINT-RADIX* NIL)
        (*READTABLE* (COPY-READTABLE NIL))
        *PRINT-PRETTY*
        *PRINT-LEVEL*
        *PRINT-LENGTH*
        (*PRINT-CASE* :UPCASE)
        FN-FILE FN-FILE-NAME)
    (CHK-INIT)
    (SETQ FN-FILE (OPEN (EXTEND-FILE-NAME FILE FILE-EXTENSION-LISP)
                        :DIRECTION :OUTPUT :IF-EXISTS
                        :RENAME-AND-DELETE))
    (FORMAT
     FN-FILE
     ";;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 ~
      -*- ;;;; ~%(IN-PACKAGE \"USER\")~2%")
    (SETQ FN-FILE-NAME
          (NAMESTRING (TRUENAME FN-FILE)))
    (TERPRI FN-FILE)
    (PRINC "(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))"
           FN-FILE)
    (TERPRI FN-FILE)
    (ITERATE FOR ATM IN (REVERSE LIB-ATOMS-WITH-DEFS) WITH TEMP
             UNLESS (FUNCALL COMPILED-FUNCTION-P-FN (SYMBOL-FUNCTION ATM))
             DO
             (PROGN (SETQ TEMP (GET ATM (QUOTE SEXPR)))
                    (PRINT (SETQ TEMP (LIST (QUOTE DEFUN)
                                            ATM
                                            (CADR TEMP)
                                            (CADDR TEMP)))
                           FN-FILE)))
    (CLOSE FN-FILE)
    (COMPILE-FILE FN-FILE-NAME)
    (LOAD (EXTEND-FILE-NAME FILE FILE-EXTENSION-BIN))
    FN-FILE-NAME))

(DEFUN COMPLEMENTARY-MULTIPLEP (WINNING-PAIR POLY1 POLY2)

;   Return T iff multiplying POLY1 by some negative integer produces POLY2.
;   WINNING-PAIR is a member of POLY1 with coefficient + or -1.

  (PROG (FACTOR)
        (COND ((NULL (SETQ TEMP-TEMP (ASSOC-EQUAL (CAR WINNING-PAIR)
                                                  (ACCESS POLY ALIST POLY2))))
               (RETURN NIL)))
        (SETQ FACTOR (COND ((EQUAL (CDR WINNING-PAIR) 1)
                            (CDR TEMP-TEMP))
                           (T (- (CDR TEMP-TEMP)))))
        (COND ((NOT (< FACTOR 0))
               (RETURN NIL)))
        (RETURN (AND (EQUAL (ACCESS POLY CONSTANT POLY2)
                            (* FACTOR (ACCESS POLY CONSTANT POLY1)))
                     (INT= (LENGTH (ACCESS POLY ALIST POLY2))
                           (LENGTH (ACCESS POLY ALIST POLY1)))
                     (ITERATE FOR PAIR1 IN (ACCESS POLY ALIST POLY1) AS PAIR2
                              IN (ACCESS POLY ALIST POLY2)
                              ALWAYS (AND (EQUAL (CAR PAIR1)
                                                 (CAR PAIR2))
                                          (EQUAL (CDR PAIR2)
                                                 (* FACTOR (CDR PAIR1)))))))))

(DEFUN COMPLEMENTARYP (LIT1 LIT2)
  (OR (AND (NVARIABLEP LIT1)
           (NOT (FQUOTEP LIT1))
           (EQ (FFN-SYMB LIT1) (QUOTE NOT))
           (EQUAL (FARGN LIT1 1) LIT2))
      (AND (NVARIABLEP LIT2)
           (NOT (FQUOTEP LIT2))
           (EQ (FFN-SYMB LIT2) (QUOTE NOT))
           (EQUAL (FARGN LIT2 1) LIT1))))

(DEFUN COMPLETE-ALIST (VARS ALIST)

;   ALIST is a substitution of terms for variables.  VARS is a set of
;   variables.  We extend ALIST with pairs of the form (var . (QUOTE 0))
;   for each var in VARS that is not already bound in ALIST.

  (NCONC (ITERATE FOR VAR IN VARS 
                  WHEN (NOT (ASSOC-EQ VAR ALIST))
                  COLLECT (CONS VAR ZERO))
         ALIST))

(DEFUN COMPLEXITY (TERM)
  (COND ((VARIABLEP TERM) 0)
        ((FQUOTEP TERM)

;   The level number of all function symbols in evgs is 0, so even if we
;   recursed into them with FN-SYMBs and ARGS we'd compute 0.

         0)
        (T (+ (GET-LEVEL-NO (FFN-SYMB TERM))
              (OR (ITERATE FOR ARG IN (FARGS TERM) MAXIMIZE (COMPLEXITY ARG))
                  0)))))

(DEFUN COMPRESS-POLY (POLY)
  (COND ((IMPOSSIBLE-POLYP POLY) (CHANGE POLY ALIST POLY NIL))
        ((TRUE-POLYP POLY) (CHANGE POLY ALIST POLY NIL))
        (T (CHANGE POLY ALIST POLY (COMPRESS-POLY1 (ACCESS POLY ALIST POLY)))))
  POLY)

(DEFUN COMPRESS-POLY1 (ALIST)
  (COND ((ATOM ALIST) NIL)
        ((EQUAL (CDAR ALIST) 0) (COMPRESS-POLY1 (CDR ALIST)))
        (T (RPLACD ALIST (COMPRESS-POLY1 (CDR ALIST))))))

(DEFUN COMPUTE-VETOES (CANDLST)

;   This function weeds out "unclean" induction candidates.  The intuition
;   behind the notion "clean" is that an induction is clean if nobody is
;   competing with it for instantiation of its variables.  What we actually do
;   is throw out any candidate whose changing induction variables -- that is
;   the induction variables as computed by INDUCT-VARS intersected with the
;   changed vars of candidate -- intersect the changed or unchanged variables
;   of another candidate.  The reason we do not care about the first candidates
;   unchanging vars is as follows.  The reason you want a candidate clean is so
;   that the terms riding on that cand will reoccur in both the hypothesis and
;   conclusion of an induction.  There are two ways to assure (or at least make
;   likely) this, change the variables in the terms as specified or leave them
;   constant.  Thus, if the first cands changing vars are clean but its
;   unchanging vars intersect another cand it means that the first cand is
;   keeping those other terms constant which is fine. (Note that the first cand
;   would be clean here.  The second might be clean or dirty depending on
;   whether its changed vars or unchanged vars intersected the first cands
;   vars.)  The reason we check only the induction vars and not all of the
;   changed vars is if cand1's changed vars include some induction vars and
;   some accumulators and the accumulators are claimed by another cand2 we
;   believe that cand1 is still clean.  The motivating example was

;   (IMPLIES (MEMBER A C) (MEMBER A (UNION: B C)))

;   where the induction on C is dirty because the induction on B and C claims
;   C, but the induction on B and C is clean because the B does not occur in
;   the C induction.  We do not even bother to check the C from the (B C)
;   induction because since it is necessarily an accumulator it is probably
;   being constructed and thus, if it occurs in somebody elses ind vars it is
;   probably being eaten so it will be ok.  In formulating this heuristic we
;   did not consider the possibility that the accums of one candidate occur as
;   constants in the other.  Oh well.

;   JULY 20, 1978.  We have added an additional heuristic, to be applied if the
;   above one eliminates all cands.  We consider a cand flawed if it changes
;   anyone elses constants.  The motivating example was GREATEST-FACTOR-LESSP
;   -- which was previously proved only by virtue of a very ugly use of the
;   no-op fn ID to make a certain induction flawed.

  (OR (ITERATE FOR CAND1 IN CANDLST WITH CHANGING-INDVARS
               UNLESS (PROGN (SETQ CHANGING-INDVARS
                                   (INTERSECTION-EQ
                                    (ACCESS CANDIDATE CHANGED-VARS
                                            CAND1)
                                    (INDUCT-VARS CAND1)))
                             (ITERATE FOR CAND2 IN CANDLST
                                      WHEN (NOT (EQ CAND1
                                                    CAND2))
                                      THEREIS (OR (INTERSECTP
                                                   CHANGING-INDVARS
                                                   (ACCESS CANDIDATE
                                                           CHANGED-VARS
                                                           CAND2))
                                                  (INTERSECTP
                                                   CHANGING-INDVARS
                                                   (ACCESS CANDIDATE
                                                           UNCHANGEABLE-VARS
                                                           CAND2)))))
               COLLECT CAND1)
      (ITERATE FOR CAND1 IN CANDLST WITH CHANGING-VARS
               UNLESS (PROGN (SETQ CHANGING-VARS
                                   (ACCESS CANDIDATE CHANGED-VARS CAND1))
                             (ITERATE FOR CAND2 IN CANDLST
                                      WHEN (NOT (EQ CAND1 CAND2))
                                      THEREIS (INTERSECTP
                                               CHANGING-VARS
                                               (ACCESS CANDIDATE
                                                       UNCHANGEABLE-VARS
                                                       CAND2))))
               COLLECT CAND1)
      CANDLST))

(DEFUN COMSUBT1 (T1)

;   We add to GENRLTLIST every common subterm t of T1 and T2 such that t has
;   property p, and no subterm of t has property p.  Property (p x) is x is not
;   a variable and the function symbol of x is not a btm object, constructor,
;   or destructor.  We return T iff T1 is a common subterm of T2, but neither
;   T1 nor any subterm of T1 has property p.

  (PROG (FAILED)
        (COND ((OR (VARIABLEP T1) (FQUOTEP T1))
               (RETURN (OCCUR T1 T2))))

;   After the following FOR, FAILED is set to T iff COMSUBT1 returned NIL on at
;   least one of the arguments of T1.  GENRLTLIST now contains all of proper
;   subterms of T1 that occur in T2, have property p, and have no subterms with
;   property p, by inductive hypothesis.

        (ITERATE FOR ARG IN (FARGS T1) WHEN (NOT (COMSUBT1 ARG))
                 DO (SETQ FAILED T))
        (COND (FAILED

;   One of T1's arguments returned NIL.  So either the argument is not a
;   subterm of T2, in which case neither is T1, or the argument or one of its
;   subterms has property p, in which case one of T1's subterms also has
;   property p.  So we return NIL and do not add T1 to GENRLTLIST.

               (RETURN NIL))
              ((NOT (OCCUR T1 T2))

;   If T1 does not occur in T2, then its not a common subterm -- regardless of
;   what properties its args have -- and so we return NIL and do not add T1 to
;   GENRLTLIST.

               (RETURN NIL))
              ((AND (NOT (SHELLP T1))
                    (NOT (AND (SETQ TEMP-TEMP
                                    (GET (FFN-SYMB T1)
                                         (QUOTE ELIMINATE-DESTRUCTORS-SEQ)))
                              (NOT (DISABLEDP (ACCESS REWRITE-RULE NAME
                                                      TEMP-TEMP))))))

;   The test above checks that T1 has property p.  We know that T1 occurs in
;   T2.  We also know that every argument of T1 recursively returned T and so
;   no argument nor any subterm has property p.  Therefore we add T1 to
;   GENRLTLIST.  We return NIL because T1 has property p.

               (SETQ GENRLTLIST (ADD-TO-SET T1 GENRLTLIST))
               (RETURN NIL))
              (T

;   T1 does not have property p.  It is a subterm of T2, and no subterm of it
;   has property p.

               (RETURN T)))))

(DEFUN COMSUBTERMS (T1 T2)

;   We add to GENRLTLIST every common subterm t of T1 and T2 such that t has
;   property p, and no subterm of t has property p.  Property (p x) is x is not
;   a variable and the function symbol of x is not a btm object, constructor,
;   or destructor.

  (COND ((> (CONS-COUNT T1) (CONS-COUNT T2))
         (OUR-SWAP T1 T2)))
  (COMSUBT1 T1))

(DEFUN CONJOIN (LST IF-FLG)
  (COND ((NULL LST) TRUE)
        ((NULL (CDR LST)) (CONJOIN2 (CAR LST) TRUE IF-FLG))
        ((NULL (CDDR LST)) (CONJOIN2 (CAR LST) (CADR LST) IF-FLG))
        (T (CONJOIN2 (CAR LST)
                     (CONJOIN (CDR LST)
                              IF-FLG)
                     IF-FLG))))

(DEFUN CONJOIN-CLAUSE-SETS (LST1 LST2)
  (LET (ANS)
    (ITERATE FOR CL IN LST1 WHEN (AND (NOT (EQUAL CL TRUE-CLAUSE))
                                      (NOT (MEMBER-EQUAL CL ANS)))
             DO (SETQ ANS (CONS CL ANS)))
    (ITERATE FOR CL IN LST2 WHEN (AND (NOT (EQUAL CL TRUE-CLAUSE))
                                      (NOT (MEMBER-EQUAL CL ANS)))
             DO (SETQ ANS (CONS CL ANS)))
    ANS))

(DEFUN CONJOIN2 (P Q IF-FLG)
  (COND ((FALSE-NONFALSEP P)
         (COND (DEFINITELY-FALSE FALSE)
               ((FALSE-NONFALSEP Q)
                (COND (DEFINITELY-FALSE FALSE)
                      (T TRUE)))
               ((NOT (OUR-BOOLEAN Q))
                (FCONS-TERM* (QUOTE IF)
                             Q TRUE FALSE))
               (T Q)))
        ((FALSE-NONFALSEP Q)
         (COND (DEFINITELY-FALSE FALSE)
               ((OUR-BOOLEAN P) P)
               (T (FCONS-TERM* (QUOTE IF) P TRUE FALSE))))
        (IF-FLG (FCONS-TERM* (QUOTE IF)
                             P
                             (COND ((OUR-BOOLEAN Q) Q)
                                   (T (FCONS-TERM* (QUOTE IF) Q TRUE FALSE)))
                             FALSE))
        (T (FCONS-TERM* (QUOTE AND) P Q))))

(DEFUN CONS-PLUS (X Y)
  (COND ((EQUAL X ZERO) Y)
        ((EQUAL Y ZERO) X)
        (T (FCONS-TERM* (QUOTE PLUS) X Y))))

(DEFUN CONS-TERM (FN ARGS)

;   After great deliberation, we have decided to guarantee throughout the
;   theorem-prover that every explicit value term should be represented as an
;   evg.  Unless the function symbol of a term being constructed is known not
;   to be a constructor or bottom object, the term should be constructed using
;   CONS-TERM rather than with FCONS-TERM or FCONS-TERM*.

  (COND ((AND (ITERATE FOR ARG IN ARGS ALWAYS (QUOTEP ARG))
              (OR (MEMBER-EQ FN *1*BTM-OBJECTS)
                  (ASSOC-EQ FN SHELL-ALIST)))

;   We wish to apply the LISP-CODE for this shell constructor or btm object to
;   the guts of each arg and QUOTE the result.  To avoid having to cons up the
;   list of guts, we will consider the common cases separately.

;   We know the LISP-CODE for these functions does not cause THROWs.

         (COND ((NULL ARGS)
                (LIST (QUOTE QUOTE)
                      (FUNCALL (GET FN (QUOTE LISP-CODE)))))
               ((NULL (CDR ARGS))
                (LIST (QUOTE QUOTE)
                      (FUNCALL (GET FN (QUOTE LISP-CODE))
                               (CADR (CAR ARGS)))))
               ((NULL (CDDR ARGS))
                (LIST (QUOTE QUOTE)
                      (FUNCALL (GET FN (QUOTE LISP-CODE))
                               (CADR (CAR ARGS))
                               (CADR (CADR ARGS)))))
               ((NULL (CDDDR ARGS))
                (LIST (QUOTE QUOTE)
                      (FUNCALL (GET FN (QUOTE LISP-CODE))
                               (CADR (CAR ARGS))
                               (CADR (CADR ARGS))
                               (CADR (CADDR ARGS)))))
               (T (LIST (QUOTE QUOTE)
                        (APPLY (GET FN (QUOTE LISP-CODE))
                               (ITERATE FOR ARG IN ARGS
                                        COLLECT (CADR ARG)))))))
        (T (CONS FN ARGS))))

(DEFUN CONSJOIN (LST)
  (COND ((ATOM (CDR LST)) (CAR LST))
        (T (CONS-TERM (QUOTE CONS)
                      (LIST (CAR LST)
                            (CONSJOIN (CDR LST)))))))

(DEFUN CONTAINS-REWRITEABLE-CALLP (NAME TERM)

;   This function scans the nonQUOTE part of TERM and determines whether it
;   contains a call of NAME not on TERMS-TO-BE-IGNORED-BY-REWRITE.

  (COND ((VARIABLEP TERM) NIL)
        ((FQUOTEP TERM) NIL)
        ((AND (EQ (FFN-SYMB TERM) NAME)
              (NOT (MEMBER-EQUAL TERM TERMS-TO-BE-IGNORED-BY-REWRITE)))
         T)
        (T (ITERATE FOR X IN (FARGS TERM) THEREIS (CONTAINS-REWRITEABLE-CALLP
                                                   NAME X)))))
 
(DEFUN CONVERT-TYPE-NO-TO-RECOGNIZER-TERM (TYPE-NO ARG)
  (LET (TYPE-SET)
    (SETQ TYPE-SET (TSLOGBIT TYPE-NO))
    (COND ((SETQ TEMP-TEMP
                 (ITERATE FOR PAIR IN RECOGNIZER-ALIST
                          WHEN (TS= TYPE-SET (CDR PAIR))
                          DO (RETURN PAIR)))
           (FCONS-TERM* (CAR TEMP-TEMP)
                        ARG))
          (T (ER HARD NIL CONVERT-TYPE-NO-TO-RECOGNIZER-TERM |called| |with|
                 |a| |number| |not| |assigned| |as| |a| |type| |no| EXCL)))))

(DEFUN CONS-COUNT (X)
  (COND ((ATOM X) 0)
        (T (+ 1 (CONS-COUNT (CAR X)) (CONS-COUNT (CDR X))))))

;   Because terms can conceivably share subexpressions, one should not
;   count on FIXNUM arithmetic in CONS-COUNT and COUNT-IFS.

(DEFUN COUNT-IFS (TERM)
  (COND ((VARIABLEP TERM) 0)
        ((FQUOTEP TERM) 0)
        ((EQ (FFN-SYMB TERM) (QUOTE IF))
         (1+ (ITERATE FOR ARG IN (FARGS TERM) SUM (COUNT-IFS ARG))))
        (T (ITERATE FOR ARG IN (FARGS TERM) SUM (COUNT-IFS ARG)))))

(DEFUN CREATE-REWRITE-RULE (NAME HYPS CONCL LOOP-STOPPER-ARG)
  (MAKE REWRITE-RULE NAME (PREPROCESS-HYPS HYPS)
        CONCL
        (OR LOOP-STOPPER-ARG (LOOP-STOPPER CONCL))))

(DEFUN DATA-BASE (QUERY NAME)
  (COND ((NOT (SYMBOLP NAME)) NIL)
        ((AND (NOT (GET NAME (QUOTE EVENT)))
              (NOT (GET NAME (QUOTE MAIN-EVENT))))
         NIL)
        (T (CASE QUERY
                 (ANCESTORS (COND ((NOT (ARITY NAME)) NIL)
                                  (T (ANCESTORS (LIST NAME)))))
                 (PRIMARY (MAIN-EVENT-OF NAME))
                 (EVENT-FORM (GET (MAIN-EVENT-OF NAME) (QUOTE EVENT)))
                 (STATUS (COND ((DISABLEDP NAME) (QUOTE DISABLED))
                               (T (QUOTE ENABLED))))
                 (IDATE (GET (MAIN-EVENT-OF NAME) (QUOTE IDATE)))
                 (SATELLITES (GET (MAIN-EVENT-OF NAME) (QUOTE SATELLITES)))
                 (IMMEDIATE-DEPENDENTS
                  (COND ((EQ (MAIN-EVENT-OF NAME) (QUOTE GROUND-ZERO))
                         (CDR (REVERSE CHRONOLOGY)))
                        (T (SORT-EVENTS (IMMEDIATE-DEPENDENTS-OF
                                         (MAIN-EVENT-OF NAME))))))
                 (ALL-DEPENDENTS (CDR (DEPENDENTS-OF (MAIN-EVENT-OF NAME))))
                 (IMMEDIATE-SUPPORTERS
                  (SORT-EVENTS (IMMEDIATE-SUPPORTERS-OF (MAIN-EVENT-OF NAME))))
                 (ALL-SUPPORTERS (SUPPORTERS-OF (MAIN-EVENT-OF NAME)))
                 (FORMULA (FORMULA-OF (MAIN-EVENT-OF NAME)))
                 (OTHERWISE (ER SOFT (QUERY) |Unrecognized| DATA-BASE |query|
                                |,| (!PPR QUERY (QUOTE |.|))))))))


(DEFUN DCL0 (NAME ARGS LISP-CODE-FLG)
  
;   This function is FUNCALLed and therefore may not be made a MACRO.
  
;   WARNING:  LISP-CODE-FLG plays a triple role here.  If non-NIL it
;   means the usual thing:
;    (a) the *1*fn for NAME is builtin or supplied,
;   but also means
;    (b) NAME is TOTAL!
;    (c) NAME is a SUBRP!

  (ADD-FACT NAME (QUOTE TYPE-PRESCRIPTION-LST)
            (CONS NAME (CONS TYPE-SET-UNKNOWN
                             (MAKE-LIST (LENGTH ARGS)))))
  (ADD-FACT NAME (QUOTE LEVEL-NO) 0)
  (ADD-FACT NAME (QUOTE TOTALP-LST)
            (CONS NAME (COND (LISP-CODE-FLG T) (T NIL))))
  (COND ((AND (NOT IN-BOOT-STRAP-FLG)
              (NOT (EQ *1*THM-MODE$ (QUOTE THM))))
         (ADD-FACT NAME (QUOTE ERRATICP) T)))
  (COND ((EQ LISP-CODE-FLG T)
         (ADD-FACT NAME (QUOTE LISP-CODE)
                   (PACK (LIST PREFIX-FOR-FUNCTIONS NAME)))
         (ADD-FACT NAME (QUOTE SUBRP) *1*T))
        (LISP-CODE-FLG

;   When LISP-CODE-FLG is non-NIL but non-T, it is a Lisp LAMBDA expression
;   suitable for giving to ADD-DCELL for compilation, etc.

         (ADD-DCELL NAME
                    (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))
                    LISP-CODE-FLG)
         (ADD-FACT NAME (QUOTE SUBRP) *1*T))
        (T (SETQ TEMP-TEMP (ITERATE FOR ARG IN ARGS COLLECT
                                    (PACK (LIST PREFIX-FOR-FORMALS ARG))))
           (ADD-DCELL NAME
                      (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))
                      `(LAMBDA ,TEMP-TEMP
                         (PROGN
                           (THROW (QUOTE REDUCE-TERM) (QUOTE *1*FAILED))
                           ,@TEMP-TEMP))))))

(DEFUN DECODE-IDATE (N)
  (LET ((REP (REVERSE (POWER-REP N 100))))
    (ITERATE WHILE (> (LENGTH REP) 6)
             DO
             (SETQ REP (CONS (+ (* 100 (CAR REP))
                                (CADR REP))
                             (CDDR REP)))
             FINALLY (RETURN (REVERSE REP)))))

(DEFUN DEFN-ASSUME-TRUE-FALSE (TERM)
  (LET (TYPE-ARG1 TYPE-ARG2 TRUE-SEG FALSE-SEG PAIR ARG1 ARG2
                  INTERSECTION LOCAL-MUST-BE-TRUE
                  LOCAL-MUST-BE-FALSE)
    (COND ((AND (NVARIABLEP TERM)
                (NOT (FQUOTEP TERM))
                (SETQ PAIR (ASSOC-EQ (FFN-SYMB TERM)
                                     RECOGNIZER-ALIST)))
           (SETQ TYPE-ARG1 (DEFN-TYPE-SET (FARGN TERM 1)))
           (COND ((AND (NULL (CDR TYPE-ARG1))
                       (TS= 0 (TSLOGAND (CAR TYPE-ARG1)
                                        (CDR PAIR))))
                  (SETQ LOCAL-MUST-BE-FALSE T))
                 ((AND (NULL (CDR TYPE-ARG1))
                       (TSLOGSUBSETP (CAR TYPE-ARG1)
                                     (CDR PAIR)))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 (T (SETQ TRUE-SEG (LIST (CONS (FARGN TERM 1)
                                               (CONS (CDR PAIR)
                                                     NIL))))
                    (SETQ FALSE-SEG
                          (LIST (CONS (FARGN TERM 1)
                                      (CONS (TSLOGDIFF (CAR TYPE-ARG1)
                                                       (CDR PAIR))
                                            (CDR TYPE-ARG1))))))))
          ((MATCH TERM (EQUAL ARG1 ARG2))
           (SETQ TYPE-ARG1 (DEFN-TYPE-SET ARG1))
           (SETQ TYPE-ARG2 (DEFN-TYPE-SET ARG2))
           (SETQ INTERSECTION (TSLOGAND (CAR TYPE-ARG1) (CAR TYPE-ARG2)))
           (COND ((AND (TS= 0 INTERSECTION)
                       (NULL (CDR TYPE-ARG1))
                       (NULL (CDR TYPE-ARG2)))
                  (SETQ LOCAL-MUST-BE-FALSE T))
                 ((AND (NULL (CDR TYPE-ARG1))
                       (NULL (CDR TYPE-ARG2))
                       (TS= (CAR TYPE-ARG1) (CAR TYPE-ARG2))
                       (MEMBER-EQUAL (CAR TYPE-ARG1) SINGLETON-TYPE-SETS))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 ((AND (EQUAL TYPE-ARG1 TYPE-ARG2)
                       (TS= 0 (CAR TYPE-ARG1))
                       (INT= (LENGTH (CDR TYPE-ARG1)) 1))
                  (SETQ LOCAL-MUST-BE-TRUE T))
                 (T (SETQ TRUE-SEG
                          (LIST (CONS TERM (CONS TYPE-SET-TRUE NIL))))
                    (COND ((NOT (TS= (CAR TYPE-ARG1) INTERSECTION))
                           (SETQ TRUE-SEG
                                 (CONS (CONS ARG1
                                             (CONS INTERSECTION
                                                   (UNION-EQ (CDR TYPE-ARG1)
                                                             (CDR TYPE-ARG2))))
                                       TRUE-SEG))))
                    (COND ((NOT (TS= (CAR TYPE-ARG2) INTERSECTION))
                           (SETQ TRUE-SEG
                                 (CONS (CONS ARG2
                                             (CONS INTERSECTION
                                                   (UNION-EQ (CDR TYPE-ARG1)
                                                             (CDR TYPE-ARG2))))
                                       TRUE-SEG))))
                    (SETQ FALSE-SEG
                          (LIST (CONS TERM (CONS TYPE-SET-FALSE NIL))))
                    (COND ((AND (MEMBER-EQUAL (CAR TYPE-ARG2)
                                              SINGLETON-TYPE-SETS)
                                (NULL (CDR TYPE-ARG2)))
                           (SETQ FALSE-SEG
                                 (CONS (CONS ARG1
                                             (CONS (TSLOGDIFF (CAR TYPE-ARG1)
                                                              (CAR TYPE-ARG2))
                                                   (CDR TYPE-ARG1)))
                                       FALSE-SEG))))
                    (COND ((AND (MEMBER-EQUAL (CAR TYPE-ARG1)
                                              SINGLETON-TYPE-SETS)
                                (NULL (CDR TYPE-ARG1)))
                           (SETQ FALSE-SEG
                                 (CONS (CONS ARG2
                                             (CONS (TSLOGDIFF (CAR TYPE-ARG2)
                                                              (CAR TYPE-ARG1))
                                                   (CDR TYPE-ARG2)))
                                       FALSE-SEG))))
                    (COND ((AND (TS= 0 (CAR TYPE-ARG2))
                                (INT= (LENGTH (CDR TYPE-ARG2)) 1)
                                (MEMBER-EQ (CADR TYPE-ARG2) (CDR TYPE-ARG1)))
                           (SETQ FALSE-SEG
                                 (CONS (CONS ARG1
                                             (CONS (CAR TYPE-ARG1)
                                                   (REMOVE (CADR TYPE-ARG2)
                                                           (CDR TYPE-ARG1)
                                                           :TEST #'EQUAL)))
                                       FALSE-SEG))))
                    (COND ((AND (TS= 0 (CAR TYPE-ARG1))
                                (INT= (LENGTH (CDR TYPE-ARG1)) 1)
                                (MEMBER-EQ (CADR TYPE-ARG1) (CDR TYPE-ARG2)))
                           (SETQ FALSE-SEG
                                 (CONS (CONS ARG2
                                             (CONS (CAR TYPE-ARG2)
                                                   (REMOVE (CADR TYPE-ARG1)
                                                           (CDR TYPE-ARG2)
                                                           :TEST #'EQUAL)))
                                       FALSE-SEG)))))))
          (T (SETQ TYPE-ARG1 (DEFN-TYPE-SET TERM))
             (COND ((AND (TS= (CAR TYPE-ARG1) TYPE-SET-FALSE)
                         (NULL (CDR TYPE-ARG1)))
                    (SETQ LOCAL-MUST-BE-FALSE T))
                   ((AND (NULL (CDR TYPE-ARG1))
                         (TS= 0 (TSLOGAND (CAR TYPE-ARG1) TYPE-SET-FALSE)))
                    (SETQ LOCAL-MUST-BE-TRUE T))
                   (T (SETQ TRUE-SEG
                            (LIST (CONS TERM (CONS (TSLOGAND (CAR TYPE-ARG1)
                                                             (TSLOGNOT
                                                              TYPE-SET-FALSE))
                                                   (CDR TYPE-ARG1)))))
                      (SETQ FALSE-SEG
                            (LIST (CONS TERM (CONS TYPE-SET-FALSE NIL))))))))
    (SETQ TRUE-TYPE-ALIST (NCONC TRUE-SEG TYPE-ALIST))
    (SETQ FALSE-TYPE-ALIST (NCONC FALSE-SEG TYPE-ALIST))
    (SETQ MUST-BE-TRUE LOCAL-MUST-BE-TRUE)
    (SETQ MUST-BE-FALSE LOCAL-MUST-BE-FALSE)
    NIL))

(DEFUN DEFN-LOGIOR (X Y)
  (CONS (TSLOGIOR (CAR X) (CAR Y))
        (UNION-EQ (CDR X) (CDR Y))))

(DEFUN DEFN-SETUP (EVENT)
  (SETQ ORIGEVENT EVENT)
  (SETQ LAST-PROCESS (QUOTE SETUP))
  (SETQ EXPAND-LST HINTED-EXPANSIONS)
  (SETQ TERMS-TO-BE-IGNORED-BY-REWRITE NIL)
  (SETQ INDUCTION-HYP-TERMS NIL)
  (SETQ INDUCTION-CONCL-TERMS NIL)
  (SETQ STACK NIL)
  (SETQ FNSTACK NIL)
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
  (RANDOM-INITIALIZATION ORIGEVENT)
  EVENT)

(DEFUN DEFN-TYPE-SET (TERM)
  (COND ((QUOTEP TERM)
         (CONS (CAR (TYPE-PRESCRIPTION (FN-SYMB TERM))) NIL))
        ((SETQ TEMP-TEMP (ASSOC-EQUAL TERM TYPE-ALIST))
         (CDR TEMP-TEMP))
        ((VARIABLEP TERM)
         (ER HARD (TERM) DEFN-TYPE-SET |has| |found| |an| |unbound| |variable|
             |in| |the| |term| (!TERM TERM (QUOTE |.|))))
        ((EQ (FN-SYMB TERM) (QUOTE IF))
         (DEFN-ASSUME-TRUE-FALSE (FARGN TERM 1))
         (COND (MUST-BE-TRUE (DEFN-TYPE-SET (FARGN TERM 2)))
               (MUST-BE-FALSE (DEFN-TYPE-SET (FARGN TERM 3)))
               (T (DEFN-LOGIOR (DEFN-TYPE-SET2 (FARGN TERM 2)
                                 TRUE-TYPE-ALIST)
                    (DEFN-TYPE-SET2 (FARGN TERM 3)
                      FALSE-TYPE-ALIST)))))
        ((SETQ TEMP-TEMP (TYPE-PRESCRIPTION (FN-SYMB TERM)))
         (DEFN-LOGIOR (CONS (CAR TEMP-TEMP) NIL)
           (COND ((CDR TEMP-TEMP)
                  (ITERATE FOR ARG IN (SARGS TERM)
                           AS FLG IN (CDR TEMP-TEMP) WITH ANS
                           INITIALLY (SETQ ANS (CONS 0 NIL))
                           WHEN FLG
                           DO (SETQ ANS (DEFN-LOGIOR (DEFN-TYPE-SET ARG) ANS))
                           FINALLY (RETURN ANS)))
                 (T (CONS 0 NIL)))))
        (T (CONS TYPE-SET-UNKNOWN NIL))))

(DEFUN DEFN-TYPE-SET2 (TERM TYPE-ALIST)
  (LET (FALSE-TYPE-ALIST) (DEFN-TYPE-SET TERM)))

(DEFUN DEFN-WRAPUP (WON-FLG)
  (SETQ WON-FLG (COND (WON-FLG (QUOTE DEFN-OK))
                      (T NIL)))
  (COND ((NOT (EQ LEMMA-STACK ORIG-LEMMA-STACK))
         (ITERPRI T)
         (ER WARNING NIL DEFN-WRAPUP |found| |a| |non-trivial| LEMMA-STACK
             EXCL)))
  (COND ((NOT (EQ LINEARIZE-ASSUMPTIONS-STACK
                  ORIG-LINEARIZE-ASSUMPTIONS-STACK))
         (ITERPRI T)
         (ER WARNING NIL DEFN-WRAPUP |found| |a| |non-trivial|
             LINEARIZE-ASSUMPTIONS-STACK EXCL)))
  (COND ((NOT WON-FLG)
         (COND ((NULL PROVE-TERMINATION-CASES-TRIED)
                (ER SOFT () |The| |admissibility| |of| |this| |definition|
                    |has| |not| |been| |established| |.|  |The| |theorem|
                    |prover's|
                    |heuristics| |found| |no| |plausible| |measure| |to|
                    |justify|
                    |the| |recursion| |.|  |In| |particular| |,| |no| |single|
                    |argument| |of| |the| |function| |is| |both| |tested|
                    |in| |each| |branch| |and| |changed| |in| |each|
                    |recursive|
                    |call| |.| |The| |definition| |is| |rejected| |.|))
               (T

                (ER SOFT
                    ((WHY (ITERATE FOR X IN PROVE-TERMINATION-CASES-TRIED
                                   COLLECT
                                   (LIST (QUOTE PROGN)
                                         (PQUOTE |Relation: |)
                                         (LIST (QUOTE !PPR)
                                               (KWOTE (CAAR X)) NIL)
                                         (QUOTE CR)
                                         (PQUOTE |Measure:  |)
                                         (LIST (QUOTE !PPR)
                                               (KWOTE (CADAR X)) NIL)
                                         (QUOTE CR)
                                         (PQUOTE |Unproved goals:|)
                                         (QUOTE CR)
                                         (LIST (QUOTE !CLAUSE-SET)
                                               (KWOTE (CDR X)) 5)))))
                    |The| |admissibility| |of| |this| |definition|
                    |has| |not| |been| |established| |.|  |The| |simplifier|
                    |could| |not| |prove| |that| |the| |measure(s)|
                    |tried| |decrease| |in| |each| |recursive|
                    |call| |.| |The| |definition| |is| |rejected| |.|
                    |Below| |are| |listed| |the| |relations| |and|
                    |measures| |tried| |and| |some| |of| |the|
                    |unproved| |goals| |for| |each| |.| CR CR
                    (!LIST1 WHY
                            (PQUOTE (PROGN CR CR))
                            (PQUOTE (PROGN CR CR)))
                    CR CR)))))
  (OR PETITIO-PRINCIPII
      (IO (QUOTE FINISHED)
          NIL NIL NIL (LIST WON-FLG))))

(DEFUN DEFN0 (NAME ARGS BODY RELATION-MEASURE-LST TRANSLATE-FLG LISP-CODE-FLG)

  #|
;   This function is FUNCALLed and therefore may not be made a MACRO.

;   The list of comments on this function do not necessarily describe the code
;   below.  They have been left around in reverse chronology order to remind us
;   of the various combinations of preprocessing we have tried.

;   If we ever get blown out of the water while normalizing IFs in a large
;   defn, read the following comment before abandoning normalization.

;   18 August 1982.  Here we go again!  At the time of this writing the
;   preprocessing of defns is as follows, we compute the induction and type
;   info on the translated body and store under sdefn the translated body.
;   This seems to slow down the system a lot and we are going to change it so
;   that we store under sdefn the result of expanding boot strap nonrec fns and
;   normalizing IFs.  As nearly as we can tell from the comments below, we have
;   not previously tried this.  According to the record, we have tried
;   expanding all nonrec fns, and we have tried expanding boot strap fns and
;   doing a little normalization.  The data that suggests this will speed
;   things up is as follows.  Consider the first call of SIMPLIFY-CLAUSE in the
;   proof of PRIME-LIST-TIMES-LIST.  The first three literals are trivial but
;   the fourth call of SIMPLIFY-CLAUSE1 is on (NOT (PRIME1 C (SUB1 C))).  With
;   SDEFNs not expanded and normalized -- i.e., under the processing as it was
;   immediately before the current change -- there are 2478 calls of REWRITE
;   and 273 calls of RELIEVE-HYPS for this literal.  With all defns
;   preprocessed as described here those counts drop to 1218 and 174.  On a
;   sample of four theorems, PRIME-LIST-TIMES-LIST, PRIME-LIST-PRIME-FACTORS,
;   FALSIFY1-FALSIFIES, and ORDERED-SORT, the use of normalized and expanded
;   sdefns saves us 16 percent of the conses over the use of untouched sdefns,
;   reducing the cons counts for those theorems from 880K to 745K.  It seems
;   unlikely that this preprocessing will blow us out of the water on large
;   defns.  For the EV used in UNSOLV and for the 386L M with subroutine call
;   this new preprocessing only marginally increases the size of the sdefn.  It
;   would be interesting to see a function that blows us out of the water.
;   When one is found perhaps the right thing to do is to so preprocess small
;   defns and leave big ones alone.

;   17 December 1981.  Henceforth we will assume that the very body the user
;   supplies (modulo translation) is the body that the theorem-prover uses to
;   establish that there is one and only one function satisfying the definition
;   equation by determining that the given body provides a method for computing
;   just that function.  This prohibits our "improving" the body of definitions
;   such as (f x) = (if (f x) a a) to (f x) = a.

;   18 November 1981.  We are sick of having to disable nonrec fns in order to
;   get large fns processed, e.g., the interpreter for our 386L class.  Thus,
;   we have decided to adopt the policy of not touching the user's typein
;   except to TRANSLATE it.  The induction and type analysis as well as the
;   final SDEFN are based on the translated typein.

;   Before settling with the preprocessing used below we tried several
;   different combinations and did provealls.  The main issue was whether we
;   should normalize sdefns.  Unfortunately, the incorporation of META0-LEMMAS
;   was also being experimented with, and so we do not have a precise breakdown
;   of who is responsible for what.  However, below we give the total stats for
;   three separate provealls.  The first, called 1PROVEALL, contained exactly
;   the code below -- except that the ADD-DCELL was given the SDEFN with all
;   the fn names replaced by *1*Fns instead of a fancy TRANSLATE-TO-INTERLISP
;   call.  Here are the 1PROVEALL stats.  Elapsed time = 9532.957, CPU time =
;   4513.88, GC time = 1423.261, IO time = 499.894, CONSes consumed = 6331517.

;   We then incorporated META0-LEMMAS.  Simultaneously, we tried
;   running the RUN fns through DEFN and found that we exploded.  The
;   expansion of nonrec fns and the normalization of IFs before the
;   induction analysis transformed functions of CONS-COUNT 300 to
;   functions of CONS-COUNT exceeding 18K.  We therefore decided to
;   expand only BOOT-STRAP fns -- and not NORMALIZE-IFS for the
;   purposes of induction analysis.  After the induction and type
;   analyses were done, we put down an SDEFN with some trivial IF
;   simplification performed -- e.g., IF X Y Y => Y and IF bool T F =>
;   bool -- but not a NORMALIZE-IFs version.  We then ran a proveall
;   with CANCEL around as a META0-LEMMA.  The result was about 20
;   percent slower than the 1PROVEALL and used 15 percent more CONSes.
;   At first this was attributed to CANCEL.  However, we then ran two
;   simultaneous provealls, one with META0-LEMMAS set to NIL and one
;   with it set to ((1CANCEL . CORRECTNESS-OF-CANCEL)).  The result
;   was that the version with CANCEL available used slightly fewer
;   CONSes than the other one -- 7303311 to 7312505 That was
;   surprising because the implementation of META0-LEMMAS uses no
;   CONSes if no META0-LEMMAS are available, so the entire 15 percent
;   more CONSes had to be attributed to the difference in the defn
;   processing.  This simultaneous run was interesting for two other
;   reasons.  The times -- while still 20 percent worse than 1PROVEALL
;   -- were one half of one percent different, with CANCEL being the
;   slower.  That means having CANCEL around does not cost much at all
;   -- and the figures are significant despite the slop in the
;   operating system's timing due to thrashing because the two jobs
;   really were running simultaneously.  The second interesting fact
;   is that CANCEL can be expected to save us a few CONSes rather than
;   cost us.

;   We therefore decided to return the DEFN0 processing to its original state.
;   Only we did it in two steps.  First, we put NORMALIZE-IFs into the
;   pre-induction processing and into the final SDEFN processing.  Here are the
;   stats on the resulting proveall, which was called
;   PROVEALL-WITH-NORM-AND-CANCEL but not saved.  Elapsed time = 14594.01, CPU
;   time = 5024.387, GC time = 1519.932, IO time = 593.625, CONSes consumed
;   = 6762620.

;   While an improvement, we were still 6 percent worse than 1PROVEALL on
;   CONSes.  But the only difference between 1PROVEALL and
;   PROVEALL-WITH-NORM-AND-CANCEL -- if you discount CANCEL which we rightly
;   believed was paying for itself -- was that in the former induction analyses
;   and type prescriptions were being computed from fully expanded bodies while
;   in the latter they were computed from only BOOT-STRAP-expanded bodies.  We
;   did not believe that would make a difference of over 400,000 CONSes, but
;   had nothing else to believe.  So we went to the current state, where we do
;   the induction and type analyses on the fully expanded and normalized bodies
;   -- bodies that blow us out of the water on some of the RUN fns.  Here are
;   the stats for PROVEALL-PROOFS.79101, which was the proveall for that
;   version. Elapsed time = 21589.84, CPU time = 4870.231, GC time = 1512.813,
;   IO time = 554.292, CONSes consumed= 6356282.

;   Note that we are within 25K of the number of CONSes used by 1PROVEALL.  But
;   to TRANSLATE-TO-INTERLISP all of the defns in question costs 45K.  So -- as
;   expected -- CANCEL actually saved us a few CONSes by shortening proofs.  It
;   takes only 18 seconds to TRANSLATE-TO-INTERLISP the defns, so a similar
;   argument does not explain why the latter proveall is 360 seconds slower
;   than 1PROVEALL.  But since the elapsed time is over twice as long, we
;   believe it is fair to chalk that time up to the usual slop involved in
;   measuring cpu time on a time sharing system.

;   We now explain the formal justification of the processing we do on the body
;   before testing it for admissibility.

;   We do not work with the body that is typed in by the user but with an
;   equivalent body' produced by normalization and the expansion of
;   nonrecursive function calls in body.  We now prove that if (under no
;   assumptions about NAME except that it is a function symbol of the correct
;   arity) (a) body is equivalent to body' and (b) (name . args) = body' is
;   accepted under our principle of definition, then there exists exactly one
;   function satisfying the original equation (name . args) = body.

;   First observe that since the definition (name . args) = body' is accepted
;   by our principle of definition, there exists a function satisfying that
;   equation.  But the accepted equation is equivalent to the equation (name .
;   args) = body by the hypothesis that body is equivalent to body'.

;   We prove that there is only one such function by induction.  Assume that
;   the definition (name . args) = body has been accepted under the principle
;   of definition.  Suppose that f is a new name and that (f . args) = bodyf,
;   where bodyf results from replacing every use of name as a function symbol
;   in body with f.  It follows that (f . args) = bodyf', where bodyf' results
;   from replacing every use of name as a function symbol in body' with f.  We
;   can now easily prove that (f . args) = (name . args) by induction according
;   to the definition of name. Q.E.D.

;   One might be tempted to think that if the defn with body' is accepted under
;   the principle of definition then so would be the defn with body and that
;   the use of body' was merely to make the implementation of the defn
;   principle more powerful.  This is not the case.  For example

;        (R X) = (IF (R X) T T)

;   is not accepted by the definitional principle, but we would accept the
;   body'-version (R X) = T, and by our proof, that function uniquely satisfies
;   the equation the user typed in.

;   One might be further tempted to think that if we changed normalize so that
;   (IF X Y Y) = Y was not applied, then the two versions were inter-acceptable
;   under the defn principle.  This is not the case either.  The function

;        (F X) = (IF (IF (X.ne.0) (F X-1) F) (F X-1) T)

;   is not accepted under the principle of defn.  Consider its normalized body.

|#

  (LET (CONTROL-VARS
        (ARITY-ALIST (CONS (CONS NAME (LENGTH ARGS)) ARITY-ALIST))
        FLG BODY1 ALIST)

    (COND (TRANSLATE-FLG
           (SETQ BODY (TRANSLATE-AND-CHK BODY))
           (SETQ RELATION-MEASURE-LST
                 (ITERATE FOR X IN RELATION-MEASURE-LST
                          COLLECT (LIST (CAR X)
                                        (TRANSLATE-AND-CHK (CADR X)))))))
    (DEFN-SETUP (LIST (QUOTE DEFN) NAME ARGS BODY RELATION-MEASURE-LST))
    (COND ((AND (NOT IN-BOOT-STRAP-FLG)
                (NOT (EQ *1*THM-MODE$ (QUOTE THM)))
                (ERRATICP BODY))
           (ADD-FACT NAME (QUOTE ERRATICP) T)))
    (PUT-INDUCTION-INFO NAME ARGS BODY RELATION-MEASURE-LST)
    (ADD-FACT NAME (QUOTE SDEFN)
              (LIST (QUOTE LAMBDA)
                    ARGS
                    (NORMALIZE-IFS (EXPAND-BOOT-STRAP-NON-REC-FNS
                                    BODY)
                                   NIL NIL NIL)))
    (PUT-TYPE-PRESCRIPTION NAME)
    (PUT-LEVEL-NO NAME)
    (AND (GET NAME (QUOTE JUSTIFICATIONS))
         (ADD-FACT NAME (QUOTE CONTROLLER-POCKETS)
                   (SCRUNCH (ITERATE FOR TEMP
                                     IN (GET NAME (QUOTE JUSTIFICATIONS))
                                     COLLECT
                                     (PROGN
                                       (SETQ CONTROL-VARS
                                             (ACCESS JUSTIFICATION SUBSET
                                                     TEMP))
                                       (ITERATE FOR FORMAL IN ARGS
                                                AS I FROM 0
                                                WITH ITERATE-ANS = 0
                                                WHEN (MEMBER-EQ FORMAL
                                                                CONTROL-VARS)
                                                DO
                                                (SETQ ITERATE-ANS
                                                      (CTLOGIOR ITERATE-ANS
                                                                (CTASH 1 I)))
                                                FINALLY (RETURN
                                                         ITERATE-ANS)))))))

;   When *1*THM-MODE$ is 'THM, everything is TOTALP except APPLY$ and EVAL$.
;   The SUBRP property is irrelevent in THM mode but is set as it would have
;   been in NQTHM mode.

    (PUT-TOTALP NAME)
    (ADD-FACT NAME (QUOTE SUBRP)
              (COND ((AND IN-BOOT-STRAP-FLG
                          (NOT (MEMBER-EQ NAME
                                          (QUOTE (V&C$ V&C-APPLY$
                                                       APPLY$ EVAL$ FOR)))))
                     *1*T)
                    (T *1*F)))     

;   The routine *1**BODY uses the EVENT property of NAME to recover the
;   BODY of the litatom unless the BODY property is non-NIL.  We must set
;   the BODY property for those boot-strap fns that are non-SUBRS (since
;   they don't have EVENT properties) and for those user-defined fns whose
;   bodies are axiomatized specially.

    (COND ((AND (MATCH BODY (EVAL$ (LIST (QUOTE QUOTE) FLG)
                                   (LIST (QUOTE QUOTE) BODY1)
                                   ALIST))
                (NOT (EQ FLG (QUOTE LIST)))
                (TERMP BODY1)
                (EQUAL ALIST (STANDARD-ALIST ARGS))
                (SUBSETP-EQ (ALL-VARS BODY1) ARGS))
           (ADD-FACT NAME (QUOTE BODY) BODY1))
          ((MEMBER-EQ NAME (QUOTE (APPLY$ EVAL$ V&C$ V&C-APPLY$ FOR)))
           (ADD-FACT NAME (QUOTE BODY) BODY)))


    (COND ((EQ LISP-CODE-FLG T)
           (ADD-FACT NAME (QUOTE LISP-CODE)
                     (PACK (LIST PREFIX-FOR-FUNCTIONS NAME)))
           (GUARANTEE-CITIZENSHIP
            (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))))
          (LISP-CODE-FLG
           
;   When LISP-CODE-FLG is non-NIL but non-T, it is a Lisp LAMBDA expression
;   suitable for giving to ADD-DCELL for compilation, etc.
           
           (ADD-DCELL NAME
                      (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))
                      LISP-CODE-FLG))
          (T
           (ITERATE FOR FN IN (ALL-FNNAMES BODY)
                    DO (OR (EQ FN NAME)
                           (GET FN (QUOTE LISP-CODE))
                           (COND (IN-BOOT-STRAP-FLG
                                  (ER WARNING (FN NAME) |it| |was| |thought|
                                      |that| |every| |function| |symbol| |had|
                                      |a|
                                      LISP-CODE |property| |but| |,| |in| |the|
                                      |definition| |of| (!PPR NAME (QUOTE |,|))
                                      (!PPR FN NIL) |does| |not| |.|))
                                 (T (ER HARD (FN NAME) |it| |was| |thought|
                                        |that| |every| |function| |symbol|
                                        |had|
                                        |a| LISP-CODE |property| |but| |,| |in|
                                        |the| |definition| |of|
                                        (!PPR NAME (QUOTE |,|))
                                        (!PPR FN NIL) |does| |not| |.|)))))
           (ADD-DCELL NAME (PACK (LIST PREFIX-FOR-FUNCTIONS NAME))
                      (LET ((TEMP (ITERATE FOR ARG IN ARGS COLLECT
                                           (PACK (LIST PREFIX-FOR-FORMALS
                                                       ARG)))))
                        (LIST (QUOTE LAMBDA)
                              TEMP
                              (MAYBE-IGNORE-SOME-ARGS
                               (SET-DIFF ARGS (ALL-VARS BODY))
                               (MAYBE-MONITOR
                                NAME
                                (TOTALP NAME)
                                (TRANSLATE-TO-LISP
                                 (SUB-PAIR-VAR ARGS TEMP
                                               BODY)))))))))
    (COND (IN-BOOT-STRAP-FLG
           (COND ((MEMBER-EQ NAME (QUOTE (V&C$)))

;   The QUOTEd list above should include every inadmissible BOOT-STRAP
;   function.  Once, we printed a warning at BOOT-STRAP time if a
;   function was inadmissible.  We are tired of seeing it and no
;   longer print it.  However, once a minor change to
;   PROVE-TERMINATION introduced a bug that caused everything to be
;   accepted.  The bug was noticed only because the warning message
;   for V&C$ was NOT printed at BOOT-STRAP.  So we have decided to be
;   very rigid and force ourselves to declare, in the list above,
;   every function that is inadmissible and check that they and only
;   they are inadmissible.
                  
                  (COND ((ADMITTED-FUNCTIONP NAME)
                         (ER HARD (NAME) DEFN0 |expected| (!PPR NAME NIL) |to|
                             |have| |unjustified| |recursion| |but| |the|
                             |function| |has| |been|
                             |admitted| |without| |comment| EXCL))))
                 ((NOT (ADMITTED-FUNCTIONP NAME))
                  (ER WARNING (NAME) |The| |recursion| |in| (!PPR NAME NIL)
                      |is| |unjustified| |.| |Since| |this| |is| |in| |a|
                      BOOT-STRAP
                      |we| |will| |not| |undo| |the| |definition| |.|
                      |To| |silence|
                      |this| |warning| |add| |the| |inadmissible| |function|
                      |name|
                      |to| |the| |list| |at| |the| |end| |of| DEFN0 |.|)))))
    NIL))

(DEFUN DELETE1 (X L)
  (COND ((ATOM L) NIL)
        ((EQUAL X (CAR L)) (CDR L))
        (T (CONS (CAR L) (DELETE1 X (CDR L))))))

(DEFUN DELETE-TAUTOLOGIES (CLAUSE-SET)
  (ITERATE FOR CL IN CLAUSE-SET
           UNLESS (ITERATE FOR TAIL ON CL
                           THEREIS (OR (AND (FALSE-NONFALSEP (CAR TAIL))
                                            (NOT DEFINITELY-FALSE))
                                       (MEMBER-EQUAL (NEGATE-LIT (CAR TAIL))
                                                     (CDR TAIL))))
           COLLECT CL))

(DEFUN DEPEND (DEPENDENT SUPPORTERS)
  (COND ((NOT (GET DEPENDENT (QUOTE EVENT)))
         (ER HARD (DEPENDENT) DEPEND |should| |not| |be| |called| |on| |a|
             |nonevent| |such| |as| (!PPR DEPENDENT (QUOTE |.|)))))
  (SETQ SUPPORTERS (REMOVE (QUOTE GROUND-ZERO)
                           (ITERATE FOR X IN SUPPORTERS WITH ITERATE-ANS DO
                                    (SETQ ITERATE-ANS
                                          (ADD-TO-SET (MAIN-EVENT-OF X)
                                                      ITERATE-ANS))
                                    FINALLY (RETURN ITERATE-ANS))))
  (COND ((MEMBER-EQ DEPENDENT SUPPORTERS)
         (ER HARD (DEPENDENT) |Attempt| |to| |make| (!PPR DEPENDENT NIL)
             |depend| |upon| |itself| EXCL)))
  (ITERATE FOR X IN SUPPORTERS DO (ADD-FACT X (QUOTE IMMEDIATE-DEPENDENTS0)
                                            DEPENDENT)))

(DEFUN DEPENDENT-EVENTS (EVENT)
  (ITERATE FOR X IN (DEPENDENTS-OF EVENT) COLLECT (GET X (QUOTE EVENT))))

(DEFUN DEPENDENTS-OF (NAME)
  (COND ((EQ NAME (QUOTE GROUND-ZERO))
         (REVERSE CHRONOLOGY))
        ((OR (NOT (SYMBOLP NAME))
             (NOT (GET NAME (QUOTE EVENT))))
         (ER HARD (NAME) DEPENDENTS-OF |must| |be| |given| |an| |event| |and|
             (!PPR NAME NIL) |is| |not| |one| |.|))
        ((EQ NAME (CAR CHRONOLOGY))
         (LIST NAME))
        (T (SORT-EVENTS (DEPENDENTS-OF1 NAME)))))

(DEFUN DEPENDENTS-OF1 (NAME)
  (COND ((EQ NAME (QUOTE GROUND-ZERO))

;   We never expect this fn to be called on GROUND-ZERO because its silly, but
;   we make it behave correctly anyway.

         (COPY-LIST CHRONOLOGY))
        (T (CONS NAME
                 (SCRUNCH (ITERATE FOR X IN (IMMEDIATE-DEPENDENTS-OF NAME)
                                   NCONC (DEPENDENTS-OF1 X)))))))

(DEFUN DESTRUCTORS (CL)

;   This function returns the set of subterms of CL such that every member is
;   the application of a function to one or more distinct variables.

  (LET (ANS) (ITERATE FOR LIT IN CL DO (DESTRUCTORS1 LIT)) ANS))

(DEFUN DESTRUCTORS1 (TERM)
  (COND ((OR (VARIABLEP TERM) (FQUOTEP TERM)) NIL)
        (T (ITERATE FOR ARG IN (FARGS TERM) DO (DESTRUCTORS1 ARG))
           (COND ((AND (FARGS TERM)
                       (ITERATE FOR ARG IN (FARGS TERM) ALWAYS (VARIABLEP ARG))
                       (NO-DUPLICATESP (FARGS TERM)))
                  (SETQ ANS (ADD-TO-SET TERM ANS)))))))

(DEFUN DISABLED-BY-BOOT-STRAPP (NAME)

; Return T iff NAME was disabled at the end of the BOOT-STRAP.
; This means that the most recent triple on DISABLED-LEMMAS
; of the form (name GROUND-ZERO . flg) has flg = T.

  (ITERATE FOR PAIR IN DISABLED-LEMMAS
           WHEN (AND (EQ (CADR PAIR) 'GROUND-ZERO)
                     (EQ (CAR PAIR) NAME))
           DO (RETURN (CDDR PAIR))))

(DEFUN DISJOIN (LST IF-FLG)
  (COND ((NULL LST) FALSE)
        ((NULL (CDR LST)) (DISJOIN2 (CAR LST) FALSE IF-FLG))
        ((NULL (CDDR LST)) (DISJOIN2 (CAR LST) (CADR LST) IF-FLG))
        (T (DISJOIN2 (CAR LST) (DISJOIN (CDR LST) IF-FLG) IF-FLG))))

(DEFUN DISJOIN-CLAUSES (CL1 CL2)
  (COND ((OR (EQUAL CL1 TRUE-CLAUSE) (EQUAL CL2 TRUE-CLAUSE))
         TRUE-CLAUSE)
        ((ITERATE FOR LIT1 IN CL1 THEREIS
                  (ITERATE FOR LIT2 IN CL2
                           THEREIS (COMPLEMENTARYP LIT1 LIT2)))
         TRUE-CLAUSE)
        (T (APPEND CL1 (SET-DIFF CL2 CL1)))))

(DEFUN DISJOIN2 (P Q IF-FLG)
  (COND ((FALSE-NONFALSEP P)
         (COND (DEFINITELY-FALSE (COND ((FALSE-NONFALSEP Q)
                                        (COND (DEFINITELY-FALSE FALSE)
                                              (T TRUE)))
                                       ((NOT (OUR-BOOLEAN Q))
                                        (FCONS-TERM* (QUOTE IF)
                                                     Q TRUE FALSE))
                                       (T Q)))
               (T TRUE)))
        ((FALSE-NONFALSEP Q)
         (COND (DEFINITELY-FALSE (COND ((OUR-BOOLEAN P) P)
                                       (T (FCONS-TERM* (QUOTE IF)
                                                       P TRUE FALSE))))
               (T TRUE)))
        (IF-FLG (FCONS-TERM* (QUOTE IF)
                             P TRUE (COND ((OUR-BOOLEAN Q) Q)
                                          (T (FCONS-TERM* (QUOTE IF)
                                                          Q TRUE FALSE)))))
        (T (FCONS-TERM* (QUOTE OR) P Q))))

(DEFUN DO-EVENTS (EVENTS)

;   This function executes each of the event commands in EVENTS.  It prints
;   each event form to PROVE-FILE and then executes it, accumulating the total
;   event times and printing the event names to the terminal if the output is
;   going elsewhere.  It aborts if some event causes an error or fails.  It
;   prints the system configuration and the accumulated times at the end of
;   PROVE-FILE.  It does not open or close any file.  It returns T if all
;   events succeeded and NIL is some failed.

  (LET (ANS FORM)
    (PROG NIL
          (SETQ UNDONE-EVENTS EVENTS)
          LOOP
          (COND ((ATOM UNDONE-EVENTS)
                 (RETURN T)))
          (SETQ FORM (CAR UNDONE-EVENTS))

;   Print out the event form to PROVE-FILE and, if PROVE-FILE is not the
;   terminal, print the name to the terminal

          (ITERPRIN 1 PROVE-FILE)
          (IPRINC EVENT-SEPARATOR-STRING PROVE-FILE)
          (ITERPRIN 2 PROVE-FILE)
          (PPRIND FORM 0 0 PROVE-FILE)
          (ITERPRI PROVE-FILE)
          (COND ((NOT (EQ PROVE-FILE NIL))
                 (IPRINC (CADR FORM) NIL)))

;   Evaluate the event form

          (SETQ ANS (ERROR1-SET (EVAL FORM)))
          (COND ((NULL ANS)
                 
;   A SOFT ERROR1 occurred during the evaluation.  Perhaps we should
;   let the user edit the form, but we have no standard editor in the
;   system.
                 
                 (RETURN NIL)))

;   Recover the actual value from the CONS produced by the ERROR1-SET
;   protection

          (SETQ ANS (CAR ANS))
                 
;   Print the answer to PROVE-FILE and, if PROVE-FILE is not the terminal,
;   print a comma or the failure message, as appropriate, to the terminal
;   to indicate completion of the event.

          (ITERPRI PROVE-FILE)
          (IPRINC ANS PROVE-FILE)
          (COND ((NOT (EQ PROVE-FILE NIL))
                 (COND ((EQ ANS NIL)
                        (ITERPRI NIL)
                        (IPRINC FAILURE-MSG NIL)
                        (ITERPRI NIL))
                       (T (IPRINC (QUOTE |,|) NIL)
                          (COND ((< (OUR-LINEL NIL NIL)
                                    (IPOSITION NIL NIL NIL))
                                 (ITERPRI NIL)))))))

;   Exit if the command failed.

          (COND ((EQ ANS NIL)
                 (RETURN NIL)))

;   Otherwise, continue looping.

          (SETQ UNDONE-EVENTS (CDR UNDONE-EVENTS))
          (GO LOOP))))

(DEFUN DO-FILE (INFILE)

;   This function executes each of the event commands in the file INFILE. 
;   The events are top level forms in the file.  It prints
;   each event form to PROVE-FILE and then executes it, accumulating the total
;   event times and printing the event names to the terminal if the output is
;   going elsewhere.  It aborts if some event causes an error or fails.  It
;   prints the system configuration and the accumulated times at the end of
;   PROVE-FILE.  It returns T if all events succeeded and NIL if some failed.

  (WITH-OPEN-FILE (INSTREAM (EXTEND-FILE-NAME INFILE NIL)
                            :DIRECTION :INPUT
                            :IF-DOES-NOT-EXIST :ERROR)
    (LET (ANS FORM)
      (PROG NIL
            LOOP 
            (SETQ FORM (READ INSTREAM NIL A-VERY-RARE-CONS))
            (COND ((EQ FORM A-VERY-RARE-CONS)
                   (RETURN T)))
        
;   Print out the event form to PROVE-FILE and, if PROVE-FILE is not the
;   terminal, print the name to the terminal

            (ITERPRIN 1 PROVE-FILE)
            (IPRINC EVENT-SEPARATOR-STRING PROVE-FILE)
            (ITERPRIN 2 PROVE-FILE)
            (PPRIND FORM 0 0 PROVE-FILE)
            (ITERPRI PROVE-FILE)
            (COND ((NOT (EQ PROVE-FILE NIL))
                   (IPRINC (CADR FORM) NIL)))

;   Evaluate the event form

            (SETQ ANS (ERROR1-SET (EVAL FORM)))
            (COND ((NULL ANS)
                 
;   A SOFT ERROR1 occurred during the evaluation.  Perhaps we should
;   let the user edit the form, but we have no standard editor in the
;   system.
                 
                   (RETURN NIL)))

;   Recover the actual value from the CONS produced by the ERROR1-SET
;   protection

            (SETQ ANS (CAR ANS))
                 
;   Print the answer to PROVE-FILE and, if PROVE-FILE is not the terminal,
;   print a comma or the failure message, as appropriate, to the terminal
;   to indicate completion of the event.

            (ITERPRI PROVE-FILE)
            (IPRINC ANS PROVE-FILE)
            (COND ((NOT (EQ PROVE-FILE NIL))
                   (COND ((EQ ANS NIL)
                          (ITERPRI NIL)
                          (IPRINC FAILURE-MSG NIL)
                          (ITERPRI NIL))
                         (T (IPRINC (QUOTE |,|) NIL)
                            (COND ((< (OUR-LINEL NIL NIL)
                                      (IPOSITION NIL NIL NIL))
                                   (ITERPRI NIL)))))))

;   Exit if the command failed.

            (COND ((EQ ANS NIL) (RETURN NIL)))

;   Otherwise, continue looping.

            (GO LOOP)))))

(DEFUN DTACK-0-ON-END (X)
  (RPLACD (OUR-LAST X) 0) X)

(DEFUN DUMB-CONJOIN (L)
  (COND ((NULL L) TRUE)
        ((NULL (CDR L)) (CAR L))
        (T (XXXJOIN 'AND L))))

(DEFUN DUMB-CONVERT-TYPE-SET-TO-TYPE-RESTRICTION-TERM (TYPE-SET ARG)

;   WARNING:  This function does not return a legal term.  In particular, it
;   might return (AND a b c ...).  It should be used only for io purposes.

  (LET (LST)
    (COND ((TS= TYPE-SET TYPE-SET-UNKNOWN) T)
          ((TS= TYPE-SET 0) 'F)
          ((TS= 0 (ASH TYPE-SET -31))
           (SETQ LST (ITERATE FOR I FROM 0 TO 30
                              WHEN (NOT (TS= (TSLOGAND TYPE-SET (TSLOGBIT I))
                                             0))
                              COLLECT (CONVERT-TYPE-NO-TO-RECOGNIZER-TERM
                                       I ARG)))
           (COND ((NULL LST) 'F)
                 ((NULL (CDR LST)) (CAR LST))
                 (T (CONS (QUOTE OR) LST))))
          (T (SETQ LST (ITERATE FOR I FROM 0 TO 30
                                WHEN (TS= 0 (TSLOGAND TYPE-SET (TSLOGBIT I)))
                                COLLECT
                                (DUMB-NEGATE-LIT
                                 (CONVERT-TYPE-NO-TO-RECOGNIZER-TERM I ARG))))
             (COND ((NULL LST) T)
                   ((NULL (CDR LST)) (CAR LST))
                   (T (CONS (QUOTE AND) LST)))))))

(DEFUN DUMB-IMPLICATE-LITS (L1 L2)

;   Like DUMB-NEGATE-LIT, this function may be called when TYPE-ALIST is not
;   valid.  Hence this function should not be modified to use TYPE-SET.

  (COND ((QUOTEP L1)
         (COND ((EQUAL L1 FALSE) TRUE)
               (T L2)))
        (T (FCONS-TERM* (QUOTE IF) L1 L2 TRUE))))

(DEFUN DUMB-NEGATE-LIT (TERM)

;   Like DUMB-IMPLICATE-LITS, this function may be called when TYPE-ALIST is
;   not valid.  Hence this function should not be modified to use TYPE-SET.

  (COND ((VARIABLEP TERM)
         (FCONS-TERM* (QUOTE NOT) TERM))
        ((FQUOTEP TERM)
         (COND ((EQUAL TERM FALSE) TRUE)
               (T FALSE)))
        ((EQ (FN-SYMB TERM) (QUOTE NOT)) (FARGN TERM 1))
        (T (FCONS-TERM* (QUOTE NOT) TERM))))

(DEFUN DUMB-OCCUR (X Y)
  (COND ((EQUAL X Y) T)
        ((VARIABLEP Y) NIL)
        ((FQUOTEP Y) NIL)
        (T (ITERATE FOR ARG IN (FARGS Y) THEREIS (DUMB-OCCUR X ARG)))))

(DEFUN DUMB-OCCUR-LST (X LST)
  (ITERATE FOR TERM IN LST THEREIS (DUMB-OCCUR X TERM)))



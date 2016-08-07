;;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 -*- ;;;;

;  Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

;  Copying of this file is authorized to those who have read and
;  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
;  LICENSE" at the beginning of the Nqthm file "basis.lisp".

;  Pc-Nqthm Version 1992 (for use with Nqthm-1992)

; This file is the work of Matt Kaufmann.  It implements DEFN-SK, which is an
; `event' level function that permits one, as an extension to Nqthm, to define
; concepts involving universal and existential quantifiers.  It is included as
; part of the system Pc-Nqthm-1992, but has been written so that it can be
; loaded directly on top of Nqthm-1992, as described in the next paragraph.

; This file is not automatically compiled or loaded when building Nqthm-1992,
; unlike the situation for Pc-Nqthm-1992.  To use this file on top of
; Nqthm-1992, after compiling and loading Nqthm-1992, compile this file and
; then load it, i.e., (compile-file "defn-sk.lisp") and (load "defn-sk").

; All of the functions in this file are fully compatible with Pc-Nqthm-1992
; as well.  For example, UNTRANSLATE-EVENT is redefined (from Nqthm-1992)
; below, and its redefinition in the Pc-Nqthm-1992 file "top-nqthm.lisp"
; is identical to the one below.

#|
@techreport(Kaufmann43,
        author="Matt Kaufmann",
        title="DEFN-SK:  An Extension of the Boyer-Moore Theorem Prover to Handle First-Order Quantifiers",
        month="May",
        year="1989",
        key="Kaufmann",
        institution="Computational Logic, Inc.",
        number="43",
        note="To appear in J. of Automated Reasoning")
|#

(IN-PACKAGE "USER")

(EVAL-WHEN (LOAD EVAL COMPILE)
	   (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))

;; Try DEFN-SK+ in place of DEFN-SK for extra fun......

(setq LEGAL-PROVE-FILE-FNS
      (add-to-set 'defn-sk LEGAL-PROVE-FILE-FNS))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;       changes to translator etc. to allow forall and exists          ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar defn-sk-*extra-propertyless-symbols-alist*-extension
  (list
   '(exists |EXISTS| |has| |appeared| |in| |a| |term| |,| |but|
	    |it| |is| |only| |supposed| |to| |appear| |at| |the|
	    |top| |level| |in| |formulas| |.| |That| |is| |,|
	    |formulas| |are| |constructed| |from| |terms| |by| |applying|
	    |any| |number| |of| |the| |following| |operators| |:| AND |,|
	    OR |,| IMPLIES |,| NOT |,| IF |,| COND |,| FORALL |,| |and| EXISTS |,|
	    |as| |well| |as| CASE |when| |the| |first| |argument| |is| |a| |term| |.|
	    |But| |here| |we| |find| |the| |formula| (!ppr x nil)
	    |after| |already| |descending|
	    |to| |the| |level| |of| |terms| |.|)
   '(forall |FORALL| |has| |appeared| |in| |a| |term| |,| |but|
	    |it| |is| |only| |supposed| |to| |appear| |at| |the|
	    |top| |level| |in| |formulas| |.| |That| |is| |,|
	    |formulas| |are| |constructed| |from| |terms| |by| |applying|
	    |any| |number| |of| |the| |following| |operators| |:| AND |,|
	    OR |,| IMPLIES |,| NOT |,| IF |,| COND |,| FORALL |,| |and| EXISTS |,|
	    |as| |well| |as| CASE |when| |the| |first| |argument| |is| |a| |term| |.|
	    |But| |here| |we| |find| |the| |formula| (!ppr x nil)
	    |after| |already| |descending|
	    |to| |the| |level| |of| |terms| |.|)))

(defun extend-*extra-propertyless-symbols-alist*-for-defn-sk ()
  (append defn-sk-*extra-propertyless-symbols-alist*-extension
	  *extra-propertyless-symbols-alist*))

(cond
 ((not (assoc-eq 'forall *extra-propertyless-symbols-alist*))
  (setq *extra-propertyless-symbols-alist*
	(cons
	 '(forall |FORALL| |is| |only| |allowed| |to| |appear|
		  |inside| |formulas| |appearing| |in| |DEFN-SK| |events| |.|)
	 *extra-propertyless-symbols-alist*))))

(cond
 ((not (assoc-eq 'exists *extra-propertyless-symbols-alist*))
  (setq *extra-propertyless-symbols-alist*
	(cons
	 '(exists |EXISTS| |is| |only| |allowed| |to| |appear|
		  |inside| |formulas| |appearing| |in| |DEFN-SK| |events| |.|)
	 *extra-propertyless-symbols-alist*))))

(defun translate-inside-formula (x)
  (let ((*extra-propertyless-symbols-alist*
	 (extend-*extra-propertyless-symbols-alist*-for-defn-sk)))
    (translate x)))

;; Note that DEFVAR is used below in case someone else has already defined
;; this variable (e.g., in pc-nqthm).  But then we must be sure to add
;; DEFN-SK to the list.
(DEFVAR *UNTRANSLATE-EVENT-TYPES*
  '(ADD-SHELL BOOT-STRAP DCL TOGGLE TOGGLE-DEFINED-FUNCTIONS
	      DEFTHEORY SET-STATUS))

(EVAL-WHEN (LOAD)
	   (SETQ *UNTRANSLATE-EVENT-TYPES*
		 (ADD-TO-SET 'DEFN-SK *UNTRANSLATE-EVENT-TYPES*)))

(DEFUN UNTRANSLATE-EVENT (EVENT)
  (LET (NAME TYPES TERM ARGS BODY HINTS INTERACTIVE-HINT OLD-NAME-OR-LIST FS)
    (CASE (CAR EVENT)
          (ADD-AXIOM (MATCH! EVENT (ADD-AXIOM NAME TYPES TERM))
                     (LIST (QUOTE ADD-AXIOM)
                           NAME TYPES (UNTRANSLATE TERM)))
          (DEFN (COND ((INT= (LENGTH EVENT) 4)
                       (MATCH! EVENT (DEFN NAME ARGS BODY))
                       (LIST (QUOTE DEFN) NAME ARGS (UNTRANSLATE BODY)))
		      ;; here is support for interactive DEFN hints
		      ((INT= (LENGTH EVENT) 6)
                       (MATCH! EVENT (DEFN NAME ARGS BODY HINTS interactive-hint))
                       (LIST (QUOTE DEFN) NAME ARGS (UNTRANSLATE BODY)
                             (ITERATE FOR X IN HINTS COLLECT
                                      (LIST (CAR X)
                                            (UNTRANSLATE (CADR X))))
                             interactive-hint))
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
          (OTHERWISE
	   (IF (MEMBER-EQ (CAR EVENT) *UNTRANSLATE-EVENT-TYPES*)
	       EVENT
	       (ER HARD (EVENT) |The| |following| |event| |was| |not|
		   |recognized| |by|
		   UNTRANSLATE-EVENT |,| (!PPR EVENT (QUOTE |.|))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;    modifications to functional variables code   ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here we modify some of Boyer and Moore's functions so
;; that the functional variables work and quantifiers work (here) get
;; along together properly.

;; I need this from pc-nqthm.
(DEFUN MAKE-IMPLICATION (ASSUMPTIONS CONCL)
  (COND
    (ASSUMPTIONS
     (FCONS-TERM* (QUOTE IMPLIES) (DUMB-CONJOIN ASSUMPTIONS) CONCL))
    (T CONCL)))

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
                 (DEFN-SK
                   (ITERATE FOR X IN (GET NAME (QUOTE LEMMAS))
                            WITH SKOLEM-AXIOMS AND N AND HYPS AND CONCL
                            WHEN (AND (MATCH X (REWRITE-RULE N HYPS CONCL &))
                                      (EQ N NAME))
                            COLLECT (MAKE-IMPLICATION HYPS CONCL) INTO SKOLEM-AXIOMS
                            FINALLY
                            (IF (EQUAL (LENGTH SKOLEM-AXIOMS) 2)
                                (RETURN (FCONS-TERM* 'AND (CADR SKOLEM-AXIOMS) (CAR SKOLEM-AXIOMS)))
                                (ER HARD (NAME) |Wrong| |number| |of| |Skolem| |axioms| |for|
                                    (!PPR NAME (QUOTE |.|))))))
                 (OTHERWISE NIL)))
          ((AND (EQ (QUOTE GROUND-ZERO) (GET NAME (QUOTE MAIN-EVENT)))
                (SETQ EVENT (GET NAME (QUOTE SDEFN))))
           (FCONS-TERM* (QUOTE EQUAL)
                        (FCONS-TERM NAME (CADR EVENT))
                        (CADDR EVENT)))
          (T NIL))))

(DEFUN HITABLE-AXIOM-INTRODUCED-BY (NAME)
  (LET ((EV (GET NAME 'EVENT)))
       (CASE (CAR EV)
             (DEFN (FCONS-TERM* 'EQUAL
                                (FCONS-TERM (CADR EV) (CADDR EV))
                                (CADDDR EV)))
             ((ADD-AXIOM CONSTRAIN) (CADDDR EV))
             (DEFN-SK (FORMULA-OF NAME))
             ((DCL ADD-SHELL) TRUE)
             (OTHERWISE (ER HARD () HITABLE-AXIOM-INTRODUCED-BY |was|
                            |called| |on| |something| |other|
                            |than| |a| DEFN |,| ADD-AXIOM |,| DEFN-SK |,| 
                            CONSTRAIN |,| DCL |,|  |or| ADD-SHELL |.|)))))

(DEFUN ANCESTORS1 (EVN)

;  EVN is the name of an event that introduces some function symbols,
;  e.g., a DEFN, DCL, CONSTRAIN, DEFN-SK, ADD-SHELL, or the BOOT-STRAP.

  (COND ((GET EVN ANCESTORS-PROPERTY)
         NIL)
        (T (SETF (GET EVN ANCESTORS-PROPERTY) T)
           (LET ((EVENT (GET EVN 'EVENT)))
                (COND ((MEMBER-EQ (CAR EVENT) '(DEFN CONSTRAIN DEFN-SK))
                       (ITERATE FOR FN IN (ALL-FNNAMES (FORMULA-OF (CADR EVENT)))
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

;; Also, the comment for RELEVANT-EVENTS should now read as follows,
;; though no change to the code is necessary.

;  RELEVANT-EVENTS for thm and fs is the set of event names, ev, such
;  that (a) ev mentions some function symbol in the domain of fs
;  (otherwise there would be nothing to instantiate) and that (b)
;  either (i) ev is a DEFN or CONSTRAIN that introduces a function
;  symbol ancestral in thm or some add-axiom or (ii) ev is an
;  add-axiom.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;                     formulas                    ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We have two potentially interesting notions of formula -- one which
;; always accepts IF and IFF as valid connectives, and the other which
;; doesn't accept either as connectives (though they may, of course,
;; be functions), except that IF is accepted when its test is
;; quantifier-free.  The latter variety will be called the class of
;; "Skolemizable formulas", and is the only kind we'll consider here.
;; Not only are these the only kind that our Skolemizer will accept,
;; but also we believe that there aren't any really interesting
;; normalizations that can be done on more general formulas that can't
;; be done on the Skolemizable ones, at least if we're careful to do
;; any such normalizations automatically in the translation process
;; (e.g., (if x y f) => (and x y)).

;; NOTE:  We never translate after the initial translation.  That way
;; we can introduce new function symbols, through substitution, during
;; the Skolemization process, and we won't have errors caused by the
;; translator.

;; The FORMULA structure has a constructor CREATE-FORMULA; however, I
;; will define MAKE-FORMULA, which (optionally) computes the free variables,
;; and I'll restrict myself to using MAKE-FORMULA.

;; The args are:

;; If OP is 'TERM, then a term
;; If OP is a prop. connective, then a list of formulas
;; If OP is a quantifier, then a variable-formula list

(defstruct
  (formula
   (:constructor create-formula
		 (op args free-vars)))
  op args free-vars)

(defparameter true-formula (create-formula 'term true nil))

(defparameter false-formula (create-formula 'term false nil))

(defun or-? (x y)
  ;; like or except x is tested against '?
  (if (eq x '?) y x))

(defun collapse-formula (formula &aux
				 (op (formula-op formula))
				 (args (formula-args formula))
				 (free-vars (formula-free-vars formula)))
  ;; Pushes up term nodes.  *** Could improve this to sometimes avoid consing up new formulas.
  (case op
	((and or implies not if)
	 (setq args (mapcar #'collapse-formula args))
	 (if (iterate for arg in args
		      always (eq (formula-op arg) 'term))
	     (make-formula 'term
			   (fcons-term op (mapcar #'formula-args args))
			   free-vars)
	   (make-formula op args free-vars)))
	((forall exists)
	 (make-formula op (list (car args) (collapse-formula (cadr args))) free-vars))
	;; otherwise, we've got a term already
	(t formula)))

(defun make-if-formula (x y z free-vars &aux x1)
  ;; We require the test to be quantifier free.  I CAN resist eliminating
  ;; tests of T and F.  x, y, and z are all formulas.
  (cond
   ((equal y true-formula) (create-formula 'or (list x z) free-vars))
   ((equal y false-formula) (create-formula 'and (list (dumb-negate-formula x) z) free-vars))
   ((equal z true-formula) (create-formula 'implies (list x y) free-vars))
   ((equal z false-formula) (create-formula 'and (list x y) free-vars))
   ((eq (formula-op (setq x1 (collapse-formula x))) 'term)
    (create-formula 'if (list x1 y z) free-vars))
   (t
    (create-formula 'and
		    (list (create-formula 'implies (list x y)
					  (union-eq (formula-free-vars x)
						    (formula-free-vars y)))
			  (create-formula 'implies
					  (list (dumb-negate-formula x) z)
					  (union-eq (formula-free-vars x)
						    (formula-free-vars z))))
		    free-vars))))

(defun make-iff-formula (x y free-vars)
  (cond
   ((equal x true-formula) y)
   ((equal x false-formula) (dumb-negate-formula y))
   ((equal y true-formula) x)
   ((equal y false-formula) (dumb-negate-formula x))
   (t 
    (make-formula 'and
		  (list (make-formula 'implies (list x y) free-vars)
			(make-formula 'implies (list y x) free-vars))
		  free-vars))))

(defun make-formula (op args &optional (free-vars '?))
  ;; assumes that arguments are legal formulas in the strong sense (e.g. no IFF)
  (cond ((eq op 'term)
	 (create-formula 'term args
			 (or-? free-vars (all-vars args))))
	((or (eq op 'forall) (eq op 'exists))
	 (create-formula op args
			 (or-? free-vars
			       (remove1 (car args) (formula-free-vars (cadr args))))))
	((eq op 'iff) 
	 (make-iff-formula
	  (car args) (cadr args)
	  (or-? free-vars
		(union-eq (formula-free-vars (car args))
			  (formula-free-vars (cadr args))))))
	((eq op 'if)
	 (make-if-formula (car args) (cadr args) (caddr args)
			  (or-? free-vars
				(union-eq (formula-free-vars (car args))
					  (union-eq (formula-free-vars (cadr args))
						    (formula-free-vars (caddr args)))))))
	((eq op 'not)
	 (create-formula op args
			 (or-? free-vars
			      (formula-free-vars (car args)))))
	((member-eq op '(and or implies))
	 (create-formula op args
			 (or-? free-vars
			       (union-eq (formula-free-vars (car args))
					 (formula-free-vars (cadr args))))))
	(t (er hard (op) |Tried| |to| |create| |formula| |with| |operator|
	       (!ppr op (quote |.|))))))

(defun chk-arity (op args)
  ;; op is propositional
  (or (equal (arity op) (length args))
      (er soft ((x (cons op args))) |Encountered| |operator| |with| |wrong| |arity| |in|
	  (!ppr x (quote |.|)))))

(defun unabbreviate-quantifier (op vars x)
  ;; x hasn't yet been translated.  Notice that vars is allowed to be empty.
  (if (consp vars)
      (list op (car vars)
	    (unabbreviate-quantifier op (cdr vars) x))
    x))

(defun translate-to-formula (x &aux op a b args)
  ;; Translates an s-expression to a formula.  Notice that we only care about
  ;; propositional equivalence at any node.  We specify the additional requirement
  ;; that all IF formulas have quantifier-free tests.
  (cond
   ((and (consp x)
	 (cdr (our-last x)))
    (er soft (x) |Contrary| |to| |the| |rules| |of| |well-formedness| |,|
	|the| |last| CDR |of| |the| |proposed| |formula| (!ppr x nil)
	|is| |non-NIL| |.|))
   ((and (match x (cons op a))
	 (member-eq op '(and or)) 
	 (< 2 (length a)))
    (translate-to-formula (list op (car a) (cons op (cdr a)))))
   ((and (match x (cons op args))
	 (member-eq op '(and or not implies if iff)))
    (chk-arity op args)
    (make-formula op (mapcar #'translate-to-formula args)))
   ((and (match x (cons op args))
	 (member-eq op '(forall exists)))
    (or (match args (list a b))
	(er soft (x op) |The| |quantifier| (!ppr op nil) |is| |given|
	    |the| |wrong| |number| |of| |arguments| |in| (!ppr x (quote |.|))))
    (when (and (consp a) (cdr (our-last a)))
	  (er soft (x) |Contrary| |to| |the| |rules| |of| |well-formedness| |,|
	      |the| |last| CDR |of| |the| |variable-list| |of| (!ppr x nil)
	      |is| |non-NIL| |.|))
    (cond
     ((or (consp a) (eq a nil))
      (translate-to-formula (unabbreviate-quantifier op a b)))
     (t
      (or (and (atom a)
	       (setq a (car (error1-set (translate a))))
	       (variablep a))
	  (er soft ((v (car args)) x) |Expected| |variable| |in| |variable| |position| |of|
	      (!ppr x nil) |but| |got| (!ppr v (quote |.|))))
      (make-formula op (list a (translate-to-formula b))))))
   ((and (match x (cons op args))
	 (member-eq op '(cond case)))
    (if (eq op 'cond)
	(translate-cond-formula x)
      (translate-case-formula x)))
   (t (make-formula 'term (translate-inside-formula x)))))

(defun translate-case-formula (x)
  ;; Adapted from part of Nqthm definition of TRANSLATE
  ;; x is a case statement
  (COND ((NOT (AND (>= (LENGTH (CDR X)) 2)
		   (ITERATE FOR PAIR IN (CDDR X)
			    ALWAYS
			    (AND (CONSP PAIR)
				 (NULL (CDR (OUR-LAST PAIR)))
				 (INT= (LENGTH PAIR) 2)))
		   (EQ (CAAR (OUR-LAST (CDR X))) 'OTHERWISE)
		   (ITERATE FOR TL ON (CDDR X) UNTIL (NULL (CDR TL))
			    NEVER (EQ (CAAR TL) 'OTHERWISE))))
	 (ER SOFT (X) |The| CASE |formula| |must| |have| |at|
	     |least| |two| |arguments,| |all| |but| |the| |first|
	     |must| |be| |proper| |lists| |of| |length| |two,|
	     |the| |last| |must| |start| |with| |the|
	     |symbol| |OTHERWISE,| |and| |none| |but| |the|
	     |last| |may| |start| |with| |that| |symbol| |.| |These|
	     |rules| |are| |violated| |in| (!PPR X '|.|))))
  (fix-case-formula (translate-inside-formula (cadr x))
		    (iterate for pair in (cddr x)
			     collect
			     (cond ((eq (car pair) 'otherwise)
				    (cons 'otherwise (translate-to-formula (cadr pair))))
				   (t (cons (translate (list 'quote (car pair)))
					    (translate-to-formula (cadr pair))))))))

(defun fix-case-formula (test alist)
  (cond ((eq (caar alist) 'otherwise)
	 (cdar alist))
	(t (make-formula 'if
			 (list (make-formula 'term (fcons-term* 'equal test (car (car alist))))
			       (cdr (car alist))
			       (fix-case-formula test (cdr alist)))))))

(defun translate-cond-formula (x)
  ;; Adapted from part of Nqthm definition of TRANSLATE
  ;; x is a case statement
  (COND ((NOT (AND (>= (LENGTH (CDR X)) 1)
		   (ITERATE FOR PAIR IN (CDR X)
			    ALWAYS
			    (AND (CONSP PAIR)
				 (NULL (CDR (OUR-LAST PAIR)))
				 (INT= (LENGTH PAIR) 2)))
		   (EQ (CAAR (OUR-LAST (CDR X))) 'T)
		   (ITERATE FOR TL ON (CDR X) UNTIL (NULL (CDR TL))
			    NEVER (EQ (CAAR TL) 'T))))
	 (ER SOFT (X) |The| COND |formula| |must| |have| |at|
	     |least| |one| |argument,| |all|
	     |must| |be| |proper| |lists| |of| |length| |two,|
	     |the| |last| |must| |start| |with| |the|
	     |symbol| |T,| |and| |none| |but| |the|
	     |last| |may| |start| |with| |that| |symbol| |.| |These|
	     |rules| |are| |violated| |in| (!PPR X '|.|))))
  (fix-cond-formula (iterate for pair in (cdr x)
			     collect
			     (cons (translate-to-formula (car pair))
				   (translate-to-formula (cadr pair))))))

(defun fix-cond-formula (alist)
  (cond ((null (cdr alist)) (cdr (car alist)))
        (t (make-formula 'if
			 (list
			  (car (car alist))
			  (cdr (car alist))
			  (fix-cond-formula (cdr alist)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;    variables and utilities for Skolemization    ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *index-separator* '-)		;used to make new variables and function symbols

(defvar *skolem-prefix*)		;set when SKOLEMIZE is called

(defvar *skolem-suffix*)		;set when SKOLEMIZE is called

(defvar *skolem-arglists*)		;set when SKOLEMIZE is called

(defvar *skolem-sort*)			;set when SKOLEMIZE is called

(defvar *new-functions-and-formals*) ;alist of (new) Skolem functions and their args

;; The invariant for *new-vars* is that it should include all free
;; variables of the formula currently being Skolemized.
(defvar *new-vars*)

(defun dumb-negate-formula (formula)
  (case (formula-op formula)
	(not (car (formula-args formula)))
	(term (make-formula 'term (dumb-negate-lit (formula-args formula))
			    (formula-free-vars formula)))
	(t (make-formula 'not (list formula) (formula-free-vars formula)))))

(defun rename-var-formula (new old formula &aux
			       (op (formula-op formula))
			       (args (formula-args formula)))
  ;; The spec is that we're substituting new for all free occurrences of old in form,
  ;; where we assume that new does not occur bound in formula.
  ;;    Important lemma (used to show that alpha-equivalent formulas have the same
  ;; free variables fields):  The free-variables of (rename-var-formula new old formula)
  ;; are just those of formula if old is not free in formula (and in fact the resulting
  ;; formula equals the given formula in that case), and otherwise
  ;; are the result of adding new to the removal of old from the free-variables
  ;; of formula.  The requisite sublemma is the similar one for terms in place of formulas.
  ;; *** Note that we completely recompute the free vars here rather than simply
  ;; replacing old with new in the original set.  I should consider making this more efficient.
  (case op
	((and or implies not if)
	 (make-formula op
		       (iterate for arg in args
				collect (rename-var-formula new old arg))))
	((forall exists)
	 (if (eq (car args) old)
	     formula
	   (if (eq (car args) new)
	       (er hard (new formula) |Variable| (!ppr new nil) |was| |captured| |by|
		   |a| |quantifier| |in| (!ppr formula (quote |.|)))
	     (make-formula op
			   (list (car args)
				 (rename-var-formula new old (cadr args)))))))
	(t (make-formula 'term (subst-var new old args)))))

(defun pack-index (fn index)
  (if (int= index 0)
      fn
    (if *index-separator*
	(pack (list fn *index-separator* index))
      (pack (list fn index)))))

(defun make-new-skolem-variable (var)
  (prog1 (setq var (make-new-skolem-variable-1 var 0 *new-vars*))
    (setq *new-vars* (cons var *new-vars*))))

(defun make-new-skolem-variable-1 (var index bound-vars
				       &aux (new-var (pack-index var index)))
  (if (not (member-eq new-var bound-vars))
      new-var
    (make-new-skolem-variable-1 var (1+ index) bound-vars)))

(defun all-bound-vars (formula &aux
			       (args (formula-args formula)))
  ;; I won't bother to return a set, since it usually will be anyhow
  (case (formula-op formula)
	((forall exists)
	 (cons (car args)
	       (all-bound-vars (cadr args))))
	(term nil)
	(otherwise (iterate for arg in args
			    nconc (all-bound-vars arg)))))

(defun make-variant (formula
		     &aux new-v
		     (op (formula-op formula))
		     (v (car (formula-args formula)))
		     (body (cadr (formula-args formula))))
  ;; Here op is a quantifier, and we return (op new-v formula[new-v/v]) for
  ;; some new-v not equal to v or in *new-vars*, and not even bound in formula.
  ;; We assume here that the free variables of formula are contained in *new-vars*.
  (setq new-v (make-new-skolem-variable-1 v 1 (nconc (all-bound-vars body)
						     *new-vars*)))
  (make-formula op
		(list new-v (rename-var-formula new-v v body))
		(formula-free-vars formula)))

(defun intersectp-eq (x y)
  ;; modified from Boyer-Moore definition of intersectp
  (iterate for e in x thereis (member-eq e y)))

(defun subst-var-formula (new old formula &aux
			      (op (formula-op formula))
			      (args (formula-args formula)))
  ;; Specified to do renaming so that new variables thus created are disjoint from *new-vars*.
  ;; Here new is any term, hence we must be careful about capture.
  ;; The spec is that we're substituting new for all free occurrences of old in form.
  ;; (old is a variable.)
  ;; We assume that all variables in new are free in formula (and hence belong
  ;; to *new-vars*).
  ;; *** Note that we completely recompute the free vars here rather than simply
  ;; replacing old with new in them.  I should consider making this more efficient.
  (if (not (member-eq old (formula-free-vars formula)))
      formula
    (case op
	  (term
	   (make-formula 'term (subst-var new old args)))
	  ((forall exists)
	   (cond
	    ((eq (car args) old)
	     formula)
	    (t
	     (when (dumb-occur (car args) new)
		   (setq formula (make-variant formula))
		   (setq args (formula-args formula)))
	     (make-formula op		;*** could compute free vars here, but I won't
			   (list (car args)
				 (subst-var-formula new old (cadr args)))))))
	  (t (make-formula op
			   (iterate for arg in args
				    collect (subst-var-formula new old arg)))))))

(defun make-new-skolem-term (fn vars &aux new-term)
  (when *skolem-prefix*
	(setq fn (pack (list *skolem-prefix* fn))))
  (when *skolem-suffix*
	(setq fn (pack (list fn *skolem-suffix*))))
  (prog1 (setq new-term
	       (cons (setq fn (make-new-skolem-fn-1 fn 0 *new-functions-and-formals*))
		     (sk-sort vars
			      (or (cdr (assoc-eq fn *skolem-arglists*))
				  *skolem-sort*))))
    (setq *new-functions-and-formals*
	  (cons new-term *new-functions-and-formals*))))

(defun make-new-skolem-fn-1 (fn index bound-fns-alist
			      &aux (new-fn (pack-index fn index)))
  (if (and (chk-new-name new-fn t)
	   (not (assoc-eq new-fn bound-fns-alist)))
      new-fn
    (make-new-skolem-fn-1 fn (1+ index) bound-fns-alist)))

(defun sk-sort (vars ordered-vars)
  (append (intersection-eq ordered-vars vars)
	  (our-stable-sort
	   (set-diff-eq vars ordered-vars)
	   (function alphorder))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;                  Skolemizer                     ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun chk-skolem-prefix (p)
  (when (and p (illegal-name p))
	(er soft (p) (!ppr p nil) |is| |an| |illegal| |object|
	    |to| |use| |for| |a| |prefix| |.|)))

(defun chk-skolem-suffix (s)
  (when (and s
	     (NOT (AND (SYMBOLP s)
		       (OK-SYMBOLP s)
		       (LEGAL-CHAR-CODE-SEQ (cons (char-code #\A) (OUR-EXPLODEN s)))))
	     ;; (illegal-name (pack (list 'a s))) ;; changed to the above*******
	     )
	(er soft (s) (!ppr s nil) |is| |an| |illegal| |object|
	    |to| |use| |for| |a| |suffix| |.|)))

(defun all-variableps (x)
  (and (null (cdr (our-last x)))
       (iterate for var in x always (variablep var))))

(defun chk-skolem-arglists (alist)
  (or
   (null alist)
   (and (null (cdr (our-last alist)))
	(iterate for x in alist
		 always
		 (and (consp x)
		      (all-variableps x)
		      (no-duplicatesp (cdr x)))))
   (er soft (alist (example '((sort-arglists (sk-foo w y) (bar c)))))
       (!ppr alist nil) |is| |an| |illegal| |functions-variables| |alist|
       |for| |the| SORT-ARGLISTS |hint| |to| DEFN-SK |.| |You| |need| |to| |provide| |a|
       |function-arguments| |association| |list| |,| |such| |as| (!ppr example (quote |.|)))))       

(defun chk-skolem-sort (vars)
  (or
   (null vars)
   (and
    (all-variableps vars)
    (no-duplicatesp vars))
   (er soft (vars) (!ppr vars nil) |is| |an| |illegal| |variable| |set|
       |for| |the| SORT |hint| |to| DEFN-SK |.| |You| |need| |a| |list| |of| |distinct|
       |variable| |names| |,| |such| |as| |(SORT V W A)| |.|)))

(defun initialize-skolem-arglists (skolem-arglists skolem-sort)
  (iterate for fn-vars in skolem-arglists
	   for args = (cdr fn-vars)
	   collect
	   (cons (car fn-vars)
		 (append args
			 (iterate for var in skolem-sort
				  when (not (member-eq var args))
				  collect var)))))

(defun skolemize-no-checks (formula parity
				    init-new-functions-and-formals
				    *skolem-prefix* *skolem-suffix* *skolem-arglists* *skolem-sort*)
  (setq *skolem-arglists* (initialize-skolem-arglists *skolem-arglists* *skolem-sort*))
  (setq *new-vars* (formula-free-vars formula))
  (setq *new-functions-and-formals* init-new-functions-and-formals)
  (sk1 (collapse-formula formula)	;collapsing is simply an optimization
       parity))

(defun skolemize (formula parity
			  &optional init-new-functions-and-formals
			  *skolem-prefix* *skolem-suffix* *skolem-arglists* *skolem-sort*)
  (chk-skolem-prefix *skolem-prefix*)
  (chk-skolem-suffix *skolem-suffix*)
  (chk-skolem-arglists *skolem-arglists*)
  (chk-skolem-sort *skolem-sort*)
  (skolemize-no-checks
   formula parity
   init-new-functions-and-formals
   *skolem-prefix* *skolem-suffix* *skolem-arglists* *skolem-sort*))

(defun sk1 (formula parity
		    &aux (op (formula-op formula)) (args (formula-args formula)))

  ;; Here PARITY is T or NIL, where for example (sk1 (forall x (p x)) t)
  ;; is (p x) while (sk1 (forall x (p x)) nil) is (p (f)).  That
  ;; is, T is the parity used for creating a formula of the form
  ;; (exists F's (forall v's phi)) which is equivalent to phi.  In our
  ;; context, phi is the DEFN-SK equivalence (which is conservative),
  ;; and hence its Skolemization (without the second-order quantifiers) is
  ;; conservative, which is why it's "sound" to add it as an axiom.
  ;; By the way, NIL is the parity used for creating a formula of the form
  ;; (forall F's (exists v's phi)) which is equivalent to phi.

  ;; This function returns a term.

  (case
   op
   (term (formula-args formula))
   ((forall exists)
    (sk1-quantifier op (car args) (cadr args) parity))
   (not 
    (dumb-negate-lit (sk1 (car args) (not parity))))
   ((and or implies if)
    (sk1-connective op args parity formula)) 
   (t (er hard (formula) |Sk1| |called| |on| |bad| |argument| |,|
	  (!PPR formula nil) excl))))

(defun sk1-connective (op args parity formula
			  &aux form1 form2 parity1 term1 term2)
  ;; op is one of and, or, implies, if
  ;; set up formulas to skolemize
  (cond
   ((eq op 'if)
    (when (not (eq (formula-op (car args)) 'term))
	  (er hard (formula) |Sk1| |called| |on| IF |formula|
	      |with| |quantifier| |in| |test| |,|
	      (!PPR formula nil) excl))
    (setq form1 (cadr args))
    (setq form2 (caddr args)))
   (t (setq form1 (car args))
      (setq form2 (cadr args))))
  ;; set up parity of first formula
  (setq parity1 (if (eq op 'implies) (not parity) parity))
  ;; Now Skolemize.  There are 2 cases, depending on if new vars should be disjoint
  (cond
   ((or (and parity (member-eq op '(and if)))
	(and (not parity) (member-eq op '(or implies))))
    ;; i.e. parity iff [op is in '(and if)].  So, we allow reuse of new vars.
    (let ((vars *new-vars*))
      (setq term1 (sk1 form1 parity1))
      (our-swap vars *new-vars*)
      (setq term2 (sk1 form2 parity))
      (setq *new-vars* (union-eq vars *new-vars*))))
   (t					; No reuse of new vars in this case.
    (setq term1 (sk1 form1 parity1))
    (setq term2 (sk1 form2 parity))))
  ;; create the answer
  (if (eq op 'if)
      (fcons-term* 'if (formula-args (car args)) term1 term2)
    (fcons-term* op term1 term2)))

(defun sk1-quantifier (op var formula parity
			  &aux new-v)
  ;; Returns the skolemization.  op is forall or exists.
  (cond
   ((eq parity (eq op 'forall))
    (setq new-v (make-new-skolem-variable var))
    (sk1 (if (eq new-v var)
	     formula
	   (subst-var-formula new-v var formula))
	 parity))
   (t
    (sk1 (subst-var-formula
	  (make-new-skolem-term var
				(remove1 var (formula-free-vars formula)))
	  var formula)
	 parity))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;                 normalizing                     ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A property of normalized formulas is that there are no double negations.
;; Another is that the set of free variables doesn't change.

(defun normalize-formula (formula)
  ;; Expects the output of translate-to-formula, which therefore
  ;; shows the entire formula structure without collapsing, except in
  ;; the tests of IFs, whose tests are assumed to be quantifier-free.
  ;; Also notice that there are no IFFs.
  (collapse-formula (normalize-formula-1 formula)))

(defun normalize-formula-1 (formula &aux
				    (op (formula-op formula))
				    (args (formula-args formula)))
  ;; Here formula is a formula.  This function should return a formula
  ;; which is logically equivalent to the input formula.
  (cond
   ((eq op 'term) formula)
   ((member-eq op '(forall exists))
    (quantify op (car args) (normalize-formula-1 (cadr args))))
   ((eq op 'not)
    ;; Making sure to get rid of double negations...
    (dumb-negate-formula (normalize-formula-1 (car args))))
   ((eq op 'if)
    (make-formula 'if (list (car args)
			    (normalize-formula-1 (cadr args))
			    (normalize-formula-1 (caddr args)))))
   (t;;(member-eq op '(and or not implies))
    (make-formula op (list (normalize-formula-1 (car args)) (normalize-formula-1 (cadr args)))))))

(defun quantify (q var formula &aux
		   (op (formula-op formula))
		   (args (formula-args formula))
		   (free-vars (formula-free-vars formula)))
  ;; Optimizes to move op as far in as possible.  Notice that if the quantified
  ;; variable var is not free in one branch of formula (where formula has a binary
  ;; propositional connective), then we can distribute it and let the next step
  ;; strip it from the irrelevant branch.
  ;;   By the time we get here, the input formula is already normalized.
  ;;  **** Could perhaps be made more efficient by "remembering" information provided
  ;; by OK-TO-DISTRIBUTE-QUANTIFIER, so that one can drop the appropriate quantifier
  ;; when a variable isn't free and one can avoid checking OK again in the NOT case.
  (cond
   ((not (member-eq var free-vars))
    formula)
   ((eq op 'not)
    ;; Don't do anything if pushing NOT doesn't do us any good.
    (if (ok-to-distribute-quantifier
	 (dual-quantifier q) var (formula-op (car args)) (formula-args (car args)))
	(dumb-negate-formula (quantify (dual-quantifier q) var (car args)))
      (make-formula q (list var formula))))
   ((not (ok-to-distribute-quantifier q var op args))
    (make-formula q (list var formula)))
   ((eq op 'if)
    (make-formula 'if
		  (list (car args)
			(quantify q var (cadr args))
			(quantify q var (caddr args)))
		  (remove1 var free-vars)))
   ((eq op 'implies)
    (make-formula op
		  (list (quantify (dual-quantifier q) var (car args))
			(quantify q var (cadr args)))
		  (remove1 var free-vars)))
   ((member-eq op '(and or))
    (make-formula op
		  (list (quantify q var (car args))
			(quantify q var (cadr args)))
		  (remove1 var free-vars)))
   (t (er hard (op) |Unexpected| |operator| |,| (!ppr op (quote |.|))))))

(defun dual-quantifier (op)
  (if (eq op 'forall) 'exists 'forall))

(defun ok-to-distribute-quantifier (q var prop args
				      &aux formula1 formula2)
  ;; q is a quantifier and we're considering whether we can distribute it
  ;; for the formula with operator op and args args.
  (cond
   ((eq prop 'if)
    ;; We never push a quantifier into a (quantifier-free) test of an IF.
    (not (member-eq var (formula-free-vars (car args)))))
   ((member-eq prop '(and or implies))
    (match! args
	    (list formula1 formula2))
    (or (and (eq q 'forall)
	     (eq prop 'and))
	(and (eq q 'exists)
	     (member-eq prop '(or implies)))
	(not (member-eq var (formula-free-vars formula1)))
	(not (member-eq var (formula-free-vars formula2)))))
   (t
    ;; *** Might want to strengthen algorithm by allowing quantifier switch
    ;; when it's helpful.
    nil)))

(defun alpha-equal (form1 form2 &aux
			  (op1 (formula-op form1))
			  (args1 (formula-args form1))
			  (op2 (formula-op form2))
			  (args2 (formula-args form2)))
  ;; Notice that alpha-equivalent formulas have the same free variables field.
  (and (eq op1 op2)
       (case op1
	     (term (equal args1 args2))
	     ((forall exists)
	      (alpha-equal-1 (car args1) (cadr args1) (car args2) (cadr args2)))
	     (t (iterate for x in args1 as y in args2
			 always (alpha-equal x y))))))

(defun alpha-equal-1 (v1 form1 v2 form2)
  ;; Says whether (Q v1 form1) is alpha-equivalent to (Q v2 form2).  Since alpha-equivalence
  ;; is an equivalence relation it's OK to ask the same question of alpha-equivalent formulas.
  ;; By definition, two formulas are alpha-equivalent if one is of the form (Q v phi) and
  ;; the other is the result of renaming v to some variable not free in phi.  Hence it is
  ;; permissible to choose any v which isn't free in either form1 or form2 and rename both
  ;; v1 and v2 (in their respective formulas) to v.  In fact we choose v so that it's not
  ;; bound in form1 or form2 either, since we want to be able to use RENAME-VAR-FORMULA.
  (when (not (eq v1 v2))
	(let ((v (make-new-skolem-variable-1
		  v1 0 (nconc (all-bound-vars form1)
			      (nconc (all-bound-vars form2)
				     (union-eq (formula-free-vars form1)
					       (formula-free-vars form2)))))))
	  (setq form1 (rename-var-formula v v1 form1))
	  (setq form2 (rename-var-formula v v2 form2))))
  (alpha-equal form1 form2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;                   new event                     ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFUN FREE-VAR-CHK-FORMULA (NAME ARGS FORMULA)
  ;; adapted from Boyer-Moore function FREE-VAR-CHK
  (LET (TEMP VARS)
    (SETQ VARS (FORMULA-FREE-VARS FORMULA))
    (SETQ TEMP (SET-DIFF VARS ARGS))
    (COND (TEMP (ER SOFT (NAME TEMP) |Illegal| |free|
                    (PLURAL? TEMP |variables| |variable|) |,|
                    (!TERM-LIST TEMP (QUOTE  |,|)) |in| |the| |definition| |of|
                    (!PPR NAME (QUOTE |.|)))))
    (SETQ TEMP (SET-DIFF ARGS VARS))
    (COND (TEMP (ER WARNING (NAME TEMP)
                    (!LIST TEMP) (PLURAL? TEMP |are| |is|) |in| |the|
                    |arglist| |but| |not| |in| |the| |body| |of| |the|
                    |definition| |of| (!PPR NAME (QUOTE |.|)))))
    NIL))

(DEFUN SKOLEMIZED-FORMULA-FOR-DEFN-SK (NAME ARGS FORMULA HINTS BODY)
  ;; Returns a 2-element list containing the term which is to be the FORMULA-OF
  ;; the new event together with an alist associating each new Skolem function
  ;; with its argument list.
  (ITERATE
   FOR X IN HINTS
   WITH BETTER-BODY AND BETTER-FORMULA
   AND P AND P-FLG AND S AND S-FLG	;prefix and suffix stuff
   and sort and sort-flg
   and sort-arglists and sort-arglists-flg
   DO
   (COND 
    ((MATCH X (FORMULA BETTER-BODY))
     (IF BETTER-FORMULA
	 (ER SOFT NIL |Encountered| |more| |than| |one| FORMULA |hint| EXCL)
	 (SETQ BETTER-FORMULA (TRANSLATE-TO-FORMULA BETTER-BODY)))
     ;; implied by alpha-equal (FREE-VAR-CHK-FORMULA NAME ARGS BETTER-FORMULA)
     (OR (ALPHA-EQUAL (NORMALIZE-FORMULA BETTER-FORMULA) (NORMALIZE-FORMULA FORMULA))
	 (ER SOFT (BODY BETTER-BODY)
	     |Unable| |to| |establish| |that|
	     CR |#| (!PPR BODY NIL) CR |and| CR |#| (!PPR BETTER-BODY NIL) CR |have| |the|
	     |same| |normal| |form| |up| |to| |renaming| |of| |bound|
	     |variables| |.|)))
    ((MATCH X (PREFIX P))
     (COND (P-FLG
	    (ER SOFT NIL |Encountered| |more| |than| |one| PREFIX |hint| EXCL))
	   (T
	    (CHK-SKOLEM-PREFIX P)
	    (SETQ P-FLG T))))
    ((MATCH X (SUFFIX S))
     (COND (S-FLG
	    (ER SOFT NIL |Encountered| |more| |than| |one| SUFFIX |hint| EXCL))
	   (T
	    (CHK-SKOLEM-SUFFIX S)
	    (SETQ S-FLG T))))
    ((MATCH X (cons 'SORT SORT))
     (COND (SORT-FLG
	    (ER SOFT NIL |Encountered| |more| |than| |one| SORT |hint| EXCL))
	   (T
	    (CHK-SKOLEM-SORT SORT)
	    (SETQ SORT-FLG T))))
    ((MATCH X (cons 'SORT-ARGLISTS SORT-ARGLISTS))
     (COND (SORT-ARGLISTS-FLG
	    (ER SOFT NIL |Encountered| |more| |than| |one| SORT-ARGLISTS |hint| EXCL))
	   (T
	    (CHK-SKOLEM-ARGLISTS SORT-ARGLISTS)
	    (SETQ SORT-ARGLISTS-FLG T))))
    (T (ER SOFT (X) |each| |element| |of| |the| HINTS |argument| |to|
	   DEFN-SK |must| |be| |a| |pair| |of| |the| |form|
	   |(FORMULA x)| |,| |(PREFIX p)| |,| |(SUFFIX s)| |,|
	   |(SORT . VARS)| |,| |or| |(SORT-ARGLISTS . ALIST)| |,|
	   |but| (!PPR X NIL) |is| |not| |.|)))
   FINALLY (RETURN
	    (LIST (SKOLEMIZE-no-checks
		   (MAKE-DEFN-SK-FORMULA NAME ARGS (OR BETTER-FORMULA FORMULA))
		   T (LIST (CONS NAME ARGS)) P S sort-arglists sort)
		  *NEW-FUNCTIONS-AND-FORMALS*))))

(DEFUN MAKE-DEFN-SK-FORMULA (NAME ARGS FORMULA
				  &AUX (NEW-ARITY-ALIST
					(CONS (CONS NAME (LENGTH ARGS)) ARITY-ALIST)))
  ;; Returns the formula defining the application of name to args to be formula.
  ;; Auxiliary to SKOLEMIZED-FORMULA-FOR-DEFN-SK, but also used by DEFN-FO.
  (MAKE-FORMULA
   'AND
   (LIST (MAKE-FORMULA 'IMPLIES
		       (LIST FORMULA
			     (LET ((ARITY-ALIST NEW-ARITY-ALIST))
				  (TRANSLATE-TO-FORMULA
				   (CONS NAME ARGS)))))
	 (MAKE-FORMULA 'IMPLIES
		       (LIST (DUMB-NEGATE-FORMULA FORMULA) 
			     (LET ((ARITY-ALIST NEW-ARITY-ALIST))
				  (TRANSLATE-TO-FORMULA
				   (LIST 'NOT (CONS NAME ARGS)))))))))

(DEFUN CHK-NAME-AND-ARGS (NAME ARGS)
  ;; taken from CHK-ACCEPTABLE-DEFN
  (CHK-NEW-NAME NAME NIL)
  (CHK-NEW-*1*NAME NAME)
  (COND ((> (LENGTH ARGS) 32)
         (ER SOFT (NAME) |Too| |many| |args| EXCL
             |because| |of| |our| |use| |of|
             |32-bit| |words| |to| |encode| |sets| |of| |recursion|
             |controllers| |we| |cannot| |accept| |functions| |,| |such| |as|
             (!PPR NAME (QUOTE |,|)) |with| |more| |than| 32 |arguments|
             |.|))))

(DEFUN CHK-ACCEPTABLE-DEFN-SK (NAME ARGS BODY HINTS 
				    &AUX FORMULA SKOLEMIZED-BODY NEW-FUNCTIONS-AND-FORMALS)
  ;; much taken here from CHK-ACCEPTABLE-DEFN.
  (CHK-NAME-AND-ARGS NAME ARGS)
  (CHK-ARGLIST NAME ARGS)		;not done for new functions, which should be OK
  (SETQ FORMULA (TRANSLATE-TO-FORMULA BODY))
  (FREE-VAR-CHK-FORMULA NAME ARGS FORMULA) 
  (MATCH! (SKOLEMIZED-FORMULA-FOR-DEFN-SK NAME ARGS FORMULA HINTS BODY)
	  (LIST SKOLEMIZED-BODY NEW-FUNCTIONS-AND-FORMALS))
  (ITERATE FOR PAIR IN NEW-FUNCTIONS-AND-FORMALS
	   WHEN (NOT (EQ (CAR PAIR) NAME))
	   DO (CHK-NAME-AND-ARGS (CAR PAIR) (CDR PAIR)))
  (COND ((EQ *1*THM-MODE$ (QUOTE THM))
	 (LET ((FNS (INTERSECTION-eq (QUOTE (APPLY$ EVAL$))
				     (ALL-FNNAMES SKOLEMIZED-BODY))))
	      (COND (FNS
		     (ER SOFT (FNS) |When| |not| |in| NQTHM |mode|
			 |it| |is| |prohibited|
			 |to| |use| |the| (PLURAL? FNS |functions| |function|)
			 (!LIST FNS) |in| |a| |definition| |.|))))))
  (QUOTATIONS-CHK SKOLEMIZED-BODY)
  (LIST NAME ARGS BODY HINTS
	SKOLEMIZED-BODY NEW-FUNCTIONS-AND-FORMALS))
	
(DEFEVENT DEFN-SK (NAME ARGS BODY &OPTIONAL HINTS)
  (EVENT-COMMAND
   (LIST (QUOTE DEFN-SK) NAME ARGS BODY HINTS)
   (LET (SKOLEMIZED-BODY NEW-FUNCTIONS-AND-FORMALS)
	(MATCH! (CHK-ACCEPTABLE-DEFN-SK NAME ARGS BODY HINTS)
		(LIST NAME ARGS BODY HINTS
		      SKOLEMIZED-BODY NEW-FUNCTIONS-AND-FORMALS))
	(MAKE-EVENT NAME
		    (IF HINTS
			(LIST 'DEFN-SK NAME ARGS BODY HINTS)
			(LIST 'DEFN-SK NAME ARGS BODY)))
	(ITERATE FOR FN-VARS IN NEW-FUNCTIONS-AND-FORMALS
		 DO
		 (DCL0 (CAR FN-VARS) (CDR FN-VARS) NIL))
	;; The following avoids something like ((name 3 NIL) (name -1 NIL)) that one
	;; would get using ADD-FACT.
	(SETF (CDAR (GET NAME (QUOTE TYPE-PRESCRIPTION-LST)))
	      (CONS TYPE-SET-BOOLEAN (CDDAR (GET NAME (QUOTE TYPE-PRESCRIPTION-LST)))))
	(ADD-LEMMA0 NAME '(REWRITE) SKOLEMIZED-BODY)
	(DEPEND NAME (SET-DIFF (ALL-FNNAMES SKOLEMIZED-BODY)
			       (MAPCAR (FUNCTION CAR) NEW-FUNCTIONS-AND-FORMALS)))
	(cond
         ((not petitio-principii)
          (PRINEVAL (PQUOTE (PROGN CR CR
                                   |Adding| |the| |Skolem| |axiom|
                                   (!TERM X (QUOTE |.|)) CR CR |#|
                                   ;; (? (|Note| |that|) (|Observe| |that|)
                                   |As| |this| |is| |a| DEFN-SK |we|
                                   |can| |conclude| |that|;;)
                                   (!PPR CONCL NIL)
                                   |is| |a| |theorem| |.| CR CR))
                    `((X . ,(FORMULA-OF NAME))
                      (CONCL . (OR (TRUEP ,(CONS NAME ARGS))
                                   (FALSEP ,(CONS NAME ARGS)))))
                    0 PROVE-FILE))))
   NAME))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;      DEFN-FO macro and UNTRANSLATE-FORMULA      ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFVAR *ADD-SKOLEM-PREFIXES* NIL)
(DEFVAR *ADD-SKOLEM-SUFFIXES* NIL)

(defun untranslate-quantifier (op var formula)
  ;; Untranslate e.g. (forall x (forall y ...)) as (forall (x y) ...).
  (iterate with vars = (list var) and new-formula = formula
	   while (eq (formula-op new-formula) op)
	   ;; invariant:  (op var formula) <=> (op (vars) new-formula)
	   do (progn (setq vars (cons (car (formula-args new-formula)) vars))
		     (setq new-formula (cadr (formula-args new-formula))))
	   finally (return (list op
				 (if (consp (cdr vars)) (nreverse vars) var)
				 (untranslate-formula new-formula)))))

(defun untranslate-formula (x &aux (args (formula-args x)) (op (formula-op x)))
  ;; Note that COND and CASE get no special treatment here -- no need for that.
  (cond
   ((eq op 'term)
    (untranslate args))
   ((and (member-eq op '(and or))
	 (or (eq (formula-op (cadr args)) op)
	     (and (eq (formula-op (cadr args)) 'term)
		  (nvariablep (formula-args (cadr args)))
		  (eq (fn-symb (formula-args (cadr args))) op))))
    (cons op
	  (cons (untranslate-formula (car args))
		(cdr (untranslate-formula (cadr args))))))
   ((member-eq op '(forall exists))
    (untranslate-quantifier op (car args) (cadr args)))
   (t (cons op
	    (iterate for arg in args
		     collect (untranslate-formula arg))))))

(defun trf (x)
  ;; just for debugging
  (untranslate-formula (translate-to-formula x)))

(DEFMACRO DEFN-FO (NAME ARGS FORMULA &OPTIONAL HINTS &AUX (NEWHINTS HINTS))
  (WHEN (AND (CONSP HINTS) (CDR (OUR-LAST HINTS)))
	(ER SOFT NIL |Non-NIL| |last| |CDR| |in| |hints| EXCL))
  (WHEN (AND HINTS (ATOM HINTS))
	(ER SOFT (HINTS) |The| |hints| |,| (!PPR HINTS (QUOTE |,|))
	    |are| |an| |atom| EXCL))
  (ITERATE FOR X IN HINTS
	   WHEN (NOT (CONSP X))
	   DO (ER SOFT (X) |Found| |atom| |,| (!PPR X (QUOTE |,|)) |in| |hints| EXCL))
  (WHEN (AND (NOT (ASSOC-EQ 'PREFIX NEWHINTS))
	     *ADD-SKOLEM-PREFIXES*)
	(SETQ NEWHINTS (CONS (LIST 'PREFIX (PACK (LIST NAME '-))) NEWHINTS)))
  (WHEN (AND (NOT (ASSOC-EQ 'SUFFIX NEWHINTS))
	     *ADD-SKOLEM-SUFFIXES*)
	(SETQ NEWHINTS (CONS (LIST 'SUFFIX (PACK (LIST '- NAME))) NEWHINTS)))
  (WHEN (NOT (ASSOC-EQ 'FORMULA NEWHINTS))
	(LET* ((P (CADR (ASSOC-EQ 'PREFIX NEWHINTS)))
	       (S (CADR (ASSOC-EQ 'SUFFIX NEWHINTS)))
	       (sort-arglists (CADR (ASSOC-EQ 'sort-arglists NEWHINTS)))
	       (sort (CADR (ASSOC-EQ 'sort NEWHINTS)))
	       (X (TRANSLATE-TO-FORMULA FORMULA))
	       (NORM (NORMALIZE-FORMULA X)))
	      (WHEN (NOT (EQUAL (SKOLEMIZE (MAKE-DEFN-SK-FORMULA NAME ARGS NORM)
					   T (LIST (CONS NAME ARGS)) P S sort-arglists sort)
				(SKOLEMIZE (MAKE-DEFN-SK-FORMULA NAME ARGS X)
					   T (LIST (CONS NAME ARGS)) P S sort-arglists sort)))
		    (SETQ NEWHINTS (CONS (LIST 'FORMULA (UNTRANSLATE-FORMULA NORM))
					 NEWHINTS)))))
  (WHEN (NOT (EQUAL NEWHINTS HINTS))
	(PRINEVAL (PQUOTE (PROGN CR CR
				 |New| |hints| |are|
				 (!PPR NEWHINTS (QUOTE |.|))))
		  (LIST (CONS 'NEWHINTS NEWHINTS))
		  0 PROVE-FILE))
  `(DEFN-SK ,NAME ,ARGS ,FORMULA
     ,@(IF NEWHINTS (LIST NEWHINTS) NIL)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;                 DEFN-SK+ macro                 ;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Usage:  replace DEFN-SK by DEFN-SK+ and you get each of the two new
;; rewrite rules attached to a single event name.  The extra baggage
;; below is so that this will work with or without pc-nqthm.

(defparameter *necc-suff-flg* nil)

(defun necc-suff (&optional (name (car chronology)))
  (if *necc-suff-flg*
      (if (eq *necc-suff-flg* 'nqthm)
	  (necc-suff-nqthm name)
	(necc-suff-pc-nqthm name)) 
    (if (fboundp 'interactively-rewrite)
	(necc-suff-pc-nqthm name)
      (necc-suff-nqthm name))))

(defun necc-suff-nqthm (&optional (name (car chronology)))
  (let ((form (formula-of name)))
    (list `(disable ,name)
	  `(prove-lemma ,(pack (list name '-suff)) (rewrite)
			,(untranslate (fargn form 1))
			((use (,name))
			 (disable-theory t)
			 (enable-theory ground-zero)))
	  `(prove-lemma ,(pack (list name '-necc)) (rewrite)
			,(untranslate (fargn form 2))
			((use (,name))
			 (disable-theory t)
			 (enable-theory ground-zero))))))

(defun necc-suff-pc-nqthm (&optional (name (car chronology)))
  (let ((form (formula-of name)))
    (list `(disable ,name)
	  `(prove-lemma ,(pack (list name '-suff)) (rewrite)
			,(untranslate (fargn form 1))
			((instructions promote (rewrite 2))))
	  `(prove-lemma ,(pack (list name '-necc)) (rewrite)
			,(untranslate (fargn form 2))
			((instructions promote (dive 1) (rewrite 2) top s))))))

(defmacro defn-sk+ (name &rest args)
  `(let (forms)
     (and
      (defn-sk ,name ,@args)
      (let (undone-events)
	(do-events
	 (setq forms (necc-suff ',name))) )
      (let ((x (car forms)) (y (cadr forms)) (z (caddr forms)))
	(prineval
	 (pquote (progn cr cr |Put| |the| |following| |forms| |in| |your| |file| |:|))
	 (list (cons 'x x) (cons 'y y) (cons 'z z))
	 0 prove-file)
	(terpri nil) (terpri nil)
	(ppr x nil) (terpri nil) (terpri nil)
	(ppr y nil) (terpri nil) (terpri nil)
	(ppr z nil) (terpri nil) (terpri nil)
	t))))


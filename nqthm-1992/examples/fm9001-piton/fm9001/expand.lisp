;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    EXPAND.LISP
;;;
;;;    EXPAND is a way to use the NQTHM rewriter to rewrite terms, for example
;;;    to provide the right hand side of complicated lemmas. 
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

(defun expand (form &optional (hyps '(true)) hints)
  (chk-init)
  (let ((dummy-var (gentemp))
        term clauses answer last-literal lhs rhs expansion)
    ;;  Check the term and hints.
    (setf term (translate-and-chk `(IMPLIES ,hyps (EQUAL ,form ,dummy-var))))
    (match! (chk-acceptable-hints hints)
            (list hints))
    (unless (iterate for hint in hints
              always (member (car hint)
                             '(enable disable enable-theory disable-theory
                                      no-built-in-arith expand hands-off)))
      (error "The only allowable hints are ENABLE, DISABLE, ENABLE-THEORY, ~
              DISABLE-THEORY, NO-BUILT-IN-ARITH and HANDS-OFF."))
    ;;  We now simplify.
    (unwind-protect
      (progn
        (setf term (apply-hints hints term))
        (setf clauses (preprocess term))
        (unless (equal (length clauses) 1)
          (error "Clausification of the original input ~
                  returned multiple clauses. ~%~s" clauses))
        (setup form clauses abbreviations-used)
        (simplify-clause-maximally (car clauses))
        (when (and (not (equal (length process-clauses) 1))
                   (not (iterate for (clause . rest) on process-clauses
                          when (consp rest)
                          always (equal (car (last clause))
                                        (car (last (car rest)))))))
          (format t
                  "Simplification returned multiple (~d) ~
                   unequivalent clauses.~%" (length process-clauses))
          (iterate for clause in process-clauses
            do (progn (pprint (prettyify-clause clause)) (terpri)))
          (error "Too many clauses."))
        (setf answer (car process-clauses))
        (setf last-literal (car (last answer)))
        (unless (and (match last-literal (equal lhs rhs))
                     (or (progn (setf expansion lhs)
                                (eq rhs dummy-var))
                         (progn (setf expansion rhs)
                                (eq lhs dummy-var))))
          (error "The resulting clause does not have the expected form :~
                  ~%~s" (prettyify-clause answer)))
        (untranslate expansion))
      (iterate for x in hint-variable-alist
        do (set (cadr x) (cadddr x))))))

(defmacro expand-lemma (name type hyps term &optional hints)
  (let ((expansion (expand term hyps hints)))
    (print `(PROVE-LEMMA ,name ,type
              ,(if (null hyps)
                   `(EQUAL ,term ,expansion)
                 `(IMPLIES
                   ,hyps
                   (EQUAL ,term ,expansion)))
              ,hints))))

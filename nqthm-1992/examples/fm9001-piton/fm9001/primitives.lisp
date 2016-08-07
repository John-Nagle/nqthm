;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    PRIMITIVES.LISP
;;;
;;;  Functions and macros to automate the creation of DUAL-EVAL lemmas for the
;;;  primitives. 
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;  Primitive result and new-state lemma macros.

(defun primitive-result (name inputs results states)
  (let* ((name& (unstring name "&"))
         (args (if inputs `(LIST ,@inputs) 'NIL))
         (state (cond
                 ((null states) 'STATE)
                 ((atom states) states)
                 (t `(LIST ,@states))))
         (value-lemma (unstring name "$VALUE"))
         (netlist (unstring name "$NETLIST")))

    `(PROGN
        
      (DEFN ,name& (NETLIST) T)
          
      (DISABLE ,name&)

      (DEFN ,netlist () NIL)

      (PROVE-LEMMA ,value-lemma (REWRITE)
        (IMPLIES
         (,name& NETLIST)
         (EQUAL (DUAL-EVAL 0 ',name ,args ,state NETLIST)
                ,results))
        ;;Hint
        ((ENABLE ,name& PRIMP DUAL-APPLY-VALUE)
         (EXPAND (DUAL-EVAL 0 ',name ,args ,state NETLIST))))

      (DISABLE ,value-lemma))))

(defun primitive-state (name inputs new-states states)
  (let* ((args (if inputs `(LIST ,@inputs) 'NIL))
         (state (cond
                 ((null states) 'STATE)
                 ((atom states) states)
                 (t `(LIST ,@states))))
         (name& (unstring name "&"))
         (state-lemma (unstring name "$STATE")))

    `(PROGN
          
      (PROVE-LEMMA ,state-lemma (REWRITE)
        (IMPLIES
         (,name& NETLIST)
         (EQUAL (DUAL-EVAL 2 ',name ,args ,state NETLIST)
                ,new-states))
        ;;Hint
        ((ENABLE ,name& PRIMP DUAL-APPLY-STATE)
         (EXPAND (DUAL-EVAL 2 ',name ,args ,state NETLIST))))

      (DISABLE ,state-lemma))))

;;;  COMMON-LISP-PRIMP-DATABASE is defined in "primp-database.lisp".

(defmacro result-and-state-lemmas ()
  `(PROGN
    ,@(iterate for (name . alist) in common-lisp-primp-database
        collect (primitive-result name
                                 (cdr (assoc 'inputs alist))
                                 (cdr (assoc 'results alist))
                                 (cdr (assoc 'states alist))))
    ,@(iterate for (name . alist) in common-lisp-primp-database
        when (member 'new-states alist :key #'car)
        collect (primitive-state name
                                 (cdr (assoc 'inputs alist))
                                 (cdr (assoc 'new-states alist))
                                 (cdr (assoc 'states alist))))))

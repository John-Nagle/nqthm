;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    MONOTONICITY-MACROS.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;    MONOTONICITY LEMMAS FOR BOOLEAN FUNCTIONS     ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; e.g.:

;;;   >(macroexpand-1 '(monotonicity-lemma f-and3))
;;;   (PROVE-LEMMA F-AND3-MONOTONE (REWRITE)
;;;       (IMPLIES (AND (B-APPROX A1 A2) (B-APPROX B1 B2) (B-APPROX C1 C2))
;;;                (B-APPROX (F-AND3 A1 B1 C1) (F-AND3 A2 B2 C2))))
;;;   T
;;;   
;;;   >

(defun monotonicity-lemma-fn (name &optional hints)
  (let* ((ev (get name 'event))
         (args (caddr ev))
         (args1
          (iterate for arg in args
                   collect (pack (list arg 1))))
         (args2
          (iterate for arg in args
                   collect (pack (list arg 2))))
         (conjuncts
          (iterate for arg1 in args1
                   as arg2 in args2
                   collect (list 'b-approx arg1 arg2))))
    (if args
        `(prove-lemma ,(pack (list name '-monotone)) (rewrite)
                      (implies
                       ,(if (consp (cdr args))
                            (cons 'and conjuncts)
                          (car conjuncts))
                       (b-approx (,name ,@args1) (,name ,@args2)))
                      ,@(and hints (list hints)))
      t)))

(defmacro monotonicity-lemma (name &optional hints)
  (monotonicity-lemma-fn name hints))

(defmacro monotonicity-lemmas (names &optional hints)
  (list 'do-events-recursive
        (list 'quote
              (iterate for name in names
                       collect
                       (monotonicity-lemma-fn name hints)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;                    DISABLE-ALL                   ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro disable-all (&rest names)
  (list 'do-events-recursive
        (list 'quote
              (iterate for name in names
                       collect
                       (list 'disable name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;           PROVE-PRIMITIVE-MONOTONICITY           ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; >(macroexpand-1 '(prove-primitive-monotonicity (AO2 AO4)))
;;; (DO-EVENTS-RECURSIVE
;;;     '((PROVE-LEMMA DUAL-EVAL-AO2-VALUE (REWRITE)
;;;           (EQUAL (DUAL-EVAL 0 'AO2 ARGS STATE NETLIST)
;;;                  (LET ((A (CAR ARGS)) (B (CAR (CDR ARGS)))
;;;                        (C (CAR (CDR (CDR ARGS))))
;;;                        (D (CAR (CDR (CDR (CDR ARGS))))))
;;;                    (CONS (F-NOR (F-AND A B) (F-AND C D)) 'NIL)))
;;;           ((ENABLE DUAL-EVAL DUAL-APPLY-VALUE)))
;;;       (PROVE-LEMMA DUAL-EVAL-AO2-STATE (REWRITE)
;;;           (EQUAL (DUAL-EVAL 2 'AO2 ARGS STATE NETLIST) 0)
;;;           ((ENABLE DUAL-EVAL DUAL-APPLY-STATE)))
;;;       (PROVE-LEMMA AO2-MONOTONE (REWRITE)
;;;           (AND (MONOTONICITY-PROPERTY 0 'AO2 NETLIST A1 A2 S1 S2)
;;;                (MONOTONICITY-PROPERTY 2 'AO2 NETLIST A1 A2 S1 S2))
;;;           ((DISABLE-THEORY T)
;;;            (ENABLE-THEORY GROUND-ZERO MONOTONICITY-LEMMAS)
;;;            (ENABLE *1*B-APPROX *1*V-APPROX *1*S-APPROX V-APPROX
;;;                    MONOTONICITY-PROPERTY-OPENER-0
;;;                    MONOTONICITY-PROPERTY-OPENER-2 DUAL-EVAL-AO2-VALUE
;;;                    DUAL-EVAL-AO2-STATE S-APPROX-IMPLIES-B-APPROX
;;;                    FOURP-IMPLIES-S-APPROX-IS-B-APPROX FOURP-F-BUF
;;;                    FOURP-F-IF)
;;;            (EXPAND (V-APPROX A1 A2) (V-APPROX (CDR A1) (CDR A2))
;;;                    (V-APPROX (CDR (CDR A1)) (CDR (CDR A2)))
;;;                    (V-APPROX (CDR (CDR (CDR A1))) (CDR (CDR (CDR A2)))))))
;;;       (PROVE-LEMMA DUAL-EVAL-AO4-VALUE (REWRITE)
;;;           (EQUAL (DUAL-EVAL 0 'AO4 ARGS STATE NETLIST)
;;;                  (LET ((A (CAR ARGS)) (B (CAR (CDR ARGS)))
;;;                        (C (CAR (CDR (CDR ARGS))))
;;;                        (D (CAR (CDR (CDR (CDR ARGS))))))
;;;                    (CONS (F-NAND (F-OR A B) (F-OR C D)) 'NIL)))
;;;           ((ENABLE DUAL-EVAL DUAL-APPLY-VALUE)))
;;;       (PROVE-LEMMA DUAL-EVAL-AO4-STATE (REWRITE)
;;;           (EQUAL (DUAL-EVAL 2 'AO4 ARGS STATE NETLIST) 0)
;;;           ((ENABLE DUAL-EVAL DUAL-APPLY-STATE)))
;;;       (PROVE-LEMMA AO4-MONOTONE (REWRITE)
;;;           (AND (MONOTONICITY-PROPERTY 0 'AO4 NETLIST A1 A2 S1 S2)
;;;                (MONOTONICITY-PROPERTY 2 'AO4 NETLIST A1 A2 S1 S2))
;;;           ((DISABLE-THEORY T)
;;;            (ENABLE-THEORY GROUND-ZERO MONOTONICITY-LEMMAS)
;;;            (ENABLE *1*B-APPROX *1*V-APPROX *1*S-APPROX V-APPROX
;;;                    MONOTONICITY-PROPERTY-OPENER-0
;;;                    MONOTONICITY-PROPERTY-OPENER-2 DUAL-EVAL-AO4-VALUE
;;;                    DUAL-EVAL-AO4-STATE S-APPROX-IMPLIES-B-APPROX
;;;                    FOURP-IMPLIES-S-APPROX-IS-B-APPROX FOURP-F-BUF
;;;                    FOURP-F-IF)
;;;            (EXPAND (V-APPROX A1 A2) (V-APPROX (CDR A1) (CDR A2))
;;;                    (V-APPROX (CDR (CDR A1)) (CDR (CDR A2)))
;;;                    (V-APPROX (CDR (CDR (CDR A1)))
;;;                              (CDR (CDR (CDR A2)))))))))
;;; T
;;; 
;;; >

(defun dual-eval-name-state* (name)
  (pack (list 'dual-eval- name '-state)))

(defun dual-eval-name-value* (name)
  (pack (list 'dual-eval- name '-value)))

(defun name-value-let-bindings (inputs)
  (iterate for i in inputs
           with x = 'args
           collect
           (prog1 (list i (list 'car x))
             (setq x (list 'cdr x)))))

(defun dual-eval-state-lemma (name inputs states new-states)
  `(prove-lemma ,(dual-eval-name-state* name) (rewrite)
                (equal (dual-eval 2 ',name args state netlist)
                       ,(if states
                            `(let ,(name-value-let-bindings inputs)
                               ,new-states)
                          0))
                ((enable dual-eval dual-apply-state))))

(defun dual-eval-value-lemma (name inputs states results)
  (declare (ignore states))
  `(prove-lemma ,(dual-eval-name-value* name) (rewrite)
                (equal (dual-eval 0 ',name args state netlist)
                       (let ,(name-value-let-bindings inputs)
                         ,results))
                ((enable dual-eval dual-apply-value))))

(defun device-monotonicity-lemma-expand-hint (name inputs states)
  (declare (ignore states))
  (cons 'expand
        (iterate for x in inputs
                 with a1 = 'a1
                 and a2 = 'a2
                 collect 
                 (prog1
                     (list 'v-approx a1 a2)
                     (ignore-variable x)
                     (setq a1 (list 'cdr a1))
                     (setq a2 (list 'cdr a2))))))

(defun device-monotonicity-lemma (name inputs states)
  `(prove-lemma
    ,(pack (list name '-monotone))
    (rewrite)
    (and (monotonicity-property 0 ',name netlist a1 a2 s1 s2)
         (monotonicity-property 2 ',name netlist a1 a2 s1 s2))
    ((disable-theory t)
     (enable-theory ground-zero monotonicity-lemmas)
     (enable *1*b-approx *1*v-approx *1*s-approx v-approx
             monotonicity-property-opener-0 monotonicity-property-opener-2
             ,(dual-eval-name-value* name) ,(dual-eval-name-state* name)
             s-approx-implies-b-approx
             fourp-implies-s-approx-is-b-approx fourp-f-buf fourp-f-if)
     ,(device-monotonicity-lemma-expand-hint name inputs states))))

(defun prove-primitive-monotonicity-events (name)
  (let ((entry (cdr (assoc name common-lisp-primp-database))))
    (let ((inputs (cdr (assoc 'inputs entry)))
          ;; (outputs (cdr (assoc 'outputs entry)))
          (results (cdr (assoc 'results entry)))
          ;; the following appears to always be 'state or nil
          (states (cdr (assoc 'states entry)))
          (new-states (cdr (assoc 'new-states entry))))
      (list (dual-eval-value-lemma name inputs states results)
            (dual-eval-state-lemma name inputs states new-states)
            (device-monotonicity-lemma name inputs states)))))

(defmacro prove-primitive-monotonicity (x)
  (let ((lst (if (consp x) x (list x))))
    (list 'do-events-recursive
          (list 'quote
                (iterate for name in lst
                         nconc (prove-primitive-monotonicity-events name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;        REVERTING THE DISABLED/ENABLED STATE      ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun old-state-events (ev-name)
  (let (on-off)
    (iterate for x in chronology
      until (eq x ev-name)
      with ans and z and ev
      do
      (setq ev (get x 'event))
      (when (and (eq (car ev) 'prove-lemma)
                 (member-eq 'rewrite (caddr ev)))
        (setq ans (cons `(disable ,x) ans)))
      (when (match ev (toggle & z on-off))
        (if on-off
            (setq ans (cons `(enable ,z) ans))
          (setq ans (cons `(disable ,z) ans))))
      finally (return ans))))

(defmacro revert-state (ev-name)
  `(do-events-recursive ',(old-state-events ev-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;    PROVE-DUAL-APPLY-VALUE-DP-RAM-16X32-LEMMA-2   ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This little hack is simply to save room in the files.

;;; (PROVE-LEMMA DUAL-APPLY-VALUE-DP-RAM-16X32-LEMMA-2 (REWRITE)
;;;     (EQUAL (DUAL-APPLY-VALUE 'DP-RAM-16X32 A S)
;;;            (DUAL-PORT-RAM-VALUE 32 4
;;;                (LIST (EVAL$ T 'READ-A0
;;;                             (APPEND (PAIRLIST
;;;                                      '(READ-A0 READ-A1 READ-A2 READ-A3
;;;                                        WRITE-B0 WRITE-B1 WRITE-B2
;;;                                        WRITE-B3 WEN D0 D1 D2 D3 D4 D5
;;;                                        D6 D7 D8 D9 D10 D11 D12 D13 D14
;;;                                        D15 D16 D17 D18 D19 D20 D21 D22
;;;                                        D23 D24 D25 D26 D27 D28 D29 D30
;;;                                        D31)
;;;                                      A)
;;;                                     (PAIRSTATES 'STATE S)))
;;;                      (EVAL$ T 'READ-A1
;;;                             (APPEND (PAIRLIST
;;;                                      '(READ-A0 READ-A1 READ-A2 READ-A3
;;;                                        WRITE-B0 WRITE-B1 WRITE-B2
;;;                                        WRITE-B3 WEN D0 D1 D2 D3 D4 D5
;;;                                        D6 D7 D8 D9 D10 D11 D12 D13 D14
;;;                                        D15 D16 D17 D18 D19 D20 D21 D22
;;;                                        D23 D24 D25 D26 D27 D28 D29 D30
;;;                                        D31)
;;;                                      A)
;;;                                     (PAIRSTATES 'STATE S)))
;;;                      ....
;;;                      (EVAL$ T 'D31
;;;                             (APPEND (PAIRLIST
;;;                                      '(READ-A0 READ-A1 READ-A2 READ-A3
;;;                                        WRITE-B0 WRITE-B1 WRITE-B2
;;;                                        WRITE-B3 WEN D0 D1 D2 D3 D4 D5
;;;                                        D6 D7 D8 D9 D10 D11 D12 D13 D14
;;;                                        D15 D16 D17 D18 D19 D20 D21 D22
;;;                                        D23 D24 D25 D26 D27 D28 D29 D30
;;;                                        D31)
;;;                                      A)
;;;                                     (PAIRSTATES 'STATE S))))
;;;                (EVAL$ T 'STATE
;;;                       (APPEND (PAIRLIST
;;;                                   '(READ-A0 READ-A1 READ-A2 READ-A3
;;;                                     WRITE-B0 WRITE-B1 WRITE-B2 WRITE-B3
;;;                                     WEN D0 D1 D2 D3 D4 D5 D6 D7 D8 D9
;;;                                     D10 D11 D12 D13 D14 D15 D16 D17 D18
;;;                                     D19 D20 D21 D22 D23 D24 D25 D26 D27
;;;                                     D28 D29 D30 D31)
;;;                                   A)
;;;                               (PAIRSTATES 'STATE S)))))
;;;     ((DISABLE-THEORY T)
;;;      (ENABLE *1*PRIMP *1*LOOKUP-MODULE *1*CDR *1*CAR *1*EVAL$
;;;              DUAL-APPLY-VALUE-DP-RAM-16X32-LEMMA-1 EVAL$-APPEND
;;;              EVAL$-APPEND-2 EVAL$-QUOTE)))

(defmacro prove-dual-apply-value-or-state-dp-ram-16x32-lemma-2 (value-or-state)
  (let ((name1 (if (eq value-or-state 'value)
                   'dual-apply-value-dp-ram-16x32-lemma-2
                 'dual-apply-state-dp-ram-16x32-lemma-2))
        (name2 (if (eq value-or-state 'value)
                   'dual-apply-value
                 'dual-apply-state))
        (name3 (if (eq value-or-state 'value)
                   'dual-port-ram-value
                 'dual-port-ram-state))
        (name4 (if (eq value-or-state 'value)
                   'dual-apply-value-dp-ram-16x32-lemma-1
                 'dual-apply-state-dp-ram-16x32-lemma-1)))
    `(prove-lemma ,name1 (rewrite)
       (equal (,name2 'dp-ram-16x32 a s)
              (,name3
               32 4
               ,(cons 'list
                      (iterate for input in dp-ram-16x32-inputs
                        collect (list 'eval$ 't (list 'quote input)
                                      (list 'append
                                            (list 'pairlist
                                                  (list 'quote
                                                        dp-ram-16x32-inputs)
                                                  'a)
                                            '(pairstates 'state s)))))
               (eval$ t 'state
                      ,(list 'append
                             (list 'pairlist
                                   (list 'quote dp-ram-16x32-inputs)
                                   'a)
                             '(pairstates 'state s)))))
       ((disable-theory t)
        (enable *1*primp *1*lookup-module *1*cdr *1*car *1*eval$
                ,name4 eval$-append rewrite-eval$
                eval$-append-2 eval$-quote)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;    GOOD-STATE LEMMAS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun device-good-s-lemma (name inputs states)
  (declare (ignore inputs states))
  `(prove-lemma
     ,(pack (list name '-preserves-good-s))
     (rewrite)
     (implies (good-s s)
              (good-s (dual-apply-state ',name args s)))
     ((disable-theory t)
      (enable-theory ground-zero)
      (enable *1*b-approx *1*v-approx *1*s-approx v-approx dual-apply-state
              *1*primp2 f-buf-preserves-good-s f-if-preserves-good-s good-s-0
              ,(dual-eval-name-value* name) ,(dual-eval-name-state* name))
      ;,(device-monotonicity-lemma-expand-hint name inputs states)
      )))

(defun prove-primitive-preserves-good-s-events (name)
  (let ((entry (cdr (assoc name common-lisp-primp-database))))
    (let ((inputs (cdr (assoc 'inputs entry)))
          ;; (outputs (cdr (assoc 'outputs entry)))
          ;; (results (cdr (assoc 'results entry)))
          ;; the following appears to always be 'state or nil
          ;; (new-states (cdr (assoc 'new-states entry)))
          (states (cdr (assoc 'states entry))))
      (list ;(dual-eval-value-lemma name inputs states results)
            ;(dual-eval-state-lemma name inputs states new-states)
            (device-good-s-lemma name inputs states)))))

(defmacro prove-primitive-preserves-good-s (x)
  (let ((lst (if (consp x) x (list x))))
    (list 'do-events-recursive
          (list 'quote
                (iterate for name in lst
                  nconc
                  (prove-primitive-preserves-good-s-events name))))))

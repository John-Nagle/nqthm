;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;   CONTROL.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    Definitions of the control states for the FM9001 control logic.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconstant
  *control-states*
  '((fetch0  . #v00000)
    (fetch1  . #v00001)
    (fetch2  . #v00010)
    (fetch3  . #v00011)
    
    (decode  . #v00100)
    (rega    . #v00101)
    (regb    . #v00110)
    (update  . #v00111)
    
    (reada0  . #v01000)
    (reada1  . #v01001)
    (reada2  . #v01010)
    (reada3  . #v01011)
    
    (readb0  . #v01100)
    (readb1  . #v01101)
    (readb2  . #v01110)
    (readb3  . #v01111)
    
    (write0  . #v10000)
    (write1  . #v10001)
    (write2  . #v10010)
    (write3  . #v10011)
 
    (sefa0   . #v10100)
    (sefa1   . #v10101)
    (sefb0   . #v10110)
    (sefb1   . #v10111)
 
    (hold0   . #v11000)
    (hold1   . #v11001)
    (v11010  . #v11010)
    (v11011  . #v11011)

    (reset0  . #v11100)
    (reset1  . #v11101)
    (reset2  . #v11110)
    (v11111  . #v11111)))

;;;  Define both vector (V_) and natural (N_) forms of the states, disable them
;;;  and their *1* counterparts, and define a theory for these events.

(defun vector-state-name (state) (unstring "V_" state))
(defun vector-state-name*1* (state) (unstring "*1*V_" state))
(defun natural-state-name (state) (unstring "N_" state))
(defun natural-state-name*1* (state) (unstring "*1*N_" state))

(defmacro define-control-states ()
  `(PROGN

    ,@(iterate for (name . val) in *control-states*
        nconc (let* ((vn (vector-state-name name))
                     (vn*1* (vector-state-name*1* name))
                     (nn (natural-state-name name))
                     (nn*1* (natural-state-name*1* name)))
                `((DEFN ,vn () ,val)
                  (DISABLE ,vn)
                  (DISABLE ,vn*1*)
                  (DEFN ,nn () (V-TO-NAT ,val))
                  (DISABLE ,nn)
                  (DISABLE ,nn*1*))))

    (DEFTHEORY VECTOR-STATE-THEORY
      ,(iterate for (name . val) in *control-states*
         collecting (vector-state-name name)))

    (DEFTHEORY NATURAL-STATE-THEORY
      ,(iterate for (name . val) in *control-states*
         collecting (natural-state-name name)))

    (PROVE-LEMMA BVP-LENGTH-STATE-VECTORS (REWRITE)
     (AND ,@(iterate for (name . val) in *control-states*
          nconc `((EQUAL (LENGTH (,(vector-state-name name))) 5)
                  (BVP (,(vector-state-name name))))))
     ;;Hint
     ((ENABLE-THEORY VECTOR-STATE-THEORY)))

    (DISABLE BVP-LENGTH-STATE-VECTORS)

    ))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;   *CONTROL-TEMPLATE*
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;;;  The fields of the control state are defined by *CONTROL-TEMPLATE*.  We
;;;  make extensive use of this database to generate lemmas.

(defconstant
  *control-template*
  ;; Line       Type (Bit/Vector)  Default
  '((rw-                 b          t)
    (strobe-             b          t)
    (hdack-              b          t)
    (we-regs             b          f) 
    (we-a-reg            b          f)
    (we-b-reg            b          f)
    (we-i-reg            b          f)
    (we-data-out         b          f)
    (we-addr-out         b          f)
    (we-hold-            b          f)
    (we-pc-reg           b          f)
    (data-in-select      b          f)
    (dec-addr-out        b          f)
    (select-immediate    b          f)
    (alu-c               b          (carry-in-help (cons c (cons f op-code))))
    (alu-zero            b          f)
    (state               5          #v00000)
    (we-flags            4          (make-list 4 f))
    (regs-address        4          pc-reg)
    (alu-op              4          op-code)
    (alu-mpg             7          (mpg (cons f (cons f op-code))))))

;;;  Define an accessor for each entry in the control state, and a theory for
;;;  all of the accessors.

(defmacro define-control-state-accessors ()
  `(PROGN

    ,@(iterate for (field type default) in *control-template*
        with pos = 0
        nconc (if (equal type 'b)
                  (prog1
                    `((DEFN ,field (CNTL-STATE) (NTH ,pos CNTL-STATE))
                      (DISABLE ,field))
                    (incf pos))
                (let ((size type))
                  (prog1
                    `((DEFN ,field (CNTL-STATE)
                        (SUBRANGE CNTL-STATE ,pos ,(1- (+ pos size))))
                      (DISABLE ,field))
                    ;; Hack to work around variable unused error message.
                    (ignore-variable default)
                    (setf pos (+ pos size))))))

    (DEFTHEORY CONTROL-STATE-ACCESSOR-THEORY
      ,(mapcar #'car *control-template*))))



;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    CONTROL-LET
;;;    
;;;  A macro for a LET that extracts and computes necessary fields and flags.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defconstant *control-arglist*
  '(RW- REGS-ADDRESS I-REG FLAGS PC-REG))

(defun control-let (body)
  `(LET ((A-IMMEDIATE-P (A-IMMEDIATE-P I-REG))
         (MODE-A        (MODE-A        I-REG))
         (RN-A          (RN-A          I-REG))
         (MODE-B        (MODE-B        I-REG))
         (RN-B          (RN-B          I-REG))
         (SET-FLAGS     (SET-FLAGS     I-REG))
         (STORE-CC      (STORE-CC      I-REG))
         (OP-CODE       (OP-CODE       I-REG)))
     (LET ((A-IMMEDIATE-P-     (NOT* A-IMMEDIATE-P))
           (STORE              (STORE-RESULTP STORE-CC FLAGS))
           (SET-SOME-FLAGS     (SET-SOME-FLAGS SET-FLAGS))
           (DIRECT-A           (OR* A-IMMEDIATE-P (REG-DIRECT-P MODE-A)))
           (DIRECT-B           (REG-DIRECT-P MODE-B))
           (UNARY              (UNARY-OP-CODE-P OP-CODE))
           (PRE-DEC-A          (PRE-DEC-P MODE-A))
           (POST-INC-A         (POST-INC-P MODE-A))
           (PRE-DEC-B          (PRE-DEC-P MODE-B))
           (POST-INC-B         (POST-INC-P MODE-B))
           (C                  (C-FLAG FLAGS))
           (ALL-T-REGS-ADDRESS (EQUAL REGS-ADDRESS #v1111)))
       (LET ((STORE-        (NOT* STORE))
             (DIRECT-A-     (NOT* DIRECT-A))
             (DIRECT-B-     (NOT* DIRECT-B))
             (UNARY-        (NOT* UNARY))
             (SIDE-EFFECT-A (AND* A-IMMEDIATE-P-
                                  (OR* PRE-DEC-A POST-INC-A)))
             (SIDE-EFFECT-B (OR* PRE-DEC-B POST-INC-B)))
         ,body))))



;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    *STATE-TABLE*
;;;
;;;    *STATE-TABLE*, along with *CONTROL-TEMPLATE*, forms a Common LISP
;;;    encoding of the FM9001 state machine. Each entry contains the
;;;    state name, an expression for the next state, and a set of control line
;;;    assignments.  If the name of a control line is given, then the
;;;    non-default Boolean value is selected.  A pair, (<control-line> <value>)
;;;    assigns that value to the control line in that state.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defconstant
  *state-table*
  '((fetch0 fetch1 we-addr-out we-a-reg (regs-address pc-reg)
            (rw- rw-) we-hold-
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons f (alu-inc-op))))))         

    (fetch1 (if hold- fetch2 hold0))
            
    (fetch2 fetch3 strobe-
            we-regs (regs-address pc-reg)
            (alu-c (carry-in-help (cons c (cons f (alu-inc-op)))))
            (alu-op (alu-inc-op))
            (alu-mpg (mpg (cons f (cons f (alu-inc-op))))))

    (fetch3 (if dtack- fetch3 decode) data-in-select we-i-reg strobe-)

    (decode (if (b-or store set-some-flags)
                (if direct-a
                    (if (b-or direct-b unary)
                        rega
                      readb0)
                  reada0)
              (if side-effect-a
                  sefa0
                (if side-effect-b
                    sefb0
                  fetch0))))

    (rega (if direct-b (if unary update regb) (if store write0 update))
          (regs-address rn-a) (select-immediate a-immediate-p) we-a-reg)

    (regb update (regs-address rn-b) we-b-reg)

    (update (if (b-and side-effect-b unary) sefb1 fetch0)
            (regs-address rn-b) (we-regs store) (we-flags set-flags)
            we-b-reg)

    (reada0 reada1 (regs-address rn-a) we-a-reg we-addr-out
            (dec-addr-out pre-dec-a))

    (reada1 reada2
            (alu-c (if* pre-dec-a
                       (carry-in-help (cons c (cons f (alu-dec-op))))
                     (carry-in-help (cons c (cons f (alu-inc-op))))))
            (alu-op (if* pre-dec-a (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-a
                         (mpg (cons f (cons f (alu-dec-op))))
                       (mpg (cons f (cons f (alu-inc-op))))))
            (regs-address rn-a) (we-regs side-effect-a))
        
    (reada2 reada3 (regs-address rn-b) we-b-reg strobe-)

    (reada3 (if dtack-
                reada3
              (if direct-b
                  update
                (if unary
                    (if store write0 update)
                  readb0)))
            data-in-select we-a-reg strobe-)

    (readb0 readb1 (regs-address rn-b) we-addr-out
            (dec-addr-out pre-dec-b) we-b-reg)

    (readb1 readb2 (regs-address rn-a) (we-a-reg direct-a)
            (select-immediate a-immediate-p))

    (readb2 readb3
            (regs-address rn-b) (we-regs (and* store- side-effect-b))
            (alu-c (if* pre-dec-b
                       (carry-in-help (cons c (cons f (alu-dec-op))))
                     (carry-in-help (cons c (cons f (alu-inc-op))))))
            (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-b
                         (mpg (cons f (cons t (alu-dec-op))))
                       (mpg (cons f (cons t (alu-inc-op))))))
            strobe-)

    (readb3 (if dtack- readb3 (if store write0 update))
            we-b-reg data-in-select strobe-)

    (write0 write1
            (we-flags set-flags) we-data-out
            (regs-address rn-b) we-b-reg we-addr-out
            (dec-addr-out pre-dec-b))

    (write1 write2
            (regs-address rn-b) (we-regs side-effect-b)
            (alu-c (if* pre-dec-b
                       (carry-in-help (cons c (cons f (alu-dec-op))))
                     (carry-in-help (cons c (cons f (alu-inc-op))))))
            (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
            (alu-mpg (if* pre-dec-b
                         (mpg (cons f (cons t (alu-dec-op))))
                       (mpg (cons f (cons t (alu-inc-op))))))
            rw-)

    (write2 write3 strobe- rw-)

    (write3 (if dtack- write3 fetch0) rw- strobe-)

    (sefa0 sefa1 (regs-address rn-a) we-a-reg)

    (sefa1 (if side-effect-b sefb0 fetch0)
           (regs-address rn-a) we-regs
           (alu-c (if* pre-dec-a
                      (carry-in-help (cons c (cons f (alu-dec-op))))
                    (carry-in-help (cons c (cons f (alu-inc-op))))))
           (alu-op (if* pre-dec-a (alu-dec-op) (alu-inc-op)))
           (alu-mpg (if* pre-dec-a
                        (mpg (cons f (cons f (alu-dec-op))))
                      (mpg (cons f (cons f (alu-inc-op)))))))
                 

    (sefb0 sefb1 (regs-address rn-b) we-b-reg)

    (sefb1 fetch0
           (regs-address rn-b) we-regs
           (alu-c (if* pre-dec-b
                      (carry-in-help (cons c (cons f (alu-dec-op))))
                    (carry-in-help (cons c (cons f (alu-inc-op))))))
           (alu-op (if* pre-dec-b (alu-dec-op) (alu-inc-op)))
           (alu-mpg (if* pre-dec-b
                        (mpg (cons f (cons t (alu-dec-op))))
                      (mpg (cons f (cons t (alu-inc-op)))))))

    (hold0 (if hold- hold1 hold0) hdack- we-pc-reg we-hold-)

    (hold1 fetch0)

    (v11010 reset0)                     ;Illegal
    (v11011 reset0)                     ;Illegal

    ;;  We use (ALU-INC-OP) as the default op-code during the reset sequence
    ;;  so that the control vector will be completely defined.  Recall that the
    ;;  OP-CODE is irrelevant to ALU operation when it is forced to zero.
    ;;  Thu Jul 18 11:33:55 1991 BB -- With new optimizations, we depend on the
    ;;  OP-CODE being set to ALU-INC-OP during zeroing!
    ;;  NB: All idiomatic expressions are necessary for later proofs; cryptic
    ;;  comments being especially opaque.

    (reset0 reset1
            (regs-address (make-list 4 f)) we-regs we-data-out
            (we-flags (make-list 4 t)) we-pc-reg we-hold-
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons f (alu-inc-op))))))

    (reset1 reset2 (regs-address (make-list 4 f)) 
            we-addr-out we-a-reg we-b-reg we-i-reg
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons f (alu-inc-op))))))

    (reset2 (if all-t-regs-address fetch0 reset2)
            we-regs
            alu-zero
            (alu-op (alu-inc-op))
            (alu-c (carry-in-help (cons c (cons t (alu-inc-op)))))
            (alu-mpg (mpg (cons t (cons f (alu-inc-op)))))
            (regs-address (v-inc regs-address)))

    (v11111 reset0)))                   ;Illegal


;;;  For each control state, define a control vector function, and lemmas to
;;;  destructure the control vector function.

(defun cv-name (state) (unstring "CV_" state))
(defun cv-lemma-name (state) (unstring "CV_" state "$DESTRUCTURE"))

;;;   Use the *STATE-TABLE* to build a CV_state function for each state.  This
;;;   is the function that creates the control-vector for each state.
;;;   Note that the reset states RESET0 and RESET1 are constants, and
;;;   in these cases we don't include the hypothesis.

(defmacro define-control-vector-functions ()
  (labels
    ((build-state
      (template)
      (cond
       ((null template) 'NIL)
       (t (if (numberp (cadar template))
              `(APPEND ,(caddar template) ,(build-state (cdr template)))
            `(CONS ,(caddar template) ,(build-state (cdr template))))))))
                      
    `(PROGN
      ,@(iterate for (state next-state . fields) in *state-table*
          nconc (progn (ignore-variable next-state)
                       (let ((template (copy-tree *control-template*)))
                         (setf (third (assoc 'state template))
                               (list (vector-state-name state)))
                         (dolist (field fields)
                           (let ((triple (assoc (if (listp field)
                                                    (car field)
                                                  field)
                                                template)))
                             (unless triple
                               (error "No field named ==> ~s." field))
                             (setf (caddr triple)
                                   (if (listp field)
                                       (cadr field)
                                     (if (equal (caddr triple) 'T)
                                         'F
                                       'T)))))
                         `((DEFN
                             ,(cv-name state)
                             ,*control-arglist*
                             ,(control-let (build-state template)))
                           (DISABLE ,(cv-name state))
                           (#+axioms
                            ADD-AXIOM
                            #-axioms
                            PROVE-LEMMA
                            ,(cv-lemma-name state) (REWRITE)
                            ,(control-let
                              `(IMPLIES
                                ,(if (member state '(RESET0 RESET1))
                                     'T
                                   '(CV-HYPS RW- REGS-ADDRESS I-REG
                                             FLAGS PC-REG))
                                (AND
                                 ,@(iterate for (field type value) in template
                                     collect
                                     (progn
                                       (ignore-variable type)
                                       `(EQUAL (,field (,(cv-name state)
                                                        ,@*control-arglist*))
                                               ,value))))))

                            ;;Hint
                            #-axioms
                            ((ENABLE ,(cv-name state)
                                     ,(vector-state-name state)
                                     OPEN-NTH NTH-IF
                                     SUBRANGE-CONS OP-CODE SET-FLAGS RN-A RN-B)
                             (ENABLE-THEORY CONTROL-STATE-ACCESSOR-THEORY)
                             (DISABLE MPG)))
                           (DISABLE ,(cv-lemma-name state))))))

      (DEFTHEORY CV-THEORY
        ,(iterate for (state . rest) in *state-table*
           collect (progn (ignore-variable rest)
                          (cv-name state))))

      (DEFTHEORY CV-DESTRUCTURE-THEORY
        ,(iterate for (state . rest) in *state-table*
           collect (progn (ignore-variable rest)
                          (cv-lemma-name state))))

      (PROVE-LEMMA BVP-CV-VECTORS (REWRITE)
        (IMPLIES
         (CV-HYPS RW- REGS-ADDRESS I-REG FLAGS PC-REG)
         (AND ,@(iterate for (state . rest) in *state-table*
                  collect
                  (progn (ignore-variable rest)
                         `(BVP (,(cv-name state)
                                RW- REGS-ADDRESS I-REG FLAGS PC-REG))))))
        ;;Hint
        ((ENABLE-THEORY CV-THEORY)
         (ENABLE BVP-LENGTH-STATE-VECTORS)))

      (DISABLE BVP-CV-VECTORS))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    SYNTHESIS
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;    Symbolic gate generation.

(defun b-not-ify (args)
  (let (arg
        (alist
         `((B-OR . B-NOR)
           (B-OR3 . B-NOR3)
           (B-OR4 . B-NOR4)
           (B-OR5 . B-NOR5)
           (B-OR6 . B-NOR6)
           (B-OR8 . B-NOR8)
           (B-AND . B-NAND)
           (B-AND3 . B-NAND3)
           (B-AND4 . B-NAND4)
           (B-AND5 . B-NAND5)
           (B-AND6 . B-NAND6)
           (B-AND8 . B-NAND8))))
    (if (match (car args) (VSS))
        '(VDD)
      (if (match (car args) (VDD))
          '(VSS)
        (if (match (car args) (B-NOT arg))
            arg
          (if (and (listp (car args)) (assoc (caar args) alist))
              (cons (cdr (assoc (caar args) alist))
                    (cdar args))
            (if (and (listp (car args)) (rassoc (caar args) alist))
                (cons (car (rassoc (caar args) alist))
                      (cdar args))
              `(B-NOT ,(car args)))))))))

(defun b-nand-ify (args)
  (let ((l (length args)))
    (case l
      (0 '(VSS))
      (1 (b-not-ify args))
      (2 `(B-NAND ,@args))
      (7 `(B-NAND (B-AND4 ,@(subseq args 0 4))
                  (B-AND3 ,@(nthcdr 4 args))))
      (t `(,(unstring "B-NAND" l) ,@args)))))

(defun b-and-ify (args)
  (let ((l (length args)))
    (case l
      (0 '(VDD))
      (1 (car args))
      (2 `(B-AND ,@args))
       (7 `(B-NOR (B-NAND4 ,@(subseq args 0 4))
                 (B-NAND3 ,@(nthcdr 4 args))))
      (t `(,(unstring "B-AND" l) ,@args)))))

(defun b-or-ify (args)
  (let ((l (length args)))
    (case l
      (0 '(VSS))
      (1 (car args))
      (2 `(B-OR ,@args))
      (7 `(B-NAND (B-NOR4 ,@(subseq args 0 4))
                  (B-NOR3 ,@(nthcdr 4 args))))
      (t `(,(unstring "B-OR" l) ,@args)))))

(defun b-nor-ify (args)
  (let ((l (length args)))
    (case l
      (0 '(VSS))
      (1 (b-not-ify args))
      (2 `(B-NOR ,@args))
      (7 `(B-NOR (B-OR4 ,@(subseq args 0 4))
                 (B-OR3 ,@(nthcdr 4 args))))
      (t `(,(unstring "B-NOR" l) ,@args)))))

;;;  This macro defines NEXT-STATE*, which takes the current decoded state
;;;  and creates a decoded version of the next state.

(defmacro define-next-state ()
  (let ((state-names (mapcar #'car *control-states*))
        (state-alist (iterate for (state . val) in *control-states*
                       collecting (list state)))
        spec hdl-body)
  
    (labels
          
      ((sname (state) (unstring "S" (position state state-names)))

       (siname (state) `(INDEX 'S ,(position state state-names)))
       
       (unwind
        (tree expr)
        (cond
         ((symbolp tree) (push expr (cdr (assoc tree state-alist))))
         ((equal (car tree) 'IF)
          (unwind (caddr tree) (cons (cadr tree) expr))
          (unwind (cadddr tree) (cons `(B-NOT ,(cadr tree)) expr)))
         (t (error "DEFINE-NEXT-STATE error"))))

       (cons-up
        (alist)
        (cond
         ((null alist) ''nil)
         (t `(CONS ,(b-nand-ify (iterate for clause in (cdar alist)
                               collecting (b-nand-ify clause)))
                   ,(cons-up (cdr alist)))))))

      (let (hdl-outputs
            ;;  (snames (mapcar #'sname state-names))
            ;;  (sinames (mapcar #'siname state-names))
            )
        
        (iterate for (state next . rest) in *state-table*
          do (progn (ignore-variable rest)
                    (unwind next (list state))))

        (setf spec (cons-up state-alist))

        (multiple-value-setq (hdl-outputs hdl-body) (logic-to-hdl spec))

        `(PROGN

          (DEFN NEXT-STATE (DECODED-STATE
                            STORE SET-SOME-FLAGS
                            UNARY DIRECT-A DIRECT-B
                            SIDE-EFFECT-A SIDE-EFFECT-B
                            ALL-T-REGS-ADDRESS
                            DTACK- HOLD-)
            (LET ,(iterate for name in state-names for n from 0
                    collecting `(,name (NTH ,n DECODED-STATE)))
              ,spec))

          (DEFN F$NEXT-STATE (DECODED-STATE
                              STORE SET-SOME-FLAGS
                              UNARY DIRECT-A DIRECT-B
                              SIDE-EFFECT-A SIDE-EFFECT-B
                              ALL-T-REGS-ADDRESS
                              DTACK- HOLD-)
            (LET ,(iterate for name in state-names for n from 0
                    collecting `(,name (NTH ,n DECODED-STATE)))
              ,(f-body spec)))

          (DISABLE F$NEXT-STATE)

          (PROVE-LEMMA F$NEXT-STATE=NEXT-STATE (REWRITE)
            (IMPLIES
             (AND (BVP DECODED-STATE)
                  (EQUAL (LENGTH DECODED-STATE) 32)
                  (BOOLP STORE) (BOOLP SET-SOME-FLAGS)
                  (BOOLP UNARY) (BOOLP DIRECT-A) (BOOLP DIRECT-B)
                  (BOOLP SIDE-EFFECT-A) (BOOLP SIDE-EFFECT-B)
                  (BOOLP ALL-T-REGS-ADDRESS)
                  (BOOLP DTACK-) (BOOLP HOLD-))
             (EQUAL (F$NEXT-STATE DECODED-STATE
                              STORE SET-SOME-FLAGS
                              UNARY DIRECT-A DIRECT-B
                              SIDE-EFFECT-A SIDE-EFFECT-B
                              ALL-T-REGS-ADDRESS
                              DTACK- HOLD-)
                    (NEXT-STATE DECODED-STATE
                              STORE SET-SOME-FLAGS
                              UNARY DIRECT-A DIRECT-B
                              SIDE-EFFECT-A SIDE-EFFECT-B
                              ALL-T-REGS-ADDRESS
                              DTACK- HOLD-)))
            ;;HINT
            ((ENABLE F$NEXT-STATE NEXT-STATE BOOLP-B-GATES)
             (DISABLE-THEORY F-GATES B-GATES)))
      
          (DEFN NEXT-STATE* ()
            (LIST
             'NEXT-STATE
             (APPEND #i(s 0 32)
                     '(STORE SET-SOME-FLAGS
                             UNARY DIRECT-A DIRECT-B
                             SIDE-EFFECT-A SIDE-EFFECT-B
                             ALL-T-REGS-ADDRESS
                             DTACK- HOLD-))
             ',hdl-outputs
             (APPEND
              (LIST
               ,@(iterate for state in state-names for n from 0
                  collecting
                  `(LIST ',(unstring "R-" n) '(,state) 'ID (LIST #i(S ,n)))))
              ',hdl-body)
             nil))

          (MODULE-PREDICATE NEXT-STATE*)

          (MODULE-NETLIST NEXT-STATE*))))))

#|
This stuff that is commented out was used to help build the specification and
DUAL-EVAL form of the control logic.

(defun partition-set (fn set)
  (iterate for el in set with p with key
    do (let* ((key (funcall fn el))
              (pair (assoc-equal key p)))
         (if pair
             (push el (cdr pair))
           (setf p (acons key (list el) p))))
    finally (return p)))

(setf equations
      (iterate for (field type default) in (cdr *control-template*)
        collecting
        (let (assignments)
          (iterate for (state next . fields) in *state-table*
            do (iterate for assignment in fields
                 do (if (equal assignment field)
                        (if (equal type 'b)
                            (if (equal default 'T)
                                (push (cons state 'F) assignments)
                              (push (cons state 'T) assignments))
                          (error "Wrong type ~s ~s" assignment type))
                      (if (consp assignment)
                          (if (equal (car assignment) field)
                              (unless (equal (cadr assignment) default)
                                (push (cons state (cadr assignment))
                                      assignments)))))))
          (list field type default
                (iterate for (key . pairs) in (partition-set #'cdr assignments)
                  collecting (cons key (mapcar #'car pairs)))))))



(iterate for (field type default assignments) in equations
  collecting
  (list field type default
        (if (and (equal type 'b) (not (equal field 'ALU-C)))
            (if (equal default 'f)
                (b-nand-ify
                 (iterate for (value . disjuncts) in assignments
                   collecting
                   (if (equal value 't)
                       (b-nor-ify disjuncts)
                     `(B-NAND ,value ,(b-or-ify disjuncts)))))
              (b-and-ify
               (iterate for (value . disjuncts) in assignments
                 collecting
                 (if (equal value 'f)
                     (b-nor-ify disjuncts)
                   `(B-NAND (B-NOT ,value) ,(b-or-ify disjuncts))))))
          assignments)))

|#



;;;  Write a lemma for the next control-state for each state in terms of the CV
;;;  functions.

(defmacro generate-next-cntl-state-lemmas ()
  (labels
    ((translate-b-fns
      (form)
      (cond
       ((symbolp form) form)
       (t (case (car form)
            (b-and (cons 'AND* (mapcar #'translate-b-fns (cdr form))))
            (b-or  (cons 'OR*  (mapcar #'translate-b-fns (cdr form))))
            (b-not (cons 'NOT* (mapcar #'translate-b-fns (cdr form))))
            (t (error "Bad form ==> ~s." form))))))

     (make-if-tree
      (tree)
      (cond
       ((symbolp tree) `(,(cv-name tree) ,@*control-arglist*))
       ((and (consp tree) (equal (car tree) 'IF))
        `(IF* ,(translate-b-fns (cadr tree))
             ,(make-if-tree (caddr tree))
           ,(make-if-tree (cadddr tree))))
       (t (error "Bad tree => ~s." tree)))))
        
    `(PROGN
      ,@(iterate for (state next-state . fields) in *state-table*
          collecting
          (progn
            (ignore-variable fields)
            (let ((v-state `(,(vector-state-name state))))
              `(PROVE-LEMMA ,(unstring "NEXT-CNTL-STATE$" state) (REWRITE)
                 (IMPLIES
                  (AND (EQUAL RESET- T)
                       (CV-HYPS RW- REGS-ADDRESS I-REG FLAGS PC-REG))
                  (EQUAL (NEXT-CNTL-STATE RESET- DTACK- HOLD- RW- ,v-state
                                          I-REG FLAGS PC-REG REGS-ADDRESS)
                         ,(control-let (make-if-tree next-state))))
                 ;;Hint
                 ((ENABLE-THEORY VECTOR-STATE-THEORY
                                 CV-THEORY IR-FIELDS-THEORY)
                  (ENABLE CV NEXT-CNTL-STATE IF*)
                  (DISABLE *1*CARRY-IN-HELP *1*MPG)))))))))

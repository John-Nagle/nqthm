;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    EXPAND-FM9001.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    SINGLE STEP SIMULATIONS
;;;
;;;  The STEP-FM9001 macro creates a lemma that describes the new state
;;;  computed by a single step of the low-level machine from the given initial
;;;  state.  This procedure is complicated by the fact that the next state
;;;  depends on the state of the memory.  Rather than produce a single lemma
;;;  that captures the behavior for all possible memory states, we create
;;;  separate lemmas only for those processor-state/memory-state configurations
;;;  that are possible during normal instruction execution.  This is important
;;;  because if the memory protocol is not followed, then unknown values may be
;;;  loaded into the processor registers.  What we are doing here is creating
;;;  a state-by-state, almost-Boolean specification of the low-level machine. 
;;;  So we obviously we want to insure that the processor state remains
;;;  Boolean. 
;;;
;;;  STEP-FM9001 is used in "expand-fm9001.events".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro step-fm9001 (state &key
                             (suffix "")
                             (addr-stable nil)
                             (data-stable nil)
                             (dtack- 'DTACK-)
                             (mem-state 0)
                             (mem-count 'MEM-COUNT)
                             (mem-dtack 'MEM-DTACK)
                             (last-rw- 'T)
                             (hyps nil)
                             (enable nil)
                             (disable nil)
                             (split-term nil))
  (let ((term
         `(RUN-FM9001 
           (LIST
            (LIST REGS
                  FLAGS
                  A-REG B-REG I-REG
                  DATA-OUT ADDR-OUT
                  RESET- ,dtack- HOLD-
                  PC-REG
                  (,(cv-name state)
                   ,last-rw- LAST-REGS-ADDRESS LAST-I-REG
                   LAST-FLAGS LAST-PC-REG))
            (LIST MEM ,mem-state CLOCK ,mem-count ,mem-dtack
                  ,last-rw-
                  ,(if addr-stable 'ADDR-OUT 'LAST-ADDRESS)
                  ,(if data-stable 'DATA-OUT 'LAST-DATA)))
           INPUTS
           N))
        (hyps
         `(AND (CV-HYPS ,last-rw- LAST-REGS-ADDRESS LAST-I-REG LAST-FLAGS
                        LAST-PC-REG)
               (CV-HYPS T PC-REG I-REG FLAGS PC-REG)
               (MEMORY-OKP 32 32 MEM)
               (regfile-okp regs)
               (BVP A-REG)
               (EQUAL (LENGTH A-REG) 32)
               (BVP B-REG)
               (EQUAL (LENGTH B-REG) 32)
               (BVP ADDR-OUT)
               (EQUAL (LENGTH ADDR-OUT) 32)
               (BVP DATA-OUT)
               (EQUAL (LENGTH DATA-OUT) 32)
               (NOT (ZEROP N))
               (RUN-INPUTS-P INPUTS 1)
               (boolp ,dtack-)
               (boolp HOLD-)
               (EQUAL RESET- T)
               ,hyps))
        (hints
         `((ENABLE-THEORY FM9001-HARDWARE-STATE-ACCESSORS)
           (DISABLE-THEORY f-gates)
           (ENABLE RUN-FM9001-STEP-CASE
                   rewrite-FM9001-NEXT-STATE-for-step-lemmas boolp-b-gates
                   NEXT-MEMORY-STATE MEMORY-VALUE
                   ,(cv-lemma-name state) OPEN-NTH
                   bvp-length-state-vectors bvp-cv-vectors
                   ,@enable)
           (DISABLE MPG MAKE-TREE *1*MAKE-TREE *1*make-list
                    open-v-threefix ,@disable))))
    
    `(#+axioms
      ADD-AXIOM
      #-axioms
      PROVE-LEMMA
      ,(unstring state "$STEP" suffix) (REWRITE)
      (IMPLIES
       ,hyps
       (EQUAL ,term 
              ,(if split-term
                   `(IF ,split-term
                        ,(print (expand term `(AND ,hyps ,split-term) hints))
                      ,(print (expand term `(AND ,hyps (NOT ,split-term))
                                      hints)))
                 (print (expand term hyps hints)))))
      ;;Hint
      #-axioms
      ,hints
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    Timing functions
;;;
;;;  T_initial-state->final-state is an expression for the amount of time
;;;  necessary to execute the indicated section of the state diagram.
;;;  CT_initial-state->final-state is an expression for the memory delay oracle
;;;  at the end of the sequence.  TIMING-IF-TREE creates an "IF" tree of calls
;;;  to timing functions based on the branching decisions that appear in the
;;;  state diagrams. 
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun t_fetch0->fetch0 ()
  1)

(defun ct_fetch0->fetch0 ()
  'CLOCK)

(defun w_fetch1->decode ()
  '(CAR CLOCK))

(defun t_fetch1->decode ()
  '(ADD1 (ADD1 (PLUS #.(w_fetch1->decode) 2))))

(defun ct_fetch1->decode ()
  '(CDR CLOCK))

(defun t_rega->rega ()
  1)

(defun ct_rega->rega ()
  'CLOCK)

(defun t_regb->update ()
  2)

(defun ct_regb->update ()
  'CLOCK)

(defun t_update->update ()
  1)

(defun ct_update->update ()
  'CLOCK)

(defun w_reada0->reada3 ()
  '(CAR CLOCK))

(defun t_reada0->reada3 ()
  '(ADD1 (ADD1 (ADD1 (PLUS #.(w_reada0->reada3) 1)))))

(defun ct_reada0->reada3 ()
  '(CDR CLOCK))

(defun w_readb0->readb3 ()
  '(CAR CLOCK))

(defun t_readb0->readb3 ()
  '(ADD1 (ADD1 (ADD1 (PLUS #.(w_readb0->readb3) 1)))))

(defun ct_readb0->readb3 ()
  '(CDR CLOCK))

(defun w_write0->write3 ()
  '(CAR CLOCK))

(defun t_write0->write3 ()
  '(ADD1 (ADD1 (ADD1 (PLUS #.(w_write0->write3) 1)))))

(defun ct_write0->write3 ()
  '(CDR CLOCK))

(defun t_sefa0->sefa1 ()
  2)

(defun ct_sefa0->sefa1 ()
  'CLOCK)

(defun t_sefb0->sefb1 ()
  2)

(defun ct_sefb0->sefb1 ()
  'CLOCK)

(defun t_sefb1->sefb1 ()
  1)

(defun ct_sefb1->sefb1 ()
  'CLOCK)

(defun timing-if-tree (state)
  (labels
    ((timify-tree
      (tree)
      (cond
       ((symbolp tree) `(,(unstring "T_" tree) CLOCK I-REG FLAGS))
       ((and (consp tree) (equal (car tree) 'IF))
        (if (equal (cadr tree) 'DTACK-)
            (timify-tree (cadddr tree))
          (if (equal (cadr tree) 'HOLD-)
              (timify-tree (caddr tree))
            `(IF ,(cadr tree)
                 ,(timify-tree (caddr tree))
               ,(timify-tree (cadddr tree))))))
       (t (error "Bad tree => ~s." tree)))))
    (control-let (timify-tree (cadr (assoc state *state-table*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;    Chunk Simulations
;;;
;;;  SIM-FM9001 is a macro that creates lemmas that describe the operation of
;;;  the machine for multiple clock cycles.  We create a multi-state simulation
;;;  for each non-branching segment of the state diagrams.  For this purpose,
;;;  we consider the states that wait for memory as "non-branching".  Notice
;;;  that some of the "multi-state" lemmas only include a single state.
;;;  
;;;  SIM-FM9001 is used in "expand-fm9001.events"
;;;  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro sim-fm9001 (start-state end-state
                                  &key
                                  (suffix "")
                                  (addr-stable nil)
                                  (data-stable nil)
                                  (dtack- 'DTACK-)
                                  (mem-state 0)
                                  (mem-count 'MEM-COUNT)
                                  (mem-dtack 'MEM-DTACK)
                                  (last-rw- 'T)
                                  (hyps nil)
                                  (enable nil)
                                  (disable nil)
                                  (split-term nil)
                                  (dtack-wait nil))
  (declare (ignore enable))                            
  (let* ((time-fn (unstring "T_" start-state "->" end-state))
         (time (eval `(,time-fn)))
         (lemma (unstring start-state "->" end-state "$SIM" suffix))
         (term
          `(RUN-FM9001 
            (LIST
             (LIST REGS FLAGS
                   A-REG B-REG I-REG
                   DATA-OUT ADDR-OUT
                   RESET- ,dtack- HOLD-
                   PC-REG
                   (,(cv-name start-state)
                    ,last-rw- LAST-REGS-ADDRESS LAST-I-REG
                    LAST-FLAGS PC-REG))
             (LIST MEM ,mem-state CLOCK ,mem-count ,mem-dtack
                   ,last-rw-
                   ,(if addr-stable 'ADDR-OUT 'LAST-ADDRESS)
                   ,(if data-stable 'DATA-OUT 'LAST-DATA)))
            INPUTS
            ,time))
         (hyps
         `(AND (CV-HYPS ,last-rw- LAST-REGS-ADDRESS LAST-I-REG LAST-FLAGS
                        PC-REG)
               (CV-HYPS T PC-REG I-REG FLAGS PC-REG)
               (MEMORY-OKP 32 32 MEM)
               (REGFILE-OKP REGS)
               (BVP A-REG)
               (EQUAL (LENGTH A-REG) 32)
               (BVP B-REG)
               (EQUAL (LENGTH B-REG) 32)
               (BVP ADDR-OUT)
               (EQUAL (LENGTH ADDR-OUT) 32)
               (BVP DATA-OUT)
               (EQUAL (LENGTH DATA-OUT) 32)
               (boolp ,dtack-)
               (boolp HOLD-)
               (RUN-INPUTS-P INPUTS ,time)
               (EQUAL RESET- T)
               ,hyps))
         (hints
          `(                            ;(no-built-in-arith t)
            (enable regfile-okp)
            (DISABLE PLUS-ADD1 MAKE-TREE *1*MAKE-TREE V-INC V-DEC BV
                     F-BUF ,@disable))))
    
    `(#+axioms
      ADD-AXIOM
      #-axioms
      PROVE-LEMMA ,lemma (REWRITE)
      (IMPLIES
       ,(if dtack-wait
            `(AND (EQUAL DTACK-WAIT ,dtack-wait)
                  ,hyps)
          hyps)
       (EQUAL ,term
              ,(if dtack-wait
                   (print (expand term
                                  `(AND (EQUAL DTACK-WAIT ,dtack-wait)
                                        (NOT (ZEROP DTACK-WAIT))
                                        ,hyps)
                                  hints))
                 (if split-term
                     `(IF ,split-term
                          ,(print (expand term `(AND ,hyps ,split-term) hints))
                        ,(print (expand term `(AND ,hyps (NOT ,split-term))
                                        hints)))
                   (print (expand term hyps hints))))))
      ;;Hint
      #-axioms
      ,(if dtack-wait
           `((INDUCT (ZEROP-NOT-ZEROP-CASES DTACK-WAIT))
             ,@hints)
         hints)
      )))

;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    MACROS.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;  We use this function to eliminate unused variable messages from
;;  within structured "LET's" inside backquoted expresions.

(defun ignore-variable (x) x)

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    UNBREAK
;;;
;;;    Turn off rewrite tracing.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun unbreak ()
  (unbreak-lemma)
  (maintain-rewrite-path nil)
  (format t "~%Ignore the above message about the rewrite path being ~
               maintained."))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    NQFIX
;;;    NQNULL
;;;    NQCAR
;;;    NQCDR
;;;    NQNTH
;;;
;;;    These are for destructuring BM terms as they are stored on the property
;;;    lists in the NQTHM database.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun nqfix (form)
  (list 'QUOTE form))

(defun nqnull (form)
  (and (equal (car form) 'QUOTE)
       (null (cadr form))))

(defun nqcar (form)
  (if (equal (car form) 'QUOTE)       
      (nqfix (caadr form))
    (if (equal (car form) 'CONS)      
        (cadr form)
      (if (equal (car form) 'APPEND)  
          (if (nqnull (cadr form))
              (nqcar (caddr form))
            (nqcar (cadr form)))
        (error "~s" form)))))

(defun nqcdr (form)
  (if (equal (car form) 'QUOTE)       
      (nqfix (cdadr form))
    (if (equal (car form) 'CONS)      
        (caddr form)
      (if (equal (car form) 'APPEND)  
          (if (nqnull (cadr form))
              (nqcdr (caddr form))
            `(APPEND ,(nqcdr (cadr form)) ,(caddr form)))
        (error "~s" form)))))

(defun nqnth (n form)
  (if (zerop n)
      (nqcar form)
    (nqnth (1- n) (nqcdr form))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    UNSTRING &rest args
;;;
;;;  Concatenates the STRING of each of its args (converting numbers to decimal
;;;  form), and INTERNs the result, returning the symbol.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun unstring (&rest args)
  (intern (apply #'concatenate 'string
                 (mapcar #'(lambda (x)
                             (if (numberp x)
                                 (format nil "~d" x)
                               (string x)))
                         args))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    SUBMODULES generator &key body
;;;    SUBMODULE-VALUE-LEMMAS generator &key body
;;;
;;;    Looks inside a generator and creates a list of the referenced
;;;    submodules.  The :BODY keyword gives a "side-door" entrance for cases
;;;    where the GENERATOR has not actually been stored, but we know what the
;;;    body is (see DEFN-TO-MODULE).
;;;    
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun submodules (generator &key body)
  (let* ((event (get generator 'event))
         (form (nth 3 event))
         (body (if body body (nqnth 3 form))))
    (labels
      ((collect
        (l)
        (cond
         ((nqnull l) nil)
         (t (cons (nqnth 2 (nqcar l)) (collect (nqcdr l)))))))
      (remove-duplicates (mapcar #'cadr (collect body))))))

(defun submodule-value-lemmas (generator &key body)
  (mapcar #'(lambda (x) (unstring x "$VALUE"))
          (submodules generator :body body)))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    MODULE-PREDICATE generator
;;;
;;;  MODULE-PREDICATE writes the netlist predicate for simple modules.  For
;;;  example, if the module is defined by (M*), then (MODULE-PREDICATE M*)
;;;  creates (M& NETLIST). 
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defmacro module-predicate (generator)
  (let* ((event (get generator 'event))
         (form (nth 3 event))
         (name (cadr (nqcar form)))
         (fn& (unstring name "&"))
         (submodules (submodules generator))
         (sub& (mapcar #'(lambda (x)
                           `(,(unstring x "&")
                             (DELETE-MODULE ',name NETLIST)))
                       submodules)))

    `(PROGN

      (DEFN ,fn& (NETLIST)
        (AND (EQUAL (LOOKUP-MODULE ',name NETLIST) (,generator))
             ,@sub&))

      (DISABLE ,fn&))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    MODULE-NETLIST generator
;;;
;;;  MODULE-NETLIST assembles the netlist for simple modules.  For
;;;  example, if the module is defined by (M*), then (MODULE-NETLIST M*)
;;;  creates (M$NETLIST NETLIST).
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defmacro module-netlist (generator)
  (let* ((event (get generator 'event))
         (form (nth 3 event))
         (name (cadr (nqcar form)))
         (netfn (unstring name "$NETLIST"))
         (submodules (submodules generator))
         (subnetlists (mapcar #'(lambda (x) `(,(unstring x "$NETLIST")))
                              submodules))
         (body (reduce #'(lambda (x y) `(UNION ,x ,y)) subnetlists)))

    `(DEFN ,netfn () (CONS (,generator) ,body))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    DEFN-TO-MODULE
;;;
;;;    DEFN-TO-MODULE converts simple BM specifications to DUAL-EVAL constants.
;;;    The BM specifications may be multiple output, but every referenced
;;;    primitive must be single output.  No vectors on inputs, outputs, or
;;;    internal modules are allowed.  Examples abound in the events.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defvar signal-counter 0)
(defvar gate-counter 0)

(defun gensignal ()
  (prog1 (unstring "W-" signal-counter) (incf signal-counter)))
(defun gengate ()
  (prog1 (unstring "G-" gate-counter) (incf gate-counter)))

(defun expand-body (body &optional top)
  (cond
   ((symbolp body) (if top
                       (let ((name (list (gensignal))))
                         (values name
                                 (list (list (gengate) name 'ID (list body)))))
                     (values (list body) nil)))
   ((and (equal (car body) 'quote) (null (cadr body))) (values nil nil))
   ((equal (car body) 'cons)
    (multiple-value-bind (car-outputs car-body) (expand-body (cadr body) t)
      (multiple-value-bind (cdr-outputs cdr-body) (expand-body (caddr body))
        (values (append car-outputs cdr-outputs)
                (append car-body cdr-body)))))
   (t (let* ((fn (car body))
             (x-args (mapcar #'(lambda (x)
                                 (multiple-value-list (expand-body x)))
                             (cdr body)))
             (wires (mapcar #'caar x-args))
             (subbody (mapcan #'cadr x-args))
             (name (list (gensignal))))
        
        (values name (cons (list (gengate) name fn wires) subbody))))))

(defun compress-body (outputs body r-body)
  (cond
   ((null body) (values outputs (reverse r-body)))
   (t (let* ((occ (car body))
             (lhs (cadr occ))
             (fn  (caddr occ))
             (rhs (cadddr occ))
             (tail (member 0 (cdr body)
                           :test #'(lambda (x occ) (declare (ignore x))
                                     (and (equal (caddr occ) fn)
                                          (equal (cadddr occ) rhs))))))
        (cond
         ((not tail) (compress-body outputs (cdr body) (cons occ r-body)))
         (t (let* ((new-occ (car tail))
                   (new-lhs (cadr new-occ))
                   (alist (mapcar #'cons new-lhs lhs)))
              (compress-body
               (sublis alist outputs)
               (cons occ (sublis alist
                                 (delete new-occ (cdr body) :test #'equal))) 
               r-body))))))))

(defun fixup-duplicate-outputs (outputs body)
  (let ((outputs
         (iterate for (output . rest) on outputs
           collecting
           (if (member output rest)
               (let* ((new-output (gensignal))
                      (new-form `(,(gengate) (,new-output) ID (,output))))
                 (setf body (append body (list new-form)))
                 new-output)
             output))))
    (values outputs body)))
                  
(defun logic-to-hdl (body)
  (setf signal-counter 0)
  (setf gate-counter 0)
  (multiple-value-bind (outputs body)
    (expand-body body t)
    (multiple-value-bind (outputs body)
      (compress-body outputs (reverse body) nil)
      (multiple-value-bind (outputs body)
        (fixup-duplicate-outputs outputs body)
        (values outputs body)))))

(defun b-to-f (name)
  (if (member name '(ID VSS VDD))
      name
    (let ((string (string name)))
      (if (equal (subseq string 0 2) "B-")
          (unstring "F-" (subseq string 2))
        (unstring "F$" string)))))

(defun f-body (body)
  (cond
   ((symbolp body) body)
   ((and (equal (car body) 'quote) (null (cadr body))) NIL)
   ((equal (car body) 'cons)
    `(CONS ,(f-body (cadr body)) ,(f-body (caddr body))))
   (t (cons (b-to-f (car body))
            (mapcar #'(lambda (x) (f-body x)) (cdr body))))))

(defmacro defn-to-module (spec &key value-lemma boolp-value-lemma)
  (let* ((defn (get spec 'event))
         (name (second defn))
         (inputs (third defn))
         (body (fourth defn)))
    (multiple-value-bind (hdl-outputs hdl-body)
      (logic-to-hdl body)
      (let* ((f-body (f-body body))
             (f$name (unstring "F$" name))
             (fn* (unstring name "*"))
             (fn& (unstring name "&"))
             (value-lemma (if value-lemma
                              value-lemma
                            (unstring name "$VALUE")))
             (boolp-value-lemma
              (if boolp-value-lemma
                  boolp-value-lemma
                (unstring f$name "=" name)))
             (boolp-inputs (mapcar #'(lambda (x)
                                       `(BOOLP ,x))
                                   inputs)))
                   
        `(PROGN

          (DEFN ,f$name ,inputs ,f-body)

          (DISABLE ,f$name)

          (DEFN ,fn* () '(,name ,inputs ,hdl-outputs ,hdl-body nil))

          (MODULE-PREDICATE ,fn*)

          (MODULE-NETLIST ,fn*)

          (PROVE-LEMMA ,value-lemma (REWRITE)
            (IMPLIES
             (,fn& NETLIST)
             (EQUAL (DUAL-EVAL 0 ',name (LIST ,@inputs) STATE NETLIST)
                    ,(if (null (cdr hdl-outputs))
                         `(LIST (,f$name ,@inputs))
                       `(,f$name ,@inputs))))
            ;;Hint
            ((ENABLE ,fn& ,f$name
                     ,@(submodule-value-lemmas fn* :body (nqfix hdl-body)))
             (DISABLE-THEORY F-GATES)))

          (DISABLE ,value-lemma)

          (PROVE-LEMMA ,boolp-value-lemma (REWRITE)
            (IMPLIES
             ,(if (null (cdr boolp-inputs))
                  (car boolp-inputs)
                `(AND ,@boolp-inputs))
             (EQUAL (,f$name ,@inputs)
                    (,name ,@inputs)))
            ;;Hint
            ((ENABLE BOOLP-B-GATES ,f$name ,spec) 
             (DISABLE-THEORY F-GATES B-GATES)))

          )))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    DESTRUCTURING-LEMMA generator
;;;
;;;  Because of quirks in equality reasoning, it "doesn't work" to simply let
;;;  module definitions open up.  Instead, we use a lemma that explicitly
;;;  states how to destructure a module definition. 
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defmacro destructuring-lemma (generator)
  (let* ((event (get generator 'event))
         (args (third event))
         (defn (fourth event))
         (name (nqnth 0 defn))
         (inputs (nqnth 1 defn))
         (outputs (nqnth 2 defn))
         (body (nqnth 3 defn))
         (states (nqnth 4 defn))
         (form `(,generator ,@args))
         (destructuring-lemma (unstring generator "$DESTRUCTURE")))
    `(PROGN

      (PROVE-LEMMA ,destructuring-lemma (REWRITE)
        (AND
         (EQUAL (CAR ,form) ,name)
         (EQUAL (CADR ,form) ,inputs)
         (EQUAL (CADDR ,form) ,outputs)
         (EQUAL (CADDDR ,form) ,body)
         (EQUAL (CADDDDR ,form) ,states)))

      (DISABLE ,generator)

      (DISABLE ,destructuring-lemma))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    MODULE-GENERATOR generator args name inputs outputs body state
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defmacro module-generator ((generator . args) name inputs outputs body state)
  (let ((destructuring-lemma (unstring generator "$DESTRUCTURE"))
        (form `(,generator ,@args)))

    `(PROGN

      (DEFN ,generator ,args
        (LIST ,name ,inputs ,outputs ,body ,state))

      (PROVE-LEMMA ,destructuring-lemma (REWRITE)
        (AND
         (EQUAL (CAR ,form) ,name)
         (EQUAL (CADR ,form) ,inputs)
         (EQUAL (CADDR ,form) ,outputs)
         (EQUAL (CADDDR ,form) ,body)
         (EQUAL (CADDDDR ,form) ,state)))

      (DISABLE ,generator)
      
      (DISABLE ,destructuring-lemma))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    GENERATE-BODY-INDUCTION-SCHEME generator
;;;    
;;;   Creates a DUAL-EVAL 1 induction scheme for body generators of the form
;;;
;;;   (IF test something (CONS occurrence recursive-call))
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defmacro generate-body-induction-scheme (generator)
  (let* ((event (get generator 'event))
         (name (unstring generator "$INDUCTION"))
         (call `(,generator ,@(nth 2 event)))
         (args (append (nth 2 event) '(BINDINGS STATE-BINDINGS NETLIST)))
         (body (nth 3 event))
         (test (nth 1 body))
         (recursion (cdr (nqcdr (nth 3 body)))))
    
    `(DEFN ,name ,args
       (IF ,test
           t
         (,name ,@recursion
                (DUAL-EVAL-BODY-BINDINGS 1 ,call
                                         BINDINGS STATE-BINDINGS NETLIST)
                STATE-BINDINGS
                NETLIST)))))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    #V reader macro.
;;;    
;;;  A reader macro for bit-vectors. For example, #v001 = (LIST T F F).
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun bit-vector-reader (stream subchar arg)
  ;;  We "unread" the vector character, and reread to get a symbol.  Otherwise
  ;;  the number following the vector character might be read as a leading zero
  ;;  of an integer.
  (declare (ignore subchar arg))
  (unread-char #\v stream)
  (let ((symbol (read stream t nil t)))
    ;;  Get rid of the vector character, reverse, and list for NQTHM.
    `(LIST ,@(map 'list #'(lambda (x)
                            (if (equal x #\1)
                                't
                              (if (equal x #\0)
                                  'f
                                (error "Non-binary digits in --> ~s."
                                       symbol))))
                  (reverse (subseq (symbol-name symbol) 1))))))
                           
(eval-when (load eval)
  (set-dispatch-macro-character #\# #\v #'bit-vector-reader))

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    #I reader macro.
;;;
;;;  A reader macro for indices.
;;;  For example, #i(a 10) = (INDEX 'A 10), and #i(a 0 n) = (INDICES 'A 0 10).
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defun index-reader (stream subchar arg)
  (declare (ignore subchar arg))
  (let* ((args (read stream t nil t))
         (name (car args))
         (num  (cadr args))
         (n    (caddr args)))
    (if n
        `(INDICES ',name ,num ,n)
      `(INDEX ',name ,num))))
                           
(eval-when (load eval)
  (set-dispatch-macro-character #\# #\i #'index-reader))

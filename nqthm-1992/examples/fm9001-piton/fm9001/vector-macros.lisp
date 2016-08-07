;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    VECTOR-MACROS.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    VECTOR-MODULE name (occ-name outputs type inputs) specs &key enable
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    VECTOR-MODULE creates simple, linear, n-bit module generators.
;;;    
;;;   Arguments:
;;;
;;;     name -- The generator will be (<name>* n)
;;;  
;;;     (occ-name outputs type inputs) --  A schematic representation of the
;;;     occurrences.  The body of the generator will contain occurrences of the
;;;     form:
;;;           (<occ-name>_n
;;;            (<output_0>_n ... <output_k>_n)
;;;            type
;;;            (<input_0>_n ... <input_k>_n))
;;;  
;;;     specs -- A list of specifications for the output vectors, written in
;;;     terms of the inputs.
;;;  
;;;     enable -- A list of events to be enabled.
;;;  
;;;   Example: (vector-module v-buf (g (y) b-buf (a)) ((v-threefix a))
;;;                           :enable (f-buf)) 
;;;
;;;   More examples in "vector-module.events".

(defmacro vector-module (name (occ-name outputs type inputs) specs
                              &key enable)
  (let* ((body-defn (unstring name "$BODY"))
         (generator (unstring name "*"))
         (destructor (unstring generator "$DESTRUCTURE"))
        (module-name `(INDEX ',name N))
        (predicate (unstring name "&"))
        (type-predicate (unstring type "&"))
        (unbound-in-body-lemma (unstring name "$UNBOUND-IN-BODY"))
        (body-value-lemma (unstring name "$BODY-VALUE"))
        (type-value-lemma (unstring type "$VALUE"))
        (value-lemma (unstring name "$VALUE"))
        (netlist (unstring name "$NETLIST"))
        (type-netlist (unstring type "$NETLIST")))
                     
    
    (labels ((mapAPPEND
              (x)
              (if (consp x)
                  (if (consp (cdr x))
                      `(APPEND ,(car x) ,(mapAPPEND (cdr x)))
                    (car x))
                nil))
             (mapAND
              (x)
              (if (consp x)
                  (if (consp (cdr x))
                      `(AND ,(car x) ,(mapAND (cdr x)))
                    (car x))
                nil)))

      `(PROGN

        (DEFN ,body-defn (M N)
          (IF (ZEROP N)
              NIL
            (CONS
             (LIST (INDEX ',occ-name M)
                   (LIST ,@(mapcar #'(lambda (x) `(INDEX ',x M)) outputs))
                   ',type
                   (LIST ,@(mapcar #'(lambda (x) `(INDEX ',x M)) inputs)))
             (,body-defn (ADD1 M) (SUB1 N)))))

        (DISABLE ,body-defn)

        (MODULE-GENERATOR
         (,generator N)
         ,module-name
         ,(mapAPPEND
           (mapcar #'(lambda (x) `(INDICES ',x 0 N)) inputs))
         ,(mapAPPEND
           (mapcar #'(lambda (x) `(INDICES ',x 0 N)) outputs))
         (,body-defn 0 N)
         NIL)

        (DEFN ,predicate (NETLIST N)
          (AND (EQUAL (LOOKUP-MODULE ,module-name NETLIST)
                      (,generator N))
               (,type-predicate (DELETE-MODULE ,module-name NETLIST))))

        (DISABLE ,predicate)

        (DEFN ,netlist (N)
          (CONS (,generator N) (,type-netlist)))

        (PROVE-LEMMA ,unbound-in-body-lemma (REWRITE)
          (IMPLIES
           (LESSP L M)
           ,(mapAND (mapcar #'(lambda (x)
                                `(UNBOUND-IN-BODY (INDEX ',x L)
                                                  (,body-defn M N)))
                            outputs)))
          ;;Hint
          ((enable ,body-defn UNBOUND-IN-BODY)))

        (DISABLE ,unbound-in-body-lemma)

        (PROVE-LEMMA ,body-value-lemma (REWRITE)
          (IMPLIES
           (AND (,type-predicate NETLIST)
                (EQUAL BODY (,body-defn M N)))
           ,(mapAND
             (mapcar
              #'(lambda (x y)
                  `(EQUAL
                    (COLLECT-VALUE
                     (INDICES ',x M N)
                     (DUAL-EVAL 1 BODY
                                BINDINGS STATE-BINDINGS NETLIST))
                    ,(let* ((spec y)
                            (fn (car spec))
                            (args (cdr spec)))
                       `(,fn ,@(mapcar #'(lambda (x)
                                           `(COLLECT-VALUE
                                             (INDICES ',x M N)
                                             BINDINGS))
                                       args)))))
              outputs specs)))
          ;;Hint
          ((INDUCT
            (VECTOR-MODULE-INDUCTION BODY M N BINDINGS STATE-BINDINGS NETLIST))
           (DISABLE-THEORY F-GATES)
           (ENABLE ,body-defn ,type-value-lemma ,unbound-in-body-lemma
                   ,@(mapcar #'car specs)
                   ,@enable)))

        (DISABLE ,body-value-lemma)

        (PROVE-LEMMA ,value-lemma (REWRITE)
          (IMPLIES
           (AND (,predicate NETLIST N)
                ,(mapAND
                  (mapcar
                   #'(lambda (x)
                       `(AND (PROPERP ,x)
                             (EQUAL (LENGTH ,x) N)))
                   inputs)))
           (EQUAL
            (DUAL-EVAL 0 ,module-name ,(mapAPPEND inputs)
                       STATE NETLIST)
            ,(mapAPPEND
              (mapcar
               #'(lambda (spec)
                   (let* ((fn (car spec))
                          (args (cdr spec)))
                     `(,fn ,@args)))
               specs))))
          ;;Hint
          ((ENABLE ,predicate ,body-value-lemma ,destructor)))

        (DISABLE ,value-lemma)

        ))))

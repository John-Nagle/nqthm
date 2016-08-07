;;; -*- Mode:LISP; Package:(SLOOP LISP);Syntax:COMMON-LISP;Base:10 -*- ;;;;;
;;;                                                                    ;;;;;
;;;     Copyright (c) 1985,86 by William Schelter,                     ;;;;;
;;;     All rights reserved                                            ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; Report bugs to wfs@carl.ma.utexas.edu
;;; It comes with ABSOLUTELY NO WARRANTY but we hope it is useful.

 
;;; The following code is meant to run in COMMON LISP and to provide
;;; extensive iteration facilities, with very high backwards compatibility
;;; with the traditional loop macro. It is meant to be publicly available!
;;; Anyone is hereby given permission to copy it provided he does not make
;;; ANY changes to the file unless he is William Schelter.  He may change
;;; the behavior after loading it by resetting the global variables such
;;; as like *Use-locatives*, *automatic-declarations*,..  listed at the
;;; beginning of this file.
 
;;; The original of this file is on
;;; rascal.ics.utexas.edu:/usr2/ftp/pub/sloop.lisp.   I am happy to accept
;;; suggestions for different defaults for various implementations, or for
;;; improvements.


;;If you want to redefine the common lisp loop you may include in your code:
;;; (defmacro loop (&body body) (parse-loop body))

;;         Principal New Features

;;; Sloop is extremely user extensible so that you may easily redefine
;;; most behavior, or add additional collections, and paths.  There are a
;;; number of such examples defined in this file, including such
;;; constructs as

;;; .. FOR v IN-FRINGE x ..         (iterate through the fringe of a tree x)
;;; .. SUM v ..                     (add the v)
;;; .. AVERAGING v ..      
;;; .. FOR sym IN-PACKAGE y         (iterate through symbols in a package y)
;;; .. COLLATE v ..                 (for collecting X into an ordered list),
;;; .. FOR (elt i) IN-ARRAY ar      (iterate through array ar, with index i)
;;; .. FOR (key elt) IN-TABLE foo.. (if foo is a hash table)

;;; you can combine any collection method with any path.
;;; Also there is iteration over products so that you may write
;;; (SLOOP FOR i BELOW k
;;;       SLOOP (FOR j BELOW i
;;;          	    COLLECTING (foo i j)))

;;; Declare is fully supported.  The syntax would be
;;; (sloop for u in l with v = 0
;;;       declare (fixnum u v)
;;;       do ....

;;; This extensibility is gained by the ability to define a "loop-macro",
;;; which plays a role analagous to an ordiary lisp macro.  See eg.
;;; definitions near that of "averaging".  Essentially a "loop-macro"
;;; takes some arguments (supplied from the body of the loop following its
;;; occurrence, and returns a new form to be stuffed onto the front of the
;;; loop form, in place of it and its arguments).
 
;;; Compile notes: For dec-20 clisp load the lisp file before compiling.


;;; there seems to be no unanimity about what in-package etc. does on
;;; loading and compiling a file.  The following is as close to the
;;; examples in the Common Lisp manual, as we could make it.  The user
;;; should put (require "SLOOP") and then (use-package "SLOOP") early in
;;; his init file.  Note use of the string to avoid interning 'sloop in
;;; some other package.


(in-package "SLOOP")  
(eval-when (compile eval load)

(export '(loop-return sloop def-loop-collect def-loop-map
		      def-loop-for def-loop-macro local-finish
		      loop-finish) (find-package "SLOOP"))

)

;;; some variables that may be changed to suit different implementations:

(eval-when (compile load eval)

(defvar *use-locatives* nil "See sloop.lisp")   ;#+lispm t #-lispm nil 
;;; If t should have locf, such that if we do
;;;   (setf b nil) (setq a (locf b))
;;;    then the command
;;;   (setf (cdr a) (cons 3 nil)) means that b==>(3).
;;; This is useful for building lists starting with a variable pointing to
;;; nil, since otherwise we must check each time if the list has really
;;; been started, before we do a (setf (cdr b) ..)

(defvar *Automatic-declarations*  #+lispm nil  #-lispm
  '(:from fixnum) "See sloop.lisp")

;;; some other reasonable ones would be :count fixnum :max fixnum
;;; Automatic declarations for variables in the stepping and collecting,
;;; so for i below n, gives i and n a :from declaration (here fixnum)


;;valid keys in *automatic-declarations*
(defvar *auto-type* '(:from :in :collect))
;;give automatic register declaration to these variables 
(defvar *auto-register* '(:from :in :collect))
(eval-when (compile eval load)
(proclaim '(declaration :register))
)


(defvar *type-check* t "If t adds a type check on bounds of from loop
if there is and automatic declare")

(defvar *macroexpand-hook-for-no-copy* #-(or lmi ti) 'funcall #+(or lmi ti) t)
;;; some lisps remember a macro so that (loop-return) will expand eq forms
;;; always in the same manner, even if the form is in a macrolet! To
;;; defeat this feature we copy all macro expansions unless
;;; *macro-expand-hook* = *macroexpand-hook-for-no-copy*
)


;;; *****ONLY CONDITIONALIZATIONS BELOW HERE SHOULD BE FOR BUG FIXES******
;;; eg. some kcls don't return nil from a prog by default!

;;; all macros here in here.
(eval-when (compile eval load)

(defparameter *sloop-translations* '((appending . append)
			 ((collecting collect) . collect)
			 ((maximizing maximize) . maximize)
			 ((minimizing minimize) . minimize)
			 (nconcing . nconc)
			 ((count counting) . count)
			 (summing . sum)
			 (if . when)
			 (as . for)
			 (in-fringe . in-fringe)
			 (collate . collate)
			 (in-table . in-table)
			 (in-carefully . in-carefully)
			 (averaging . averaging)
			 (repeat . repeat)
			 (first-use . first-use)
			 (in-array . in-array))
  "A list of cons's where the translation is the cdr, and the car
is a list of names or name to be translated.  Essentially allows 'globalizing'
a symbol for the purposes of being a keyword in a sloop")


(defparameter *additional-collections* nil)

(defmacro lcase (item &body body)
  (let (bod last-case tem)
    (do ((rest body (cdr rest)) (v))
	((or last-case (null rest)))
      (setq  v (car rest))
      (push
	(cond ((eql (car v) t) (setq last-case t) v)
	      ((eql (car v) :collect)
	       `((loop-collect-keyword-p .item.) ,@ (cdr v)))
	      ((eql (car v) :no-body)
	       `((parse-no-body  .item.) ,@ (cdr v)))
	      ((setq tem
		     (member (car v) '(:sloop-macro :sloop-for :sloop-map)))
	       `((and (symbolp .item.)(get .item. ,(car tem))) ,@ (cdr v)))
	      (t
	       `((l-equal .item. ',(car v)) ,@ (cdr v))))
	bod))
    (or last-case (push `(t (error "lcase fell off end ~a  " .item.)) bod))
    `(let ((.item. (translate-name ,item)))
       (cond ,@ (nreverse bod)))))

(defun desetq1 (form val)
  (cond ((symbolp form)
	 (and form `(setf ,form ,val)))
	((consp form)
	 `(progn ,(desetq1 (car form) `(car ,val))
		 ,@ (if (consp (cdr form))
			(list(desetq1 (cdr form) `(cdr ,val)))
		      (and (cdr form) `((setf ,(cdr form) (cdr ,val)))))))
	(t (error ""))))

(defmacro desetq (form val)
  (cond ((atom val) (desetq1 form val))
	(t (let ((value (gensym)))
	     `(let ((,value ,val)) , (desetq1 form value))))))

(defmacro loop-return (&rest vals)
  (cond ((<=  (length vals) 1)
	 `(return ,@ vals))
	(t`(return (values  ,@ vals)))))

(defmacro loop-finish ()
  `(go finish-loop))

(defmacro local-finish ()
  `(go finish-loop))

(defmacro sloop (&body body)
  (parse-loop body))
  
(defmacro def-loop-map (name args &body body)
  (def-loop-internal name args body 'map))
(defmacro def-loop-for (name args &body body )
  (def-loop-internal name args body 'for nil 1))
(defmacro def-loop-macro (name args &body body)
  (def-loop-internal name args body 'macro))
(defmacro def-loop-collect (name arglist &body body )
       "Define function of 2 args arglist= (collect-var value-to-collect)"
  (def-loop-internal name arglist body 'collect '*additional-collections* 2 2))

(defmacro sloop-swap ()
 `(progn (rotatef a *loop-bindings*)
  (rotatef b  *loop-prologue*)
  (rotatef c *loop-epilogue*)
  (rotatef e *loop-end-test*)
  (rotatef f *loop-increment*)
  (setf *inner-sloop* (not *inner-sloop*))
  ))

) ;;end of macros

(defun l-equal (a b)
  (and (symbolp a)
       (cond ((symbolp b)
	      (equal (symbol-name a) (symbol-name b)))
	     ((listp b)
	      (member  a b :test 'l-equal)))))

(defun loop-collect-keyword-p (command)
  (or (member command '(collect append nconc sum count) :test 'l-equal)
      (find command *additional-collections* :test 'l-equal)))
 			 
(defun translate-name (name)
  (cond ((and (symbolp name)
	      (cdar (member name *sloop-translations*
			    :test 'l-equal :key 'car))))
	(t name)))

(defun loop-pop ()
  (declare (special *last-val* *loop-form*))
  (cond (*loop-form*
          (setq *last-val* (pop *loop-form*)))
	(t (setq *last-val* 'empty-form) nil)))

(defun loop-un-pop ()  (declare (special *last-val* *loop-form*))
  (case *last-val*
	(empty-form nil)
	(already-un-popped (error "you are un-popping without popping"))
	(t  (push *last-val* *loop-form*)
	    (setf *last-val* 'alread-un-popped))))

(defun loop-peek () (declare (special *last-val* *loop-form*))
   (car *loop-form*))

(defun loop-let-bindings(binds)
  (do ((v (car binds) (cdr v)))
      ((null v) (nreverse (car binds)))
      (or (cdar v) (setf (car v) (caar v)))))

(defun parse-loop (form &aux inner-body)
  (let ((*loop-form* form)
	(*Automatic-declarations* *Automatic-declarations*)
	*last-val* *loop-map* 
	*loop-body* 
	*loop-name*
	*loop-prologue* *inner-sloop*
	*loop-epilogue* *loop-increment*
	*loop-collect-pointers*  *loop-map-declares*
	*loop-collect-var* 	*no-declare*
	*loop-end-test*
	*loop-bindings*
	*product-for*
	*type-test-limit*
	local-macros
	(finish-loop 'finish-loop)
	)
    (declare (special *loop-form* *last-val* *loop-map* 
		      *loop-collect-pointers*
		      *loop-name* *inner-sloop*
		      *loop-body*
		      *loop-prologue* 
		      *no-declare*
		      *loop-bindings*
		      *loop-collect-var*  *loop-map-declares*
		      *loop-epilogue* *loop-increment*
		      *loop-end-test* *product-for*
		      *type-test-limit*
		      ))
    (unless (and (symbolp (car *loop-form*))  (car *loop-form*))
	    (push 'do  *loop-form*))	;compatible with common lisp loop..
    (parse-loop1)
    (when (or *loop-map* *product-for*)
	  (or *loop-name* (setf *loop-name* (gensym "SLOOP")))
	  (and (eql 'finish-loop finish-loop)
	       (setf finish-loop (gensym "FINISH"))))
;;; some one might use local-finish,local-return or loop-finish, so they might
;;; be bound at an outer level.  WE have to always include this since
;;; loop-return may be being bound outside.
    (and				; *loop-name*
      (push 
	`(loop-return (&rest vals)
		      `(return-from ,',*loop-name* (values ,@ vals)))
	local-macros))
    (when  t;; (or (> *loop-level* 1) (not (eql finish-loop 'finish-loop)))
	   (push 	 `(loop-finish () `(go ,',finish-loop)) local-macros)
	   (push 	 `(local-finish () `(go ,',finish-loop)) local-macros))
    (and *loop-collect-var*
	 (push   `(return-from ,*loop-name* , *loop-collect-var*)
		 *loop-epilogue*))
    (setq inner-body (append  *loop-end-test*
			      (nreverse *loop-body*)
			      (nreverse	*loop-increment*)))
    (cond (*loop-map*
	    (setq inner-body (substitute-sloop-body inner-body)))
	  (t (setf inner-body (cons 'next-loop
				    (append inner-body '((go next-loop)))))))
    (let ((bod 
	    `(macrolet ,local-macros
		       (block ,*loop-name*
			      (tagbody
				,@ (append
				     (nreverse *loop-prologue*)
				     inner-body
				     `(,finish-loop)
				     (nreverse *loop-epilogue*)
				     #+kcl '((loop-return  nil))))))
	    
	    ))
;;; temp-fix..should not be necessary but some lisps cache macro
;;; expansions.  and ignore the macrolet!!
      (unless  (eql *macroexpand-hook* *macroexpand-hook-for-no-copy*)
	       (setf bod (copy-tree bod)))
      (dolist (v *loop-bindings*)
	      (setf bod
		    `(let ,(loop-let-bindings v)
		       ,@(and (cdr v) `(,(cons 'declare (cdr v))))
		       ,bod)))
      bod
      ))) 

(defun parse-loop1 ()
  (declare (special *loop-form*
		    *loop-body* *loop-increment*
		    *no-declare* *loop-end-test*
		    *loop-name* ))
  (lcase (loop-peek)
	 (named (loop-pop) (setq *loop-name* (loop-pop)))
	 (t nil))
  (do ((v (loop-pop) (loop-pop)))
      ((and (null v) (null *loop-form*)))
      (lcase v
	     (:no-body)
	     (for (parse-loop-for))
	     (while (push
		      `(or ,(loop-pop) (local-finish))  *loop-body*))
	     (until (push
		      `(and ,(loop-pop) (local-finish))  *loop-body*))
	     (do (setq *loop-body* (append (parse-loop-do) *loop-body*)))
	     ((when unless) (setq *loop-body*
				  (append (parse-loop-when) *loop-body*)))
	     (:collect  (setq *loop-body*
			      (append (parse-loop-collect) *loop-body*)))
	     )))


(defun parse-no-body (com &aux (found t) (first t))
  "Reads successive no-body-contribution type forms, like declare,
initially, etc.  which can occur anywhere. Returns t if it finds some
otherwise nil"
  (declare (special *loop-form*
		    *loop-body*
		    *loop-increment*
		    *no-declare* *loop-end-test*
		    *loop-name* ))
  (do ((v com (loop-pop)))
      ((null (or first *loop-form*)))
      (lcase v
	     ((initially finally)(parse-loop-initially v))
	     (nil nil)
	     (with      (parse-loop-with))
	     (declare   (parse-loop-declare (loop-pop) t))
	     (nodeclare  (setq *no-declare* (loop-pop)))
	     ;take argument to be consistent.
	     (increment (setq *loop-increment*
			      (append (parse-loop-do) *loop-increment*)))
	     (end-test  (setq *loop-end-test*
			      (append (parse-loop-do) *loop-end-test*)))
	     (with-unique (parse-loop-with nil t))
	     (:sloop-macro (parse-loop-macro v :sloop-macro))
	     (t
	       (cond (first
		       (setf found nil))
		     (t (loop-un-pop)))
	       (return 'done)))
      (setf first nil))
  found)

(defun parse-loop-with (&optional and-with only-if-not-there)
  (let ((var  (loop-pop)))
    (lcase (loop-peek)
      (= (loop-pop)
	 (or (symbolp var) (error "Not a variable ~a" var))
	 (loop-add-binding var (loop-pop)
			   (not and-with) nil nil t only-if-not-there))
      (t (loop-add-temps var nil nil (not and-with) only-if-not-there)))
    (lcase (loop-peek)
      (and (loop-pop)
	   (lcase (loop-pop)
	     (with (parse-loop-with t ))
	     (with-unique (parse-loop-with t t))
	     (t (loop-un-pop) (parse-loop-with t))
	     ))
      (t nil))))

(defun parse-loop-do (&aux result)
  (declare (special *loop-form*))
  (do ((v (loop-pop) (loop-pop)) )
      (())
    (cond
      ((listp v)
       (push v result)
       (or *loop-form* (return 'done)))
      (t (loop-un-pop) (return 'done))))
  (or result (error "empty clause"))
  result)
  
(defun parse-loop-initially (command )
  (declare (special *loop-prologue* *loop-epilogue* *loop-bindings*))
  (lcase
    command
    (initially
      (let ((form (parse-loop-do)))
	(dolist (v (nreverse form))
		(cond ((and (listp v)
			    (member (car v) '(setf setq))
			    (eql (length v) 3)
			    (symbolp   (second v))
			    (constantp (third v))
			    (assoc (second v) (caar *loop-bindings*))
			    (loop-add-binding (second v) (third v)
					      nil nil nil t t)
			    ))
		      (t (setf *loop-prologue*
			       (cons v *loop-prologue*)))))))
    (finally
      (setf *loop-epilogue* (append (parse-loop-do) *loop-epilogue*)))))

(defun parse-one-when-clause ( &aux this-case  (want 'body) v)
  (declare (special *loop-form*))
  (prog
    nil
    next-loop
    (and (null *loop-form*) (return 'done))
    (setq v (loop-pop))
    (lcase v
	   (:no-body)
	   (:collect (or (eql 'body want) (go finish))
		     (setq this-case (append  (parse-loop-collect) this-case))
		     (setq want 'and))
	   (when  (or (eql 'body want) (go finish))
		  (setq this-case (append   (parse-loop-when) this-case))
		  (setq want 'and))
	   (do    (or (eql 'body want) (go finish))
		  (setq this-case (append   (parse-loop-do) this-case))
		  (setq want 'and))
	   (and    (or (eql 'and  want) (error "Premature AND"))
		   (setq want 'body))
	   (t  (loop-un-pop)(return 'done)))
    (go next-loop)
    finish
    (loop-un-pop))
  (or this-case (error "Hanging conditional"))
  this-case)


(defun parse-loop-when (&aux initial else else-clause)
  (declare (special *last-val* ))
  (let ((test (cond ((l-equal *last-val* 'unless) `(not , (loop-pop)))
		    (t (loop-pop)))))
    (setq initial (parse-one-when-clause))
    (lcase (loop-peek)
	   (else
	     (loop-pop)
	     (setq else t)
	     (setq else-clause (parse-one-when-clause)))
	   (t nil))
    `((cond (,test ,@ (nreverse initial))
	    ,@ (and else `((t ,@ (nreverse else-clause))))))))

(defun pointer-for-collect (collect-var)
  (declare (special *loop-collect-pointers*))
  (or (cdr (assoc collect-var *loop-collect-pointers*))
      (let ((sym(loop-add-binding (gensym "POIN") nil nil :collect )))
	(push (cons collect-var sym)
	      *loop-collect-pointers*)
	sym)))

(defun parse-loop-collect ( &aux collect-var pointer name-val)
  (declare (special *last-val* *loop-body* *loop-collect-var*
		    *loop-collect-pointers* *inner-sloop*
		    *loop-prologue* ))
  (and *inner-sloop* (throw 'collect nil))
  (let ((command   *last-val*)
	(val (loop-pop)))
    (lcase
      (loop-pop)
      (into (loop-add-binding (setq collect-var (loop-pop)) nil nil t nil t ))
      (t (loop-un-pop)
	 (cond (*loop-collect-var* (setf collect-var *loop-collect-var*))
	       (t  (setf collect-var
			 (setf *loop-collect-var*
			       (loop-add-binding (gensym "COLL") nil )))))))
    (lcase command
	   ((append nconc collect)
	    (setf pointer (pointer-for-collect collect-var))
	    (cond (*use-locatives*
		    (pushnew `(setf ,pointer
				    (locf ,collect-var))
			     *loop-prologue* :test 'equal)))
	    (lcase command
		   ( append
		      (unless (and (listp val) (eql (car val) 'list))
			      (setf val `(copy-list ,val))))
		   (t nil)))
	   (t nil))
    (cond ((and  (listp val) (not *use-locatives*))
	   (setq name-val (loop-add-binding (gensym "VAL") nil nil)))
	  (t (setf name-val val)))
    (let
	((result
	   (lcase
	     command
	     ((nconc append)
	      (let ((set-pointer
		      `(and (setf (cdr ,pointer) ,name-val)
			    (setf ,pointer (last (cdr ,pointer))))))
		(cond (*use-locatives*
			(list set-pointer))
		      (t
			`((cond (,pointer ,set-pointer)
				(t (setf ,pointer
					 (last (setf
						 ,collect-var
						 ,name-val))))))))))
	     (collect
	       (cond (*use-locatives*
		       `((setf (cdr ,pointer)
			       (setf ,pointer (cons ,name-val nil)))))
		     (t `((cond (,pointer
				   (setf (cdr ,pointer)
					 (setf ,pointer (cons ,name-val nil))))
				(t (setf ,collect-var
					 (setf ,pointer
					       (cons ,name-val nil)))))))))
	     (t (setq command (translate-name command))
		(cond ((find command *additional-collections* :test 'l-equal)
		       (loop-parse-additional-collections
			 command collect-var name-val))
		      (t (error "loop fell off end ~a" command)))))))
      (cond ((eql name-val val)
	     result)
	    (t (nconc result `((setf ,name-val ,val) )))))))

(defun loop-parse-additional-collections
  (command collect-var name-val &aux eachtime)
  (declare (special *loop-prologue* *last-val*
		    *loop-collect-var* *loop-epilogue* ))
  (let* ((com  (find command *additional-collections* :test 'l-equal))
	 (helper (get com :sloop-collect)))
    (let ((form (funcall helper collect-var name-val)))
      (let ((*loop-form* form) *last-val*)
	(declare (special  *loop-form* *last-val*))
	(do ((v (loop-pop) (loop-pop)))
	    ((null *loop-form*))
	    (lcase v
		   (:no-body)
		   (do (setq eachtime (parse-loop-do)))))
	eachtime))))

(defun the-type (symbol type)
  (declare (special *no-declare*))
  (and *no-declare* (setf type nil))
  (and type (setf type (or (getf *Automatic-declarations* type)
			   (and  (not (keywordp type)) type))))
  (and (consp type) (eq (car type) 'type) (setf type (second  type)))
  (cond (type (list 'the type symbol ))
	(t symbol)))

(defun type-error ()
  (error "While checking a bound of a sloop, I found the wrong type 
for something in sloop::*automatic-declarations*.
    Perhaps your limit is wrong? 
If not either use nodeclare t or set sloop::*automatic-declarations* to nil. 
recompile."))


;;; this puts down code to check that automatic declarations induced by
;;; :from are indeed valid!  It checks both ends of the interval, and so
;;; need not check the numbers in between.

(defun make-value (value type-key &aux type )
  (declare (special *no-declare* *type-test-limit*))
  (cond ((and
	  (not *no-declare*)
	  *type-check*
	  (eq type-key :from)
	  (setq type (getf  *Automatic-declarations* type-key)))
	  (setq type
	       (cond ((and (consp type)
			   (eq (car type) 'type))
		      (second type))
		     (t type)))
	 (cond ((constantp value)
		(let ((test-value
		       (cond (*type-test-limit*
			      (eval (subst value
					   'the-value *type-test-limit*)))
			     (t (eval value)))))
		(or (typep test-value type)
		    (error
		     "~&Sloop found the type of ~a was not type ~a,~%~
                      Maybe you want to insert SLOOP NODECLARE T ..."
		     value
		     type))
		(list value)))
	       (t  (let (chk)
		     `((let ,(cond ((atom value)
				    nil)
				   (t `((,(setq chk(gensym)) ,value))))
			 (or
			  (typep
			   ,(if *type-test-limit*
				(subst (or chk value)
				       'the-value *type-test-limit*)
			      (or chk value))
			   ',type)
			  (type-error))
			 ,(or chk value)))))))
	(t (list value))))


;;; keep track of the bindings in a list *loop-bindings* each element of
;;; the list will give rise to a different let.  the car will be the
;;; variable bindings, the cdr the declarations.


(defun loop-add-binding
       (variable value &optional (new-level t) type force-type (force-new-value t)
			 only-if-not-there &aux tem)
;;; Add a variable binding to the current or new level.  If FORCE-TYPE,
;;; ignore a *no-declare*.  If ONLY-IF-NOT-THERE, check all levels.
  (declare (special *loop-bindings*))
  (when  (or new-level (null *loop-bindings*))
	 (push (cons nil nil) *loop-bindings*))
  (cond ((setq tem (assoc variable (caar  *loop-bindings*) ))
	 (and force-new-value
	      (setf (cdr tem) (and value (make-value value type)))))
	((and (or only-if-not-there (and (null (symbol-package variable))
					 (constantp value)))
	      (dolist (v (cdr *loop-bindings*))
		(cond ((setq tem (assoc variable (car v)))
		       (and force-new-value
			    (setf (cdr tem)
				  (and value (make-value value type))))
		       (return t))))))
	(t (push (cons variable  (and value (make-value value type)))
		 (caar *loop-bindings*))))
  (and type (loop-declare-binding variable type force-type))
  variable)

;(defmacro nth-level (n) `(nth ,n *loop-bindings*))
;if x = (nth i *loop-bindings*)
;(defmacro binding-declares (x) `(cdr ,x)) ;(cons 'declare (binding-declares x)) to get honest declare statement
;(defmacro binding-values (x) `(car ,x))  ;(let (binding-values x) ) to get let.

(defun loop-declare-binding (var type force-type &optional odd-type
				 &aux found )
  (declare (special *loop-bindings* *automatic-declarations*
		    *no-declare* *loop-map*))
  odd-type ;;ignored
  (and type
       (member type *auto-type*)
       (setf type (getf  *automatic-declarations* type))
       *auto-register*
       (loop-declare-binding var :register force-type))
  (when (and type(or force-type (null *no-declare*)))
    (dolist (v *loop-bindings*)
      (cond ((assoc var (car v)) (setf found t)
	     (pushnew
	       (if (and (consp type)
			(eq (car type) 'type))
		   (list 'type (second type) var)
		   (if odd-type (list 'type type var)
		       
		   (list type var)))
	       (cdr v) :test 'equal)
	     (return 'done)
	     )))
    (or found *loop-map* (error "Could not find variable ~a in bindings" var)))
  var)

(defun parse-loop-declare (&optional (decl-list (loop-pop)) (force t))
  (let ((type (car decl-list)) odd-type)
    (cond ((eq type 'type)
	   (setf decl-list (cdr decl-list) type (car decl-list) odd-type t)))
    (dolist (v (cdr decl-list))
      (loop-declare-binding v (car decl-list) force odd-type))))
	
(defun loop-add-temps (form &optional val type new-level only-if-not-there)
  (cond ((null form))
	((symbolp form)
	 (loop-add-binding form val new-level type nil  t only-if-not-there))
	((listp form)
	 (loop-add-temps (car form))
	 (loop-add-temps (cdr form)))))


(defun add-from-data (data &rest args)
   "rest = var begin end  incr direction or-eql"
   (or data (setq data (copy-list '(nil 0 nil 1 + nil))))
   (do ((l data (cdr l))
        (v args (cdr v)))
      ((null v) l)
     (and (car v) (setf (car l) (car v))))
   data)

(defun parse-loop-for ( &aux  inc  from-data)
  (declare (special *loop-form*  *loop-map-declares*  *loop-map* 
		    *loop-body* *loop-increment* *no-declare*
		    *loop-prologue*
		    *loop-epilogue*
		    *loop-end-test*
		    *loop-bindings*
		    ))
  (let* ((var (loop-pop)) test incr)
    (do ((v (loop-pop) (loop-pop)))
	(())
	(lcase v
	       (in (let ((lis (gensym "LIS")))
		     (loop-add-temps var nil :in t)
		     (loop-add-binding lis (loop-pop) nil)
		     (push  `(desetq ,var (car ,lis)) *loop-body*)
		     (setf incr `(setf ,lis (cdr ,lis)))
		     (setq test   `(null ,lis) )
		     ))
	       (on (let ((lis
			   (cond ((symbolp var) var)
				 (t (gensym "LIS")))))
		     (loop-add-temps var nil :in t)
		     (loop-add-binding lis (loop-pop) nil)
		     (setf incr `(setf ,lis (cdr ,lis)))
		     (unless (eql lis var)
			     (push `(desetq ,var ,lis) *loop-body*))
		     (setf test `(null ,lis))))
        
	       ((upfrom from)
		(setq from-data (add-from-data from-data
					       var (loop-pop) nil  nil '+)))
	       (downfrom
		 (setq from-data  (add-from-data
				    from-data var (loop-pop) nil  nil '-)))
	       (by
		 (setq inc (loop-pop))
		 (cond (from-data
			 (setq from-data (add-from-data
					   from-data nil nil nil inc)))
		       (t (assert (eq (car (third incr)) 'cdr))
			  (setq incr
				`(setf ,(second incr)
				       ,(if (and (consp inc)
						(member (car inc) '(quote function)))
					  `(,(second inc) ,(second incr))
					  `(funcall
					    ,inc ,(second incr))))))))
	       (below
		 (setq from-data (add-from-data from-data
						var nil (loop-pop) nil '+)))
	       (above
		 (setq from-data (add-from-data from-data
						var nil (loop-pop) nil '-)))
	       (to
		 (setq from-data (add-from-data from-data
						var nil (loop-pop) nil nil t)))
	       (:sloop-for (parse-loop-macro (translate-name v)
					     :sloop-for var )
			   (return 'done))
	       (:sloop-map (parse-loop-map (translate-name v) var )
			   (return nil))
	       (t(or			
		   (loop-un-pop))
		 (return 'done))))
    
    ;;whew finished parsing a for clause..
    
    (cond (from-data
	    (let
		((op (nth 4 from-data))
		 (or-eql (nth 5 from-data))
		 (var (car from-data))
		 (end (third from-data))
		 (inc (fourth from-data))
		 type)
	      (loop-add-binding var (second from-data) t :from)
	      (or (constantp inc) (setq *no-declare* t))
	      (setf incr `(setf ,var ,(the-type `(,op  ,var ,inc) :from)))
	      (cond (end
		      (let ((lim (gensym "LIM"))
			    (*type-test-limit*
			      (cond ((and (eql inc 1)
					  (null (nth 5 from-data)))
				     nil)
				    (t `(,op
					   the-value , inc)))))
			(declare (special *type-test-limit*))
			(loop-add-binding lim end nil :from nil nil)
			(setq test `(,(cond (or-eql
					      (if (eq op '+) '> '<))
					    (t (if (eq op '+) '>= '<=)))
				     ,var ,lim))))
		    ((and (not *no-declare*)
			  *type-check*
			  (setq type (getf *automatic-declarations* :from))
			  (progn (if (and (consp type)(eq (car type) 'type))
				     (setf type      (second type)))
				 (subtypep type 'fixnum)))
		     (or (constantp inc) (error "increment must be constant."))
		     (push
		       `(or
			  ,(cond ((eq op '+)
				  `(< ,var ,(- most-positive-fixnum
					       (or inc 1))))
				 (t `(> ,var  ,(+ most-negative-fixnum
						  (or inc 1)))))
			  (type-error))
		       *loop-increment*)
		     )))))
    
    (and test (push (copy-tree `(and ,test (local-finish))) *loop-end-test*))
    (and incr (push incr *loop-increment*))
    ))


(defun parse-loop-macro (v type &optional initial &aux result)
  (declare (special *loop-form*))
  (let ((helper (get v type)) args)
    (setq args
	  (ecase type
	    (:sloop-for
	     (let ((tem (get v :sloop-for-args)))
	       (or (cdr tem) (error "sloop-for macro needs at least one arg"))
	       (cdr tem)))
	    (:sloop-macro(get v :sloop-macro-args))))
    (let ((last-helper-apply-arg
	    (cond ((member '&rest args)
		   (prog1 *loop-form* (setf *loop-form* nil)))
		  (t (dotimes (i (length args) (nreverse result))
			     (push (car *loop-form*) result)
			     (setf *loop-form* (cdr *loop-form*)))))))
      (setq *loop-form*
	    (append 
	      (case type
		    (:sloop-for (apply helper initial last-helper-apply-arg))
		    (:sloop-macro(apply helper  last-helper-apply-arg)))
	      *loop-form*)))))

(defun parse-loop-map (v var)
  (declare (special *loop-map* *loop-map-declares* *loop-form*))
  (and *loop-map* (error "Sorry only one allowed loop-map per sloop"))
  (let ((helper (get v :sloop-map))
	(args  (get v :sloop-map-args)))
    (or args (error "map needs one arg before the key word"))
    (cond ((member '&rest args)
	   (error "Build this in two steps if you want &rest")))
    (let* (result
	    (last-helper-apply-arg
	      (dotimes (i (1- (length args)) (nreverse result))
		       (push (car *loop-form*) result)
		       (setf *loop-form* (cdr *loop-form*)))))
      (setq *loop-map-declares*
	    (do ((v (loop-pop)(loop-pop)) (result))
		((null (l-equal v 'declare))
		 (loop-un-pop)
		 (and result (cons 'declare result)))
		(push (loop-pop) result)))
      (setq *loop-map* (apply helper var last-helper-apply-arg))
      nil)))

(defun substitute-sloop-body (inner-body)
  (declare (special *loop-map* *loop-map-declares*))
    (cond (*loop-map*
	   (setf inner-body (list  (subst (cons 'progn inner-body)
					  :sloop-body *loop-map*)))
	   (and *loop-map-declares*
		(setf inner-body(subst *loop-map-declares*
				       :sloop-map-declares inner-body)))))
  inner-body)

;;; **User Extensible Iteration Facility**

(eval-when (compile eval load)
(defun def-loop-internal (name args  body type
			       &optional list min-args max-args
			       &aux (*print-case* :upcase)
			       (helper (intern
				  (format nil "~a-SLOOP-~a" name type))))
  (and min-args (or (>= (length args) min-args)(error "need more args")))
  (and max-args (or (<= (length args) max-args)(error "need less args")))
  `(eval-when (load compile eval)
	      (defun ,helper ,args
		,@ body)
	      ,@ (and list `((pushnew ',name ,list)))
	      (setf (get ',name ,(intern (format nil "SLOOP-~a" type)
					 (find-package 'keyword))) ',helper)
	      (setf (get ',name ,(intern (format nil "SLOOP-~a-ARGS" type)
					 (find-package 'keyword))) ',args)))
)
		

;;; DEF-LOOP-COLLECT lets you get a handle on the collection var.  exactly
;;; two args.  First arg=collection-variable. Second arg=value this time
;;; thru the loop.

(def-loop-collect sum (ans val)
  `(initially (setq ,ans 0)
    do (setq ,ans (+ ,ans ,val))))
(def-loop-collect logxor (ans val)
  `(initially (setf ,ans 0)
  do (setf ,ans (logxor ,ans ,val))
  declare (fixnum ,ans ,val)))
(def-loop-collect maximize (ans val)
  `(initially (setq ,ans nil) 
  do (if ,ans (setf ,ans (max ,ans ,val)) (setf ,ans ,val))))

(def-loop-collect minimize (ans val) 
  `(initially (setq ,ans nil)
  do (if ,ans (setf ,ans (min ,ans ,val)) (setf ,ans ,val))))

(def-loop-collect count (ans val)
  `(initially (setq ,ans 0)
  do (and ,val (setf ,ans (1+ ,ans)))))

(def-loop-collect thereis (ans val)(declare(ignore ans))
  `(do (if ,val (loop-return ,val))))
(def-loop-collect always (ans val)
  `(initially (setq ,ans t) do (and (null ,val)(loop-return nil))))
(def-loop-collect never (ans val)
  `(initially (setq ,ans t) do (and  ,val  (loop-return nil))))
 

;;; DEF-LOOP-MACRO
;;; If we have done
;;;  (def-loop-macro averaging (x)
;;;    `(sum ,x into .tot. and count t into .how-many.
;;;	   finally (loop-return (/ .tot. (float .how-many.)))))

;;; (def-loop-collect average (ans val)
;;;   `(initially (setf ,ans 0.0)
;;;     with-unique .how-many. = 0
;;;     do (setf ,ans (/  (+ (* .how-many. ,ans) ,val) (incf .how-many.)))
;;;     ))

;;; Finally we show how to provide averaging with
;;; current value the acutal average.

(def-loop-macro averaging (x)
  `(with-unique .average. = 0.0
    and with-unique .n-to-average. = 0
    declare (float .average. ) declare (fixnum .n-to-average.)
    do (setf .average. (/
			 (+ (* .n-to-average. .average.) ,x)
			 (incf .n-to-average.)))
    finally (loop-return .average.)))

(def-loop-macro repeat (x)
  (let ((ind (gensym)))
    `(for ,ind below ,x)))

(def-loop-macro return (x)
  `(do (loop-return ,@ (if (and (consp x) (eq (car x) 'values))
			   (cdr x)
			 (list x)))))

;;; then we can write:
;;; (sloop for x in l when (oddp x) averaging x)


;;; DEF-LOOP-FOR def-loop-for and def-loop-macro are almost identical
;;; except that the def-loop-for construct can only occur after a for:

;;; (def-loop-for in-array (vars array)
;;;   (let ((elt (car vars))
;;;	 (ind (second vars)))
;;;   `(for ,ind below (length ,array) do (setf ,elt (aref ,array ,ind)))))

;;; (sloop for (elt ind) in-array ar when (oddp elt) collecting ind)

;;; You are just building something understandable by loop but minus the
;;; for.  Since this is almost like a "macro", and users may want to
;;; customize their own, the comparsion of tokens uses eq, ie. you must
;;; import IN-ARRAY to your package if you define it in another one.
;;; Actually we make a fancier in-array below which understands from, to,
;;; below, downfrom,.. and can have either (elt ind) or elt as the
;;; argument vars.

;;; DEF-LOOP-MAP A rather general iteration construct which allows you to
;;; map over things It can only occur after FOR.  There can only be one
;;; loop-map for a given loop, so you want to only use them for
;;; complicated iterations.

(def-loop-map in-table (var table)
  `(maphash #'(lambda ,var :sloop-map-declares :sloop-body) ,table))

;;; Usage  (sloop for (key elt) in-table table
;;;               declare (fixnum elt)
;;;               when (oddp elt) collecting (cons key elt))


(def-loop-map in-package (var pkg)
  `(do-symbols (,var (find-package ,pkg))  :sloop-body))

;;; Usage:
;;; (defun te()
;;;  (sloop for sym in-package 'sloop when (fboundp sym) count t)) 

;;; IN-ARRAY that understands from,downfrowm,to, below, above,etc.  I used
;;; a do for the macro iteration to be able include it here.

(def-loop-for in-array (vars array &rest args)
  (let (elt ind to)
    (cond ((listp vars) (setf elt (car vars) ind (second vars)))
	  (t (setf elt vars ind (gensym "INDEX" ))))
    (let ((skip (do ((v args (cddr v)) (result))
		    (())
		   (lcase (car v)
		       ((from downfrom) )
		       ((to below above) (setf to t))
		       (by)
		       (t (setq args (copy-list v))
			  (return (nreverse result))))
		   (push (car v) result) (push (second v) result))))
      (or to (setf skip (nconc `(below (length ,array)) skip)))
      `(for ,ind 
	,@ skip
	with ,elt 
	do (setf ,elt (aref ,array ,ind)) ,@ args))))

;;; usage: IN-ARRAY
;;; (sloop for (elt i) in-array ar from 4
;;;       when (oddp i)
;;;       collecting elt)

;;; (sloop for elt in-array ar below 10 by 2
;;;        do (print elt))

(def-loop-for = (var val)
  (lcase (loop-peek)
    (then (loop-pop) `(with ,var initially (desetq ,var ,val) increment (desetq ,var ,(loop-pop))))
    (t  `(with ,var do (desetq ,var ,val)))))

(def-loop-macro sloop (for-loop)
  (lcase (car for-loop)
    (for))
  (let (*inner-sloop* *loop-body* *loop-map* inner-body
	(finish-loop (gensym "FINISH"))
	a b c e f (*loop-form* for-loop))
    (declare (special *inner-sloop* *loop-end-test* *loop-increment*
		      *product-for* *loop-map*
		      *loop-form*  *loop-body*  *loop-prologue*
		      *loop-epilogue* *loop-end-test*
		      *loop-bindings*
		      ))
    (setf *product-for* t)
    (loop-pop)
    (sloop-swap)
    (parse-loop-for)
     (sloop-swap)
    (do ()
	((null *loop-form*))
      (cond ((catch 'collect  (parse-loop1)))
	    ((null *loop-form*)(return 'done))
	    (t ;(fsignal "hi")
	     (print *loop-form*)
	     (sloop-swap)
	     (parse-loop-collect)
	     (sloop-swap)
	     	     (print *loop-form*)
	     )))
    (sloop-swap)
    (setf inner-body (nreverse *loop-body*))
    (and *loop-map*  (setf inner-body (substitute-sloop-body inner-body)))
    (let ((bod
	    `(macrolet ((local-finish () `(go ,',finish-loop)))
	      (tagbody
		  ,@ (nreverse *loop-prologue*)
	          ,@ (and (null *loop-map*) '(next-loop))
		  ,@ (nreverse *loop-end-test*)
		  ,@ inner-body
		  ,@ (nreverse *loop-increment*)
		  ,@ (and (null *loop-map*) '((go next-loop)))
		  ,finish-loop
		  ,@ (nreverse *loop-epilogue*)))))
      (dolist (v *loop-bindings*)
	(setf bod
	      `(let ,(loop-let-bindings v) ,@(and (cdr v) `(,(cons 'declare (cdr v))))
		    ,bod)))
      (sloop-swap)
      `(do ,bod))))

;;; Usage: SLOOP (FOR 
;;; (defun te ()
;;;   (sloop for i below 5
;;;	  sloop (for j  to i collecting (list i j))))

(def-loop-for in-carefully (var lis)
  "Path with var in lis except lis may end with a non nil cdr" 
  (let ((point (gensym "POINT")))
    `(with ,point and with ,var initially (setf ,point ,lis)
           do(desetq ,var (car ,point))
	   end-test (and (atom ,point)(local-finish))
	   increment (setf ,point (cdr ,point)))))

;;; Usage: IN-CAREFULLY
;;; (defun te (l)
;;;   (sloop for v in-carefully l collecting v))

;;; Note the following is much like the mit for i first expr1 then expr2
;;; but it is not identical, in that if expr1 refers to paralell for loop
;;; it will not get the correct initialization.  But since we have such
;;; generality in the our definition of a for construct, it is unlikely
;;; that all people who define This is why we use a different name

(def-loop-for first-use (var expr1 then expr2)
  (or (l-equal then 'then) (error "First must be followed by then"))
  `(with ,var initially (desetq ,var ,expr1) increment (desetq ,var ,expr2)))

;;; I believe the following is what the original loop does with the FIRST
;;; THEN construction.  

(def-loop-for first (var expr1 then expr2)
  (declare (special *loop-increment*))
  (or (l-equal then 'then) (error "First must be followed by then"))
  ;; If this is the first for, then we don't need the flag, but can
  ;; move the FIRST setting into the INITIALLY section
  (cond ((null *loop-increment*)
	 `(with ,var initially (desetq ,var ,expr1)
		increment (desetq ,var ,expr2)))
	(t
	  (let ((flag (gensym)))
	    `(with ,var with ,flag
		   do (cond (,flag (desetq ,var ,expr2))
			    (t (desetq ,var ,expr1)))
		   increment (desetq ,flag t))))))


(defvar *collate-order* #'<)

;;; of course this should be a search of the list based on the order and
;;; splitting into halves (binary search).  I was too lazy to include one
;;; here, but it should be done.

(defun find-in-ordered-list
       (it list &optional (order-function *collate-order*) &aux prev)
  (do ((v list (cdr v)))
      ((null v) (values prev nil))
	 (cond ((eql (car v) it) (return (values v t)))
	       ((funcall order-function it (car v))
		(return (values prev nil))))
	 (setq prev v)))

(def-loop-collect collate (ans val)
  "Collects values into a sorted list without duplicates.
Order based order function *collate-order*"
  `(do (multiple-value-bind
       (after already-there )
       (find-in-ordered-list ,val ,ans)
       (unless already-there
	  (cond (after (setf (cdr after) (cons ,val (cdr after))))
		(t (setf ,ans (cons ,val ,ans))))))))

;;; Usage: COLLATE
;;; (defun te ()
;;;   (let ((res
;;;	   (sloop for i below 10
;;;               sloop (for j downfrom 8 to 0 
;;;		          collate (* i (mod j (max i 1)) (random 2)))))
;;;

;;;  Two implementations of slooping over the fringe of a tree

;;;(defun map-fringe (fun tree)
;;;      (do ((v tree))
;;;	       (())
;;;	(cond ((atom v)
;;;		    (and v (funcall fun v))(return 'done))
;;;	      ((atom (car v))
;;;		    (funcall fun (car v)))
;;;	      (t (map-fringe fun (car v) )))
;;;	     (setf v (cdr v))))
;;;
;;;(def-loop-map in-fringe (var tree)
;;;  "Map over the non nil atoms in the fringe of tree"
;;;  `(map-fringe #'(lambda (,var) :sloop-map-declares :sloop-body) ,tree))

;;; The next version is equivalent to the previous but uses labels and so
;;; avoids having to funcall an anonymous function. [as suggested
;;; by M. Ballantyne]

(def-loop-map in-fringe (var tree)
  "Map over the non nil atoms in the fringe of tree"
  (let  ((v (gensym)))
    `(let (,var)
       (labels
	   ((map-fringe-aux (.xtree.)
			    (do ((,v .xtree.))
				((null ,v))
			      (cond ((atom ,v) (setf ,var ,v) (setf ,v nil))
				    (t (setf ,var (car ,v))(setf ,v (cdr ,v))))
			      (cond ((null ,var))
				    ((atom ,var)
				     :sloop-map-declares :sloop-body)
				    (t (map-fringe-aux ,var ))))))
	 (map-fringe-aux ,tree)))))

;;; Usage: IN-FRINGE
;;; (sloop for v in-fringe '(1 2 (3 (4 5) . 6) 8 1 2)
;;;        declare (fixnum v)
;;;        maximize v)

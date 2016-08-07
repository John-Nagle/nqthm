;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    SYSLOAD.LISP
;;; 
;;;  Utility file to load Common Lisp macros.
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;  This loads all of the Common Lisp support files.  This form must be
;;;  evaluated before staring from a "NOTE-LIB".

(progn
  (backquote-setting 'nqthm)

  ;;  Akcl specific settings.  The following form may be necessary depending
  ;;  on the size of the Akcl.
  ;;  #+akcl  (setf si::*multiply-stacks* 4)
  ;;  #+akcl  (setf si::*notify-gbc* nil)
  ;;  #+(and akcl sparc) (setq compiler::*split-files* 200000)

  ;;  Lisp Works specific settings.
  ;;  #+LISPWORKS (lw::extend-current-stack 1000)

  ;;  Lucid specific settings.
  ;; #+Lucid (CHANGE-MEMORY-MANAGEMENT :GROWTH-LIMIT 2000)

  ;;  Work around a bug in Allegro.  This is a work around for the '(if* . t)
  ;;  PRINT bug in Allegro CL 4.1 suggested by duane@Franz.COM, concering
  ;;  bug report spr6115:
  ;; #+Allegro (SET-PPRINT-DISPATCH '(CONS (MEMBER IF*)) NIL)

  (setq *thm-suppress-disclaimer-flg* t)
  (setq reduce-term-clock 2000)
  ;;  (setf linel-value 69)

  ;; Following used in DO-FILES-WITH-INTERMEDIATE-LIBS below:
  (load "do-files.lisp"            :print t)

  ;; Following used in approx.events (via monotonicity-macros.lisp):
  (load "do-events-recursive.lisp" :print t)

  (load "disable.lisp"             :print t)
  (load "macros.lisp"              :print t)
  (load "expand.lisp"              :print t)
  (load "vector-macros.lisp"       :print t) 
  (load "primp-database.lisp"      :print t)    
  (load "primitives.lisp"          :print t)
  (load "control.lisp"             :print t)
  (load "expand-fm9001.lisp"       :print t)
  (load "monotonicity-macros.lisp" :print t)
  (load "translate.lisp"           :print t)
  (load "purify.lisp"              :print t))

;;;  Below we define a load sequence for the FM9001 specification and proof.
;;;  This sequence creates a number of intermediate libraries.  If any failures
;;;  occur along the way, a library called "failed" will be created.  If the
;;;  run was a success, one should go back and delete the intermediate
;;;  libraries since they take up a lot of space.

(defmacro do-files-with-intermediate-libs (args)
  (if args
      `(IF (DO-FILES ',(caar args))
           (PROGN
            (MAKE-LIB ,(cadar args) T)
            (DO-FILES-WITH-INTERMEDIATE-LIBS ,(cdr args)))
         (MAKE-LIB "failed"))
    nil))

(princ "
The FM9001 macros have been defined.  You should next execute:

   (in-package \"USER\")

and then you may execute any of:

   (note-lib \"dual-eval\" t)
   (note-lib \"chip\" t)
   (note-lib \"proofs\" t)
   (note-lib \"fm9001\" t)

")

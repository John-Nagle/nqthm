;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

(in-package "USER")

(defun safe-cadr (x)
  (and (consp x)
       (consp (cdr x))
       (cadr x)))

(defun library-filename (filename)
  (let ((pathname (pathname filename)))
    (namestring (make-pathname :host (pathname-host pathname)
                               :device (pathname-device pathname)
                               :directory (pathname-directory pathname)
                               :name (pathname-name pathname)))))

(defun make-lib-conditional (filename save? compile?)
; Do a MAKE-LIB and compile the resulting .lisp file depending on
; the value of the flags SAVE? and COMPILE?
  (cond (save? (make-lib filename)
               (cond (compile?
                      (proclaim-nqthm-file filename)
                      (compile-file 
                       (extend-file-name filename
                                         file-extension-lisp)))))))

(defun do-files (infiles &optional (save nil) (compile nil))
  ;; This does a sequence of files, stopping the first time a failed
  ;; event is encountered. If the flag SAVE is set, a library is saved
  ;; at the end of each file. If the flag SAVE is set and the flag COMPILE
  ;; is set, then the saved lisp file is compiled.
  (if (every #'probe-file infiles)
      (iterate for infile in infiles
               do (cond ((do-file infile)
                         (make-lib-conditional (library-filename infile)
                                               save compile))
                        (t (make-lib-conditional (library-filename infile)
                                                 save compile)
                           (return nil)))
               finally (return t))
      (format t "~%*** File ~a not found. ***"
              (some (function (lambda (x) (and (not (probe-file x)) x)))
                    infiles))))

(DEFUN DO-FILE (INFILE &optional start-name)

;; patched so that one can specify the event at which one wants to begin

;   This function executes each of the event commands in the file INFILE. 
;   The events are top level forms in the file.  It prints
;   each event form to PROVE-FILE and then executes it, accumulating the total
;   event times and printing the event names to the terminal if the output is
;   going elsewhere.  It aborts if some event causes an error or fails.  It
;   prints the system configuration and the accumulated times at the end of
;   PROVE-FILE.  It returns T if all events succeeded and NIL if some failed.

  (WITH-OPEN-FILE (INSTREAM (EXTEND-FILE-NAME INFILE NIL)
                            :DIRECTION :INPUT
                            :IF-DOES-NOT-EXIST :ERROR)
    (LET (ANS FORM)
      (PROG NIL

            (when start-name
                  (loop  (setq form (READ INSTREAM NIL A-VERY-RARE-CONS))
                         (COND ((EQ FORM A-VERY-RARE-CONS)
                                (RETURN T)))
                         (when (eq (safe-cadr form) start-name)
                               (go run-form))))
            LOOP 
            (SETQ FORM (READ INSTREAM NIL A-VERY-RARE-CONS))
            run-form
            
            (COND ((EQ FORM A-VERY-RARE-CONS)
                   (RETURN T)))
        
;   Print out the event form to PROVE-FILE and, if PROVE-FILE is not the
;   terminal, print the name to the terminal

            (ITERPRIN 1 PROVE-FILE)
            (IPRINC EVENT-SEPARATOR-STRING PROVE-FILE)
            (ITERPRIN 2 PROVE-FILE)
            (PPRIND FORM 0 0 PROVE-FILE)
            (ITERPRI PROVE-FILE)
            (COND ((NOT (EQ PROVE-FILE NIL))
                   (IPRINC (safe-CADR FORM) NIL)))

;   Evaluate the event form

            (SETQ ANS (ERROR1-SET (EVAL FORM)))
            (COND ((NULL ANS)
                 
;   A SOFT ERROR1 occurred during the evaluation.  Perhaps we should
;   let the user edit the form, but we have no standard editor in the
;   system.
                 
                   (RETURN NIL)))

;   Recover the actual value from the CONS produced by the ERROR1-SET
;   protection

            (SETQ ANS (CAR ANS))
                 
;   Print the answer to PROVE-FILE and, if PROVE-FILE is not the terminal,
;   print a comma or the failure message, as appropriate, to the terminal
;   to indicate completion of the event.

            (ITERPRI PROVE-FILE)
            (IPRINC ANS PROVE-FILE)
            (COND ((NOT (EQ PROVE-FILE NIL))
                   (COND ((EQ ANS NIL)
                          (ITERPRI NIL)
                          (IPRINC FAILURE-MSG NIL)
                          (ITERPRI NIL))
                         (T (IPRINC (QUOTE |,|) NIL)
                            (COND ((< (OUR-LINEL NIL NIL)
                                      (IPOSITION NIL NIL NIL))
                                   (ITERPRI NIL)))))))

;   Exit if the command failed.

            (COND ((EQ ANS NIL) (RETURN NIL)))

;   Otherwise, continue looping.

            (GO LOOP)))))

;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;  Work of Matt Kaufmann.

(IN-PACKAGE "USER")

(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))

(defparameter *mods-alist*
  (if (boundp '*mods-alist*)            ;so it can work with Nqthm-1987
      (if (not (assoc-eq 'purify *mods-alist*))
          (cons (cons 'purify
                      "A facility for creating event files from
libraries, even when those libraries were created using
various hacks rather than a `pure' Nqthm or Pc-Nqthm.
See \"purify.doc\" for documentation.")
                *mods-alist*)
        *mods-alist*)
    nil))

;; The purpose of this utility is to allow one to take a completed
;; proof effort using (pc-)nqthm and "purify" it a sense I'll now
;; describe.

;; Nqthm users commonly write macros that generate events.  Also,
;; nqthm users at CLI tend to use the "saved_pc-nqthm" core image,
;; which includes local modifications to pc-nqthm.  In some cases
;; there's really no use of pc-nqthm at all beyond what's in nqthm,
;; except perhaps for theories; hence I've also created a file
;; "deftheory.lisp" that contains the disabledp patch and deftheory,
;; but only these.  (Probably I could have left out the disabledp
;; patch, but I didn't want to think about the ramifications that
;; would have for deftheory.)

;; At any rate, once one chooses a core image that corresponds to
;; one of the the publicly released systems -- i.e. either nqthm
;; or pure-pc-nqthm -- one might like to specify some additional
;; forms to execute (perhaps to load files like "deftheory" or
;; "fast-clausifier") and also a library to replay.  The effect should
;; be as illustrated below.

;; 1. The library is used to create an events file.

;; 2. Nqthm or pure-pc-nqthm is started up, with the indicated forms
;;    executed.

;; 3. A proveall is run using the events file created in the first step.

;; A sample transcript occurs at the end of the file.

;; Modifications by B. Brock, July 1993.
;;
;; This now simply creates a file of events, NOT a PROVEALL.
;; 
;; The FM9001 proof contains several occurrences of COMPILE-UNCOMPILED-DEFNS,
;; of which there is no trace in the final chronology.  I defined a new macro,
;; COMPILE-UNCOMPILED-DEFNS*, and modified Matt's LIBRARY-TO-EVENTS, to handle
;; this problem.  This macro introduces a new Nqthm function called
;; COMPILE-UNCOMPILED-DEFNS, whose ENABLE events are recognized and used as a
;; tag to insert calls to COMPILE-UNCOMPILED-DEFNS. 
;;
;; We also automatically add the (SETQ REDUCE-TERM-CLOCK 2000) form.

(defmacro library-to-events (filename
                             &optional event-filename events-list-name
                             &rest forms)
  ;; e.g. (library-to-events "foo" "foo.events") should write to
  ;; "foo.events" a list of events that could be run in order to create
  ;; the library "foo", i.e. "foo.lib" and "foo.lisp".  This should work
  ;; even if the filenames have directory prefixes.
  (setq event-filename
        (or event-filename
            (concatenate 'string filename "-replay.events")))
  (setq events-list-name
        (or events-list-name
            (concatenate 'string filename "-replay")))
  `(progn
     (note-lib ,filename)
     (database-to-events ,event-filename ,events-list-name ',forms)))

(defun database-to-events (event-filename events-list-name forms)
  (declare (ignore events-list-name))
  ;; Writes out a list of events to event-filename that could be run
  ;; in order to create the current prover state.
  (or (equal ".events"
             (subseq event-filename
                     (- (length event-filename) 7)
                     (length event-filename)))
      (error "The first argument to database-to-events should be a ~
              string that ends in \".events\", ~%but ~a does not."
             event-filename))
  (with-open-file
    (str event-filename :direction :output)
    (format t "~%Creating events file ~s...." event-filename)
    (when forms
      (format str "~s~%~%" (if (cdr forms)
                               (cons 'progn forms)
                             (car forms)) str))
    (ppr (quote (boot-strap nqthm)) str)
    (iterpri str)
    (iterpri str)
    (ppr (quote (setq reduce-term-clock 2000)) str)
    (iterpri str)
    (iterpri str)
    ;;  CAR is (BOOT-STRAP NQTHM) -- added above before (SETQ ... )
    (iterate for name in (cdr (reverse chronology))
      do
      (let (event)
        (progn
          (setf event (untranslate-event (get name (quote event))))
          (ppr event str)
          (iterpri str)
          (iterpri str)
          (when (and
                 (equal (car event) (quote toggle))
                 (equal (caddr event) (quote compile-uncompiled-defns))
                 (equal (cadddr event) nil))
            (ppr (quote (compile-uncompiled-defns "tmp")) str)
            (iterpri str)
            (iterpri str)))))
    (print `(make-lib ,(subseq event-filename 0
                               (- (length event-filename) 7)) t) str)
    (format t " done.~%")))

(defmacro compile-uncompiled-defns* (filename)
  `(PROGN
    ,(let ((sdefn (get 'compile-uncompiled-defns 'sdefn)))
       (if sdefn
           (unless (equal sdefn '(LAMBDA () '*1*TRUE))
             (error "~%COMPILE-UNCOMPILED-DEFNS is already defined!"))
         `(DEFN COMPILE-UNCOMPILED-DEFNS () T)))
    (ENABLE COMPILE-UNCOMPILED-DEFNS)
    (COMPILE-UNCOMPILED-DEFNS ,filename)))

#| 

Sample transcript.  It assumes that we used pc-nqthm on the following
events to create library "foo", i.e. "foo.lib" and "foo.lisp" in that
same directory.

(do-events '(

(prove-lemma times-comm (rewrite)
  (equal (times x z) (times z x)))

(defn blob (x)
  (let ((y (plus x x)))
    (times y 3)))

(prove-lemma times-add1 (rewrite)
  (equal (times (add1 x) y)
         (plus y (times x y))))

(prove-lemma blob-val nil
  (equal (blob x)
         (cond ((zerop x) 0)
               (t (times 6 x)))))
))

.... and, here's what we do to create a pure nqthm events file
"foo-replay.events":

% pc-nqthm
AKCL (Austin Kyoto Common Lisp)  Version(1.527) Mon Jan  7 12:51:51 CST 1991
Contains Enhancements by W. Schelter

Nqthm, with functional instantiation.
Initialized with (BOOT-STRAP NQTHM) on January 7, 1991  14:22:37.
>(load "purify.o")
Loading purify.o
start address -T 30b800 Finished loading purify.o
1864

>(library-to-events "foo" nil nil (print "hi") (print "there"))
To print patch messages, (PRINT-NQTHM-PATCH-DISCLAIMER)
Loading foo.lib
Finished loading foo.lib
Loading foo.lisp
Finished loading foo.lisp

Creating events file "foo-replay.events".... done.
NIL

>(bye)
Bye.
% nqthm
AKCL (Austin Kyoto Common Lisp)  Version(1.527) Mon Jan  7 12:51:51 CST 1991
Contains Enhancements by W. Schelter

Nqthm, with functional instantiation.
Initialized with (BOOT-STRAP NQTHM) on January 7, 1991  14:22:37.
>(load "foo-replay.events")
Loading foo-replay.events

"hi" 
"there" 
NQTHM,TIMES-COMM,BLOB,TIMES-ADD1,BLOB-VAL,
Total Statistics:
[ 6.6 18.0 1.8 ]

(MAKE-LIB foo-replay)
Finished loading foo-replay.events
T

>

|#

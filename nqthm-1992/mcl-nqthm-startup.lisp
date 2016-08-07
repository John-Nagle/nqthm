#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".

|#

; A start-up file for using Nqthm-1992 on a Mac under Mac Common Lisp 2.0.

(in-package "COMMON-LISP-USER")

; This file belongs in the Nqthm-1992 directory.  After starting up MCL, load
; this file via the EVAL window, and as a result, nqthm.lisp will be loaded,
; *default-nqthm-path* will be set to this directory, and the command cd will
; be defined to connect back to this directory.  Also, optimizations will be
; set for maximum speed.

; This file should not be compiled.

(let ((temp (choose-file-default-directory)))
  (format t "~%Loading nqthm.lisp.~%")
  (load (format nil "~anqthm.lisp" temp))
  (format t "~%Finished loading nqthm.lisp~%")
  (format t "~%Setting *default-nqthm-path* to ~a.~%"
          (set (intern "*DEFAULT-NQTHM-PATH*" "USER")
               (namestring temp))))

; We eval the next form only to avoid getting an error report when we load this
; file into FRED.  This is the file that creates the USER package.

(format t "~%Proclaiming to optimize for maximum speed.~%")

(proclaim '(optimize (speed 3) (safety 0) (space 0)))

(defun user::cd (&optional (x user::*default-nqthm-path*))
  (set-mac-default-directory x))

(format t "~%Now execute (IN-PACKAGE \"USER\"), then (COMPILE-NQTHM) ~
    or (LOAD-NQTHM).~%")
;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    DISABLE.LISP
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

(defun disableable-citizens (event-name bad-names)
  (iterate for x in (cons event-name (get event-name 'satellites))
           when (and (not (member-eq x bad-names))
                     (not (disabledp x)))
           collect x))

(defun enabled-citizens-back-to (name)
  (or (member-eq name chronology)
      (er soft (name) (!ppr name nil) |is|
          |not| |in| |the| |chronology| excl))
  (iterate for x in chronology
           with bad-names =
           ;; from definition in nqthm of CHK-DISABLEABLE
           (append
            (iterate for x in *1*btm-objects collect
                     (pack (list prefix-for-functions x)))
            (iterate for x in shell-alist collect
                     (pack (list prefix-for-functions (car x)))))
           until (eq x name)
           when (not (member-eq (car (get x 'event)) '(toggle deftheory)))
           nconc (disableable-citizens x bad-names)))

(defun enabled-citizens-between (start-name end-name &aux temp)
  (or (member-eq start-name chronology)
      (er soft (start-name) (!ppr start-name nil) |is|
          |not| |in| |the| |chronology| excl))
  (or (setq temp (member-eq end-name chronology))
      (er soft (end-name) (!ppr end-name nil) |is|
          |not| |in| |the| |chronology| excl))
  (or (member-eq start-name temp)
      (er soft (start-name end-name) (!ppr start-name nil) |is|
          |in| |the| |chronology| |,| |but| |occurs| |later|
          |than| (!ppr end-name nil) excl))
  (iterate for x in (member-eq end-name chronology)
           with last-name
           and bad-names =
           ;; from definition in nqthm of CHK-DISABLEABLE
           (append
            (iterate for x in *1*btm-objects collect
                     (pack (list prefix-for-functions x)))
            (iterate for x in shell-alist collect
                     (pack (list prefix-for-functions (car x)))))
           until (prog1 (eq (print last-name) (print start-name))
                   (setq last-name x))
           when (not (member-eq (car (get x 'event)) '(toggle deftheory)))
           nconc (disableable-citizens x bad-names)))

(defun disable-all-fn (lst)
  (cons 'progn
        (iterate for x in lst
                 collect (list 'disable x))))

(defmacro disable-all (lst &optional (name 'temp))
  (disable-all-fn lst))

(defun enable-all-fn (lst)
  (cons 'progn
        (iterate for x in lst
                 collect (list 'enable x))))

(defmacro enable-all (&rest lst)
  (enable-all-fn lst))

(defmacro disable-back-to (name &optional theory-name print-flg)
  (let* ((enabled-citizens (enabled-citizens-back-to name))
         (disabling-events
          (iterate for x in enabled-citizens
                   collect (list 'disable x)))
         (form
          (cons 'progn
                (if theory-name
                    (cons `(deftheory ,theory-name ,enabled-citizens)
                          disabling-events)
                  disabling-events))))
    (if print-flg
        (print form)
      form)))

;; To reproduce the existing enable-disable state, we disable all
;; non-disabled new disableable events, and we also restore all
;; existing events that had been touched.

(defun disabledp-as-of (name alternate-disabled-lemmas)
  (let ((pair (assoc-eq name alternate-disabled-lemmas)))
    (if pair
        (cddr pair)
      nil)))

(defun untampering-events (name)
  (let ((alternate-disabled-lemmas disabled-lemmas)
        possibly-tampered-names)
    ;; take new events off alternate-disabled-lemmas and
    ;; set possibly-tampered-names
    (iterate for x in chronology
             until (or (eq x name)
                       (null alternate-disabled-lemmas))
             when (eq (cadr (car alternate-disabled-lemmas)) x)
             do
             (setq possibly-tampered-names
                   (add-to-set (car (car alternate-disabled-lemmas))
                               possibly-tampered-names))
             (setq alternate-disabled-lemmas
                   (cdr alternate-disabled-lemmas)))
    (and (not (eq alternate-disabled-lemmas disabled-lemmas))
         (iterate for x in possibly-tampered-names
                  for old-status = (disabledp-as-of
                                    x alternate-disabled-lemmas)
                  when (not (eq old-status (disabledp x)))
                  collect (if old-status
                              `(disable ,x)
                            `(enable ,x))))))

(defmacro better-disable-back-to (name &optional print-flg)
  (let* ((enabled-citizens (enabled-citizens-back-to name))
         (disabling-events
          (iterate for x in enabled-citizens
                   collect (list 'disable x)))
         (form
          (cons 'progn
                (append disabling-events (untampering-events name)))))
    (if print-flg
        (print form)
      form)))

(defmacro disable-closed-interval (start-name end-name
                                              &optional theory-name print-flg)
  (let* ((enabled-citizens (enabled-citizens-between start-name end-name))
         (disabling-events
          (iterate for x in enabled-citizens
                   collect (list 'disable x)))
         (form
          (cons 'progn
                (if theory-name
                    (cons `(deftheory ,theory-name ,enabled-citizens)
                          disabling-events)
                  disabling-events))))
    (if print-flg
        (print form)
      form)))

(defmacro enable-or-disable-theory (name enable-flg print-flg)
  (let (citizen-names)
    (or (match (get name 'event)
               (deftheory & citizen-names))
        (er soft (name) |There| |is| |no| DEFTHEORY |event|
            |called| (!ppr name (quote |.|))))
    (let ((form (cons 'progn
                      (iterate for x in citizen-names
                               with ev-type = (if enable-flg 'enable 'disable)
                               when (eq (disabledp x) enable-flg)
                               collect (list ev-type x)))))
      (if print-flg
          (print form)
        form))))

(defmacro disable-theory (name &optional print-flg)
  `(enable-or-disable-theory ,name nil ,print-flg))

(defmacro enable-theory (name &optional print-flg)
  `(enable-or-disable-theory ,name t ,print-flg))

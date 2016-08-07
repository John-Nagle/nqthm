; This file, doc/nq.el, contains the definition of a Gnu Emacs utility for
; finding documentation on Nqthm-1992 topics in the file logic-reference.doc.
; To use nq.el, first edit, below, the definition of the variable
; nqthm-doc-file so that it is the name of the logic-reference.doc file at your
; site.  Then, load nq.el into your Emacs.  For convenience, you may want to
; place the line

;   (load ".../doc/nq.el")

; in your .emacs file, where ... is the name of the nqthm-1992 directory at
; your site.

; The Gnu Emacs command 

;  M-X nq <topic> <RETURN>

; will find the file logic-reference.doc in a buffer and search for an entry on
; <topic>.  Given a null topic, the nq command will continue searching for the
; previous topic.  <topic> is a regular expression.  A topic name need not be
; spelled out completely.  nq's search strategy is very simple minded, but
; perhaps better than nothing.

; The variable nqthm-doc-file below should be edited to be the full name of the
; nqthm-1992/doc/logic-refernce.doc file at your site.
(defvar nqthm-doc-file "/slocal/src/nqthm-1992/doc/logic-reference.doc")

; The previous pattern.
(defvar last-nqthm-search-key "")

(defun nq (word)
  "Search the Nqthm-1992 documentation for an entry about WORD, a regexp.
If WORD is empty, continue searching for the previous pattern."
  (interactive "sTopic (regexp): ")
  (find-file nqthm-doc-file)
  (cond ((equal word "")
	 (setq word last-nqthm-search-key)
	 (forward-line 3))
	(t (setq last-nqthm-search-key word)
	   (goto-char (point-min))))
  (let ((str
	 (format
	  (concat
	   ;; We examine (1) titles of numbered sections,
	   "^[0-9][0-9.]*. %s\\|"
	   ;; (2) axiomatic definitions,
	   "^Defining Axiom .*\n(%s\\|"
	   ;; (3) functions in shell invocations,
	   "^Shell Definition.[^.]* %s")
	  word word word)))
    (or (re-search-forward str nil t)
	;; and (4), anywhere at all, as a last resort.
	(re-search-forward (format "%s" word)))
    (goto-char (match-beginning 0))
    (recenter 0)))


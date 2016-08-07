#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".


                A Conventional Syntax Pretty-Printer for Nqthm


                             Introduction

The functions in this file implement a pretty-printer for Nqthm events.  The
syntax produced is a somewhat conventional mathematical notation, in Latex
format.  Send complaints to boyer@cli.com.  Criticism of all sorts solicited.

The following remarks are, currently, the only documentation for this facility,
but these remarks should suffice for most simple utilization.

This file is not automatically compiled or loaded when building Nqthm-1992.  To
use this printer, after compiling and loading Nqthm, compile this file and load
it, i.e., (compile-file "infix.lisp") and (load "infix").

Assume we have a file whose extension is `events', say, "foo.events", in proper
syntactic form for acceptance by prove-file.  That is to say, suppose that the
file "foo.events" contains only legal event commands such as defn's and
prove-lemma's, Lisp style comments, and the few other sorts of miscellaneous
instructions documented as legal instructions to prove-file.  If one invokes
(infix-file "foo"), then the Latex file "foo.tex" will be generated.  Run
"foo.tex" through Latex and print.

To get an index, too, run Latex twice, with makeindex once
in between, i.e.,
   % latex foo
   % makeindex foo
   % latex foo

Treatment of comments.  `infix-file' preserves comments between events, but
skips over, that is, ignores comments within events.  If a comment begins with
;\ or has the form #|\ ... |#, then the rest of the comment (excluding the
comment markers and the backslash) is left for Latex to process as ordinary
Latex text.  On the other hand, if the comment start is not immediately
followed by a backslash, `infix-file' puts the entire comment (including the ;
or #| |#) into a Latex `verbatim' environment.  If `infix-file' is given the
keyword argument :nq with value t, then certain specially marked Nqthm
expressions in comments are replaced with their conventional notation.  See the
documentation of the function `nqtex2tex' below for a description of the
special syntax for this replacement process.  We completely skip comments
within events because we have not figured out how to place them appropriately
mechanically.

Coverage.  `infix-file' file handles the entirety of the Nqthm-1992 term syntax
checked by prove-file.  But note that we deliberately do not print out the
`hint' parts of events.

Motivation.  We hope this notation will facilitate the communication of work
with Nqthm to those who do not happily read Lisp notation.  But we have no
expectation that this notation will make it easier for the Nqthm user to
formulate or to prove theorems.

Warning about the absence of error checking.  In general, user-callable
subroutines of Nqthm do extensive syntactic checking on their input and
explicitly report syntactic errors.  But this pretty printer does not do such
syntactic checking.  Rather, we assume the given input is known to be
syntactically correct, namely as though checked by `prove-file'.  Failure to
provide input in correct syntactic form can result in nasty, brutish, and short
Lisp errors.

Besides `infix-file', here are the other user-level functions supported by this
file.

(a) (print-examples) creates a stand-alone, Latex file named
"infix-examples.tex", which is a summary of the syntax we print in terms of the
official Nqthm syntax.  This file will also correctly report any user
modifications made to the syntax by invocation of the make... functions
described later.  We hope that users will want to include this file in reports
about Nqthm use to make clear what syntactic conventions they are using.

(b) (nqtex2tex "foo") copies the file "foo.nqtex" to the file "foo.tex", but
along the way, Nqthm terms preceded by an exclamation mark and certain
alphabetic characters are replaced with the Latex for the conventional notation
this printer generates.  For example, if nqtex2tex encounters !t(gcd x
(difference y x)) in a file, it will replace it with {\rm{gcd}}\,({\it{x\/}},
{\it{y\/}} $-$ {\it{x\/}}).  We find the former much easier to read in a file.
nqtex2tex thus permits one to keep Nqthm forms in files to be read and edited
by humans, e.g., in comments in Nqthm event files.  Ordinary uses of !, e.g.,
uses of it followed by white space or punctuation characters, are, of course,
unaltered.  See the comment at the beginning of the definition of nqtex2tex,
below, for details on the syntax and replacements.  There is also an option to
nqtex2tex for simply stripping out the ! commands.

(c) (infix-form fm) prints (to *standard-output*) the Latex for the
conventional notation for the Nqthm term fm.  `infix-form', `infix-event', and
`ppe-latex' can be used to generate Latex to be inserted manually into papers,
but we recommend the use of nqtex2tex, described above, for this purpose.

(d) (infix-event ev) prints (to *standard-output*) the Latex for the
conventional notation for the Nqthm event ev.

(e) (ppe-latex name) prints what the Nqthm command `ppe' prints, but prints the
events in Latex.


                           USER EXTENSION OF SYNTAX

`infix-file' is table-driven, and it is very easy to extend in certain ways,
e.g., to introduce a new infix operator.  See the very end of this file, at
`USER MODIFIABLE TABLE SETUP', for examples of how to establish new syntax.
See the variable *infix-wide* for one user-settable flag that affects the
formatting of the usual associative and commutative binary operators.


                         PARENTHESES and PRECEDENCE

This pretty-printer does not provide a facility for the suppression of
parentheses via the declaration of precedence for operators.  An objective in
printing a formula is clarity.  We know of very, very few cases (e.g., + and *)
where precedence is something on which people agree.  As a small contribution
towards the suppression of parentheses, we do drop the outermost parentheses of
a formula when the formula is (a) at the very top level or (b) an argument of a
function that is being printed in the usual f(x,y) notation, with subterms
separated by parentheses and commas.


                            END OF COMMENTS ON USE

|#


;                            IMPLEMENTATION COMMENTS


;  The three `tables' that govern the printing are the variables:

; 1. *atom-alist*, which governs printing of variables, numbers, T, F, and NIL.

; 2. *fn-alist*, which governs the printing of any term that starts with a
; function symbol, including LET, COND, CASE, LIST, LIST*, and FOR.

; 3. *event-printer-alist*, which governs the printing of events.

; Each table is an alist.  Each member of any of these alists is a list (symbol
; fn), where symbol is the car of a form (or in the case of a non-consp form,
; the form itself) which is about to be printed.  fn is a Common Lisp function
; of one argument which is called on the form in question to do the printing.
; For each alist, there is a default function that is returned if a symbol is
; not explicitly represented.  One such default is the function
; default-fn-printer, which is a good function to study before contemplating
; serious modifications to this file.

; Although adding new members to these alists, and defining corresponding
; special purpose functions, is certainly sensible and easy, there are several
; points to be made.

; 1.  It is unlikely that there will be any call to edit `*atom-alist*' until
; and unless TRANSLATE is changed.

; 2.  *fn-alist* can be most easily modified by the use of the macros
; make-infix-op, make-unary-prefix-op, make-unary-suffix-op,
; make-infix-multiple-op, and make-prefix-multiple-op.  See the very end of the
; file for many examples of how syntax operators can be easily established.

; We really do assume throughout this code that the input file has passed
; through prove-file, e.g., we assume that the last test in a `cond' is on T,
; the last test in a case is an `otherwise', and that the third argument to
; `prove-lemma' is something that translate can accept.


(IN-PACKAGE "USER")

(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))

;                             STANDARD OUTPUT USED

; Printing.  We do *all* of our printing of formulas to *standard-output*, so
; we call princ and write-char on just one argument, the thing to be printed.


(eval-when (load eval compile)
           (or (boundp 'file-extension-events)
               (error "~%~%infix.lisp is to be compiled and used with Nqthm versions 1992 or later,~%~
                       not stand-alone or with older versions of Nqthm.~%")))


;                                   PRINTING


; The setting of the *left-margin* causes only the stuff within tabbing
; environments to be moved over.  Nqthm event forms that do not use that
; tabbing environment should be adjusted by other means by the user if desired.
; *left-margin* may be set before invoking infix-form or infix-event.

(defparameter *left-margin* 0)

; *rightmost-char-number* is bound sometimes to alter subsidiary printing
; operations that more text needs to be printed on the same line after they
; finish.

(defparameter *rightmost-char-number* 77)

; *infix-loc* is a good estimate of how far in from the left margin we
; currently are, counting as 1 any character, or any symbol not wired in.

(defparameter *infix-loc* 0)

; If *testing* is t, then we are not really printing but only counting the
; characters we would print, trying to see if a line break is necessary.

(defparameter *testing* nil)

(defparameter *latex-tab-limit* 13)

; In *tabs-in* we keep track of how deep into tabs we are so that we can punt
; if necessary.

(defparameter *tabs-in* 0)

(defparameter *do-not-use-tabs* nil)

; *tabs-list* is the list of the value of *infix-loc* when we set tabs.

(defparameter *tab-list* nil)

; We cannot place final defparameters for the following three special
; symbols at this place in the file because their initial values
; contain `functions' of functions to be defined later.  We tried proclaiming
; them special, but the Allegro compiler objected.

(defvar *atom-alist*)
(defvar *fn-alist*)
(defvar *event-printer-alist*)

; *top-parens-eliminable* is a special that is bound to t whenever, in printing
; arguments, it will be ok to omit the outermost parentheses of the arguments
; we are about to print.

(defparameter *top-parens-eliminable* nil)

; There is some question about how long an index entry can be in Latex.  For example,
; after 64 characters, a `subitem' is randomly inserted.

(defparameter *index-entry-max* 100)

(defparameter *negative-infix-table* nil)

(defparameter *infix-ops* nil)

(defparameter *infix-multiple-ops* nil)

(defparameter *prefix-multiple-ops* nil)

(defparameter *unary-prefix-ops* nil)

(defparameter *negative-unary-prefix-table* nil)

(defparameter *unary-suffix-ops* nil)

(defparameter *negative-unary-suffix-table* nil)

(defparameter *unary-abs-ops* nil)

(defparameter *tracing-advise-break* nil)

(defparameter *white-space* '(#\Space #\Newline #\Tab #\Page))

(defparameter *typical-characters-following-excl* (list #\Space #\Tab #\Newline #\= #\*))

;  != and !* occur in C code.

(defparameter *started-a-verbatim* nil)

(defparameter *reported-tabs* nil)

(defparameter *copy-comments-in-file* nil)

;  This `secret' function symbol is used to print out integers generated by
; readins #b, #o, or #x syntax.

(defparameter *infix-radix* (make-symbol "*infix-radix*"))

; Anyone extending the syntax by hand rather than by use of one of the make...
; functions ought also to add something to this list of examples to illustrate
; the new syntax.

(defparameter *wired-in-infix-examples*
  '((if x y z)
    (cond (test1 value1) (test2 value2) (t value3))
    (case x (key1 answer1) (key2 answer2) (otherwise default))
    (for x in l when (test x) collect (fn x))
    (let ((var1 val1) (var2 val2)) form)
    (forall (x y) (p x))
    (exists (x y) (p x))
    (not x)))

(defparameter *constant-font* "\\sc")

(defparameter *neg-str* (format nil "$~a$"  "\\neg"))

; Severe warning on printing.  It is illegal for any function in this file,
; with the exception of ppe-latex (which we hardly think of being in this
; file), to do any printing except via these four printing macros: pprinc,
; pprin1, pformat, and pwrite-char.  This rule is imposed so that the `hack' of
; printing invisibly (see *testing*) will work.  The point is that any printing
; operation may be called many times!  But we do not want to print unless the
; special *testing* is bound to nil!  Key fact: if *testing* if t, we DO NOT
; print.

; A very sloppy fudge factor to account for the fact that in \tt mode, characters are
; fatter.

(defparameter *tt-size* 1.3)

(defparameter *do-not-index-calls* nil)

(defparameter *infix-comma* (make-symbol "comma"))

(defparameter *infix-comma-atsign* (make-symbol "comma-atsign"))

(defparameter *infix-backquote* (make-symbol "backquote"))

(defparameter *do-not-index-calls-of* (list *infix-radix* *infix-comma* *infix-comma-atsign* *infix-backquote*))

(defparameter *infix-wide* nil)

#| *infix-wide* is intended as a user-settable variable that determines whether
we print infix expressions such as (+ a b c), when it is necessary to break
lines, as
  (a
    +
   b
    +
   c)
or as
  (a
   + b
   + c)
This only affects those operators declared with make-infix-op, which by
default, includes equal, lessp, leq, greaterp, geq, member, implies, iff,
difference, quotient remainder, union, plus, times, and, and or.  |#

(defmacro pprinc (x)
  `(or *testing* (princ ,x)))

(defmacro pprin1 (x)
  `(or *testing* (prin1 ,x)))

(defmacro pformat (&rest x)
  `(or *testing* (format ,@x)))

(defmacro pwrite-char (x)
  `(or *testing* (write-char ,x)))

; It is absolutely desireable that any printing done by any function inside this
; file, within the scope of a tabbing environment, be done with with pprinci,
; pprin1, or print-atom IF the printing is to contribute `real', i.e.,
; non-formatting, characters to the final output.  The optional second argument
; specifies how many characters are being contributed, with default 1.  If
; *testing* is t, not only do we not want to print, but we want to throw out to
; advise-break if we have exceeded the *rightmost-char-number*.

(defmacro pprinci (x &optional (i 1))
  `(progn (pprinc ,x)
          (incf *infix-loc* ,i)
          (cond ((and *testing*
                      (> *infix-loc* *rightmost-char-number*))
                 (throw 'advise-break t)))))
          
(defmacro pprin1i (x)
  `(progn (let ((x ,x))
            (pprin1 x)
            (incf *infix-loc* (our-flatc x)))
          (cond ((and *testing*
                      (> *infix-loc* *rightmost-char-number*))
                 (throw 'advise-break t)))))


;                             SIX GENERAL OPERATOR SCHEMAS

; The following make-... macros are used to generate functions and entries for
; the *fn-alist*.  See the end of this file for many examples of usage which can
; be easily extended.

(defun clean-up (fn)

; This function is supposed to remove completely all trace of any prior establishment
; of any syntax for the function symbol fn.

  (or (symbolp fn)
      (error "Illegal function symbol name: ~a." fn))
  (iterate for lst in '(*infix-ops* *unary-prefix-ops* *unary-suffix-ops* *unary-abs-ops*) do
           (set lst (remove fn (eval lst))))
  (iterate for alist in '(*fn-alist* *negative-infix-table* *negative-unary-prefix-table*
                                     *negative-unary-suffix-table* *prefix-multiple-ops*
                                     *infix-multiple-ops*) do
           (set alist (iterate for pair in (eval alist) unless (eq fn (car pair)) collect pair))))

(defmacro make-infix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-infix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-infix-printer
           term
           ,(format nil "$~a$" str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *infix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil "$~a$" neg-str))
                              *negative-infix-table*)))
       ',name)))
                 
(defmacro make-infix-multiple-op (name &rest strs)
  (let ((fn-name (intern (format nil "~s-infix-multiple-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-infix-multiple-printer
           term
           ',(iterate for str in strs collect
                      (format nil "$~a$" str))))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push (cons ',name ,(length strs)) *infix-multiple-ops*)
       ',name)))

(defmacro make-prefix-multiple-op (name &rest strs)
  (let ((fn-name (intern (format nil "~s-prefix-multiple-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-prefix-multiple-printer
           term
           ',(iterate for str in strs collect
                      (format nil "$~a$" str))))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push (cons ',name ,(length strs)) *prefix-multiple-ops*)
       ',name)))
                 
(defmacro make-unary-prefix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-unary-prefix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-prefix-printer
           term
           ,(format nil "$~a$" str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-prefix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil "$~a$" neg-str))
                              *negative-unary-prefix-table*)))
       ',name)))

(defmacro make-unary-suffix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-unary-suffix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-suffix-printer
           term
           ,(format nil "$~a$" str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-suffix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil "$~a$" neg-str))
                              *negative-unary-suffix-table*)))
       ',name)))

(defmacro make-unary-abs-op (name lhs-str rhs-str)
  (let ((fn-name (intern (format nil "~s-unary-abs-op-printer" name))))
    `(progn
       (clean-up ',name)
       (defun ,fn-name
         (term)
         (default-unary-abs-printer
           term
           ,(format nil "$~a$" lhs-str)
           ,(format nil "$~a$" rhs-str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-abs-ops*)
       ',name)))


;                                    TABBING

; infix-file generates text that uses the Latex `tabbing' environment, setting
; a tab for each new level of indentation.  We find this a convenient
; sublanguage to target.  It appears based upon various experiment that perhaps
; Latex cannot handle tabs more than about 14 deep, or so.  The following
; parameter, latex-tab-limit, could perhaps be increased if one had a Latex
; wherein this limit has been raised.  However, it is a relatively rare
; function that needs terms that are more than 13 function calls deep.  When
; infix-file hits this limit, it falls back upon the standard Nqthm
; pretty-printer, and puts the result in a verbatim environment.

(defun begin-tabbing ()

; Tabbing environments cannot be nested, here or in Latex.

  (setq *tab-list* nil)
  (princ "\\begin{tabbing}")
  (cond ((> *left-margin* 0)
         (iterate for i from 1 to *left-margin* do (pprinc "M"))
         (pprinc "\\=\\+\\kill")
         (pwrite-char #\Newline)))
  (setq *infix-loc* *left-margin*))

(defun end-tabbing ()
  (princ "\\end{tabbing}"))

(defun set-tab ()

; Generate LaTeX instructions to set a tab, and also cause \\ to tab to this
; column in the future.  `Punt' if we hit the limit, by throwing all the way
; out.

  (cond (*do-not-use-tabs* nil)
        (t (cond ((= *tabs-in* *latex-tab-limit*)
                  (throw 'taboverflow t)))
           (setq *tabs-in* (1+ *tabs-in*))
           (push *infix-loc* *tab-list*)
           (pprinc "\\=\\+"))))
        
(defun pop-tab ()

;  Generate LaTeX for `tab to one tab less in'.

  (cond (*do-not-use-tabs* nil)
        (t (setq *tabs-in* (1- *tabs-in*))
           (pop *tab-list*)
           (pprinc "\\-"))))

(defun newline-and-tab ()

; Generates LaTeX for `tab in to current setting.'  The extra spaces seem to
; help around \\ , but I don't know why.

  (cond (*do-not-use-tabs* (pprinci " "))
        (t (pprinc " \\\\ ")
           (pwrite-char #\Newline)
           (setq *infix-loc* (car *tab-list*)))))


;                                  PRINT-ATOM

; We want to slashify special Tex characters in the following three lists in
; case they appear in an Nqthm symbol.  Used only by print-atom and index.

(defconstant tex-special-chars (coerce "#$%&~_^\\{}" 'list))

(defconstant tex-other-chars (coerce "<>|" 'list))

(defconstant latex-index-specials (coerce "@|!\"" 'list))

; We also to handle the characters in tex-other-chars specially, by going into
; math mode, since slashification with backslash does not work.

(defun print-atom (atm)

; Our own atom printer, which slashifies the tex-special-chars and
; tex-other-chars in symbols and strings.  We print all Nqthm symbols with this
; function because we want to avoid generating stuff that will make Latex barf,
; e.g., a symbol with an unslashified $, <, or { in it.

  (cond ((symbolp atm)
         (iterate with str = (symbol-name atm)
                  for i below (length (symbol-name (the symbol atm)))
                  for char = (char (the string str) (the fixnum i))
                  do (progn
                       (cond ((eql char #\^)
                              (pprinc "\\verb|^|"))
                             ((member char tex-special-chars)
                              (pwrite-char #\\)
                              (pwrite-char (cond ((eq *print-case* :downcase)
                                                  (char-downcase char))
                                                 (t char))))
                             ((member char tex-other-chars)
                              (pwrite-char #\$)
                              (pwrite-char (cond ((eq *print-case* :downcase)
                                                  (char-downcase char))
                                                 (t char)))
                              (pwrite-char #\$))
                             (t (pwrite-char (cond ((eq *print-case* :downcase)
                                                    (char-downcase char))
                                                   (t char))))))
                  finally (incf *infix-loc* (length str))))
        ((stringp atm)
         (incf *infix-loc* (+ 4 (* 2 (length atm))))
         (pprinc "{\\tt{\"")
         (iterate for i below (length atm)
                  for char = (char (the string atm) (the fixnum i))
                  do (progn
                       (cond ((member char tex-special-chars)
                              (incf *infix-loc* 1)
                              (pwrite-char #\\))
                             ((member char tex-other-chars)
                              (incf *infix-loc* 2)
                              (pwrite-char #\$)
                              (pwrite-char char)
                              (pwrite-char #\$)))
                       (pwrite-char char)))
         (pprinc "\"}}"))
        (t (pprin1i atm)))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))


;                             FONT SYMBOL PRINTERS

(defun bf-sym-printer (x)

; Print in bold face.

  (pprinc "{\\bf{")
  (print-atom x)
  (pprinc "}}"))

(defun tt-sym-printer (x)

; Print in typewriter font.

  (pprinc "{\\tt{")
  (print-atom x)

; We charge more for tt characters.

  (incf *infix-loc* (* (- *tt-size* 1) (our-flatc x)))
  (pprinc "}}"))


;                                   *ATOM-ALIST*

; *atom-alist* is one of the three tables off of which this printer is driven.
; It determines how a variable symbol is printed.  It is unlikely that anyone
; would want to change this unless translate changes because t, f, and nil are
; the only symbols that translate treats specially as constants instead of as
; variable symbols.

; We would like to put this at the beginning of the file but cannot, so we put
; a special declaration up there.

(defparameter *atom-alist*
  (list (list 't   (function bf-sym-printer))
        (list 'f   (function bf-sym-printer))
        (list 'nil (function bf-sym-printer))))

(defun default-atom-printer (var)

; We put variables in italics, strings in typewriter.

  (cond ((symbolp var)
         (pprinc "{\\it{")
         (print-atom var)
         (pprinc "\\/}}"))
        ((stringp var)
          (print-atom var))
        ((numberp var)
         (tt-sym-printer var))
        (t (pprin1 var))))

(defun get-atom-printer (sym)
  (let ((a (assoc sym *atom-alist*)))
    (cond (a (cadr a))
          (t (function default-atom-printer)))))


;                                     QUOTE

; The printing of quote terms is intrinsically intertwined with the printing of
; backquoted terms.  The backquoted terms have been read with our
; special-to-infix-file backquote reader.

(defun quote-printer1 (term)

; How we output a quoted term.

  (cond ((atom term)
         (tt-sym-printer term))
        ((eq (car term) 'quote)
         (quote-printer term))
        ((eq (car term) *infix-comma*)
         (comma-printer term))
        ((eq (car term) *infix-comma-atsign*)
         (comma-atsign-printer term))
        ((eq (car term) *infix-backquote*)
         (backquote-printer term))
        ((eq (car term) *infix-radix*)
         (funcall (function *infix-radix*-printer) term))
        ((advise-break (list 'quote term))
         (pprinci "{\\tt{(}}" *tt-size*)
         (set-tab)
         (iterate for tail on term do
                  (progn (quote-printer1 (car tail))
                         (cond ((null (cdr tail))
                                (pprinci "{\\tt{)}}" *tt-size*))
                               ((or (atom (cdr tail))
                                    (eq (car (cdr tail))
                                        *infix-comma*)
                                    (eq (car (cdr tail))
                                        *infix-comma-atsign*)
                                    (eq (car (cdr tail))
                                        *infix-backquote*))
                                (newline-and-tab)
                                (pprinci "{\\tt{.\\ }}" 4)
                                (quote-printer1 (cdr tail))
                                (pprinci "{\\tt{)}}" *tt-size*)
                                (return nil))
                               ((and (or (atom (car tail))
                                         (eq *infix-radix* (car (car tail))))
                                     (cdr tail)
                                     (or (atom (cadr tail))
                                         (eq *infix-radix* (car (cadr tail))))
                                     (not (advise-break (list 'quote (cadr tail)))))
                                (pprinci "{\\tt{ }}" *tt-size*))
                               (t (newline-and-tab))))
                  until (atom (cdr tail)))
         (pop-tab))
        (t (pprinci "{\\tt{(}}" *tt-size*)
           (iterate for tail on term do
                    (progn (quote-printer1 (car tail))
                           (cond ((null (cdr tail))
                                  (pprinci "{\\tt{)}}" *tt-size*))
                                 ((or (atom (cdr tail))
                                    (eq (car (cdr tail))
                                        *infix-comma*)
                                    (eq (car (cdr tail))
                                        *infix-comma-atsign*)
                                    (eq (car (cdr tail))
                                        *infix-backquote*))
                                  (pprinci "{\\tt{ .\\ }}" 4)
                                  (quote-printer1 (cdr tail))
                                  (pprinci "{\\tt{)}}" *tt-size*)
                                  (return))
                                 (t (pprinci "{\\tt{ }}" *tt-size*))))
                    until (atom (cdr tail))))))
                                
(defun quote-printer (term)
  (pprinci "{\\tt{'}}" *tt-size*)
  (quote-printer1 (cadr term)))

(defun backquote-printer (term)
  (pprinci "{\\tt{`}}" *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-printer (term)
  (pprinci "{\\tt{,}}" *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-atsign-printer (term)
  (pprinci "{\\tt{,@}}" 4)
  (quote-printer1 (cadr term)))

; We arrange to read #b, #o, and #x syntax preserving what was read and to
; print it in the conventional notation whereby #o10 comes out as

;      10
;        8

; We do this by having READ fake numbers into the parse tree looking like
; function calls of the function whose name is the uninterned symbol that is
; the value of *infix-radix*, and by supplying a printer for this symbol.

; The 6 read macros for this syntax:

(defun smash-infix-readtable ()
  (iterate for c in '(#\B #\b #\O #\o #\X #\x)
           as n in '(2 2 8 8 16 16)
           for l = (case n
                         (2 '(#\0 #\1))
                         (8 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7))
                         (16 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                               #\A #\B #\C #\D #\E #\F
                               #\a #\b #\c #\d #\e #\f)))
           do
           (set-dispatch-macro-character
            #\#
            c
            (let ((l l)
                  (nn n)
                  (arithmetic-signs '(#\+ #\- #\/)))
              (function (lambda (stream char n)
                          (declare (ignore char n))
                          (list* *infix-radix* nn
                                 (iterate for ch = (read-char stream)
                                          with ll = nil
                                          do
                                          (cond ((or (member ch l)
                                                     (member ch arithmetic-signs))
                                                 (push ch ll))
                                                (t (unread-char ch stream)
                                                   (return (nreverse ll)))))))))))

; Also setup the backquote reader.

  (set-macro-character
   #\`
   #'(lambda (stream char)
       (declare (ignore char))
       (list *infix-backquote* (read stream t nil t))))
  (set-macro-character
   #\,
   #'(lambda (stream char)
       (declare (ignore char))
       (case (peek-char nil stream t nil t)
             ((#\@ #\.)
              (read-char stream)
              (list *infix-comma-atsign* (read stream t nil t)))
             (t (list *infix-comma* (read stream t nil t)))))))

(defun *infix-radix*-printer (term)
  (pprinc "${\\tt{")
  (iterate for ch in (cddr term) do (pprinci ch 2))
  (pprinc "}_{")
  (pprin1i (cadr term))
  (pprinc "}}$"))


; A FEW HAND-CODED FORM PRINTERS:  IF, COND, CASE, LET, FOR, FORALL and EXISTS.

(defun math-space (n)
  (cond (*do-not-use-tabs* (setq n 1)))
  (pprinc "$")
  (iterate for i from 1 to n do
           (pprinci "\\;"))
  (pprinc "$"))

(defun condify (term)
  (let (x u v)
    (iterate with pairs
             while (match term (if x u v))
             do
             (push (list x u) pairs)
             (setq term v)
             finally
             (progn (push (list t term) pairs)
                    (return (cons 'cond (reverse pairs)))))))

(defun if-printer (term)
  (cond-printer (condify term)))

; We take the attitude that we can print an untranslated term t as we would
; print an untranslated term t' provided that t and t' translate to the same
; term.  This point of view is to be found expressed in our treatment of nested
; if's as though they were conds.

(defun cond-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cddr term))
           (infix-print-term1 (cadr (cadr term))))
          (t (let ((cases (cdr term))
                   (first-case (car (cdr term))))
               (set-tab)
               (pprinci "{\\bf if }" 3)
               (infix-print-term1 (car first-case))
               (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
                        (advise-break (cadr first-case)))
                      (newline-and-tab))
                     (t (math-space 2)))
               (pprinci "{\\bf then }" 5)
               (infix-print-term1 (cadr first-case))
               (newline-and-tab)
               (iterate for tail on (cdr cases) do
                        (cond ((null (cdr tail))
                               (pprinci "{\\bf else }" 5)
                               (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
                                 (infix-print-term1 (cadr (car tail))))
                               (math-space 1)
                               (pprinci "{\\bf  endif}" 6)
                               (pop-tab))
                              (t (pprinci "{\\bf elseif }" 7)
                                 (infix-print-term1 (caar tail))
                                 (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
                                          (advise-break (cadar tail)))
                                        (newline-and-tab))
                                       (t (math-space 2)))
                                 (pprinci "{\\bf then }" 5)
                                 (infix-print-term1 (cadar tail))
                                 (newline-and-tab)))))))))

(defun case-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cdddr term))
           (infix-print-term1 (cadr (caddr term))))
          (t (let ((cases (cddr term))
                   (first-case (car (cddr term))))
               (set-tab)
               (pprinci "{\\bf case on }" 9)
               (infix-print-term1 (cadr term))
               (pprinci ":")
               (newline-and-tab)             
               (pprinci "{\\bf case = }" 7)
               (infix-print-term1 (car first-case))
               (newline-and-tab)
               (pprinc "{\\bf ")
               (pprinci "then }" 5)
               (infix-print-term1 (cadr first-case))
               (newline-and-tab)
               (iterate for tail on (cdr cases) do
                        (cond ((null (cdr tail))
                               (pprinci "{\\bf otherwise }" 10)
                               (infix-print-term1 (cadr (car tail)))
                               (math-space 1)
                               (let ((*rightmost-char-number* (- *rightmost-char-number* 8)))
                                 (pprinci "{\\bf  endcase}" 8))
                               (pop-tab))
                              (t (pprinci "{\\bf case = }" 6)
                                 (infix-print-term1 (caar tail))
                                 (newline-and-tab)
                                 (pprinc "{\\bf ")
                                 (math-space 2)
                                 (pprinci "then }" 5)
                                 (infix-print-term1 (cadar tail))
                                 (newline-and-tab)))))))))

(defun let-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cadr term))
           (infix-print-term1 (caddr term)))
          (t (let ((lets (cadr term)))
               (set-tab)
               (pprinci "{\\bf let }" 5)
               (set-tab)
               (iterate for tail on lets
                        for let = (car tail)
                        do
                        (infix-print-term1 (car let))
                        (pprinc "{\\bf ")
                        (math-space 1)
                        (pprinci " be" 3)
                        (math-space 2)
                        (pprinc "}")
                        (infix-print-term1 (cadr let))
                        (cond ((cdr tail)
                               (pprinci "," 1))
                              (t (pop-tab)))
                        (newline-and-tab))
               (pprinci "{\\bf in}" 3)
               (newline-and-tab)
               (let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
                 (infix-print-term1 (caddr term)))
               (math-space 1)
               (pprinci "{\\bf  endlet}" 7)
               (pop-tab))))))

(defun for-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((equal (length (cdr term)) 6)
           (let ((*top-parens-eliminable* nil))
             (default-fn-printer term)))
          (t (set-tab)
             (pprinci "{\\bf for }" 4)
             (default-atom-printer (cadr term))
             (pprinc "{\\bf ")
             (math-space 1)
             (pprinci " in }" 3)
             (infix-print-term1 (cadddr term))
             (newline-and-tab)
             (cond ((eq (fifth term) 'when)
                    (pprinci "{\\bf when }" 5)
                    (infix-print-term1 (sixth term))
                    (newline-and-tab)
                    (setq term (cddr (cddddr term))))
                   (t (setq term (cddr (cddr term)))))
             (pprinc "{\\bf ")
             (print-atom (car term))
             (pprinci "} " 1)
             (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
               (infix-print-term1 (cadr term)))
             (math-space 1)
             (pprinci "{{\\bf  endfor}}" 6)
             (pop-tab)))))

(defun forall-printer (term)
  (let (vars body)
    (match! term (forall vars body))
    (pprinci "$\\forall\\;$" *tt-size*)
    (cond ((atom vars)
           (funcall (get-atom-printer vars) vars))
          (t (iterate for tail on vars do
	              (funcall (get-atom-printer (car tail)) (car tail))
                      (cond ((cdr tail)
                             (pprinci ", " *tt-size*))))))
    (math-space 1)
    (infix-print-term1 body)))

(defun exists-printer (term)
  (let (vars body)
    (match! term (exists vars body))
    (pprinci "$\\exists\\;$" *tt-size*)
    (cond ((atom vars)
           (funcall (get-atom-printer vars) vars))
          (t (iterate for tail on vars do
    	              (funcall (get-atom-printer (car tail)) (car tail))
                      (cond ((cdr tail)
                             (pprinci ", " *tt-size*))))))
    (math-space 1)
    (infix-print-term1 body)))


;                                   *FN-ALIST*

; *fn-alist* is considerably extended via calls to make-... at the end of this
; file.  This initial value given here picks up the very few entries for which
; we have totally ad hoc handling.  Although LIST and LIST* are essentially
; macros, we handle them by the default-fn-printer, since they evaluate all
; their arguments.  We could have handled IF this default way, too.  It was
; essential that we handle QUOTE, COND, CASE, LET, and FOR specially because
; they do not evaluate all their arguments but `parse' them to some extent.

; We would like to put this at the top but have to put it after the functions
; are defined.

(defparameter *fn-alist*
  (list (list 'quote (function quote-printer))
        (list *infix-backquote* (function backquote-printer))
        (list *infix-radix* (function *infix-radix*-printer))
        (list 'if    (function if-printer))
        (list 'let   (function let-printer))
        (list 'cond  (function cond-printer))
        (list 'case  (function case-printer))
        (list 'for   (function for-printer))
        (list 'forall (function forall-printer))
        (list 'exists (function exists-printer))))

(defun get-fn-printer (sym)
  (or (symbolp sym)
      (error "Illegal object where function symbol expected: ~a." sym))
  (let ((a (assoc sym *fn-alist*)))
    (cond (a (cadr a))
          (t (function default-fn-printer)))))

(defun default-fn-printer (term)

; This function is a good function to study if one finds it necessary to define
; by hand a special handler for a function symbol.  We annotate rather
; verbosely as a pedagogical device.

; In general, we know that term is a lisp object on which TRANSLATE does not
; cause an error.

; Binding *top-parens-eliminable* is a sign to the infix, prefix, and suffix
; operators immediately below that we are putting out syntactic noise (e.g.,
; commas) that is so strong that they need not emit an initial outer layer of
; parentheses.

  (let ((*top-parens-eliminable* t)
        (advice (advise-break term)))

    (cond ((atom (car term))

; First put out the function symbol, in roman.
; Functions of no arguments are printed as constants, without parentheses,
; rather than with, e.g., foo().

           (cond ((null (cdr term))
                  (pprinc "{")
                  (pprinc *constant-font*)
                  (pprinc "{")
                  (print-atom (car term))
                  (pprinc "}}")
                  (return-from default-fn-printer nil)))

; We want a very tiny space in front of the open parenthesis because otherwise,
; it looks like some function symbols touch the open parenthesis.  In some
; cases, this results in a touch more space than we like, and perhaps there
; exists a more delicate kerning command.

           (pprinc "{\\rm{")
           (print-atom (car term))
           (pprinc "}}")
           (pprinci "\\,("))
          (t (pprinci "(")
             (setq term (cons 'foo term))))
    (cond ((null (cdr term))
           (pprinci ")"))
          ((null (cddr term))
           (infix-print-term1 (cadr term))
           (pprinci ")"))

; The coder of the printer for each function should consider whether to print
; flat or not, by calling advise-break.  This is a somewhat aesthetic and
; heuristic decision.

          (advice

; If it is decided not to print flat, one needs somewhere early to set a tab
; stop to which to return.

           (set-tab)
           (iterate for tail on (cdr term)
                    do
                    (progn (infix-print-term1 (car tail))
                           (cond ((cdr tail)
                                  (pprinci ",")

; Each call of newline-and-tab will return to the tab we set.

                                  (newline-and-tab))
                                 (t (pprinci ")")

; Now we get rid of the tab.

                                    (pop-tab))))))
          (t
           (iterate for tail on (cdr term)
                    do
                    (progn (infix-print-term1 (car tail))
                           (cond ((cdr tail)
                                  (pprinci ", "))
                                 (t (pprinci ")")))))))))


;                                    BREAKS

(defun advise-break (term)

; advise-break is the only place that *testing* is bound, and here it is bound
; to t, meaning that we want no printing, just want to know if we can print
; term flat.  We also bind, just to restore, the current *infix-loc* and
; *tab-list*.

; This first cond is only for debugging purposes.  Same for the second value
; of the prog1.

  (cond (*tracing-advise-break*
         (format *terminal-io* "~%Entering *infix-loc* = ~a, *testing* = ~a~%" *infix-loc* *testing*)))
  (prog1
      (let ((*infix-loc* *infix-loc*)
            (*tab-list* *tab-list*))
        (cond (*testing* nil)
              (t (catch 'advise-break
                   (let ((*testing* t))
                     (infix-print-term1 term)
                     nil)))))
    (cond (*tracing-advise-break*
           (format *terminal-io* "~%Exiting *infix-loc* = ~a~%" *infix-loc*)))))

(defun advise-break-if-testing ()

; A printer function that is sure that it will break should short circuit the
; expense of calculating whether printing flat is ok.

  (cond (*testing*
         (throw 'advise-break t))))

(defun do-not-index-call-of (fn)
  (or *do-not-index-calls*
      (propertyless-symbolp fn)
      (eq 'ground-zero (get fn 'main-event))
      (member fn *do-not-index-calls-of*)))
      
(defun index-call (fn)
  (cond (*testing* nil)
        ((do-not-index-call-of fn) nil)
        (t (index fn))))

(defun infix-print-term1 (term)
  (cond ((atom term)
         (funcall (get-atom-printer term) term))
        (t (funcall (get-fn-printer (car term))
                    term)
           (index-call (car term)))))

(defun infix-print-term (term)
  (pwrite-char #\Newline)
  (setq *infix-loc* *left-margin*)
  (infix-print-term1 term)
  (pwrite-char #\Newline)
  (setq *infix-loc* *left-margin*)
  nil)

(defun default-infix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (cond ((and advice

; We hate to see (member x (foo ...)) broken right after the x, where
; x is an atom.

                (not (and (equal (length term) 3)
                          (atom (cadr term)))))
           (set-tab)
           (iterate for tail on (cdr term)
                    do
                    (progn (infix-print-term1 (car tail))
                           (cond ((cdr tail)
                                  (newline-and-tab)
                                  (if *infix-wide* (math-space 5))
                                  (pprinci op 3)
                                  (cond (*infix-wide*
                                         (newline-and-tab))
                                        (t (math-space 4))))
                                 (t (cond ((null top-parens-were-eliminable)
                                           (pprinci ")")))
                                    (pop-tab))))))
          (t
           (iterate for tail on (cdr term)
                    do
                    (progn (infix-print-term1 (car tail))
                           (cond ((cdr tail)
                                  (pprinci " ")
                                  (pprinci op 3)
                                  (pprinci " "))
                                 (t (cond ((null top-parens-were-eliminable)
                                           (pprinci ")")))))))))))

(defun default-unary-prefix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (pprinci op 3)
    (pprinci " ")
    (infix-print-term1 (cadr term))
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-infix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-tab)
    (infix-print-term1 (cadr term))
    (iterate for arg in (cddr term)
             as str in strs do
             (cond (advice (newline-and-tab))
                   (t (pprinci " ")))
             (pprinci str)
             (cond (advice (newline-and-tab))
                   (t (pprinci " ")))
             (infix-print-term1 arg))
    (pop-tab)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-prefix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-tab)
    (iterate for tail on (cdr term)
             as str in strs do
             (pprinci str)
             (cond (advice (newline-and-tab))
                   (t (pprinci " ")))
             (infix-print-term1 (car tail))
             (cond ((null (cdr tail)) nil)
                   (advice (newline-and-tab))
                   (t (pprinci " "))))
    (pop-tab)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-unary-suffix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (infix-print-term1 (cadr term))
    (pprinci " ")
    (pprinci op 3)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))
        
(defun default-unary-abs-printer (term lhs-str rhs-str)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* nil))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (pprinci lhs-str)
    (pprinci " ")
    (infix-print-term1 (cadr term))
    (pprinci " ")
    (pprinci rhs-str)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))


;                            PRINTING INDEX ENTRIES

; Who could ever have guessed that it would take this much code to print out a
; simple \index{foo} command for an arbitrary Nqthm function symbol foo.  There
; are so many special cases one can hardly believe one's eyes.

(defparameter index-subitem-length 30)

(defparameter nqtex2tex-chars
  (coerce "eipqtv" 'list))

(defun index (x)

#|
; Yuk city on quotations of weird characters.

See the latex guide to indexes,
tex3.0/TeX3.0/LaTeX/LaTeXmakeindex/doc/makeindex.tex.  The characters vertical
bar, @, and ! are used within index strings, and need to be quoted with a
single double quote mark.

Also, it looks like makeindex chokes on index entries of more than 64
characters, in the sense that after 64, things suddenly become subitems, which
is a good way to get screwed if there are weird characters in the first 64 that
need quoting or balancing.

|#

  (pprinc "\\index{")
  (let ((str (symbol-name x))
        (num-chars 0)
        (inserted-excl nil))
    (iterate with brace-count = 0
             for i below (length str)
             for char = (char (the string str) (the fixnum i))
             until (> num-chars *index-entry-max*)
             do
             (progn
               (cond ((and (> num-chars index-subitem-length)
                           (not inserted-excl)
                           (not (member char nqtex2tex-chars :test #'equalp))
                           (= brace-count 0))

; There is some sort of a bug in the Latex indexing machinery whereby if an
; entry has more than 64 characters, a `subitem' is automatically started.  But
; this may happen in a bad place, in terms of character quotation, so we force
; a subitem earlier, at our convenience.

                      (pwrite-char #\!)
                      (setq inserted-excl t)))

; It is a tad subtle getting a caret printed.

               (cond ((eql char #\^)
                      (pprinc "\\char'136")
                      (incf num-chars 8))

; If braces are not balanced, the index machinery will barf, so we keep track
; and try to help out later, if we can.

                     ((eql char #\{)
                      (incf brace-count 1)
                      (pwrite-char #\\)
                      (pwrite-char char)
                      (incf num-chars 2))
                     ((eql char #\})
                      (decf brace-count 1)
                      (pwrite-char #\\)
                      (pwrite-char char)
                      (incf num-chars 2))

; There are the special characters like @ which have a special meaning just in
; Latex indexing, and they have to be quoted their own special way.

                     ((member char latex-index-specials)
                      (pwrite-char #\")
                      (pwrite-char char)
                      (incf num-chars 2))

; And of course, one has to watch our for such standard special TeX characters
; as $.

                     ((member char tex-special-chars)
                      (pwrite-char #\\)
                      (pwrite-char char)
                      (incf num-chars 2))

; If one tries to set an ordinary < or >, it won't work, and just quoting with
; backslash doesn't work either, so we sneak into math mode.

                     ((member char tex-other-chars)
                      (pwrite-char #\$)
                      (pwrite-char char)
                      (pwrite-char #\$)
                      (incf num-chars 3))
                     (t (pwrite-char (cond ((eq *print-case* :downcase)
                                            (char-downcase char))
                                           (t char)))
                        (incf num-chars 1)))
               (cond ((< brace-count 0)
                      (pformat *terminal-io*
                               "~% Error: The index entry for ~a will ~
                                fail because of the imbalance of set ~
                                braces.~%"
                               x))))
             finally
             (progn
                (cond ((> num-chars *index-entry-max*)
                       (pformat *terminal-io*
                                "~% Warning: Index entry for ~a truncated to ~a characters. ~%"
                                 x num-chars)
                       (pprinc "...")))
                (cond ((not (equal brace-count 0))
                       (cond ((> brace-count 0)
                              (iterate for i from 1 to brace-count do
                                       (pprinc "\\}"))))
                       (pformat *terminal-io*
                                "~%Warning:  Balancing set braces on ~
                                 ~a so Latex indexing will work.~%"
                                x))))))
  (pprinc "}"))


;                                EVENT PRINTERS

(defun print-default-event-header ()
  (pformat *standard-output* "~%\\noindent{\\sc Event}:   "))

(defun no-tab-event-trailer ()
  (pformat *standard-output* "~%~%\\addvspace{18pt}"))

(defun default-event-printer (event)
  (begin-tabbing)
  (print-default-event-header)
  (pprinc "  \\\\ The fact that we do not do a better job printing 
            this event means that this event is of type unknown to us. \\\\ ")
  (quote-printer1 event)
  (end-tabbing))

(defun boot-strap-printer (term)
  (print-default-event-header)
  (pformat *standard-output*
          "Start with the initial {\\bf ~a} theory."
          (case (cadr term)
                ((thm nil) "thm")
                (nqthm "nqthm")))
  (no-tab-event-trailer))

(defun compile-uncompiled-defns-printer (term)
  (declare (ignore term))
  (print-default-event-header)
  (pprinc "For efficiency, compile those definitions not yet compiled.")
  (no-tab-event-trailer))

(defun prove-lemma-printer (term)
  (begin-tabbing)
  (pprinc "{\\sc Theorem}:  ")
  (print-atom (cadr term))
  (pprinc " \\\\ ")
  (index (cadr term))
  (infix-print-term (cadddr term))
  (end-tabbing))

(defun add-axiom-printer (term)
  (begin-tabbing)
  (pprinc "{\\sc Axiom}:  ")
  (print-atom (cadr term))
  (pprinc " \\\\ ")
  (index (cadr term))
  (infix-print-term (cadddr term))
  (end-tabbing))

(defun dcl-printer (term)
  (print-default-event-header)
  (pprinc "Introduce the function symbol {\\it ")
  (print-atom (cadr term))
  (index (cadr term))
  (cond ((equal 1 (length (caddr term)))
         (pprinc "\\/} of one argument."))
        (t (pformat *standard-output*
                   "\\/} of ~a arguments."
                   (length (caddr term)))))
  (no-tab-event-trailer))

(defun constrain-printer (term)
  (begin-tabbing)
  (pprinc "{\\sc Conservative Axiom}:  ")
  (print-atom (cadr term))
  (pprinc " \\\\ ")
  (index (cadr term))
  (infix-print-term (cadddr term))
  (end-tabbing)
  (let ((wa (car (cddddr term))))
    (cond (wa
           (pprinc "\\noindent Simultaneously, we introduce")
           (cond ((null (cdr wa))
                  (pprinc " the new function symbol {\\it ")
                  (print-atom (caar wa))
                  (pprinc "\\/}."))
                 ((null (cddr wa))
                  (pprinc " the new function symbols {\\it ")
                  (print-atom (caar wa))
                  (pprinc "\\/} and {\\it ")
                  (print-atom (caadr wa))
                  (pprinc "\\/}."))
                 ((null (cddr wa))
                  (pprinc " the new function symbols {\\it ")
                  (print-atom (caar wa))
                  (pprinc "\\/} and {\\it")
                  (print-atom (caadr wa))
                  (pprinc "\\/}."))
                 (t (pprinc " the new function symbols {\\it ")
                    (iterate for tail on wa do
                             (print-atom (caar tail))
                             (cond ((cdr tail)
                                    (pprinc "\\/}, ")
                                    (cond ((null (cddr tail))
                                           (pprinc "and ")))
                                    (pprinc "{\\it "))))
                    (pprinc "\\/}.")))))))

(defun defn-printer1 (term equiv)
  (let ((eq (list equiv (cons (cadr term) (caddr term))
                  (cadddr term))))
    (begin-tabbing)
    (pprinci "{\\sc Definition}:" 12)
    (index (cadr term))
    (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
             (advise-break eq))
           (pprinc " \\\\  "))
          (t (math-space 2)))
    (infix-print-term eq)
    (end-tabbing)))

(defun defn-printer (term)
  (defn-printer1 term 'equal))

(defun defn-sk-printer (term)
  (defn-printer1 term 'iff))

(defun disable-printer (term)
  (print-default-event-header)
  (pprinc "Disable ")
  (print-atom (cadr term))
  (pprinc ".")
  (no-tab-event-trailer))

(defun enable-printer (term)
  (print-default-event-header)
  (pprinc "Enable ")
  (print-atom (cadr term))
  (pprinc ".")
  (no-tab-event-trailer))

(defun make-lib-printer (term)
  (print-default-event-header)
  (pprinc "Make the library ")
  (print-atom (cadr term))
  (cond ((caddr term)
         (pprinc " and compile it."))
        (t (pprinc ".")))
  (no-tab-event-trailer))

(defun note-lib-printer (term)
  (print-default-event-header)
  (pprinc "Start with the library ")
  (print-atom (cadr term))
  (cond ((caddr term)
         (pprinc " using the compiled version."))
        (t (pprinc ".")))
  (no-tab-event-trailer))

(defun add-shell-printer (term)
  (let (name btm recog trips accs trs dvs)
    (match term (add-shell name btm recog trips))
    (setq accs (iterate for x in trips collect (car x)))
    (setq trs (iterate for x in trips collect (cadr x)))
    (setq dvs (iterate for x in trips collect (caddr x)))
    (print-default-event-header)
    (pprinc "Add the shell ")
    (default-atom-printer name)
    (index name)
    (cond (btm (pprinc ", with bottom object function symbol ")
               (default-atom-printer btm)))
    (pprinc ", with recognizer function symbol ")
    (default-atom-printer recog)
    (cond (btm (pprinc ",")))
    (pprinc " and")
    (cond ((null dvs) (pprinc " no accessors."))
          ((null (cdr accs)) (pprinc " 1 accessor: "))
          (t (pformat *standard-output* " ~s accessors: " (length trips))))
    (iterate for ac in accs as tr in trs as dv in dvs as i from 1 do
             (default-atom-printer ac)
             (pprinc ", with type restriction ")
             (pprinc tr)
             (pprinc " and default value ")
             (print-atom dv)
             (cond ((= i (length trips))
                    (pprinc "."))
                   (t (pprinc "; ")))))
  (no-tab-event-trailer))
    
(defun toggle-printer (term)
  (let (name oldname flg)
    (match term (toggle name oldname flg))
    (print-default-event-header)
    (cond (flg
           (pprinc "Enable ")
           (print-atom oldname)
           (pprinc "; name this event `")
           (print-atom name)
           (pprinc "'."))
          (t
           (pprinc "Disable ")
           (print-atom oldname)
           (pprinc "; name this event `")
           (print-atom name)
           (pprinc "'.")))
    (index name))
  (no-tab-event-trailer))

(defun toggle-defined-functions-printer (term)
  (let (name flg)
    (match term (toggle-defined-functions name flg))
    (print-default-event-header)
    (cond (flg
           (pprinc "Enable defined functions; name this event `")
           (print-atom name)
           (pprinc "'."))
          (t
           (pprinc "Disable defined functions; name this event `")
           (print-atom name)
           (pprinc "'.")))
    (index name))
  (no-tab-event-trailer))

(defun ubt-printer (term)
  (print-default-event-header)
  (cond ((null (cdr term))
         (pprinc "Undo the last event."))
        (t (pprinc "Undo back through the event named `")
           (print-atom (cadr term))
           (pprinc "'.")))
  (no-tab-event-trailer))

(defun deftheory-printer (term)
  (print-default-event-header)
  (let (name eventnames)
    (match term (deftheory name eventnames))
    (pprinc "Let us define the theory {\\it{")
    (print-atom name)
    (pprinc "}} to consist of the following events: ")
    (iterate for tail on eventnames do
             (print-atom (car tail))
             (cond ((cdr tail)
                    (pformat *standard-output* ",~%"))))
    (pprinc ".")
    (index name))
  (no-tab-event-trailer))

(defun set-status-printer (term)
  (let (name names alist)
    (match term (set-status name names alist))
    (print-default-event-header)
    (pprinc "Set the status of ")
    (cond ((eq names t)
           (pprinc "all events"))
          ((and names (symbolp names))
           (pprinc "the events in the theory ")
           (print-atom names))
          ((and (symbolp (cdr names))
                (cdr names))
           (pprinc "the events between ")
           (print-atom (car names))
           (pprinc " and ")
           (print-atom (cdr names)))
          (t (pprinc "these events: ")
             (iterate for tail on names do
                      (print-atom (car tail))
                      (cond ((cdr tail)
                             (pformat *standard-output* ",~%"))))))
    (pprinc ".  ")
    (pprinc "The status of each event is to be set as follows.  ")
    (iterate for pair in alist do
             (case (car pair)
                   (boot-strap
                    (pprinc "Each `boot-strap' satellite is to be "))
                   (add-shell
                    (pprinc "Each `add-shell' satellite is to be "))
                   (*1*defn
                    (pprinc "Each `*1* function' is to be "))
                   ((add-axiom prove-lemma constrain functionally-instantiate)
                     (pformat *standard-output* "Each `~a' is to be " (car pair)))
                   ((otherwise)
                    (pprinc "Anything not otherwise mentioned is to be ")))
             (case (cadr pair)
                   ((enable) (pprinc "enabled.  "))
                   ((disable) (pprinc "disabled.  "))
                   ((as-is) (pprinc "left ``as-is''.  "))
                   ((initial) (pprinc "returned to the initial condition.  "))))
    (pprinc " Name this event `")
    (print-atom name)
    (pprinc "'.")
    (index name))
  (no-tab-event-trailer))

(defun disable-theory-printer (term)
  (print-default-event-header)
  (pprinc "Disable theory ")
  (cond ((atom (cadr term))
         (print-atom (cadr term))
         (pprinc "."))
        (t (pprinc "\{")
           (iterate for tail on (cadr term) do
                    (print-atom (car tail))
                    (cond ((cdr tail)
                           (pprinc ", "))))
           (pprinc "\}.")))
  (no-tab-event-trailer))

(defun enable-theory-printer (term)
  (print-default-event-header)
  (pprinc "Enable theory ")
  (print-atom (cadr term))
  (cond ((atom (cadr term))
         (print-atom (cadr term))
         (pprinc "."))
        (t (pprinc "\{")
           (iterate for tail on (cadr term) do
                    (print-atom (car tail))
                    (cond ((cdr tail)
                           (pprinc ", "))))
           (pprinc "\}.")))
  (no-tab-event-trailer))

(defun setq-printer (term)
  (print-default-event-header)
  (let (name value)
    (match term (setq name value))
    (pformat *standard-output* "Give the Nqthm control variable {\\tt ~a} the value {\\tt ~s}." name value))
  (no-tab-event-trailer))

; We would like to put this at the top.

(defparameter *event-printer-alist*
  (list (list 'setq (function setq-printer))
        (list 'deftheory (function deftheory-printer))
        (list 'disable-theory (function disable-theory-printer))
        (list 'enable-theory (function enable-theory-printer))
        (list 'set-status (function set-status-printer))
        (list 'ubt (function ubt-printer))
        (list 'toggle-defined-functions (function toggle-defined-functions-printer))
        (list 'toggle (function toggle-printer))
        (list 'add-shell (function add-shell-printer))
        (list 'dcl (function dcl-printer))
        (list 'disable (function disable-printer))
        (list 'enable (function enable-printer))
        (list 'prove-lemma (function prove-lemma-printer))
        (list 'lemma (function prove-lemma-printer))
        (list 'add-axiom (function add-axiom-printer))
        (list 'axiom (function add-axiom-printer))
        (list 'constrain (function constrain-printer))
        (list 'functionally-instantiate (function prove-lemma-printer))
        (list 'defn (function defn-printer))
        (list 'defn-sk (function defn-sk-printer))
        (list 'defn-sk+ (function defn-sk-printer))
        (list 'compile-uncompiled-defns (function compile-uncompiled-defns-printer)) 
        (list 'boot-strap (function boot-strap-printer))
        (list 'note-lib (function note-lib-printer))
        (list 'make-lib (function make-lib-printer))))

(defun get-event-printer (sym)
  (let ((a (assoc sym *event-printer-alist*)))
    (cond (a (cadr a))
          (t (function default-event-printer)))))


;                           COPY COMMENTS

(defun wrap-up-copy-comments ()
  (cond (*started-a-verbatim* (pformat *standard-output* "\\end{verbatim}")))
  (throw 'copy-comments nil))

(defun end-verbatim-and-write (c)
  (cond (*started-a-verbatim*
         (pformat *standard-output* "\\end{verbatim}")
         (setq *started-a-verbatim* nil)))
  (pwrite-char c))

(defun chk-verbatim-and-write (c)

; Note: Latex causes an error on an empty verbatim environment, so we watch out
; for that as a special case.  Also, Latex forbids control-l in a verbatim
; environment, so we watch out for that, too.

       (cond  ((and (not *started-a-verbatim*)
                    (not (member c *white-space*)))
               (pformat *standard-output* "\\begin{verbatim}")
               (setq *started-a-verbatim* t)))
       (cond ((and *started-a-verbatim*
                   (eql c #\Tab)
                   (not *reported-tabs*))
              (setq *reported-tabs* t)
              (pformat *terminal-io* 
                 "WARNING: about tabs!~%We note the presence of a tab ~
                  in a comment that we are copying~%into a verbatim ~
                  environment.  Tabs will be treated just like ~%single spaces ~
                  by Latex.  Consider removing all tabs, e.g., ~%with the ~
                  Emacs command M-x untabify.~%")))
       (cond ((and *started-a-verbatim*
                   (eql c #\Page))
              (pformat *standard-output* "\\end{verbatim}~%\\newpage~%\\begin{verbatim}~%"))
             (t (pwrite-char c))))

(defun copy-comments-read-char ()
       (let ((c (read-char *copy-comments-in-file* nil a-very-rare-cons)))
         (cond ((eq c a-very-rare-cons)
                (wrap-up-copy-comments))
               (t c))))

(defun copy-comments (*copy-comments-in-file*)

; This function tries to sneak up to the next top-level open parenthesis,
; parsing all of the Lisp comments up till there.

  (let ((*started-a-verbatim* nil))
    (catch 'copy-comments
      (iterate for ch = (copy-comments-read-char)

; The top level loop for simulating the skimming of whitespace and comments
; that READ would perform to get to the next open parenthesis.

               (case ch

; Semicolon starts a comment.  If the semicolon is followed by a backslash, then
; we treat the rest of the line as Latex rather than putting it into a verbatim.

                     (#\;
                      (setq ch (copy-comments-read-char))
                      (cond ((eql ch #\\)
                             (iterate for ch = (copy-comments-read-char)
                                      do
                                      (end-verbatim-and-write ch)
                                      (cond ((eql ch #\Newline)
                                             (return)))))
                            (t (chk-verbatim-and-write #\;)
                               (unread-char ch *copy-comments-in-file*)
                               (iterate for ch = (copy-comments-read-char)
                                        do
                                        (chk-verbatim-and-write ch)
                                        (cond ((eql ch #\Newline)
                                               (return)))))))

; #| starts a comment.  If the #| is followed by a backslash, then we treat the
; rest of the comment as Latex rather than putting it into a verbatim.

                     (#\#
                      (setq ch (copy-comments-read-char))
                      (cond ((not (eql ch #\|))
                             (error "Do not know how to handle #~s while copying at the top level." ch)))
                      (setq ch (copy-comments-read-char))
                      (cond ((eql ch #\\)
                             (iterate for ch = (copy-comments-read-char)
                                      with number-deep = 1 do
                                      (cond ((eql ch #\|)
                                             (let ((ch (copy-comments-read-char)))
                                               (cond ((eql ch #\#)
                                                      (decf number-deep 1)
                                                      (cond ((= number-deep 0)
                                                             (return))
                                                            (t (end-verbatim-and-write #\|)
                                                               (end-verbatim-and-write #\#))))
                                                     (t (end-verbatim-and-write #\|)
                                                        (unread-char ch *copy-comments-in-file*)))))
                                            ((eql ch #\#)
                                             (end-verbatim-and-write #\#)
                                             (let ((ch (copy-comments-read-char)))
                                               (cond ((eql ch #\|)
                                                      (incf number-deep 1)
                                                      (end-verbatim-and-write #\|))
                                                     (t (unread-char ch *copy-comments-in-file*)))))
                                            (t (end-verbatim-and-write ch)))))
                            (t (chk-verbatim-and-write #\#)
                               (chk-verbatim-and-write #\|)
                               (unread-char ch *copy-comments-in-file*)
                               (iterate for ch = (copy-comments-read-char)
                                        with number-deep = 1 do
                                        (progn
                                          (chk-verbatim-and-write ch)
                                          (cond ((eql ch #\|)
                                                 (let ((ch (copy-comments-read-char)))
                                                   (cond ((eql ch #\#)
                                                          (chk-verbatim-and-write ch)
                                                          (decf number-deep 1)
                                                          (cond ((= number-deep 0) (return))))
                                                         (t (unread-char ch *copy-comments-in-file*)))))
                                                ((eql ch #\#)
                                                 (let ((ch (copy-comments-read-char)))
                                                   (cond ((eql ch #\|)
                                                          (chk-verbatim-and-write ch)
                                                          (incf number-deep 1))
                                                         (t (unread-char ch *copy-comments-in-file*)))))))))))
                     (#\(
                      (unread-char #\( *copy-comments-in-file*)
                      (wrap-up-copy-comments))
                     (otherwise (chk-verbatim-and-write ch)))))))

(defun infix-form (form &key ((:print-case *print-case*) :downcase))
  (let ((*top-parens-eliminable* t)
        (*print-pretty* nil))
    (cond ((catch 'taboverflow
             (let ((*tabs-in* 1))
               (or *do-not-use-tabs* (begin-tabbing))
               (infix-print-term1 form)
               (or *do-not-use-tabs* (end-tabbing))
               nil))
           (pformat *terminal-io* "~%Sorry.  Exceeded Latex tabbing limit.~%
                                ~%Use the normal pretty printer on that one.~%~%"
                   form))))
  nil)

(DEFUN PPE-LATEX (NAME)
  (ITERPRI NIL)
  (COND ((OR (NOT (SYMBOLP NAME))
             (AND (NOT (GET NAME 'EVENT))
                  (NOT (GET NAME 'MAIN-EVENT))))
         (PPR (CONS (QUOTE *****)
                    (CONS NAME
                          (QUOTE (|is| |neither| |an|
                                  |event| |nor|
                                  |satellite|))))
              NIL))
        ((GET NAME 'EVENT)
         (infix-event (UNTRANSLATE-EVENT (GET NAME 'EVENT))))
        (T
         (COND ((GET NAME 'SDEFN)

; The only symbols with SDEFNs that are not DEFNs are the DEFN0s of BOOT-STRAP.
; We recover the original DEFN0 form and represent it as an event, because it
; is prettier than the SDEFN.  (Compare the SDEFN of 'PLUS with what we print.)

                (infix-event (ITERATE
                      FOR X IN BOOT-STRAP-INSTRS
                      WHEN
                      (OR (AND (EQ (CAR X) 'DEFN0)
                               (EQ (CADR X) NAME))
                          (AND (MEMBER-EQ (CAR X)
                                          '(IF-NQTHM-MODE IF-NOT-NQTHM-MODE))
                               (EQ (CAR (CADR X)) 'DEFN0)
                               (EQ (CADR (CADR X)) NAME)))
                      DO

; All uses of DEFN0 in BOOT-STRAP-INSTRS have the TRANSLATE-FLG set to T,
; meaning that the body provided in the DEFN0 is in untranslated form.  Thus,
; we do not translate these forms.

                      (RETURN
                       (COND ((EQ (CAR X) 'DEFN0)
                              (LIST 'DEFN (CADR X) (CADDR X) (CADDDR X)))
                             (T (LIST 'DEFN (CADR (CADR X))
                                      (CADDR (CADR X))
                                      (CADDDR (CADR X))))))
                      FINALLY
                      (ER HARD (NAME)
                          |It| |was| |thought| |that| |the| |only|
                          |satellites| |that| |had| |SDEFNs| |were|
                          |defined| |on| BOOT-STRAP-INSTRS |with|
                          |a| DEFN0 |but| (!PPR NAME NIL) |is| |an|
                          |example| |to| |the| |contrary| |.|)))
                (ITERPRI NIL)
                (ITERPRI NIL)))
         (PPR (LIST (QUOTE *****) NAME (QUOTE |is|)
                    (QUOTE |a|) (QUOTE |satellite|) (QUOTE |of|)
                    (UNTRANSLATE-EVENT
                     (GET (GET NAME (QUOTE MAIN-EVENT))
                          (QUOTE EVENT))))
              NIL)))
  (ITERPRI NIL))
  
(defun infix-event (form &key ((:print-case *print-case*) :downcase))
  (let ((*top-parens-eliminable* t)
        (*print-pretty* nil))
    (cond ((catch 'taboverflow
             (let ((*tabs-in* 1))
               (funcall (get-event-printer (car form)) form)
               nil))
           (pformat *terminal-io* "~%Sorry.  Exceeded Latex tabbing limit.~%
                                ~%Use the normal pretty printer on that one.~%~%"
                   form)))))

(defun infix-file (fl &key ((:print-case *print-case*) :downcase)
                      (chars-wide 77)
                      (suppress-prelude nil)
                      (nq nil))

; infix-file takes a root file name, e.g., foo, reads the file foo.events,
; which we suppose has been previously checked by prove-file, and creates the
; file foo.tex, which the user can then run through Latex, etc.  By default, we
; lowercase all variable and function symbols, but the user can override this
; with the keyword parameter.


; If the keyword nq is given as true, then we first generate fl.nqtex, and then
; invoke nqtex2tex, generating fl.tex.

  (let ((infl (extend-file-name fl file-extension-events))
        (outfl (extend-file-name fl (if nq "nqtex" "tex")))
        (a-very-rare-cons (cons nil nil))
        (*print-pretty* nil)
        (*top-parens-eliminable* t)
        (*readtable* (copy-readtable nil))
        (*reported-tabs* nil)
        (*left-margin* 0)
        (error-flg t)
        (*rightmost-char-number* chars-wide))
    (smash-infix-readtable)
    (with-open-file
     (instr infl :direction :input)
     (unwind-protect
         (with-open-file

; We do *all* of our printing of terms to *standard-output*, giving princ only
; one argument.

          (*standard-output* outfl :direction :output :if-exists :rename-and-delete)

; The Latex opening.

          (or suppress-prelude
              (pformat *standard-output*
                       "\\documentstyle[makeidx]{article}~%~
               \\makeindex~%~
               %\\setlength{\\oddsidemargin}{.5in}~%~
               %\\setlength{\\evensidemargin}{.5in}~%~
               %\\setlength{\\textwidth}{5.8in}~%~
               \\begin{document}~%~
               %\\setlength{\\parindent}{0pt}~%~
               %\\newcounter{bean}~%~
               %\\begin{list}{\\arabic{bean}.}~
               {\\usecounter{bean}~
                \\setlength{\\leftmargin}{0pt}~
                \\setlength{\\rightmargin}{0pt}~
                \\setlength{\\listparindent}{20pt}~
                \\setlength{\\parsep}{5pt}}~
               ~%%\\item[]~%~%"))

          (iterate for inpos = (file-position instr)
                   for form = (progn (copy-comments instr)
                                     (read instr nil a-very-rare-cons))

; We remember where we are in the output file as part of our mechanism for
; recovering from the very small finiteness of the Latex tabbing mechanism.  We
; will rewrite to the current position and start printing in verbatim mode with
; PPR if we exceed the Latex tabbing mechanism.

                   for outpos = (file-position *standard-output*)
                   until (eq form a-very-rare-cons)
                   do
; (pformat *standard-output* "\\filbreak %\\item~%")
                   (cond ((or (eq (car form) 'comment)
                              (cond ((catch 'taboverflow
                                       (let ((*tabs-in* 1))
                                         (funcall (get-event-printer (car form)) form))
                                       nil)
                                     (pformat *terminal-io* "~%Warning: Latex tab limit reached in event ~a.~
                                             ~%Just copying that one.~%~%"
                                              (cadr form))
                                     t)))
                          (file-position *standard-output* outpos)
                          (pformat *standard-output* "%\\item ~%\\begin{verbatim}~%")
                          (let ((stop (file-position instr))
                                (*started-a-verbatim* t))
                            (file-position instr inpos)
                            (iterate while (< (file-position instr) stop)
                                     do (chk-verbatim-and-write (read-char instr))))
                          (pformat *standard-output* "~%\\end{verbatim}~%"))
                         (t nil))
                   #|(pprinc "\\filbreak")|#)
          (or suppress-prelude
              (pformat *standard-output*
                       "~%%\\end{list}~%~
                      \\printindex~%~
                      \\end{document}~%"))
          (setq error-flg nil))
       (if error-flg
           (format *terminal-io* "Error encountered at location ~a of file ~a."
                   (file-position instr) infl)))))
    (if nq (nqtex2tex fl))
    fl)

(defparameter nqtex-white-space '(#\Space #\Newline #\Tab #\Page #\Return))

(defparameter nqtex-normal-clause-enders '(#\. #\! #\? #\, #\; #\:))

(defparameter nqtex-break-chars '(#\( #\) #\` #\' #\" #\; #\,))

(defun nqthm-read-preserving-whitespace-error (instr)
  (error "A character for an integer or an Nqthm symbol was expected~
          ~%at location ~a of input."
         (file-position instr)))

(defun nqthm-read-preserving-whitespace (instr)

; This function does the READing right after a ! command.  This
; function is almost the same as read-preserving-whitespace.  It is
; different only because of the peculiar problem of trailing
; punctuation marks.  We sometimes stop the reading before Common Lisp
; would.

; In processing ! commands, we call READ on the following text.  If
; the text starts with an open parenthesis or string-quote, it is
; clear where the READing should stop.  However, if a mere symbol or
; number follows a ! command, then when READing the symbol we treat
; an exclamation mark, colon, question mark, or period that is
; followed by whitespace as a punctuation mark, not as part of the
; symbol that is to be READ.  The other ordinary English clause ending
; punctuation characters (comma and semicolon) already naturally
; terminate a READ, as do parentheses, quotation marks, and
; whitespace.

; Example.  When we do a READ while processing a ! command under
; nqtex2tex, we have to decide what to do about text such as

;    !tnil.

; The question is, does the period belong to the token to be read, or
; is it just some user punctuation?  We take the attitude that the
; answer is punctuation.  Now, this attitude is a bit arbitrary.  nil.
; is a legal Common Lisp symbol.  BUT it is not a legal Nqthm symbol.
; In Nqthm, a symbol may not contain a period.  One might ask, who
; cares?  The reason we care is that nil, and other symbols on
; *atom-alist*, get printed specially.  For example, nil is printed in
; bold, not italics.  If we read nil. as one symbol, it would come out
; in intalics because nil. is not on *atom-alist*.

; The idea of fiddling with READ so that it is `smart' about not
; reading a trailing punctuation character is weird.  But then,
; calling READ in the middle of Tex file is weird, too.  We have found from
; experience that it is very hard to write sentences that have
; whitespace after every symbol.  We want to be able to write things
; like !tnil, and !tnil.  So here is the general procedure for how far
; we READ after a ! command.  When we say READ below, we really mean
; read-preserving-whitespace.

; We peek at the first nonwhitespace character after the ! command,
; and we consider the cases on this character.

; If it is ( or " we simply call READ, knowing that upon encountering
; the closing " or ) READ will not look at any trailing punctuation.

; If it is ' or ` we recursively read further with this function and
; then quote or backquote the result.  This is so that `foo. will come
; out right.

; Otherwise, we call READ on the string consisting of all of the
; characters up to but not including the first (a) whitespace, (b)
; terminating readmacro Common Lisp character, i.e., ()`'"";,, or (c)
; normal English clause ending character, i.e., .!?:, that is followed
; by a whitespace.

; Known ambiguity.  Although periods are permitted at the ends of
; numbers in Nqthm syntax, we treat them as ends of sentences, if they
; are followed by white space.  Thus in reading !t5. , the read
; would not pick up the period.  So the period would appear in the
; final text.  It is hard to see whether this is a bug, a feature, or
; a problem that simply never arises.

; Known ambiguity.  Because the quotation mark is a legal character
; in Nqthm symbols, a minor question arises about the handling of
; a terminal question mark in an Nqthm symbol; we treat it as punctuation.
; Thus !qfoo? will come out as `foo'? rather than `foo?'.

; All this peeking stuff doesn't work really correctly if there are
; comments in the way, so we adopt this rule: don't put comments in
; expressions after ! commands.  Typically, this function is called
; inside of a comment.  If the text to be read extends over a line and
; the next line begins with a ; character, you may not get at all what
; you want because the text on the line after the ; will be skipped.

  (case (peek-char t instr)
        ((#\( #\") (read-preserving-whitespace instr))
        (#\'
         (read-char instr)
         (list 'quote (nqthm-read-preserving-whitespace instr)))
        (#\`
         (read-char instr)
         (list *infix-backquote* (nqthm-read-preserving-whitespace instr)))
        (otherwise 
         (read-from-string
          (coerce
           (nconc
            (prog (c ans c2)
                  loop
                  (setq c (peek-char nil instr nil a-very-rare-cons))
                  (cond ((or (eq c a-very-rare-cons)
                             (member c nqtex-white-space)
                             (member c nqtex-break-chars))
                         (cond ((null ans)
                                (nqthm-read-preserving-whitespace-error instr)))
                         (return (nreverse ans)))
                        ((member c '(#\| #\; #\\))
                         (nqthm-read-preserving-whitespace-error instr))
                        ((member c nqtex-normal-clause-enders)
                         (read-char instr)
                         (setq c2 (peek-char nil instr nil a-very-rare-cons))
                         (cond ((or (member c2 nqtex-white-space)
                                    (eq c2 a-very-rare-cons))
                                (unread-char c instr)
                                (cond ((null ans)
                                       (nqthm-read-preserving-whitespace-error instr)))
                                (return (nreverse ans)))
                               (t (push c ans))))
                        (t (read-char instr)
                           (push c ans)))
                  (go loop))

; Sticking on this extra space is not strictly necessary.  We do it to
; work around a bug in AKCL 1-605.

            (list #\Space))
           'string)))))

(defun nqtex2tex (fl &key
                  ((:print-case *print-case*) :downcase)
                  ((:left-margin *left-margin*) 5)
                  ((:print-width *rightmost-char-number*) 77)
                  (just-remove-! nil))

; Copies the file fl.nqtex file to the file fl.tex file, replacing Nqthm forms
; preceded by a two character sequence starting with an exclamation mark with
; the results described below.  If an exclamation mark is not followed by one
; of these special characters, then the following form is preserved unchanged,
; and the exclamation mark and the character following it are preserved, too.

; Although we may extend this set of replacement commands, we *promise* to give
; special meanings only to alphabetic characters after !.  Thus we promise
; never to give !!  a replacement effect.

; In every case, for one of the replacement characters, upper or lower case has
; the same effect.

; !Eev, where ev is an Nqthm event form, e.g., (defn foo (x) 3), results in
; conventional notation for ev.  We may introduce line breaks via the Latex
; \begin{tabbing} command.  Mnemonic: E -- think Event.

; !Ifoo, where foo is a symbol, results in foo, but with with all Tex sensitive
; characters quoted.  For example, !Ia$b would result in a\$b.  Mnemonic: I --
; think Identity.

; !Pfm, where fm is an Nqthm term, e.g., (plus x y), results in conventional
; mathematical notation for fm.  May introduce line breaks via the Latex
; \begin{tabbing} command.  Mnemonic: P -- think Pretty print.

; !Qfn, where fn is a symbol, results in fn surrounded by single gritches,
; after TeX sensitive characters have been quoted, e.g., !qfoo results in
; `foo'.  Useful for distinguishing function symbols from other words in a
; sentence, since function symbols appear in Roman.  Mnemonic: Q -- think
; Quote.

; !Tfm, where fm is an Nqthm term, results in conventional mathematical
; notation for fm, but without any line breaks.  Mnemonic: T -- think Term.

; !Vfoo means that foo is printed as is, but in typewriter font, and with
; special Tex characters quoted.  Mnemonic: V -- think Verbatim.

; ! followed by anything else is left alone, along with the exclamation mark.

; Implementation note:  please keep the parameter nqtex2tex-chars up to date
; when adding or subtracting characters. 

; One can certainly use nqtex2tex on the result of running infix-file, but one
; must do so deliberately by first running infix-file, then renaming the
; resulting file, say foo.tex, to be foo.nqtex, and then running nqtex2tex.
; More convenient is to run infix-file with the :nq keyword parameter set to t,
; which causes infix-file first to generate a .nqtex file and second to run
; nqtex2tex on that file.

; If the :just-remove-! keyword is t, then a file named root.stripped is
; created, with all of our special ! commands options removed.

; Implementation note.  In all the cases we treat explicitly, the characters
; after !? are read with the Lisp function READ-PRESERVING-WHITESPACE, which
; is just the same as READ except that it doesn't gratuitously consume whitespace
; at the end of a READ.

; Warning: Because we use a relative of READ to obtain the forms immediately
; after the two character exclamation commands, the user must beware that if a
; form to be read extends for more than a line, and if a semicolon (comment
; character) is encountered on the next line, say at the beginning, READ will
; skip that line from the semicolon on, which may not be what the user intends.
; Thus it can be safer to use the #| ... |# construct for comments containing
; !, especially if one is in the habit of using the Emacs command M-x fill
; paragraph to rearrange paragraphs that begin with the comment delimiter
; semicolon.

  (let ((infl (extend-file-name fl "nqtex"))
        (*print-pretty* nil)
        (orig-readtable (copy-readtable nil))
        (error-flg t)
        (outfl (extend-file-name fl (if just-remove-! "stripped" "tex")))
        (a-very-rare-cons (cons nil nil))
        (*readtable* (copy-readtable nil)))
    (smash-infix-readtable)
    (with-open-file
     (instr infl :direction :input)
     (unwind-protect 
         (with-open-file
          (*standard-output* outfl :direction :output :if-exists :rename-and-delete)
          (iterate for c = (read-char instr nil a-very-rare-cons)
                   do
                   (cond ((eq c a-very-rare-cons) (return))
                         ((eql c #\!)
                          (let ((c (read-char instr nil a-very-rare-cons)))
                            (cond ((eq c a-very-rare-cons)
                                   (pwrite-char #\!)
                                   (return)))
                            (case c
                                  ((#\E #\e)
                                   (or just-remove-!
                                       (let ((term (nqthm-read-preserving-whitespace instr)))
                                         (infix-event term))))
                                  ((#\I #\i)
                                   (or just-remove-!
                                       (let ((term (nqthm-read-preserving-whitespace instr)))
                                         (print-atom term))))
                                  ((#\P #\p)
                                   (or just-remove-!
                                       (let ((term (nqthm-read-preserving-whitespace instr)))
                                         (infix-form term))))
                                  ((#\Q #\q)
                                   (or just-remove-!
                                       (let ((term (nqthm-read-preserving-whitespace instr)))
                                         (pprinc "`")
                                         (print-atom term)
                                         (pprinc "'"))))
                                  ((#\T #\t)
                                   (or just-remove-!
                                       (let ((term (nqthm-read-preserving-whitespace instr))
                                             (*do-not-use-tabs* t))
                                         (infix-form term))))
                                  ((#\V #\v)
                                   (or just-remove-!
                                       (let* ((*readtable* orig-readtable)
                                              (term (nqthm-read-preserving-whitespace instr))
                                              (*do-not-use-tabs* t))
                                         (quote-printer1 term))))
                                  (otherwise
                                   (cond ((member c *typical-characters-following-excl*) nil)
                                         (t (pformat
                                             *terminal-io*
                                             "We have encountered a surprising ~
                                              (to us) character after !, ~
                                              namely ~a, ~%at position ~a of ~
                                              the file \"~a\".  ~%~%This ~
                                              occurrence of ! will be treated ~
                                              as normal text, i.e., left ~
                                              alone, ~%and you may ignore this ~
                                              message.  To suppress this ~
                                              advisory in the future, ~%push ~
                                              the character #\\~a onto the ~
                                              Lisp variable ~
                                              ~%*typical-characters-following-excl*."
                                             c
                                             (file-position instr)
                                             infl
                                             c)))
                                   (pwrite-char #\!)
                                   (pwrite-char c)))))
                         (t (pwrite-char c))))
          (setq error-flg nil))
       (if error-flg
           (format *terminal-io* "Error encountered at location ~a of file ~a."
                   (file-position instr) infl))))))
                              

                                   
;                             DEFINITION BY EXAMPLES

(defun functify (l)

; Removes redundant elements from an alist.

  (iterate for tail on l with ans do
           (cond ((null (assoc (car (car tail)) ans))
                  (push (car tail) ans)))
           finally
           (return (nreverse ans))))


(defun print-examples ()

; Illustrates the current syntax via a brief Latex document.

  (let ((*print-pretty* nil)
        (*print-case* :downcase))
    (with-open-file
     (*standard-output* "infix-examples.nqtex" :direction :output
                        :if-exists :rename-and-delete)
     (pprinc

       "\\documentstyle{article} \\begin{document} 

        Here is a summary of the conventional syntax in terms of the official syntax
        of the Nqthm logic.

        \\begin{enumerate}
        \\item Variables are printed in italics, unless specified otherwise in the table below.

        \\item Function application.  For any function symbol for which special
        syntax is not given below, an application of the symbol is printed with
        the usual notation; e.g., the term !v(fn x y z) is
        printed as !t(fn x y z).  Note that the function symbol is printed in
        Roman.  In the special case that !qc is a function symbol of no
        arguments, i.e., it is a constant, the term !v(c) is printed merely as
        !t(c), in small caps, with no trailing parentheses.  Because variables are printed in
        italics, there is no confusion between the printing of variables and
        constants.

        \\item 
        Quoted constants are printed in the ordinary syntax of the Nqthm logic,
        in a `typewriter font.'  For example,
        {\\tt '(a b c)} is still printed just that way.  \\verb+#b001+ is printed
        as !t#b001, \\verb+#o765+ is printed as !t#o765, and \\verb+#xa9+ is printed as
        !t#xa9, representing binary, octal and hexadecimal, respectively.")
     (iterate for form in (functify *wired-in-infix-examples*)
              do
              (let ((*do-not-use-tabs* t))
                (pprinc "\\item ")
                (quote-printer1 form)
                (pformat *standard-output* " is printed as ~%")
                (infix-form form))
              (pformat *standard-output* ".~%~%"))
     (pformat *standard-output* "\\item  The remaining symbols that are printed specially are
               described in the following table.~%~%")
     (pprinc "\\end{enumerate}")
     (pformat *standard-output* "~%~%\\begin{tabular}{|c|c|}\\hline~%~
                                 Nqthm Syntax &  Conventional Syntax \\\\ \\hline \\hline")
     (iterate for form in
              (append (iterate for pair in (functify *atom-alist*)
                               collect (car pair))
                      (iterate for name in (scrunch *infix-ops*)
                               collect (list name 'x 'y))
                      (iterate for pair in (functify *negative-infix-table*)
                               collect (list 'not (list (car pair) 'x 'y)))
                      (iterate for name in (scrunch *unary-prefix-ops*)
                               collect (list name 'x))
                      (iterate for pair in (functify *negative-unary-prefix-table*)
                               collect (list 'not (list (car pair) 'x)))
                      (iterate for name in (scrunch *unary-suffix-ops*)
                               collect (list name 'x))
                      (iterate for pair in (functify *negative-unary-suffix-table*)
                               collect (list 'not (list (car pair) 'x)))
                      (iterate for name in (scrunch *unary-abs-ops*)
                               collect (list name 'x))
                      (iterate for pair in (functify *prefix-multiple-ops*)
                               collect (cons (car pair)
                                             (iterate for i from 1 to (cdr pair) collect
                                                      (intern (format nil "X~a" i)))))
                      (iterate for pair in (functify *infix-multiple-ops*)
                               collect (cons (car pair)
                                             (iterate for i from 1 to (1+ (cdr pair)) collect
                                                      (intern (format nil "X~a" i))))))
              do

              (let ((*do-not-use-tabs* t))
                (quote-printer1 form)
                (pprinc "&")
                (infix-form form)
                (pprinc " \\\\  ")
                (pwrite-char #\Newline)))
     (pprinc "  \\hline \\end{tabular}")
     (pprinc "\\end{document}"))
    (nqtex2tex "infix-examples")))


;                                      NOT

; The following code is for the special handling of NOT, which involves diving
; into the term negated to turn a predicate into one that has a slash through
; it.  We advise that the casual user not touch this.

(defun not-printer (term)
  (let (x)
    (cond ((atom (cadr term))
           (default-unary-prefix-printer
             term
             *neg-str*))
          ((setq x (assoc (car (cadr term))
                          *negative-infix-table*))
           (default-infix-printer
                (cadr term)
                (cadr x)))
          ((setq x (assoc (car (cadr term))
                          *negative-unary-prefix-table*))
           (default-unary-prefix-printer
                (cadr term)
                (cadr x)))
          ((setq x (assoc (car (cadr term))
                          *negative-unary-suffix-table*))
           (default-unary-suffix-printer
             (cadr term)
             (cadr x)))
          (t (default-unary-prefix-printer
              term
              *neg-str*)))))

(eval-when (load eval compile)
           (or (not (boundp '*fn-alist*))
               (assoc 'not *fn-alist*)
               (push (list 'not (function not-printer))
                     *fn-alist*))
           'not)


;                          USER MODIFIABLE TABLE SETUP


; It is easy to augment, or even to modify, the syntax printed by calling one
; of the make-... functions illustrated below.  The non-initial arguments to
; these make-...  functions are strings to be printed by Latex to generate
; operators and other noise words when printing a term whose function symbol is
; the initial argument of the call to make-...

; make-infix-op, make-unary-prefix-op, and make-unary-suffix-op take an
; optional second argument, *neg-str*, which indicates how to print the
; negation of an application of the function symbol in question.

; In TeX or Latex, one can do astonishingly clever things.  But the strings
; that we have in mind should do nothing clever involving motion.  They should
; only result in characters being placed at the current location.  While being
; printed, the strings will be passed no arguments or information about the
; context in which printing is to take place. Typically, these strings should
; be nothing more than instructions to print a single symbol. The strings are
; processed in `math mode', and in fact, they are auomatically embedded in
; $...$.

; None of the operators or function symbols below are built into this printer
; anywhere else except by the code below.  The meaning of `not', defined above,
; is wired in because it gives the meaning to the optional *neg-str* arguments.


;                                     INFIX-OPS

; infix-ops (infix operators) should be function symbols of two or more
; arguments for which it is desired that one symbol come out between every
; adjacent pair of arguments.  E.g., invoking (make-infix-op plus "+") causes
; the term (plus a b c d) to be printed as (a $+$ b $+$ c $+$ d).  Invoking
; (make-infix-op equal "=" "\\not=") causes the term (equal x y) to be printed
; as (x $=$ y), and it also causes the term (not (equal x y)) to be printed as
; (x $\not=$ y).

; Thus, for example, if one introduces a new function, say join, and wants to
; print terms of the form (join x y) as (x \bigtriangledown y), cf. p. 44 of
; the Latex manual, then one should invoke:

;   (make-infix-op join "\\bigtriangledown")

; from Lisp.  That is all that need be done to cause infix-file subsequently to
; print `join' terms this way.

; Note that throughout the following examples, we have used two backslashes to
; get one because, in Common Lisp, backslash is a character for quoting other
; characters.

; Examples of make-infix-op.

(make-infix-op equal          "="        "\\not=")
(make-infix-op lessp          "<"        "\\not<")
(make-infix-op leq            "\\leq"    "\\not\\leq")
(make-infix-op greaterp       ">"        "\\not>")
(make-infix-op geq            "\\geq"    "\\not\\geq")
(make-infix-op member         "\\in"     "\\not\\in")
                            
(make-infix-op implies        "\\rightarrow")
(make-infix-op iff            "\\leftrightarrow")
(make-infix-op difference     "-")
(make-infix-op quotient       "\\div")
(make-infix-op remainder      "{}${\\bf{mod}}${}")
(make-infix-op union          "\\cup")
(make-infix-op plus           "+")
(make-infix-op times          "*")
(make-infix-op and            "\\wedge")
(make-infix-op or             "\\vee")


;             UNARY-PREFIX-OPS, UNARY-SUFFIX-OPS, and UNARY-ABS-OPS

; Use make-unary-prefix-op and make-unary-suffix-op only for function symbols
; of one argument.  The string str (or *neg-str*) will be printed before or
; after the argument.

; unary-suffix-ops should be unary function symbols.

; (make-unary-suffix-op foo x str) makes (foo x) print as (x $str$).

; Examples of make-unary-suffix-op.

(make-unary-suffix-op sub1    "-\\;1")
(make-unary-suffix-op numberp "\\in\\;${\\bf{N}}${}"        "\\not\\in\\;${\\bf{N}}${}")
(make-unary-suffix-op zerop   "\\simeq {\\tt{0}}"                 "\\not\\simeq {\\tt{0}}")
(make-unary-suffix-op nlistp  "\\simeq\\;${{\\bf{nil}}}${}" "\\not\\simeq\\;${{\\bf{nil}}}${}")

; unary-prefix-ops should be unary function symbols. 

; (make-unary-prefix-op foo str) makes (foo x) print as ($str$ x).

; Examples of make-unary-prefix-op.

(make-unary-prefix-op add1    "1\\;+")
(make-unary-prefix-op minus   "-")

; unary-abs-ops should be unary function symbols.

; To create syntax like that for absolute value, use (make-unary-absolute-op
; lhs-str rhs-str), where lhs-str and rhs-str are the strings to print on the
; left and right of the argument.  (make-unary-abs-op foo str1 str2) makes (foo
; x) print as (str1 x str2).  See the example for abs below.


;                           SOME POSSIBLE EXTENSIONS


(defun simple-extension ()

; Here are a few examples of normal mathematical notation for functions not in
; the boot-strap.  Invoke this function to put these into effect.

  (make-unary-abs-op    abs        "\\mid" "\\mid")

  (make-unary-suffix-op fact       "{\\rm{!}}")


  (make-infix-op        subsetp     "\\subset"         "\\not\\subset")
  (make-infix-op        intersect   "\\cap"))
  

(defun dmg-syntax ()

; Here are some examples once tentatively proposed by David Goldschlag for his
; work.  Invoke this function to put these into effect.

; prefix-multiple-op's should be function symbols that take as many arguments as
; make-prefix-multiple-op is given arguments.  (make-prefix-multiple-op foo str1
; str2) makes (foo x y) print as ($str1$ x $str2$ y).  That is, the first string
; comes first.

  (make-prefix-multiple-op invariant         "\\Box"           "{}${\\bf{in}}${}")
  (make-prefix-multiple-op eventually-stable "\\Diamond\\Box"  "{}${\\bf{in}}${}")

; infix-multiple-op's should be function symbols that take one more argument
; than make-infix-multiple-op is given arguments.  (make-infix-multiple-op foo
; str1 str2) makes (foo x y z) print as (x $str1$ y $str2$ z).  That is, the
; strings are placed between adjacent arguments.

  (make-infix-multiple-op leads-to       "\\mapsto"              "{}${\\bf{in}}${}")
  (make-infix-multiple-op unless         "{}${\\bf{unless}}${}"    "{}${\\bf{in}}${}")
  (make-infix-multiple-op ensures        "{}${\\bf{ensures}}${}"   "{}${\\bf{in}}${}")
  (make-infix-multiple-op e-ensures      "\,${\\bf{e-ensures}}$\," "{}${\\bf{for}}${}"
                          "{}${\\bf{in}}${}")
  (make-infix-multiple-op n              "\\leadsto"             "{}${\\bf{by}}${}")
  (make-infix-multiple-op initial-condition "{}${{\\bf{initially\\;in}}}${}"))

; Undoing.  To cause applications of a function symbol fn to be printed in the
; default way, i.e., fn(x, y), invoke (clean-up 'fn).

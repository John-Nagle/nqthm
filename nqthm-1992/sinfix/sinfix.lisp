#|
  Copyright (C) 1994 Computational Logic, Inc.  All Rights Reserved.

  Copying of this file is authorized to those who have read and
  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
  LICENSE" at the beginning of the Nqthm file "basis.lisp".

|#

; NQTHM Version 1992
; 
; Comments, bugs, suggestions to:
; 
;   Michael K. Smith
;   Computational Logic Inc.
;   1717 W 6th, Suite 290
;   Austin, TX 78703-4776
; 
;   Fax  : (512) 322-0656
;   Email: mksmith@cli.com
;
;----------------------------------------------------------------------------

#|

   	        A Conventional Syntax Pretty-Printer for Nqthm

		      Originially written by Rober Boyer
		   Modified by Michael K. Smith (2/92,8/93)


				 INTRODUCTION

The functions in this file implement a pretty-printer for Nqthm events.  The
syntax produced is conventional mathematical notation.  The original version
was infix.lisp.  Because Smith added Scribe support, this verson is
sinfix.lisp.  Or as I like to call it `SinFix'.

This file is not automatically compiled or loaded when building Nqthm-1992.
To use this printer, after compiling and loading Nqthm, compile this file
and load it, i.e., (compile-file "sinfix.lisp") and (load "sinfix").  For
more information on installation see the README file in the directory
containing this file.

The following text is, currently, the only documentation for this facility.
Criticism of all sorts solicited.


				  BASIC USE

The intent is to take an NQTHM events file and produce a nicely formatted
document.  Knowing what text formatter you are targeting, you can insert
text formatting commands into comments.  You can also request an infix
transformation of prefix forms in comments (see documentation of function
NQFMT2FMT.

ONE NOTE OF CAUTION: It is important that you know what text formatter you
are targetting, since the bulk of your comments will be copied literally
into the text input file.  It is up to you to ensure that the interaction of
your comments with the formatting convention of choice for the various
comment types results in legal text formatting commands.  That is, if you
are in Scribe mode and a comment contains an email message with net addresss
you should quote occurences of "@" as "@@".  More importantly, if you decide
that ";\" introduces a line to be formatted as raw LaTex (the default in
"latex" mode), you need to ensure that any occurrence of "_" or other LaTeX
special characters on such a line results in a meaningful formatting
command.  For simple transformations of .event files to LaTeX I suggest you
use the default :COMMENT-FORMAT (= 'BOYER).  This causes most comments to be
formatted within verbatim environments, which are not so picky about special
characters.  Scribe is more forgiving of these problems because it only has
the single special character, "@" that needs to be watched out for. (See
`SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'.)

There are two basic modes, "latex" and "scribe".  You can then build on top
of these to customize the printing of functions in your theory.  All mode
sensitivity should be contained in the file <mode>-theory.lisp.  Normally
this file also loads a basic file called <mode>-init.lisp.  The idea is that
the `-init' files contain the minimal required information for SinFix to do
its job with respect to a particular text formatter.  The `-theory' file
contains the details of how you want the functions in your theory to be
printed.  `Scribe-theory.lisp' and `latex-theory.lisp' load
`scribe-init.lisp' and `latex-init.lisp', respectively.

In order to customize printing for a particular file of events, say
"clock.events", we suggest the following approach.  Each column shows the
procedure for the corresponding text formatter, Latex or Scribe.

First, assume we have a file "clock.events", in proper syntactic form for
acceptance by prove-file.  That is to say, suppose that the file
"clock.events" contains only legal event commands such as defn's and
prove-lemma's, Lisp style comments, and the few other sorts of miscellaneous
instructions documented as legal instructions to prove-file.


1. Create clock-theory.lisp.  It should have the following form:

-    Tex                                 Scribe
-    ----------------------------------------------------------------
-    (load-base "latex-theory.lisp")     (load-base "scribe-theory.lisp")
-     ... 
-     Your extensions and/or redefinitions.  
-     See in particular the documentation on make-infix et.al.
-     under `SIX GENERAL OPERATOR SCHEMAS', and the examples at the
-     end of this file and in scribe-theory.lisp and latex-theory.lisp.
-     ...
-     INFIX-SETTINGS provides some simple control over an assortment of 
-     formatting options.  See `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'. 
-     ...
-    (infix-settings :mode "clock"       (infix-settings :mode "clock" 
-               :extension "tex" ...)               :extension "mss" ...)

2. Save clock-theory.lisp, preferably in the same directory with clock.events.

3. Call infix-file.  The simplest call on infix-file would be just

-    (infix-file "clock").

   which will result in the file "clock.tex" or "clock.mss" 

4. Run the appropriate formatter.

5. Special considerations for latex vs. scribe.
   
-  To get an index in LaTeX.             To avoid an index in Scribe
-  ----------------------------------------------------------------
-  %latex clock                          Insert @disable(Index) in clock.mss.
-  %makeindex clock
-  %latex clock


A full blown call to infix-file includes a file root and keyword arguments.
Below is such a call with keywords supplied with their defaults.

-  (infix-file fl :print-case :downcase :mode nil ;chars-wide 77 ;nq t)
-
-   :print-case - must be one of :downcase, :upcase, or :capitalize.
-                 DEFAULT: :downcase.
-
-   :mode       - if not provided (thus defaulting to nil) we look for
-                 "fl-theory.lisp" and load it if present.  If not, we use 
-                 the mode of the last successfull call to infix-file or 
-                 query whether you want to use Scribe or Latex mode.
-                 In this last case you will need to know where the basic
-                 theory files are located.  Simplest is to create a trivial
-                 -theory file in the same directory as the event files that 
-                 just loads appropriate scribe or latex -theory file.
-                 DEFAULT: fl root name.  If not found, queries the user.
-
-   :chars-wide - approximate width in characters of the formatted output.
-                 Controls where infix inserts line breaks within expressions.
-                 DEFAULT: 77.
-
-   :nq         - If t, then certain specially marked Nqthm expressions in 
-                 comments are replaced with their conventional notation.  
-                 See the documentation of the function `nqfmt2fmt' below for 
-                 a description of the special syntax for this replacement 
-                 process.  We assume you use this feature.  If not,
-                 set *nq-default* to NIL in your mode file.
-                 DEFAULT: T.


			       COMMENT HANDLING

- Jul 28 93 MKS - Extended comment handling.  
- Aug  3 93 MKS - Still haven't done anything with internal comments.

Modified Treatment of comments: `infix-file' preserves comments between
events, but skips over comments within events.  We completely skip comments
within events because we have not figured out how to place them appropriately
mechanically.

Comments are formatted in several ways, depending on the character immediately
following the semi-colon or OPEN-BAR-COMMENT.  A comment may be turned into:

- 1. Running TEXT.  The comment chars (see definition following) are
- eliminated and the text is copied to the output file.
- 
- 2. A FORMATted environment.  The comment chars (see definition
- following) are eliminated, line breaks and spaces are preserved, and
- the font is the default document font.
- 
- 3. A VERBATIM environment. The comment chars may or may not be preserved, 
- line breaks and spaces are PRESERVED and the font is a fixed width font.
- 
- 4. An EMPHASIS environment. Like format, but the font is italic.

This set, which is used by the named formats in *comment-format-alist* can
be extended by modifying the value of *comment-environment-mapping* in your
theory file.

To replace the comment format conventions, use (define-comment-format name
format).

The format argument has two parts, one for semi-colon comments
and the other for #| ... |# comments.  The assignment below corresponds to
Boyer's initial setting.

- (define-format 'boyer
-   '((#\; (("\\"   nil   text))
-      nil verbatim #\;)
-     (#\# (("\\"   nil   text))
-      t verbatim)))

The structure of each of these lists is
-  type      ::= (label (substring*) spaces-p format [char])
-  substring ::= (string spaces-p format [char])

LABEL indicates which of the two types of comments we are looking at, either
those that start with a SEMI-COLON or those that start with LB VERTICAL-BAR.
We determine what to do in the various cases (which amounts to choosing
SPACES-P, FORMAT, and CHAR) based on whether the comment type indicated by
LABEL is followed by any of the strings that begin SUBSTRINGS or not.  If it
matches, we use the components of the matching substring, otherwise we use
the default for the comment type, i.e.  the elements of the type list.

-  If SPACES-P, consume one space if there is one.
-  Begin formatting according to FORMAT.
-  Insert CHAR.

So, for the example above, the first sublist, whose car is the semi-colon
character, describes how to format comments that begin with a semi-colon
followed by specific strings.  There are two possibilites.  If the
semi-colon is not followed by a back-slash (\) we use the type info.  We
don't look for a space, we ensure we are in a verbatim environment, and
print a semi-colon.  If semi-colon is followed by a back-slash, we don't
look for a space and ensure that we are in a text environment.

Thus, if we encounter a comment beginning ";\", the comment should be
inserted as top level text with no special formatting.  The ";\" will not show
up in the output.


- COMMENT TRANSFORMATIONS:

There are three versions.  One reflects MKSmith's preferences, one Boyer's,
and one the Common Lisp defaults.  MKSmiths is the default.  To get Boyer's,
do (setup-comment-format 'boyer).  To get Common Lisp's, do
(setup-comment-format 'cl).  You can insert this form in your theory file.
To create your own conventions, see DEFINE-COMMENT-FORMAT.  

- Description:

-  BT begins means running text, with no environment modifiers.  
-  BF ... EF corresponds  to <begin-format> ... <end-format>
-  BV ... EV corresponds  to <begin-verbatim> ... <end-verbatim> 
-  BE ... EE corresponds  to <begin-emphasis> ... <end-emphasis> 
-  BS ... ES corresponds  to <begin-section-name> ... <end-section-name> 
- 
-              MKS           Boyer             CL
-  
-  #| ... |#   BT...         BV ... EV         BT...   
-  #|\ ... |#  BT...         BT ...            BT...   
-  #|- ... |#  BF... EF      BV- ... EV        BF... EF
-  #|; ... |#  BV... EV      BV; ... EV        BV... BV
-  
-  ; ...       BT...         BV; ... EV        BE... EE
-  ;; ...      BF... EF      BV;; ... EV       BF... EF
-  ;;; ...     BV... EV      BV;;; ... EV      BT...   
-  ;;;; ...    BV;... EV     BV;;;; ... EV     BS... ES

-  ;\ ...      BT...         BT ...            BT...   
-  ;- ...      BF... EF      BV;- ... EV       BF... EF
-  ;+ ...      BV... EV      BV;+ ... EV       BV... EV
-  ;! ...      BE... EE      BV;! ... EV       BE... EE

-  ;;- ...     BF; ... EF    BV;;- ... EV      BF; ... EF
-  ;;+ ...     BV; ... EV    BV;;+ ... EV      BV; ... EV
-  ;;! ...     BE; ... EE    BV;;! ... EV      BE; ... EE


				   COVERAGE

The `infix-file' function handles the entirety of the Nqthm-1992 term syntax
checked by prove-file.  But note that we deliberately do not print out the
`hint' parts of events.


				  MOTIVATION

We hope this notation will facilitate the communication of work with Nqthm to
those who do not happily read Lisp notation.  But we have no expectation that
this notation will make it easier for the Nqthm user to formulate or to prove
theorems.


			      NO ERROR CHECKING

Warning about the absence of error checking: In general, user-callable
subroutines of Nqthm do extensive syntactic checking on their input and
explicitly report syntactic errors.  But this pretty printer does not do such
syntactic checking.  Rather, we assume the given input is known to be
syntactically correct, namely as though checked by `prove-file'.  Failure to
provide input in correct syntactic form can result in nasty, brutish, and
short Lisp errors.


			  OTHER USER-LEVEL FUNCTIONS

Besides `infix-file', here are the other user-level functions supported by
this file.

(a) (print-examples) creates a stand-alone, file named "infix-examples.tex"
or "infix-examples.mss", which is a summary of the syntax we print in terms
of the official Nqthm syntax.  This file will also correctly report any user
modifications made to the syntax by invocation of the make... functions
described later.  We hope that users will want to include this file in
reports about Nqthm use to make clear what syntactic conventions they are
using.

(b) (NQFMT2FMT "foo") copies the file "foo.nqthm" to the file "foo.tex" or
"foo.mss", but along the way, Nqthm terms preceded by an exclamation mark
and certain alphabetic characters are replaced with the formatting commands
for the conventional notation this printer generates.  For example, when in
latex mode, if nqfmt2fmt encounters !t(gcd x (difference y x)) in a file, it
will replace it with {\rm{gcd}}\,({\it{x\/}}, {\it{y\/}} $-$ {\it{x\/}}).
We find the former much easier to read in a file.  nqfmt2fmt thus permits
one to keep Nqthm forms in files to be read and edited by humans, e.g., in
comments in Nqthm event files.  Ordinary uses of !, e.g., uses of it
followed by white space or punctuation characters, are, of course,
unaltered.

Let ev  be an Nqthm event form, e.g., (defn foo (x) 3)
    fm  be an Nqthm term, e.g., (plus x y)
    foo be a symbol

Summary:

!Pfm  - Pretty print.
!Tfm  - Pretty print but without any line breaks.  
!Eev  - Format event.
!Ifoo - Identity, handling special chars of formatter.
!Qfn  - `fn'. 
!Vfoo - Verbatim.

Detail:

!Eev  - Event. Results in conventional notation for ev.

!Ifoo - Identity. Results in foo, but with with formatting sensitive
        characters quoted.

!Pfm  - Pretty print.  Results in conventional mathematical notation.

!Qfn  - where fn is a symbol, results in fn surrounded by single gritches,
        after formatting sensitive characters have been quoted, e.g., !qfoo results 
        in `foo' in TeX.  Useful for distinguishing function symbols from other 
        words in a sentence, since function symbols appear in Roman.  
        Mnemonic: Q -- think Quoted.

!Tfm  - where fm is an Nqthm term, results in conventional mathematical
        notation for fm, but without any line breaks.  
        Mnemonic: T -- think Term.

!Vfoo - foo is printed as is, but in typewriter font, and with special characters quoted.  
        Mnemonic: V -- think Verbatim.

! followed by anything else is left alone, along with the exclamation mark.

See the comment at the beginning of the definition of nqfmt2fmt, below, for
details on the syntax and replacements.  There is also an option to nqfmt2fmt
for simply stripping out the !commands.

(c) (infix-form fm) prints (to *standard-output*) the formatting input for the
conventional notation for the Nqthm term fm.  `infix-form', `infix-event', and
`ppe-fmt' can be used to generate Latex or Scribe to be inserted manually into
papers, but we recommend the use of nqfmt2fmt, described above, for this
purpose.

(d) (infix-event ev) prints (to *standard-output*) the Latex or Scribe for the
conventional notation for the Nqthm event ev.

(e) (ppe-fmt name) prints what the Nqthm command `ppe' prints, but prints the
events in Latex or Scribe.


			   USER EXTENSION OF SYNTAX

`infix-file' is table-driven, and it is very easy to extend in certain ways,
e.g., to introduce a new infix operator.  See the very end of this file, at
`USER MODIFIABLE TABLE SETUP', for examples of how to establish new syntax.

Also see `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP' to see how to
control additional features of the printing process, e.g. indexing, details of 
comment handling, parentheses around expressions, etc.


			  PARENTHESES and PRECEDENCE

This pretty-printer does not provide a facility for the suppression of
parentheses via the declaration of precedence for operators.  An objective in
printing a formula is clarity.  We know of very, very few cases (e.g., + and
*) where precedence is something on which people agree.  As a small
contribution towards the suppression of parentheses , we do drop the outermost
parentheses of a formula when the formula is an argument of a function that is
being printed in the usual f(x,y) notation, with subterms separated by
parentheses and commas.

In addition, the user has two alternatives to fully parenthesized notation.

1. Eliminate them at the top level by setting *TOP-PARENS-ELIMINABLE*
   to T.

2. Eliminate them except where absolutely required (e.g. around
   normal, prefix function arguments) by setting
   *TOP-PARENS-ELIMINABLE-DEFAULT* to T.

See the section `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP'.


			       OTHER FORMATTERS

There are some functions in this file that take advantage of similarities
between LaTeX and Scribe.  They are marked with `WARNING: Latex/Scribe
dependency'.  If you want to generate input to some other formatter you may
want to take a look at these.  Not guaranteed to be complete.  In order to
built a -init.lisp file for some other formatter make sure you look at
`SPECIAL VARIABLES THAT MUST BE DEFINED IN MODE-INIT.LISP'.


			    END OF COMMENTS ON USE

|#

#| ---------------------------------------------------------------------------------

                          COMPILATION DEPENDENCIES               
|#

;; Set this to be the directory in which we compile this file.
(defparameter *infix-directory* #.(namestring (probe-file "./")))

(defun load-base (s)
  (load (concatenate 'string *infix-directory* s)))

; Fix bug in AKCL interpreter's use of proclaim.
#+akcl (load-base "akcl-patch.lisp")

;; Check that we are in a compatible Nqthm.

(eval-when (load eval compile)
           (or (boundp 'file-extension-events)
               (error "~%~%infix.lisp is to be compiled and used with Nqthm versions 1992 or later,~%~
                       not stand-alone or with older versions of Nqthm.~%")))

; NOTE: we depend on the following externally (in nqthm) defined objects:

; Functions/macros: untranslate-event, our-flatc, iterate
; Variables: a-very-rare-cons


#| ---------------------------------------------------------------------------------

	     SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP. 

Use INFIX-SETTINGS to set this first set of properties.
See files latex-mode.lisp and scribe-mode.lisp for examples.

The things you can control with INFIX-SETTINGS are listed below.  The first
choice is the default, so if you are happy with the default you don't need
to fool with the setting.  See examples after the enumeration.  These are
all keyword arguments to INFIX-SETTINGS.

1. MODE: a string naming the theory we are in.  The default is constructed
   the the name of the events file.  If no corresponding -theory file is found,
   query the user.

2. EXTENSION: type of output file ("mss", "tex", ...)

3. OP-LOCATION: ['FRONT, 'BACK]
   Controls where operator is printed when printing on multiple lines
   'FRONT - put operator at beginning of line (Smith's way)
   'BACK  - put operator at end of line (Boyer's way)

4. COMMENT-FORMAT: ['SMITH, 'BOYER, 'CL]
   Chooses from one of the predefined conventions for determining from the character
   following the comment character how to format the comment.  This interacts
   with your use of native-mode formatting commands in comments in the .events file.

   For your own control over this, use (DEFINE-COMMENT-FORMAT name format).
   See the description of comment handling for more information.

5. FORMAT-!-IN-COMMENTS: [T, nil]
   If true, run nqfmt2fmt over comments

6. ELIMINATE-TOP-PARENS: boolean [T, nil]
   Indicates whether you wish the outermost parentheses of function bodies suppressed.

7. ELIMINATE-INNER-PARENS: boolean [T, nil]
   Suppresses all precedence related parentheses.  Much cleaner output, though an 
   expression printed with this flag=true may reconstruct oddly, depending on the 
   reader's precedence model.  The indentation of large expressions helps somewhat.

   Example: Consider the defn, 
   (defn foo (l)
     (and (plistp l) (and (bar l) (baz (cdr l)))))

   Below is a table showing how the body (the AND) would be printed.

   TOP  INNER  Printed output of body of foo
   t    t      plistp(l) & bar(l) & baz(cdr(l))
   t    nil    plistp(l) & (bar(l) & baz(cdr(l)))
   nil  t      (plistp(l) & bar(l) & baz(cdr(l)))
   nil  nil    (plistp(l) & (bar(l) & baz(cdr(l))))

8. NO-INDEX-CALLS: boolean [NIL, T] or list
   If you want all function calls indexed, NIL. you do not want any function use indexed, T.
   If you want to exclude certain function calls, provide a list of function 
   names to be ignored.

If you do not provide a keyword value pair, the settings remains unchanged.
Thus, you really don't have to call this function.  Though typically you want
to change the :mode if you have created a special theory extension on top of
Scribe or Latex.

For example if you are simply making 

the minimal call requires a mode and extension.

(INFIX-SETTINGS :MODE                   "scribe"
		:EXTENSION              "mss"   )
	
Maximal call, setting everything explicitly.
The following shows infix-settings with all of the default settings as
arguments.  The comments indicate required types of values.  `...' indicates
settings that the user may extend with more work.

(INFIX-SETTINGS :MODE                   "scribe" ; string ["SCRIBE","latex",...]
		:EXTENSION              "mss"    ; string ["MSS","tex"]
		:OP-LOCATION            'FRONT   ; ['FRONT,'BACK]
		:COMMENT-FORMAT         'SMITH   ; ['SMITH,'boyer,...]
		:FORMAT-!-IN-COMMENTS   T        ; [T,nil]
		:ELIMINATE-TOP-PARENS   T        ; [T,nil]
		:ELIMINATE-INNER-PARENS T        ; [T,nil]
		:NO-INDEX-CALLS         NIL      ; [t,NIL,l]
		)

|#


; Variable controlling handling of special formatting within comments.  See `NQFMT2FMT'.

(defparameter *nq-default* t)

; If *INFIX-OP-LOCATION* is 'BACK then you get Boyer's printing of a list of infix 
; operators and arguments.  IF 'FRONT, you get Smiths.  Smiths is the default.  
; You can tell who last editted this file.

;- BACK form is      e.g
;-  arg1 op               foo(a,b,c) &
;-  arg2 op               bar(a,1) &
;-  argn                  some-long-function-name(a,b,1)

;- FRONT form is       e.g
;-     arg1                 foo(a,b,c)
;-  op arg2               & bar(a,1)
;-  op argn               & some-long-function-name(a,b,1)


; Either FRONT or BACK.
(defparameter *infix-op-location* 'front)

; Extension of input file.
(defparameter file-extension-events "events")



#|
	     SETTINGS THAT MAY BE RESET IN MODE-THEORY.LISP. (2)

The following variables do not NEED to be reset in your mode file, but they may be.




|#

(defparameter *top-parens-eliminable* nil)

; *TOP-PARENS-ELIMINABLE-DEFAULT* is a global.  If t, then it is ALWAYS
; assumed to be ok to omit the outermost parentheses of the expressions
; we are about to print.

(defparameter *top-parens-eliminable-default* nil)

#|\

INDEXING

If you do not want occurences of functions indexed (SETQ *DO-NOT-INDEX-CALLS* T).
If you want to exclude certain functions, add them to the list *DO-NOT-INDEX-CALLS-OF*.
If you want no index, see comments at beginning of file. 


DEBUGGING

Setting *INFIX-TRACE* to T will provide some debugging help when testing new mode files.


		     END OF SETTINGS FOR MODE-INIT.LISP.

---------------------------------------------------------------------------------
|#


; ---------------------------------------------------------------------------------
;
;             SPECIAL VARIABLES THAT MUST BE DEFINED IN MODE-INIT.LISP.
;
; Use INFIX-SETTINGS to set this variable.  See Introduction.

; One of NIL, "latex", "scribe", or another string.
(defparameter *infix-mode* nil)	         


					; STRINGS BASED ON THE TARGET FORMATTER (LaTeX, Scribe, ...)

;; Default extension of created files.
(defvar *mode-extension* nil)

(defparameter *standard-prelude* nil)
(defparameter *standard-postlude* nil)

(defparameter *example-prelude* nil)
(defparameter *begin-example-table*  nil)
(defparameter *example-postlude*  nil)

;; BASIC BRACKETS AND THEIR QUOTED VERSION.

(defparameter *begin*  nil)
(defparameter *end*    nil)
(defparameter *lbrace*  nil)
(defparameter *rbrace*  nil)

;; ENVIRONMENT BEGIN-END PAIRS

(defparameter *begin-index*  nil)
(defparameter *end-index*  nil)

(defparameter *begin-verbatim-env* nil)
(defparameter *end-verbatim-env* nil)

(defparameter *begin-format-env* nil)
(defparameter *end-format-env* nil)

(defparameter *begin-emphasis-env*  nil)
(defparameter *end-emphasis-env*  nil)

(defparameter *begin-section-env*  nil)
(defparameter *end-section-env*  nil)

(defparameter *begin-tt-env*  nil)
(defparameter *end-tt-env*    nil)

(defparameter *begin-bold-env*  nil)
(defparameter *end-bold-env*    nil)

(defparameter *begin-italic-env*  nil)
(defparameter *end-italic-env*    nil)

(defparameter *begin-sc-env*  nil)
(defparameter *end-sc-env*    nil)

(defparameter *begin-enumerate-env*  nil)
(defparameter *end-enumerate-env*  nil)
(defparameter *begin-item*  nil)
(defparameter *end-item*  nil)

(defparameter *forall* nil)
(defparameter *exists* nil)

;; TABBING AND INDENTING ENVIRONMENT AND TAB OPERATIONS

(defparameter *begin-tabbing-env*  nil)
(defparameter *end-tabbing-env*  nil)
(defparameter *new-tab-row*  nil)

;; Needs to be redefined in <mode>-init.lisp
(defun new-tab-row (&optional followed-by-infix-print-term)
  (declare (ignore followed-by-infix-print-term))
  (pprinc *new-tab-row*))

(defparameter *tab*  nil)

(defparameter *column-separator* nil)

; *tabs-list* is a text-formatter specific variable.  Typically of the form of a 
; list of pairs, either (tab . n) or (lm . n), where n is the value of
; *infix-loc* when we set tabs and margins.

(defparameter *tab-list* nil)

(defparameter *set-margin* nil)
(defparameter *pop-margin*  nil)
(defparameter *set-tab* nil)

(defparameter *default-op-tab-space* "")

(defparameter *adjust-tab-before-margin* nil)

;; FONTS

(defparameter *function-font*  nil)
(defparameter *neg-str* nil)

;; MATH ENV AND OPERATORS

(defparameter *math-format*  nil)
(defparameter *math-begin*  nil)
(defparameter *math-end*  nil)

(defparameter *math-thick-space*  nil)
(defparameter *math-thin-space*  nil)

(defparameter *subscript*  nil)

(defparameter *begin-subscript* nil)
(defparameter *end-subscript* nil)

;; MISC.

(defparameter *newpage*  nil)

(defparameter *comma-atsign*  nil)
(defparameter *caret*  nil)

(defparameter *dotted-pair-separator* " . ")
(defparameter *dotted-pair-separator-newline* ". ")

(defparameter *no-tab-event-trailer*  nil)
(defparameter *print-default-event-header*  nil)

#|\---------------------------------------------------------------------------------

	      FUNCTIONS THAT MUST BE DEFINED IN MODE-INIT.LISP.

Signatures as passed to (proclaim '(ftype ...) ..)

() -> t : function of no args, returning arbitrary type
 
            begin-tabbing                end-tabbing
            set-margin                   pop-margin
            get-margin                   pop-tab
            do-tab

            newline-to-current-margin    to-current-margin
            force-newline-in-result

(t) -> t : function of one arbitray arg, returning arbitrary type

    	    set-tab

(character) -> t : function of one character arg, returning arbitrary type

            handle-special-chars
            handle-special-chars-in-string
            char                         { Why is this in this list? }


---------------------------------------------------------------------------------

			   IMPLEMENTATION COMMENTS

The three `tables' that govern the printing are the variables:

1. *atom-alist*, which governs printing of variables, numbers, T, F, and NIL.

2. *fn-alist*, which governs the printing of any term that starts with a
function symbol, including LET, COND, CASE, LIST, LIST*, and FOR.

3. *event-printer-alist*, which governs the printing of events.

Each table is an alist.  Each member of any of these alists is a list (symbol
fn), where symbol is the car of a form (or in the case of a non-consp form,
the form itself) which is about to be printed.  fn is a Common Lisp function
of one argument which is called on the form in question to do the printing.
For each alist, there is a default function that is returned if a symbol is
not explicitly represented.  One such default is the function
default-fn-printer, which is a good function to study before contemplating
serious modifications to this file.

Although adding new members to these alists, and defining corresponding
special purpose functions, is certainly sensible and easy, there are several
points to be made.

1.  It is unlikely that there will be any call to edit `*atom-alist*' until
and unless TRANSLATE is changed.

2.  *fn-alist* can be most easily modified by the use of the macros
make-infix-op, make-unary-prefix-op, make-unary-suffix-op,
make-infix-multiple-op, and make-prefix-multiple-op.  See the very end of the
file for many examples of how syntax operators can be easily established.

We really do assume throughout this code that the input file has passed
through prove-file, e.g., we assume that the last test in a `cond' is on T,
the last test in a case is an `otherwise', and that the third argument to
`prove-lemma' is something that translate can accept.


STANDARD OUTPUT USED

Printing.  We do *all* of our printing of formulas to *standard-output*, so we
call princ and write-char on just one argument, the thing to be printed.

|#

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

(defparameter *latex-indent-number-limit* 13)

; In *tabs-in* we keep track of how deep into tabs we are so that we can punt
; if necessary.

(defparameter *tabs-in* 0)

(defparameter *do-not-use-tabs* nil)

; We cannot place defparameters for the following three special symbols at this
; place in the file because their initial values contain `functions' of
; functions to be defined later.

(proclaim '(special *atom-alist* *fn-alist* *event-printer-alist*))

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

(defparameter *started-a-verbatim* nil)

(defparameter *started-a-format* nil)

(defparameter *reported-tabs* nil)

(defparameter *copy-comments-in-file* nil)

;  This `secret' function symbol is used to print out integers generated by
; readins #b, #o, or #x syntax.

(defparameter *infix-radix* (make-symbol "*infix-radix*"))

; One should add to this list if any other special forms are hard wired into
; this printer.

(defparameter *wired-in-infix-examples*
  '((if x y z)
    (cond (test1 value1) (test2 value2) (t value3))
    (case x (key1 answer1) (key2 answer2) (otherwise default))
    (for x in l when (test x) collect (fn x))
    (let ((var1 val1) (var2 val2)) form)
    (forall (x y) (p x))
    (exists (x y) (p x))
    (not x)))

; Severe warning on printing.  It is illegal for any function in this file,
; with the exception of ppe-fmt (which we hardly think of being in this
; file), to do any printing except via these four printing macros: pprinc,
; pprin1, pformat, and pwrite-char.  This rule is imposed so that the `hack' of
; printing invisibly (see *testing*) will work.  The point is that any printing
; operation may be called many times!  But we do not want to print unless the
; special *testing* is bound to nil!  Key fact: if *testing* is t, we DO NOT
; print.


; A very sloppy fudge factor to account for the fact that in \tt mode, characters are
; fatter.

(defparameter *tt-size* 1.3)

(defparameter *do-not-index-calls* nil)

(defparameter *infix-comma* (make-symbol "comma"))

(defparameter *infix-comma-atsign* (make-symbol "comma-atsign"))

(defparameter *infix-backquote* (make-symbol "backquote"))

(defparameter *do-not-index-calls-of*
  (list *infix-radix* *infix-comma* *infix-comma-atsign* *infix-backquote*))

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


;		     SIX GENERAL OPERATOR SCHEMAS

; The following make-... macros are used to generate functions and entries for
; the *fn-alist*.  See the end of this file for many examples of usage which can
; be easily extended.

(defun clean-up (fn)

; This function is supposed to remove completely all trace of any prior establishment
; of any syntax for the function symbol fn.

  (or (symbolp fn)
      (er hard (fn) |Illegal| |function| |symbol| |name| |:| (!ppr fn nil) |.|))
  ;; DELTA !!!!
  (setf (get fn 'literalform) nil)
  (iterate for lst in '(*infix-ops* *unary-prefix-ops* *unary-suffix-ops* *unary-abs-ops*)
	   do  (set lst (remove fn (eval lst))))
  (iterate for alist in '(*fn-alist* *negative-infix-table* *negative-unary-prefix-table*
                                     *negative-unary-suffix-table* *prefix-multiple-ops*
                                     *infix-multiple-ops*)
	   do  (set alist (iterate for pair in (eval alist)
				   unless (eq fn (car pair))
				   collect pair))))

;; Used to reinitialize during clean-up-everything
(defparameter *save-fn-alist* nil)

(defun clean-up-everything ()
  (iterate for alist in '(*fn-alist* *negative-infix-table* *negative-unary-prefix-table*
                                     *negative-unary-suffix-table* *prefix-multiple-ops*
                                     *infix-multiple-ops*) 
	   do (progn
		(iterate for pair in (eval alist)
			 do (clean-up (car pair)))
		(set alist nil)))
  ;; Reinitialize 
  (setq *fn-alist* *save-fn-alist*))
                 
(defmacro make-infix-op (name str &optional neg-str)
  (let ((fn-name (intern (format nil "~s-infix-op-printer" name))))
    `(progn
       (clean-up ',name)
       (setf (get ',name 'literalform) ,(format nil *math-format* str))
       (defun ,fn-name
         (term)
         (default-infix-printer
           term
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *infix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
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
                      (format nil *math-format* str))))
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
                      (format nil *math-format* str))))
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
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-prefix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
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
           ,(format nil *math-format* str)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-suffix-ops*)
       ,(cond (neg-str `(push (list ',name ',(format nil *math-format* neg-str))
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
           ,(concatenate 'string *math-begin* lhs-str)
           ,(concatenate 'string rhs-str *math-end*)))
       (push (list ',name (function ,fn-name))
             *fn-alist*)
       (push ',name *unary-abs-ops*)
       ',name)))

(defmacro declare-atom-printer (x v)
  `(let ((temp (assoc ',x *atom-alist*)))
     (if (null temp)
	 (setq *atom-alist* (cons (list ',x ,v) *atom-alist*))
	 (rplacd temp (list ,v)))))

(defmacro declare-fn-printer (x v)
  `(let ((temp (assoc ',x *fn-alist*)))
     (if (null temp)
	 (setq *fn-alist* (cons (list ',x ,v) *fn-alist*))
	 (rplacd temp (list ,v)))))

(defmacro declare-event-printer (x v)
  `(let ((temp (assoc ',x *event-printer-alist*)))
     (if (null temp)
	 (setq *event-printer-alist* (cons (list ',x ,v) *event-printer-alist*))
	 (rplacd temp (list ,v)))))


;                                    TABBING

; Infix-File generates text that uses the Latex `tabbing' or Scribe `format' environment, 
; setting a tab for each new level of indentation.  We find this a convenient
; sublanguage to target.  

; It appears based upon various experiment that perhaps Latex cannot handle tabs
; more than about 14 deep, or so.  

; The parameter, *latex-indent-number-limit*, could perhaps be increased if one 
; had a Latex wherein this limit has been raised.  However, it is a relatively rare
; function that needs terms that are more than 13 function calls deep.  When
; infix-file hits this limit in Latex mode, it falls back upon the standard Nqthm
; pretty-printer, and puts the result in a verbatim environment.

;; All of the following should be defined in the text-formatting init file,
;; e.g., latex-init.lisp or scribe-init.lisp.

(proclaim '(ftype (function nil t)
		  begin-tabbing
		  begin-group-tabbing
		  end-tabbing
		  set-margin
		  pop-margin
		  get-margin
		  pop-tab
		  do-tab
		  newline-to-current-margin
		  to-current-margin
		  force-newline-in-result))

(proclaim '(ftype (function (&optional t) t)
		  set-tab))

(proclaim '(ftype (function (character) t)
		  handle-special-chars
		  handle-special-chars-in-string char))


;                                  PRINT-ATOM

; We want to slashify special characters in the following three lists in
; case they appear in an Nqthm symbol.  Used only by print-atom and index.

(defparameter doc-special-chars  nil)
(defparameter doc-other-chars    nil)
(defparameter doc-index-specials nil)

; We also to handle the characters in doc-other-chars specially, by going into
; math mode, since slashification with backslash does not work.

(defun print-string (str &optional i)

; Our own printer, which slashifies (or otherwise quotes) the doc-special-chars and
; doc-other-chars in strings.  We print all Nqthm symbols with this
; function and print-atom because we want to avoid generating stuff that will make 
; the text formatter barf, e.g., in Latex, a symbol with an unslashified $, <, or { in it.

  (cond ((stringp str)
         (iterate for i below (length (the string str))
                  for char = (char (the string str) (the fixnum i))
                  do  (handle-special-chars-in-string char)
                  finally (incf *infix-loc* (or i (length str)))))
	((symbolp str)
	 (print-atom str i))
        (t (pprin1i str)))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))

(defun print-atom (atm &optional i)
  (declare (ignore i))

; Our own atom printer, which slashifies (or otherwise quotes) the doc-special-chars and
; doc-other-chars in symbols and strings.  We print all Nqthm symbols with this
; function because we want to avoid generating stuff that will make the text formatter barf,
; e.g., in Latex, a symbol with an unslashified $, <, or { in it.

  (cond ((symbolp atm)
         (iterate with str = (symbol-name atm)
                  for i below (length (symbol-name (the symbol atm)))
                  for char = (char (the string str) (the fixnum i))
                  do  (handle-special-chars char)
                  finally (incf *infix-loc* (or i (length str)))))
        ((stringp atm)
         (incf *infix-loc* (+ 4 (* 2 (length atm))))
         (pprinc *begin-tt-env*)
         (pprinc "\"")
         (iterate for i below (length atm)
                  for char = (char (the string atm) (the fixnum i))
                  do  (handle-special-chars-in-string char))
         (pprinc "\"")
         (pprinc *end-tt-env*))
        (t (pprin1i atm)))
  (cond ((and *testing*
              (> *infix-loc* *rightmost-char-number*))
         (throw 'advise-break t))))


;                             FONT SYMBOL PRINTERS

(defun bold-sym-printer (x &optional i)		; Print in bold face.
  (pprinc *begin-bold-env*)
  (if (symbolp x)
      (print-atom x i)
      (print-string x i))
  (pprinc *end-bold-env*))

(defun italic-sym-printer (x &optional i)		; Print in italic face.
  (pprinc *begin-italic-env*)
  (if (symbolp x)
      (print-atom x i)
      (print-string x i))
  (pprinc *end-italic-env*))

(defun tt-sym-printer (x &optional i)		; Print in typewriter font.
  (pprinc *begin-tt-env*)
  (if (symbolp x)
      (print-atom x i)
      (print-string x i))
  ;; We charge more for tt characters.
  (incf *infix-loc* (* (- *tt-size* 1) (our-flatc x)))
  (pprinc *end-tt-env*))

(defun small-caps-sym-printer (x &optional i)		; Print in small caps.
  (pprinc *begin-sc-env*)
  (if (symbolp x)
      (print-atom x i)
      (print-string x i))
  (pprinc *end-sc-env*))

(defun font-sym-printer (symbol font)
  (case font
    (bold   (bold-sym-printer symbol))
    (italic (italic-sym-printer symbol))
    (tt     (tt-sym-printer symbol))
    (sc     (small-caps-sym-printer symbol))
    (otherwise (format *terminal-io* "Bad font descriptor (~a) passed to subscript printer.~%" font)
	       (tt-sym-printer symbol))))

(defun subscript (x)
  (pprinc *begin-subscript*)
  (print-atom x)
  (pprinc *end-subscript*))

;                                   *ATOM-ALIST*

; *atom-alist* is one of the three tables off of which this printer is driven.
; It determines how a variable symbol is printed.  It is unlikely that anyone
; would want to change this unless translate changes because t, f, and nil are
; the only symbols that translate treats specially as constants instead of as
; variable symbols.

; We would like to put this at the beginning of the file but cannot, so we put
; a special declaration up there.

(defparameter *atom-alist*
  (list (list 't   (function bold-sym-printer))
        (list 'f   (function bold-sym-printer))
        (list 'nil (function bold-sym-printer))))

(defun default-atom-printer (var)

; We put variables in italics, strings in typewriter.

  (cond ((symbolp var) (italic-sym-printer var))
        ((stringp var) (print-atom var))
        ((numberp var) (tt-sym-printer var))
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
	 (quote-printer1-advise-break term))
        (t (quote-printer1-tt-form term))))

(defun tt-pprinci (term &optional (size 1))
  (pprinci *begin-tt-env* size)
  (pprinci term size)
  (pprinci *end-tt-env*))   

(defun quote-printer1-tt-form (term)
  (tt-pprinci "(" *tt-size*)
  (iterate for tail on term do
	   (progn (quote-printer1 (car tail))
		  (cond ((null (cdr tail)) (tt-pprinci ")" *tt-size*))
			((or (atom (cdr tail))
			     (eq (car (cdr tail)) *infix-comma*)
			     (eq (car (cdr tail)) *infix-comma-atsign*)
			     (eq (car (cdr tail)) *infix-backquote*))
			 (tt-pprinci *dotted-pair-separator*  4)
			 (quote-printer1 (cdr tail))
			 (tt-pprinci ")" *tt-size*)
			 (return))
			(t (tt-pprinci " " *tt-size*))))
	   until (atom (cdr tail))))
                                
(defun quote-printer1-advise-break (term)
  (tt-pprinci "(" *tt-size*)
  (set-margin)
  ;; (let ((*left-margin-tab-context* nil)) )
  (iterate for tail on term
	   do (progn (quote-printer1 (car tail))
		     (cond ((null (cdr tail))
			    (tt-pprinci ")" *tt-size*))
			   ((or (atom (cdr tail))
				(eq (car (cdr tail)) *infix-comma*)
				(eq (car (cdr tail)) *infix-comma-atsign*)
				(eq (car (cdr tail)) *infix-backquote*))
			    (newline-to-current-margin)
			    (tt-pprinci *dotted-pair-separator-newline* 4)
			    (quote-printer1 (cdr tail))
			    (tt-pprinci ")" *tt-size*)
			    (return nil))
			   ((and (or (atom (car tail)) (eq *infix-radix* (car (car tail))))
				 (cdr tail)
				 (or (atom (cadr tail)) (eq *infix-radix* (car (cadr tail))))
				 (not (advise-break (list 'quote (cadr tail)))))
			    (tt-pprinci " " *tt-size*))
			   (t (newline-to-current-margin))))
	   until (atom (cdr tail)))
  (pop-margin))

(defun quote-printer (term)
  (tt-pprinci "'" *tt-size*)
  (quote-printer1 (cadr term)))

(defun backquote-printer (term)
  (tt-pprinci "`" *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-printer (term)
  (tt-pprinci "," *tt-size*)
  (quote-printer1 (cadr term)))

(defun comma-atsign-printer (term)
  (tt-pprinci *comma-atsign* 4)
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

  (set-macro-character #\`
    #'(lambda (stream char)
       (declare (ignore char))
       (list *infix-backquote* (read stream t nil t))))
  (set-macro-character #\,
   #'(lambda (stream char)
       (declare (ignore char))
       (case (peek-char nil stream t nil t)
             ((#\@ #\.)
              (read-char stream)
              (list *infix-comma-atsign* (read stream t nil t)))
             (t (list *infix-comma* (read stream t nil t)))))))

(defun *infix-radix*-printer (term)
  (pprinc *math-begin*)
  (pprinc *begin-tt-env*)
  (iterate for ch in (cddr term) do (pprinci ch 2))
  (pprinc *end*)
  (pprinc *subscript*)			; "}_{"
  (pprinc *begin*)
  (pprin1i (cadr term))
  (pprinc *end-tt-env*)
  (pprinc *math-end*))

(defun subscript-printer (symbol subscript &optional (font 'tt))
  ;; Font must be one of bold, italic, tt, sc (small caps)
  (pprinc *math-begin*)
  (font-sym-printer symbol font)
  (pprinc *subscript*)			; "_" in latex
  (pprinc *begin*)
  (font-sym-printer subscript font)
  (pprinc *end*)
  (pprinc *math-end*))


; A FEW HAND-CODED FORM PRINTERS:  IF, COND, CASE, LET, FOR, FORALL and EXISTS.

(defun math-space (&optional (n 1))
  (cond (*do-not-use-tabs* (setq n 1)))
  (pprinc *math-begin*)
  (iterate for i from 1 to n do
           (pprinci *math-thick-space*))
  (pprinc *math-end*))

(defun math-thin-space (&optional (n 1))
  (cond (*do-not-use-tabs* (setq n 1)))
  (pprinc *math-begin*)
  (iterate for i from 1 to n do
           (pprinci *math-thin-space*))
  (pprinc *math-end*))

(defun condify (term)
  (let (x u v)
    (iterate with pairs
             while (match term (if x u v))
             do (progn (push (list x u) pairs)         ; ??? I put the push and setq into a PROGN ???
		       (setq term v))
             finally
             (progn (push (list t term) pairs)
                    (return (cons 'cond (reverse pairs)))))))

(defun if-printer (term)
  (cond ((null (cddr term))
	 (format *terminal-io* "~%Ill formed if-expression - ~a~%" term)
	 (cond-printer (condify (append term '(nil nil)))))
	((null (cdddr term))
	 (format *terminal-io* "~%Ill formed if-expression - ~a~%" term)
	 (cond-printer (condify (append term '(nil)))))
	(t (cond-printer (condify term)))))

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
               (set-margin)
	       ;; (let ((*left-margin-tab-context* nil))  )
	       (bold-sym-printer "if " 3)
	       (infix-print-term1 (car first-case))
	       (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
			(advise-break (cadr first-case)))
		      (newline-to-current-margin))
		     (t (math-space 1)))
	       (bold-sym-printer " then " 5)
	       (infix-print-term1 (cadr first-case))
	       (newline-to-current-margin)
	       (iterate for tail on (cdr cases) do
			(cond ((null (cdr tail))
			       (bold-sym-printer " else " 5)
			       (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
				 (infix-print-term1 (cadr (car tail))))
			       (math-space 1)
			       (bold-sym-printer " endif" 6)
			       (pop-margin))
			      (t (bold-sym-printer " elseif " 7)
				 (infix-print-term1 (caar tail))
				 (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
					  (advise-break (cadar tail)))
					(newline-to-current-margin))
				       (t (math-space 1)))
				 (bold-sym-printer " then " 5)
				 (infix-print-term1 (cadar tail))
				 (newline-to-current-margin)))))))))

(defun case-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cdddr term))
           (infix-print-term1 (cadr (caddr term))))
          (t (let ((cases (cddr term))
                   (first-case (car (cddr term))))
               (set-margin)
	       ;; (let ((*left-margin-tab-context* nil))   ... )
	       (bold-sym-printer "case on " 9)
	       (infix-print-term1 (cadr term))
	       (pprinci ":")
	       (newline-to-current-margin)             
	       (bold-sym-printer " case = " 7)
	       (infix-print-term1 (car first-case))
	       (newline-to-current-margin)
	       (bold-sym-printer " then " 5)
	       (infix-print-term1 (cadr first-case))
	       (newline-to-current-margin)
	       (iterate for tail on (cdr cases) do
			(cond ((null (cdr tail))
			       (bold-sym-printer " otherwise " 10)
			       (infix-print-term1 (cadr (car tail)))
			       (math-space 1)
			       (let ((*rightmost-char-number* (- *rightmost-char-number* 8)))
				 (bold-sym-printer "  endcase" 8))
			       (pop-margin))
			      (t (bold-sym-printer " case = " 6)
				 (infix-print-term1 (caar tail))
				 (newline-to-current-margin)
				 (bold-sym-printer " then " 5)
				 (infix-print-term1 (cadar tail))
				 (newline-to-current-margin)))))))))

(defun let-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((null (cadr term))
           (infix-print-term1 (caddr term)))
          (t (let ((lets (cadr term)))
               (set-margin)
	       ;; (let ((*left-margin-tab-context* nil)) .. )
	       (bold-sym-printer "let " 5)
	       (set-margin)
	       (cond ((symbolp lets) (infix-print-term1 lets))
		     (t (iterate for tail on lets
				 for let = (car tail)
				 do (progn (infix-print-term1 (car let))
					   (bold-sym-printer " be " 3)
					   (infix-print-term1 (cadr let))
					   (cond ((cdr tail)
						  (pprinci ", " 1))
						 (t (bold-sym-printer " in " 3) (pop-margin)))
					   (newline-to-current-margin)))))
	       (let ((*rightmost-char-number* (- *rightmost-char-number* 7)))
		 (infix-print-term1 (caddr term)))
	       (math-space 1)
	       (bold-sym-printer " endlet" 7)
	       (pop-margin))))))

; (defun for-printer (term)
;   (advise-break-if-testing)
;   (let ((*top-parens-eliminable* t))
;     (cond ((equal (length (cdr term)) 6)
;            (let ((*top-parens-eliminable* *top-parens-eliminable-default*))
;              (default-fn-printer term)))
;           (t (set-margin)
; 	     ;; (let ((*left-margin-tab-context* nil)) .. )
; 	     (bold-sym-printer "for " 4)
; 	     (default-atom-printer (cadr term))
; 	     (bold-sym-printer " in " 3)
; 	     (infix-print-term1 (cadddr term))
; 	     (newline-to-current-margin)
; 	     (cond ((eq (fifth term) 'when)
; 		    (bold-sym-printer " when " 5)
; 		    (infix-print-term1 (sixth term))
; 		    (newline-to-current-margin)
; 		    (setq term (cddr (cddddr term))))
; 		   (t (setq term (cddr (cddr term)))))
; 	     (math-space 1)
; 	     (bold-sym-printer (car term)) ; "{\\bf xxx }"
; 	     (math-space 1)
; 	     (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
; 	       (infix-print-term1 (cadr term)))
; 					; (math-space 1)
; 	     (bold-sym-printer " endfor" 6)
; 	     (pop-margin)))))

(defun make-alist-pairlist (l)
  (if (not (consp l))
      l
      (cons (list (caar l) (cdar l))
	    (make-alist-pairlist (cdr l)))))

(defun dequote (x) (if (and (listp x) (equal (car x) 'quote)) (cadr x) x))

(defun for-printer (term)
  (advise-break-if-testing)
  (let ((*top-parens-eliminable* t))
    (cond ((equal (length (cdr term)) 6)
	   ; 6 arg version.  Basic form.
	   ; (FOR 'var lst 'cond 'op 'body alist)
           ; (let ((*top-parens-eliminable* *top-parens-eliminable-default*))
	   ;   (default-fn-printer term))
	   (let ((var   (dequote (nth 1 term)))
		 (lst   (nth 2 term))
		 (cond  (dequote (nth 3 term)))
		 (op    (dequote (nth 4 term)))
		 (body  (dequote (nth 5 term)))
		 (alist (nth 6 term)))
	     (set-margin)
	     (bold-sym-printer "for " 4)
	     (default-atom-printer var)
	     (bold-sym-printer " in " 3)
	     (infix-print-term1 lst)
	     (newline-to-current-margin)
	     (bold-sym-printer " when " 5)
	     (infix-print-term1 cond)
	     (newline-to-current-margin)
	     (math-space 1)
	     (bold-sym-printer op) ; "{\\bf xxx }"
	     (math-space 1)
	     (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
	       (infix-print-term1 (list 'let (make-alist-pairlist alist) body)))
	     (bold-sym-printer " endfor" 6)
	     (pop-margin)))
          (t ; The 5 argument version: (FOR var IN lst op body)
	     ; The 7 argument version: (FOR var IN lst WHEN cond op body)
	     (set-margin)
	     ;; (let ((*left-margin-tab-context* nil)) .. )
	     (bold-sym-printer "for " 4)
	     (default-atom-printer (nth 1 term))
	     (bold-sym-printer " in " 3)
	     (infix-print-term1 (nth 3 term))
	     (newline-to-current-margin)
	     (cond ((eq (nth 4 term) 'when)
		    (bold-sym-printer " when " 5)
		    (infix-print-term1 (nth 5 term))
		    (newline-to-current-margin)
		    (setq term (cddr (cddddr term))))
		   (t (setq term (cddr (cddr term)))))
	     (math-space 1)
	     (bold-sym-printer (car term)) ; "{\\bf xxx }"
	     (math-space 1)
	     (let ((*rightmost-char-number* (- *rightmost-char-number* 6)))
	       (infix-print-term1 (cadr term)))
	     (bold-sym-printer " endfor" 6)
	     (pop-margin)))))

(defun forall-printer (term)
  (let (vars body)
    (match! term (forall vars body))
    (pprinci *forall* *tt-size*)
    (cond ((atom vars)
           (funcall (get-atom-printer vars) vars))
          (t (iterate for tail on vars do
                      (funcall (get-atom-printer (car tail)) (car tail))
                      (cond ((cdr tail)
                             (pprinci ", " *tt-size*))))))
    (pprinc ":")
    (math-space 1)
    (infix-print-term1 body)))

(defun exists-printer (term)
  (let (vars body)
    (match! term (exists vars body))
    (pprinci *exists* *tt-size*)
    (cond ((atom vars)
	   (funcall (get-atom-printer vars) vars))
          (t (iterate for tail on vars do
		      (funcall (get-atom-printer (car tail)) (car tail))
                      (cond ((cdr tail)
                             (pprinci ", " *tt-size*))))))
    (pprinc ":")
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
      (er hard (sym) |illegal| |object| |where| |function| |symbol| |expected| |:| SYM |.|))
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
		  (roman-font (car term))
                  (return-from default-fn-printer nil)))

; We want a very tiny space in front of the open parenthesis because otherwise,
; it looks like some function symbols touch the open parenthesis.  In some
; cases, this results in a touch more space than we like, and perhaps there
; exists a more delicate kerning command.

           (roman-font (car term))
	   (math-thin-space)
           (pprinci "("))
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

           (set-margin)
	   ;; (let ((*left-margin-tab-context* nil)) .. )
	   (iterate for tail on (cdr term)
		    do (progn (infix-print-term1 (car tail))
			      (cond ((cdr tail)
				     (pprinci ",")
				     ;; Each call of newline-to-current-margin will
				     ;; return to the indent we set.
				     (newline-to-current-margin))
				    (t
				     (pprinci ")")
				     ;; Now we get rid of the indent.
				     (pop-margin))))))
          (t
           (iterate for tail on (cdr term)
                    do (progn (infix-print-term1 (car tail))
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

;; Let set-margin and set-tab know if they are in a context where
;; we are using a left margin followed by a tab.
(defparameter *left-margin-tab-context* nil)

(defun default-infix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))

; We hate to see (member x (foo ...)) broken right after the x, where
; x is an atom.

    (cond ((and advice
                (not (and (equal (length term) 3)
                          (atom (cadr term)))))
	   (if (eq *infix-op-location* 'FRONT)
	       (smith-infix-print-tail op (cdr term) top-parens-were-eliminable)
	       (boyer-infix-print-tail op (cdr term) top-parens-were-eliminable)))
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

; See `SETTINGS THAT MAY BE MODIFIED IN MODE-THEORY.LISP' for a description
; of the difference between these two modes of printing.

(defun boyer-infix-print-tail (op args top-parens-were-eliminable)
  (set-tab)
  (iterate for tail on args
	   do
	   (progn (infix-print-term1 (car tail))
		  (cond ((cdr tail)
			 (newline-and-tab)
			 (math-space 5)
			 (pprinci op 3)
			 (newline-and-tab))
			(t (cond ((null top-parens-were-eliminable)
				  (pprinci ")")))
			   (pop-tab))))))

(defun smith-infix-print-tail (op args top-parens-were-eliminable)
  (set-margin)
  (set-tab op)
  ;; (let ((*left-margin-tab-context* t)) ... )
  (infix-print-term1 (car args))
  (iterate for tail on (cdr args)
	   do
	   (progn (to-current-margin)
		  (pprinci op 3)
		  (do-tab)
		  (infix-print-term1 (car tail))
		  (cond ((cdr tail)
			 (to-current-margin))
			(t (cond ((null top-parens-were-eliminable)
				  (pprinci ")")))
			   (pop-margin)
			   (newline-to-current-margin))))))

(defun default-unary-prefix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (pprinci op 3)
    (pprinci " ")
    (infix-print-term1 (cadr term))
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))

(defun default-infix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (if (eq *infix-op-location* 'FRONT)
	(smith-infix-multiple-printer term strs advice)
	(boyer-infix-multiple-printer term strs advice))
    (cond ((null top-parens-were-eliminable)
	   (pprinci ")")))))

(defun boyer-infix-multiple-printer (term strs advice)
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
    (pop-tab))

(defun smith-infix-multiple-printer (term strs advice)
  (set-margin)
  ;; (let ((*left-margin-tab-context* nil)) .. )
  (infix-print-term1 (cadr term))
  (iterate for arg in (cddr term)
	   as str in strs 
	   do (progn (cond (advice (newline-to-current-margin))
			   (t (pprinci " ")))
		     (pprinci str)
		     ;;(cond (advice (newline-to-current-margin))
		     ;;      (t (pprinci " ")))
		     (pprinci " ")
		     (infix-print-term1 arg)))
  (pop-margin))

(defun default-prefix-multiple-printer (term strs)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*)
         (advice (advise-break term)))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (set-margin)
    ;; (let ((*left-margin-tab-context* nil)) .. )
    (iterate for tail on (cdr term)
	     as str in strs
	     do (progn (pprinci str)
		       ;;(cond (advice (newline-to-current-margin))
		       ;;      (t (pprinci " ")))
		       (pprinci " ")
		       (infix-print-term1 (car tail))
		       (cond ((null (cdr tail)) nil)
			     (advice (newline-to-current-margin))
			     (t (pprinci " ")))))
    (pop-margin)
    (cond ((null top-parens-were-eliminable)
	   (pprinci ")")))))

(defun default-unary-suffix-printer (term op)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
    (cond ((null top-parens-were-eliminable)
           (pprinci "(")))
    (infix-print-term1 (cadr term))
    (pprinci " ")
    (pprinci op 3)
    (cond ((null top-parens-were-eliminable)
           (pprinci ")")))))
        
(defun default-unary-abs-printer (term lhs-str rhs-str)
  (let* ((top-parens-were-eliminable *top-parens-eliminable*)
         (*top-parens-eliminable* *top-parens-eliminable-default*))
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

; Should be re-defined in mode-init.lisp, e.g. latex-init.lisp.

(defparameter index-subitem-length 30)

(defun index (x &optional subkind)
  ;; Subkind must be string or atom.
  (pprinc *begin-index*)
  (print-atom x)
  ;; WARNING: Latex/Scribe dependency.
  (if subkind
      (cond ((stringp subkind) (pprinc ", ") (print-string subkind))
	    ((symbolp subkind) (pprinc ", ") (print-atom subkind))
	    (t nil)))
  (pprinc *end-index*))


;                                EVENT PRINTERS

(defun print-default-event-header ()
  (pformat *standard-output* *print-default-event-header*))

(defun no-tab-event-trailer ()
  (pformat *standard-output* *no-tab-event-trailer*))

(defun default-event-printer (event)
  (pwrite-char #\Newline)
  (begin-tabbing)
  (small-caps-sym-printer "Event:  ")
  (new-tab-row t)
  (pprinc "The fact that we do not do a better job printing 
this event means that this event is of type unknown to us. ")
  (new-tab-row t)
  (quote-printer1 event)
  (end-tabbing))

(defun boot-strap-printer (term)
  (pwrite-char #\Newline)
  (begin-group-tabbing)
  (small-caps-sym-printer "Event:  ")
  (pformat *standard-output* "~%Start with the initial ")
  (bold-sym-printer (case (cadr term)
		      ((thm nil) "thm")
		      (nqthm "nqthm")))
  (pformat *standard-output* " theory.")
  (end-tabbing))

(defun compile-uncompiled-defns-printer (term)
  (declare (ignore term))
  (pwrite-char #\Newline)
  (begin-group-tabbing)
  (small-caps-sym-printer "Event:  ")
  (pprinc "For efficiency, compile those definitions not yet compiled.")
  (end-tabbing))

(defun prove-lemma-printer (term)
  (pwrite-char #\Newline)
  (begin-group-tabbing)
  (small-caps-sym-printer "Theorem:  ")
  (print-atom (cadr term))
  (index (cadr term))
  (new-tab-row t)
  (infix-print-term (cadddr term))
  (end-tabbing))

(defun add-axiom-printer (term)
  (pwrite-char #\Newline)
  (begin-group-tabbing)
  (small-caps-sym-printer "Axiom:  ")
  (print-atom (cadr term))
  (index (cadr term))
  (new-tab-row t)
  (infix-print-term (cadddr term))
  (end-tabbing))

(defun dcl-printer (term)
  (pwrite-char #\Newline)
  (begin-group-tabbing)
  (small-caps-sym-printer "Event:  ")
  (pprinc "Introduce the function symbol ")
  (italic-sym-printer (cadr term))
  (index (cadr term))
  (cond ((equal 1 (length (caddr term)))
         (pprinc " of one argument."))
        (t (pformat *standard-output* " of ~a arguments." (length (caddr term)))))
  (end-tabbing))

(defparameter *noindent* nil)

(defun constrain-printer (term)
  (pwrite-char #\Newline)
  (begin-tabbing)
  (small-caps-sym-printer "Conservative Axiom:  ")
  (print-atom (cadr term))
  (index (cadr term))
  (new-tab-row t)
  (infix-print-term (cadddr term))
  (end-tabbing)
  (let ((wa (car (cddddr term))))
    (cond (wa
           (pprinc *noindent*)
           (pprinc "Simultaneously, we introduce")
           (cond ((null (cdr wa))
                  (pprinc " the new function symbol ")
                  (italic-sym-printer (caar wa))
                  (pprinc "."))
                 ((null (cddr wa))
                  (pprinc " the new function symbols ")
                  (italic-sym-printer (caar wa))
                  (pprinc " and ")
                  (italic-sym-printer (caadr wa))
                  (pprinc "."))
                 ((null (cddr wa))
                  (pprinc " the new function symbols ")
                  (italic-sym-printer (caar wa))
                  (pprinc " and ")
                  (italic-sym-printer (caadr wa))
                  (pprinc "."))
                 (t (pprinc " the new function symbols ")
                    (iterate for tail on wa do
                             (italic-sym-printer (caar tail))
                             (cond ((cdr tail)
                                    (pprinc ", ")
                                    (cond ((null (cddr tail))
                                           (pprinc "and "))))))
                    (pprinc ".")))
	   (no-tab-event-trailer)))))

(defun defn-printer1 (term equiv)
  (let* ((form (cons (cadr term) (caddr term)))
	 (body (cadddr term))
	 (eq (list equiv form body)))
    (pwrite-char #\Newline)
    (begin-group-tabbing)
    (small-caps-sym-printer "Definition: ")
    (index (cadr term) "defined")
    ; I will always go to a new line.
    ;(cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
    ;        (advise-break eq))
    ;       (pprinc *new-tab-row*))
    ;      (t (math-space 2)))
    (to-current-margin)
    ;; Can we fit the defn on one line?
    (cond ((let ((*rightmost-char-number* (- *rightmost-char-number* 12)))
            (advise-break eq))
	   ;; No.
	   (infix-print-term1 form)
	   (newline-to-current-margin)
	   (format *standard-output* " ~a " (get equiv 'literalform))
	   (new-tab-row t)
	   (infix-print-term body))
          (t (infix-print-term1 form)
	     (pprinc (format nil " ~a " (get equiv 'literalform)))
	     (infix-print-term1 body)))
    (to-current-margin)
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
  (pprinc "Start with the library:")
  (force-newline-in-result)
  (print-atom (cadr term))
  (cond ((caddr term)
         (pprinc ".  Using the compiled version."))
        (t (pprinc ".")))
  (no-tab-event-trailer))

(defun do-file-printer (term)
  (print-default-event-header)
  (pprinc "Do all forms in the file:")
  (force-newline-in-result)
  (print-atom (cadr term))
  (pprinc ".")
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
    (pprinc "Let us define the theory ")
    (italic-sym-printer name)
    (pprinc " to consist of the following events: ")
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
        (t (pprinc *lbrace*)
           (iterate for tail on (cadr term) do
                    (print-atom (car tail))
                    (cond ((cdr tail)
                           (pprinc ", "))))
           (pprinc *rbrace*)
           (pprinc ".")))
  (no-tab-event-trailer))

(defun enable-theory-printer (term)
  (print-default-event-header)
  (pprinc "Enable theory ")
  (print-atom (cadr term))
  (cond ((atom (cadr term))
         (print-atom (cadr term))
         (pprinc "."))
        (t (pprinc *lbrace*)
           (iterate for tail on (cadr term) do
                    (print-atom (car tail))
                    (cond ((cdr tail)
                           (pprinc ", "))))
           (pprinc *rbrace*)
           (pprinc ".")))
  (no-tab-event-trailer))

(defun setq-printer (term)
  (print-default-event-header)
  (let (name value)
    (match term (setq name value))
    (pformat *standard-output* "Give the Nqthm control variable ")
    (tt-sym-printer name)
    (pformat *standard-output* " the value ")
    (tt-sym-printer value)
    (pformat *standard-output* "."))
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
        (list 'definition (function defn-printer))
        (list 'compile-uncompiled-defns (function compile-uncompiled-defns-printer)) 
        (list 'boot-strap (function boot-strap-printer))
        (list 'note-lib (function note-lib-printer))
        (list 'make-lib (function make-lib-printer))
        (list 'do-file (function do-file-printer))))

(defparameter *save-event-printer-alist* *event-printer-alist*)

(defun get-event-printer (sym)
  (let ((a (assoc sym *event-printer-alist*)))
    (cond (a (cadr a))
          (t (function default-event-printer)))))


;                           COPY COMMENTS

;; MKS Tue Jul 13 1993
;; Make ;- comments and BAR-COMMENTs followed by a dash appear in
;; a formatted (in Latex, verbatim) environment.

(defparameter *comment-environment* nil)

(defparameter *comment-format* "Smith")

(defparameter *comment-semi-net* nil)
(defparameter *comment-lb-net* nil)

;; We use this two stage template/eval kludge so that if the template can 
;; be used to reset the variable after the user has defined these variables.

;; Note a problem with this flexibility.  In some contexts we need to format 
;; special characters and in others we don't.  Thus in LaTeX, in a Verbatim
;; we don't need to quote `_', but in running text we do need to quote it.

(defparameter *comment-environment-mapping-template*
  (quote `((text     "" "")
	   (format   ,*begin-format-env*   ,*end-format-env*)
	   (verbatim ,*begin-verbatim-env* ,*end-verbatim-env*)
	   (emphasis ,*begin-emphasis-env* ,*end-emphasis-env*)
	   (section ,*begin-section-env*   ,*end-section-env*))))

(defparameter *comment-environment-mapping*
  (eval *comment-environment-mapping-template*))

(defparameter *saved-whitespace* nil)

(defun wrap-up-copy-comments ()
  (setq *saved-whitespace* nil)
  (end-environment)
  (throw 'copy-comments nil))

(defun begin-environment (env)
  (setq *comment-environment* env)
  (pformat *standard-output*
	   (or (cadr (assoc env *comment-environment-mapping*)) "")))

(defun end-environment ()
  (if *comment-environment*
      (pformat *standard-output*
	       (or (caddr (assoc *comment-environment*
				 *comment-environment-mapping*))
		   "")))
  (setq *comment-environment* nil))

(defun end-environment-and-write (c)
  (end-environment)
  (pwrite-char c))

(defun pop-environment-write-and-push (string)
  (let ((saved-env *comment-environment*))
    (if (not saved-env)
	(pprinc string)
	(progn (end-environment)
	       (pprinc string)	     
	       (begin-environment saved-env)))))

(defun end-environment-if-not (env)
  (if (not (equal *comment-environment* env))
      (end-environment)))

(defun white-space-string-p (s)
  (let ((x t))
    (iterate for i from 0 to (- (length s) 1) 
	     do (setq x (and x (member (char s i) *white-space*))))
    x))

(defun insert-newpage ()
  (pop-environment-write-and-push (pformat nil "~%~a~%" *newpage*)))

(defun check-environment-and-write (env ch)

  ;; Note: Latex causes an error on an empty VERBATIM environment, so we watch out
  ;; for that as a special case.  Also, Latex forbids control-l in a verbatim
  ;; environment, so we watch out for that, too.

  ;; Thus, we forbid any empty environments, and we always pull a page break 
  ;; out of the current environment.

  ;; First, end an existing environment if it is not ENV.

  (end-environment-if-not env)

  (cond ((not *comment-environment*)	; We are in no environment.  Enter one.
	 (cond ((and ch (not (member ch *white-space*)))
		(begin-environment env)
		(iterate for c in *saved-whitespace*
			 do (if (stringp c) (pprinc c) (pwrite-char c)))
		(setq *saved-whitespace* nil))
	       ((and ch (eql ch #\Page) (equal env 'verbatim))
		(setq *saved-whitespace*
		      (append *saved-whitespace*
			      (list (format nil "~%~a~%" *newpage*)))))
	       (ch (setq *saved-whitespace*
			(append *saved-whitespace* (list ch)))))))
  ;; Tabs
  (cond ((and (equal env 'verbatim)
	      (eql ch #\Tab) 
	      (not *reported-tabs*))
	 (setq *reported-tabs* t)
	 (pformat *terminal-io* 
		  "WARNING: about tabs!~%We note the presence of a tab ~
                  in a comment that we are copying~%into a verbatim ~
                  environment.  Tabs will be treated just like ~%single spaces ~
                  by Latex.  Consider removing all tabs, e.g., ~%with the ~
                  Emacs command M-x untabify.~%")))

  ;; Print it or not, checking #\Page.
  (cond (*saved-whitespace*)
	((and (eql ch #\Page) (equal env 'verbatim))
	 (end-environment)
	 (pformat *standard-output* "~%~a~%" *newpage*)
	 (begin-environment env))		
	(ch (pwrite-char ch))))

(defun copy-comments-read-char ()
       (let ((c (read-char *copy-comments-in-file* nil a-very-rare-cons)))
         (cond ((eq c a-very-rare-cons)
		;; We are no longer in a comment.  
		;; Exit whatever environment we are in, which will be either
		;; verbatim, format, or none.
                (wrap-up-copy-comments))
               (t c))))

(defun copy-comments-read-net (net)
  ;; Net is cdr of a net whose car = #\;
  ;; Have already read a #\; 
  ;;
  ;; Test (progn (read-char)(COPY-COMMENTS-READ-NET *comment-semi-net*))
  ;;
  (let* ((subnet (car net))
	 (action (cadr net))
	 (c (copy-comments-read-char)) ; on EOF does a throw out once it cleans up.
	 (branch (assoc c subnet)))
    (cond ((null branch) 
	   (unread-char c *copy-comments-in-file*)
	   (list (car action) (cadr action)))
	  (t (copy-comments-read-net (cdr branch))))))

(defun copy-comments (*copy-comments-in-file*)

; This function tries to sneak up to the next top-level open parenthesis,
; parsing all of the Lisp comments up till there.
; NOTE:  Jul 13 93 MKS 
; Random atoms, nubmers, strings and characters are treated as if they were in
; comments.  And are printed in a FORMAT environment.

  (let (*comment-environment*)
    (catch 'copy-comments
      (iterate
       for ch = (copy-comments-read-char)

; The top level loop for simulating the skimming of whitespace and comments
; that READ would perform to get to the next open parenthesis.

       (case ch

; Semicolon starts a comment.  If the semicolon is followed by a backslash, then
; we treat the rest of the line as input to the text formatter, rather than putting 
; it into a verbatim.  Ditton if the comment begins with ;;.
; Jul 13 93 MKS 
; If it is followed by a dash (-) we assume it should go into a FORMAT environment.
; Which in Latex is just a VERBATIM, but without the comment chars and -  at the 
; beginning of the line.

	 (#\;				
	  (let ((action (copy-comments-read-net *comment-semi-net*)))
	    (check-environment-and-write (car action) (cadr action))
	    (iterate for ch = (copy-comments-read-char)
		     do (progn (cond ((eql ch #\Page) (insert-newpage))
				     (*comment-environment* (pwrite-char ch))
				     (t (check-environment-and-write (car action) ch)))
			       (if (eql ch #\Newline) (return))))))

; #\| starts a comment.  If it is is followed by a backslash, then we treat the
; rest of the comment as something to be formatted (Latex in TeX mode) 
; rather than putting it into a verbatim.   \|# ends one. 

	 (#\#
	  (setq ch (copy-comments-read-char))
	  (cond ((not (eql ch #\|))
		 (error "Do not know how to handle #~s while copying at the top level." ch)))
	  (let ((action (copy-comments-read-net *comment-lb-net*)))
	    
	    ;; The following may not put us into an env if (cadr
	    ;; action) is whitspace.
	    (check-environment-and-write (car action) (cadr action))

	    ;; We ignore formatting changes within imbedded #| |# comments.
	    ;; They are stuck with whatever the outermost comment
	    ;; decreed.

	    (iterate for ch = (copy-comments-read-char)
		     with number-deep = 1
		     do
		     (cond ((eql ch #\|)
			    (let ((ch (copy-comments-read-char)))
			      (cond ((eql ch #\#)
				     (decf number-deep 1)
				     (cond ((= number-deep 0)
					    (end-environment)
					    (return)))))
			      (if *comment-environment*
				  (progn (pwrite-char #\|) (pwrite-char ch))
				  (progn (check-environment-and-write (car action) #\|)
					 (pwrite-char ch)))))
			   ((eql ch #\#)
			    (let ((ch (copy-comments-read-char)))
			      (if (eql ch #\|)
				  (incf number-deep 1))
			      (if *comment-environment*
				  (progn (pwrite-char #\|) (pwrite-char ch))
				  (progn (check-environment-and-write (car action) #\|)
					 (pwrite-char ch)))))
			   ((eql ch #\Page) (insert-newpage))
			   (*comment-environment* (pwrite-char ch))
			   (t (check-environment-and-write (car action) ch))))))

	 ;; A raw ^L at the top level, not in a comment.
	 (#\Page (end-environment)
	  (pformat *standard-output* "~%~a~%" *newpage*))

	 (#\(
	  (unread-char #\( *copy-comments-in-file*)
	  (wrap-up-copy-comments))
	 (otherwise (pwrite-char ch)))))))


;;--------------------------------------------------------------------------------
;
;                       COMMENT FORMATS
;

(defparameter *comment-format-alist* nil)
(defparameter *comment-format* nil)

(defun update-alist (al key value)
  (cond ((not (consp al)) (list (cons key key value)))
	((eq key (caar al)) (cons (cons key value) (cdr al)))
	(t (cons (car al) (update-alist (cdr al) key value)))))

(defun define-comment-format (n format)
  ;; Last call to this sets *comment-format*.
  ;; Can be overruled by 
  ;;  1. assigning directly to *comment-format*,
  ;;  2. calling (setup-comment-format format-name), or 
  ;;  3. calling infix-setup with the appropriate arguments.
  (cond ((assoc n *comment-format-alist*)
	 (if (check-comment-character-net)
	     (progn (setq *comment-format* n)
		    (setq  *comment-format-alist* (update-alist *comment-format-alist* n format)))
	     (format *terminal-io* "~%Ill formed definition for comment format")))
	(t (setq *comment-format* n)
	   (setq *comment-format-alist* (cons (cons n format) *comment-format-alist*)))))

(define-comment-format 'boyer
  '((#\; (("\\"   t   text))
     nil verbatim #\;)
    (#\# (("\\"   t   text))
     nil verbatim)))

(define-comment-format 'smith
  '((#\; (("\;"   t   format   )
	  ("\;\;" t   verbatim )
	  ("\\"   t   text     )
	  ("-"    t   format   )
	  ("+"    t   verbatim )
	  ("!"    t   emphasis )
	  ("\;\\" nil   text     #\;)
	  ("\;-"  nil   format   #\;)
	  ("\;+"  nil   verbatim #\;)
	  ("\;!"  nil   emphasis #\;))
     t text)
    (#\# (("\\"   t   text     )
	  ("-"    t   format   )
	  ("\;"   t   verbatim ))
     t text )))

(define-comment-format 'CL
  '((#\; (("\;"   t    format )
	  ("\;\;" t    text   )
	  ("\;\;\;" t  section)

	  ("\\"   t   text     )
	  ("-"    t   format   )
	  ("+"    t   verbatim )
	  ("!"    t   emphasis )
	  ("\;\\" nil   text     #\;)
	  ("\;-"  nil   format   #\;)
	  ("\;+"  nil   verbatim #\;)
	  ("\;!"  nil   emphasis #\;))
     t emphasis)
    (#\# (("\\"   t   text     )
	  ("-"    t   format   )
	  ("\;"   t   verbatim ))
     t text )))

(defun setup-comment-format (&optional n)
  (cond ((and n (assoc n *comment-format-alist*)) (setq *comment-format* n))
	((null *comment-format*)
	 (cond ((eq *infix-op-location* 'FRONT)
		(setq *comment-format* 'smith))		;(format *terminal-io* "~%Because infix-op-location = front - ")
	       ((eq *infix-op-location* 'BACK)
		(setq *comment-format* 'boyer))		;(format *terminal-io* "~%Because infix-op-location = back - ")
	       (t (setq *comment-format* 'smith)))      ;(terpri)
	 ;(format *terminal-io* "Setting comment preference to ~a." *comment-format*)
	 )
	((and *comment-format*
	      (assoc *comment-format* *comment-format-alist*)))
	(t (setq *comment-format* 'smith)))
  (compute-comment-character-net)
  ;; We have side-effected *comment-semi-net* and *comment-lb-net*
  ;; Update mapping info AFTER users theory file loaded.
  (setq *comment-environment-mapping* (eval *comment-environment-mapping-template*)))

(defun check-comment-character-net ()
  (let ((l (assoc *comment-format* *comment-format-alist*)))
    (if (null l)
	(format *terminal-io* "*COMMENT-FORMAT* is not present in *COMMENT-FORMAT-ALIST*."))
    (if (not (assoc #\; l))
	(format *terminal-io* "Selected comment format should include a list labelled \"\;\"."))
    (if (not (assoc #\# l))
	(format *terminal-io* "Selected comment format  should include a list labelled \"\#\"."))
    ;; Each branch is of the form (string flag environment [echo-character])
    (check-comment-character-net2 l)))

(defun check-comment-character-net2 (l)
  (cond ((null l) t)
	((and (listp l)
	      (listp (car l))
	      (characterp (caar l))
	      (every (function (lambda (branch)
			    (if (check-comment-character-branch branch)
				t
				(format *terminal-io* "Ill-formed branch in *COMMENT-FORMAT-ALIST*.~
                                                       ~%~a" branch))))
		     (cadr (car l)))
	      (let ((top (cddr (car l))))
		(and (or (equal (car top) 't) (null (car top)))
		     ;; Must be known environment.
		     (assoc (cadr top) *comment-environment-mapping*)
		     (or (null (cddr top)) (characterp (caddr top))))))
	 ;; Do the other one, if there.
	 (check-comment-character-net2 (cdr l)))
	(t nil)))

(defun check-comment-character-branch (b)
  (and (listp b)
       (> (length b) 2)
       (stringp (car b))
       (or (equal (cadr b) 't) (null (cadr b)))
       ;; Must be known environment.
       (assoc (caddr b) *comment-environment-mapping*)
       (or (null (cdddr b))
	   (characterp (cadddr b)))))

(defun compute-comment-character-net ()
  (let ((l (cdr (assoc *comment-format*  *comment-format-alist*))))
    (let ((net (assoc #\; l)))
      (setq *comment-semi-net*
	    (if net
		(cdr (compute-net -1 (car net) (cadr net) (caddr net) (cdddr net)))
		nil)))
    (let ((net (assoc #\# l)))
      (setq *comment-lb-net*
	    (if net
		(cdr (compute-net -1 (car net) (cadr net) (caddr net) (cdddr net)))
		nil)))))

(defun compute-net (n char net skip-one-blank-p default)
  (list char
	(append (if skip-one-blank-p
		    `((#\  nil ,default))
		    nil)
		(compute-branches (+ n 1) net))
	default))

(defun compute-branches (n net)
  (cond ((null net) nil)
	(t (merge-net (compute-branch n (car net))
		      (compute-branches n (cdr net))))))

(defun compute-branch (n branch)
  ;; branch is of the form (string flag . default)
  (let ((string (car branch))
	(flag (cadr branch))
	(default (cddr branch)))
  (cond ((> n (length string)) nil)
	((= n (length string))
	 (if flag
	     `(#\  nil ,default)
	     nil))
	(t (append (list (char string n)
			 (list (compute-branch (+ n 1) branch)))
		   (if (= (+ n 1) (length string)) (list default) nil))))))

(defun merge-net (branch net)
  ;; All branches of net begin with a unique character.
  ;; As does the result.
  (cond ((null net) (list branch))
	((char= (car branch) (caar net))
	 (let ((def1 (caddr branch))
	       (def2 (caddr (car net))))
	   (cons (list (car branch)
		       (merge-net (caadr branch) (cadr (car net)))
		       (cond ((equal def1 def2) def1)
			     ((and def1 def2)
			      (format *terminal-io* "Your comment network is in conflict ~a ~a." branch (car net))
			      def1)
			     (def1 def1)
			     (t def2)))
		 (cdr net))))
	(t (cons (car net) (merge-net branch (cdr net))))))

;; End of comment stuff.

(defun infix-form (form &key ((:print-case *print-case*) :downcase))
  (let ((*top-parens-eliminable* t)
        (*print-pretty* nil))
    (cond ((catch 'taboverflow
             (let ((*tabs-in* 1))
               (or *do-not-use-tabs* (begin-tabbing))
               (infix-print-term1 form)
               (or *do-not-use-tabs* (end-tabbing))
               nil))
           (pformat *terminal-io* "~%Sorry.  Exceeded Latex tabbing limit.~%~
                                   ~%Use the normal pretty printer on that one.~%~%"
                   form))))
  nil)

(DEFUN PPE-fmt (NAME)
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

(defparameter *last-mode* nil)

(defparameter *infix-trace* nil)

(defun current-directory ()
  ;; This is somewhat redundant.  
  ;; That is (probe-file file) should equal 
  ;; (probe-file (concatenate 'string (current-directory) file))
  ;; But we let *current-directory* also be set by the input file.
  (probe-file "./"))

;; This may be set by the function above or based on the directory of the input file.
(defparameter *current-directory* nil)

(defun probe-theory (fl)
  (or (probe-file (concatenate 'string fl "-theory.lisp"))
      (probe-file (concatenate 'string *current-directory* fl "-theory.lisp"))
      (probe-file (concatenate 'string *infix-directory* fl "-theory.lisp"))))

;; Check that *infix-directory* contains at least a latex and scribe theory.
(eval-when (load eval)
	   (if (not (and (probe-theory "scribe") (probe-theory "latex")))
	       (format *terminal-io* "~%Seem to be missing theory of scribe or latex or both.~%")))

(defun infix-file (fl &key ((:print-case *print-case*) :downcase)
		      (mode nil)
                      (chars-wide 77)
                      (nq *nq-default*))

  (let ((*current-directory* (or (directory-namestring fl) (current-directory))))
    (cond ((and mode (string= mode *infix-mode*))
	   (format t "~%Processing in ~a mode.~%" mode))
	  ((stringp mode)
	   (setq *infix-mode* mode)
	   (format t "~%Entering ~a mode.~%" *infix-mode*)
	   (load-infix-init-file))
	  (mode
	   (setq *infix-mode* (string mode))
	   (format t "~%Entering ~a mode.~%" *infix-mode*)
	   (load-infix-init-file))
	  ((probe-theory fl)
	   (setq *infix-mode* (pathname-name fl))
	   (format t "~%Entering ~a mode.~%" *infix-mode*)
	   (load-infix-init-file))
	  ((null *infix-mode*)
	   (cond ((y-or-n-p "Enter Latex mode? ")
		  (setq *infix-mode* "latex"))
		 ((y-or-n-p "Enter Scribe mode? ")
		  (setq *infix-mode* "scribe"))
		 (t (setq *infix-mode* nil)))
	   (if *infix-mode*
	       (progn (format t "~%Entering ~a mode.~%" *infix-mode*)
		      (load-infix-init-file))))
	  (t (format t "~%Remaining in ~a mode.~%" *infix-mode*)))

; infix-file takes a root file name, e.g., foo, reads the file foo.events,
; which we suppose has been previously checked by prove-file, and creates the
; file foo.tex, which the user can then run through Latex, etc.  By default, we
; lowercase all variable and function symbols, but the user can override this
; with the keyword parameter.

; If the keyword nq is given as true, then we first generate fl.nqxxx and then
; invoke nqfmt2fmt, generating fl.xxx (.tex or .mss).

    ;; Update comment information AFTER users theory file loaded.
    (setup-comment-format)

    (if *infix-mode*
	(let ((infl	 (extend-file-name fl file-extension-events))  ; "events"
	      ;; .mss, .tex, .nqmss, .nqtex
	      (outfl	 (extend-file-name fl (fmtfile-extension *infix-mode* nq)))  
	      (a-very-rare-cons (cons nil nil))
	      (*print-pretty* nil)
	      (*top-parens-eliminable* t)
	      (*readtable* (copy-readtable nil))
	      (*reported-tabs* nil)
	      (*infix-loc* 0)
	      (*left-margin* 0)
	      (*rightmost-char-number* chars-wide)
	      (count 1)
	      inpos)
	  (smash-infix-readtable)
	  (with-open-file
	   (instr infl :direction :input)
     
	   (with-open-file

; We do *all* of our printing of terms to *standard-output*, giving princ only
; one argument.

	    (*standard-output* outfl :direction :output :if-exists :rename-and-delete)

; The formatting system opening.

	    (pformat *standard-output* *standard-prelude*)
	    (iterate for form = (progn (copy-comments instr)
				       ;; Set this here so we don't rewrite preceding comment, 
				       ;; if tabs overflow.
				       (setq inpos (file-position instr))
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
					   (if *infix-trace*
					       (format *terminal-io* "~% ~a " (car form)))
					   ;; Let the user know we are making some kind of progress, every 10 events.
					   (if (= count 10) (progn (format *terminal-io* ".") (setq count 1))
					       (incf count))
					   (funcall (get-event-printer (car form)) form))
					 nil)
				       (pformat *terminal-io* "~%Warning: Tab limit reached in event ~a.~
                                             ~%Just copying that one.~%~%"
						(cadr form))
				       t)))
			    ;; If taboverflow, go back to where we started printing and
			    ;; print over the previous stuff.  In the 'commment case our
			    ;; position is unchanged.
			    (file-position *standard-output* outpos)
			    ;; (pformat *standard-output* "~%%~a~%~a~%" *begin-item* *begin-verbatim-env*)
			    ;; (pformat *standard-output* "~%~a" *begin-verbatim-env*)
			    (begin-environment 'verbatim)
			    (let ((stop (file-position instr)))
			      (file-position instr inpos)
			      (iterate while (< (file-position instr) stop)
				       do (check-environment-and-write 'verbatim (read-char instr))))
			    ;; (pformat *standard-output* "~%~a~a~%" *end-verbatim-env* *end-item*)
			    (end-environment 'verbatim))
			   (t nil)))
	    (pformat *standard-output* *standard-postlude*)))
	  (if nq
	      (nqfmt2fmt fl)
	      outfl))
	(format t "~%No mode specified (e.g. Latex or Scribe), aborting.~%"))))

(defun load-obj-or-lisp (file root)
  (let* ((suffix (if (member 'sparc *features*)
		    "-sparc.o"
		    "-sun.o"))
	 (object (concatenate 'string root suffix)))
    (if (and (probe-file object)
	     (> (file-write-date object) (file-write-date file)))
	(load object)
	(load file))))

(defun load-theory-or-init (dir)
  (let* ((initroot   (concatenate 'string dir *infix-mode* "-init"))
	 (initfile   (concatenate 'string initroot ".lisp"))
	 (theoryroot (concatenate 'string dir *infix-mode* "-theory"))
	 (theoryfile (concatenate 'string theoryroot ".lisp")))
    ;; We assume that, if present, the -theory file loads the -init file.
    (cond ((probe-file theoryfile)
	   (load-obj-or-lisp theoryfile theoryroot) t)
	  ((probe-file initfile)
	   (load-obj-or-lisp initfile initroot) t)
	  (t nil))))

(defun load-infix-init-file ()
  (clean-up-everything)
  (cond ((null *infix-mode*)
	 (format t "~%Failed to initialize.  *infix-mode* is NIL.~%"))
	((not (stringp *infix-mode*))
	 (format t "~%Failed to initialize.~
                    ~%*infix-mode* (~a) is not a string.~%" *infix-mode*))
	((load-theory-or-init *current-directory*))
	((load-theory-or-init *infix-directory*))
	(t (format t "~%Failed to initialize.  No init or theory file in ~a nor ~a.~%"
		   *current-directory* *infix-directory*)
	   (setq *infix-mode* nil))))

(defun fmtfile-extension (mode nq)
  (cond ((and *mode-extension* (stringp *mode-extension*))
	 (if nq (concatenate 'string "nq" *mode-extension*) *mode-extension*))
	((string= mode "latex")
	 (if nq "nqtex" "tex"))
	((string= mode "scribe")
	 (if nq "nqmss" "mss"))
	(t (if nq "nqnq" "nq"))))

(defun fmt2fmt-extension (remove! mode)
  (cond (remove! "stripped")
	((and *mode-extension* (stringp *mode-extension*))
	 (concatenate 'string "nq" *mode-extension*))
	((string= mode "latex")  "nqtex")
	((string= mode "scribe") "nqmss")
	(t "nqnq")))

;; Pulled in from /usr/local/src/nqthm-1992/infix.lisp
;; Aug  6 93 MKS 
;; What else was fixed after I grabbed this stuff!

(defparameter nqtex-white-space '(#\Space #\Newline #\Tab #\Page #\Return))

(defparameter nqtex-normal-clause-enders '(#\. #\! #\? #\, #\; #\:))

(defparameter nqtex-break-chars '(#\( #\) #\` #\' #\" #\; #\,))

(defun nqthm-read-preserving-whitespace-error (instr)
  (error "A character for an integer or an Nqthm symbol was expected at location ~a of input."
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

(defparameter nqtex2tex-chars
  (coerce "eipqtv" 'list))


;             NQFMT2FMT

(defun nqfmt2fmt (fl &key
                  ((:print-case *print-case*) :downcase)
                  ((:left-margin *left-margin*) 5)
                  (just-remove-! nil))

; Copies the file fl.nqxxx file to the file fl.xxx file, replacing Nqthm forms
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
; conventional notation for ev.  We may introduce line breaks via tabbing commands.
; Mnemonic: E -- think Event.

; !Ifoo, where foo is a symbol, results in foo, but with with formatting sensitive
; characters quoted.  For example, in TeX, !Ia$b would result in a\$b.  
; Mnemonic: I -- think Identity.

; !Pfm, where fm is an Nqthm term, e.g., (plus x y), results in conventional
; mathematical notation for fm.  May introduce line breaks via tabbing.
; Mnemonic: P -- think Pretty print.

; !Qfn, where fn is a symbol, results in fn surrounded by single gritches,
; after formatting sensitive characters have been quoted, e.g., !qfoo results in
; `foo' in TeX.  Useful for distinguishing function symbols from other words in a
; sentence, since function symbols appear in Roman.  
; Mnemonic: Q -- think Quoted.

; !Tfm, where fm is an Nqthm term, results in conventional mathematical
; notation for fm, but without any line breaks.  
; Mnemonic: T -- think Term.

; !Vfoo means that foo is printed as is, but in typewriter font, and with
; special characters quoted.  
; Mnemonic: V -- think Verbatim.

; ! followed by anything else is left alone, along with the exclamation mark.

; One can certainly use nqfmt2fmt on the result of running infix-file, but one
; must do so deliberately by first running infix-file, then renaming the
; resulting file, say foo.tex, to be foo.nqtex, and then running nqfmt2fmt.
; More convenient is to run infix-file with the :nq keyword parameter set to t,
; which causes infix-file first to generate a .nqtex file and second to run
; nqfmt2fmt on that file.

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
; Thus it can be safer to use the #\| ... \|# construct for comments containing
; !, especially if one is in the habit of using the Emacs command M-x fill
; paragraph to rearrange paragraphs that begin with the comment delimiter
; semicolon.

  (let ((infl (extend-file-name fl (fmt2fmt-extension just-remove-! *infix-mode*)))
        (*print-pretty* nil)
        (orig-readtable (copy-readtable nil))
        (outfl (extend-file-name fl (fmtfile-extension *infix-mode* nil)))
        (a-very-rare-cons (cons nil nil))
	(count 1)
        (*readtable* (copy-readtable nil)))
    (smash-infix-readtable)
    (with-open-file
     (instr infl :direction :input)
     (with-open-file
      (*standard-output* outfl :direction :output :if-exists :rename-and-delete)
      (iterate for c = (read-char instr nil a-very-rare-cons)
               (cond ((eq c a-very-rare-cons) (return-from nqfmt2fmt outfl))
		     ;; The Latex indexing routines may insert new exclamation points!!!
                     ((eql c #\\)
		      (if (skip-index-entries instr)
			  nil
			  (pwrite-char c)))
                     ((eql c #\!)
                      (let ((c (read-char instr nil a-very-rare-cons)))
                        (cond ((eq c a-very-rare-cons)
                               (pwrite-char #\!)
                               (return-from nqfmt2fmt outfl)))
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
                              ((#\Space #\Tab #\Newline)
                               (pwrite-char #\!)
                               (pwrite-char c))
                              (otherwise (or just-remove-!
                                             (pformat *terminal-io* "Surprising character after ! ~a.~%" c))
                                         (pwrite-char #\!)
                                         (pwrite-char c)))))
		     ;; Let the user know we are making some kind of progress, every 60 lines
		     ((eql c #\Newline)
		      (if (= count 60) (progn (format *terminal-io* "-") (setq count 1))
			  (incf count))
		      (pwrite-char c))
                     (t (pwrite-char c))))))))
                              
(defun skip-index-entries (instr)
  ;; We are looking at a backslash. In Tex mode we need to skip to the end 
  ;; of the entry, because we may add !'s.  In Scribe mode this is just NIL.
  (declare (ignore instr))
  nil)

;                        INFIX SETTINGS

; This function should be called by the <mode>-init file, or may be called by
; the <mode>-theory file to override the <mode>-init settings.

(defun infix-settings
  (&key (mode                   nil p-mode)                   ; string ["SCRIBE","latex",...]
        (extension              nil p-extension)              ; string ["MSS","tex"]
        (op-location            nil p-op-location)            ; ['FRONT,'BACK]
        (comment-format         nil p-comment-format)         ; ['SMITH,'boyer]
        (format-!-in-comments   nil p-format-!-in-comments)   ; [T,nil]
        (eliminate-top-parens   nil p-eliminate-top-parens)   ; [T,nil]
        (eliminate-inner-parens nil p-eliminate-inner-parens) ; [T,nil]
        (no-index-calls         nil p-no-index-calls))        ; [t,NIL,l]

  (if p-mode           (setq *infix-mode* mode))
  (if p-extension      (setq *mode-extension* extension))
  (if p-op-location    (setq *infix-op-location* op-location))
  (if p-comment-format (setup-comment-format comment-format))
  (if p-format-!-in-comments   (setq *nq-default* format-!-in-comments))
  (if p-eliminate-top-parens   (setq *top-parens-eliminable* eliminate-top-parens))
  (if p-eliminate-inner-parens (setq *top-parens-eliminable-default* eliminate-inner-parens))
  (if p-no-index-calls
      (cond ((consp no-index-calls)
             (setq *do-not-index-calls-of* (append no-index-calls *do-not-index-calls-of*))
             (setq *do-not-index-calls* nil))
	    (t  (setq *do-not-index-calls* no-index-calls)))))

(defun will-will-not (x)
  (if x "will" "will not"))

(defun show-infix-settings ()
  (format *terminal-io* "~%Expecting a .~a file to be mapped to .~a file to be formatted by ~a."
	  file-extension-events *mode-extension* *infix-mode*)
  (format *terminal-io* "~%Multiline infix ops will be printed at the ~a of the line." *infix-op-location*)
  (format *terminal-io* "~%Comment format is ~a." *comment-format*)
  (format *terminal-io* "~%!formatting ~a be in effect." (will-will-not *nq-default*))
  (format *terminal-io* "~%Topmost parens ~a be suppressed." (will-will-not *top-parens-eliminable*))
  (format *terminal-io* "~%Inner parens ~a be suppressed." (will-will-not *top-parens-eliminable-default*))
  (format *terminal-io* "~%Calls ~a be indexed." (will-will-not (not *do-not-index-calls*))))

                                   
;                             DEFINITION BY EXAMPLES

; Anyone extending the syntax by hand rather than by use of one of the make...
; functions ought also to add something to this list of examples to illustrate
; the new syntax.

(defun functify (l)
  ;; Removes redundant elements from an alist.
  (iterate for tail on l with ans
	   do (cond ((null (assoc (car (car tail)) ans))
		     (push (car tail) ans)))
           finally (return (nreverse ans))))

(defvar *infix-source-directory* "/home1/mksmith/tools/xinfix/test/")

(defun print-examples ()

; Illustrates the current syntax via a brief sample document.

  (cond ((stringp *infix-mode*)
	 (format t "~%Entering ~a mode.~%" *infix-mode*)
	 (load-infix-init-file))
	((null *infix-mode*)
	 (cond ((y-or-n-p "Enter Latex mode? ")
		(setq *infix-mode* "latex"))
	       ((y-or-n-p "Enter Scribe mode? ")
		(setq *infix-mode* "scribe"))
	       (t (setq *infix-mode* nil)))
	 (if *infix-mode*
	     (progn (format t "~%Entering ~a mode.~%" *infix-mode*)
		    (load-infix-init-file))))
	(t (format t "Remaining in ~a mode." *infix-mode*)))

  (let ((*print-pretty* nil)
        (*print-case* :downcase))
    (with-open-file
     (*standard-output* (extend-file-name "infix-examples"
					  (fmt2fmt-extension nil *infix-mode*))
			:direction :output
                        :if-exists :rename-and-delete)
     (pformat *standard-output* *example-prelude* *infix-mode*)
     (iterate for form in (functify *wired-in-infix-examples*)
              do (let ((*do-not-use-tabs* t))
		   (pprinc *begin-item*)
		   (quote-printer1 form)
		   (pformat *standard-output* " is printed as ~%~%")
		   (infix-form form)
		   (pformat *standard-output* ".~%")
		   (pprinc *end-item*))
              (pformat *standard-output* "~%"))
     (pprinc *begin-item*)
     (pformat *standard-output* "The remaining symbols that are printed specially are
described in the following table.")
     (pprinc *end-item*)
     (pprinc *end-enumerate-env*)
     (pformat *standard-output* "~%~%")
     (pformat *standard-output* *begin-example-table*)
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
              do (let ((*do-not-use-tabs* t))
		   (quote-printer1 form)
		   (pprinc *column-separator*)
		   (infix-form form)
		   (new-tab-row nil)
		   (setq *infix-loc* *left-margin*)))
     (pprinc *example-postlude*))
    (nqfmt2fmt "infix-examples")))


; The following should be modified to interact with the vaiables that set 
; parens printing.  In particular, this seems to be the piece of precedence that
; is most easily screwed up.

;                                      NOT

; The following code is for the special handling of NOT, which involves diving
; into the term negated to turn a predicate into one that has a slash through
; it.  We advise that the casual user not touch this.

(defun not-printer (term)
  (let (x)
    (cond ((atom (cadr term))
           (default-unary-prefix-printer term *neg-str*))
          ((setq x (assoc (car (cadr term)) *negative-infix-table*))
           (default-infix-printer (cadr term) (cadr x)))
          ((setq x (assoc (car (cadr term)) *negative-unary-prefix-table*))
           (default-unary-prefix-printer (cadr term) (cadr x)))
          ((setq x (assoc (car (cadr term)) *negative-unary-suffix-table*))
           (default-unary-suffix-printer (cadr term) (cadr x)))
          (t (default-unary-prefix-printer term *neg-str*)))))

(eval-when (load eval compile)
           (or (not (boundp '*fn-alist*))
               (assoc 'not *fn-alist*)
               (progn (push (list 'not (function not-printer))
			    *fn-alist*)
		      (setq *save-fn-alist* *fn-alist*)))
           'not)


;                          USER MODIFIABLE TABLE SETUP


; It is easy to augment, or even to modify, the syntax by calling one of the
; make-... functions illustrated below.  The non-initial arguments to these
; make-...  functions are strings to be printed by Latex to generate operators
; and other noise words when printing a term whose function symbol is the
; intial argument of the call to make-...

; make-infix-op, make-unary-prefix-op, and make-unary-suffix-op take an
; optional second argument, *neg-str*, which indicates how to print an the
; negation of an application of the function symbol in question.

; In TeX or Latex, one can do astonishingly clever things.  But the strings
; that we have in mind should do nothing clever involving motion, they should
; only result in characters being placed at the current location.  While being
; printed, the strings will be passed no arguments or information about the
; context in which printing is to take place. Typically, these strings should
; be nothing more than instructions to print a single symbol. The strings are
; processed in `math mode', and in fact, they are auomatically embedded in
; $...$.

; None of the operators below are built into this printer anywhere else except
; by the code below.  The meaning of `not', defined above, is wired in because
; it gives the meaning to the optional *neg-str* arguments.


;                                     INFIX-OPS

; infix-ops (infix operators) should be function symbols of two or more
; arguments for which it is desired that one symbol come out between every
; adjacent pair of arguments.  E.g., invoking (make-infix-op plus "+") causes
; the term (plus a b c d) to be printed as (a $+$ b $+$ c $+$ d).  Invoking
; (make-infix-op equal "=" "\\not=") causes the term (equal x y) to be printed
; as (x $=$ y) and it also causes the term (not (equal x y)) to be printed as
; (x $\not= y).

; Thus, for example, if one introduces a new function, say join, and wants to
; print terms of the form (join x y) as (x \bigtriangledown y), cf. p. 44 of
; the Latex manual, then one should invoke:

;   (make-infix-op join "\\bigtriangledown")

; from Lisp.  That is all that need be done to cause infix-file to subsequently
; print `join' terms this way.

; Note that throughout the following examples, we have used two backslashes to
; get one because, in Common Lisp, backslash is a character for quoting other
; characters.

; Examples of make-infix-op are contained in latex-theory.lisp.  Look for INFIX OPERATORS.


;             UNARY-PREFIX-OPS, UNARY-SUFFIX-OPS, and UNARY-ABS-OPS

; Use make-unary-prefix-op and make-unary-suffix-op only for function symbols
; of one argument.  The string str (or *neg-str*) will be printed before or
; after the argument.

; For more examples, see latex-theory.lisp.

; unary-suffix-ops should be unary function symbols.

; (make-unary-suffix-op foo x str) makes (foo x) print as (x $str$).

; Examples of make-unary-suffix-op.

; unary-prefix-ops should be unary function symbols. 

; (make-unary-prefix-op foo str) makes (foo x) print as ($str$ x).

; unary-abs-ops should be unary function symbols.

; To create syntax like that for absolute value, use (make-unary-absolute-op
; lhs-str rhs-str), where lhs-str and rhs-str are the strings to print on the
; left and right of the argument.  (make-unary-abs-op foo str1 str2) makes (foo
; x) print as (str1 x str2).  See the example for abs below.


;                           SOME POSSIBLE EXTENSIONS


;; (simple-extension)		; see latex-theory.lisp
;; (dmg-syntax)                 ; see latex-theory.lisp

; Undoing.  To cause applications of a function symbol fn to be printed in the
; default way, i.e., fn(x, y), invoke (clean-up 'fn).


;; TESTING

;; Lines in the test file are the following form:

;;    filename 
;; or (filename mode)
;; or (filename mode nq)

;; nq defaults to T.

(defvar *mode-list* '("latex" "scribe"))

(defvar *test-file* "testfile")

;; Better to use test-directory
(defun test-infix ()
  (let ((files (read-file-list *test-file*)))
    (iterate for test in files
	     do (cond ((or (stringp test)
			   (and (consp test) (null (cdr test))))
		       ;; "file" or (file)
		       (if (consp test) (setq test (car test)))
		       (iterate for mode in *mode-list*
				do (progn (format *terminal-io* "~%Translating ~a in ~a mode.~%" test mode)
					  (infix-file test :mode mode :nq t))))
		      ((and (consp test) (eql (length test) 2))
		       ;; (file mode)
		       (format *terminal-io* "~%Translating ~a in ~a mode.~%" (car test) (cadr test))
		       (infix-file (car test) :mode (cadr test) :nq t))
		      ((and (consp test) (eql (length test) 3))
		       ;; (file mode nq)
		       (format *terminal-io* "~%Translating ~a in ~a mode, with nq = ~a.~%"
			       (car test) (cadr test) (caddr test))
		       (infix-file (car test) :mode (cadr test) :nq (caddr test)))
		      (t (format *terminal-io* "~%BAD TEST FILE SPEC: ~ad.~%" test))))))

(defun read-file-list (file)
  (cond ((null (probe-file file))
	 (format t "~%Failed to find file: ~a~%" file))
	(t (with-open-file
	    (instr file :direction :input)
	    (iterate for form = (read instr nil a-very-rare-cons)
		     until (eq form a-very-rare-cons)
		     collect form)))))


;; Testing functions

;; USE:
;; mks: script test.log
;; mks: nqthm-1992
;; >(load "sinfix")
;; >(test-directory "/usr/home/mksmith/tools/xinfix/test/*.events" "scribe")
;; >(bye)
;; mks: foreach f (*.mss)
;; ? scribe $f
;; ? end
;; mks: ^D
;; mks: sed -e s/^V^M// test.log > test-scribe.log

(defun test-directory (dir mode)
  ;; ONLY EXPECTING mode = "latex" or "scribe"
  (let ((type (if (string= mode "latex") "tex" "mss")))
    (mapc (function (lambda (f) 
		      (format *terminal-io* "~%Infixing ~a.events." (pathname-name f))
		      (if (probe-file (make-pathname :type type :defaults f))
			  (format *terminal-io* "~%~a.~a already exists. Skipping.~%" (pathname-name f) type)
			  (infix-file (pathname-name f) :mode mode))))
	  (directory dir))))


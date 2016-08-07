;;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 -*- ;;;;
(IN-PACKAGE "USER")

;  Copyright (C) 1989-1994 by Robert S. Boyer, J Strother Moore, and
;  Computational Logic, Inc. All Rights Reserved.

;  Copying of this file is authorized to those who have read and
;  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
;  LICENSE" at the beginning of the Nqthm file "basis.lisp".

;  NQTHM Version 1992

#|
                  Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE
                           Computational Logic, Inc.
                          1717 West Sixth, Suite 290
                           Austin, Texas 78703-4776

Please  read  this  license  carefully before using the Nqthm-1992 Software. By
using the Nqthm-1992 Software, you are agreeing to be bound  by  the  terms  of
this license. If you do not agree to the terms of this license, promptly return
the Nqthm-1992 Software to the place where you obtained it.

The Nqthm-1992 Software was developed by Computational Logic, Inc.(CLI).    You
own  the disk or other medium on which the Nqthm-1992 Software is recorded, but
CLI retains title to the Nqthm-1992 Software.  The purposes of this license are
to  identify  the  Nqthm-1992  Software  and  to  make the Nqthm-1992 Software,
including its source code, freely available.  This license allows you  to  use,
copy,  distribute and modify the Nqthm-1992 Software, on the condition that you
comply with all the Copying Policies set out below.

COPYING POLICIES

1. You may copy and distribute verbatim copies of the  Nqthm-1992  Software  as
you  receive  it,  in any medium, including embedding it verbatim in derivative
works, provided that you a) conspicuously and  appropriately  publish  on  each
copy  a  valid  copyright notice "Copyright (C) 1989-1994 by Robert S. Boyer, J
Strother Moore, and Computational Logic, Inc. All Rights  Reserved.",  b)  keep
intact on all files the notices that refer to this License Agreement and to the
absence of any warranty, and c) give all recipients of the Nqthm-1992  Software
a copy of this License Agreement along with the program.

2. You may modify your copy or copies of the Nqthm-1992 Software or any portion
of it, and copy and distribute such modifications provided you tell  recipients
that  what  they have is a modification by your organization of the CLI version
of the Nqthm-1992 Software.

3. You may incorporate parts of the Nqthm-1992  Software  into  other  programs
provided that you

    a) acknowledge Computational Logic, Inc. in the program documentation, and

    b) send a copy of a user's manual for the program to

       Software-Request                 or     Software-Request@CLI.COM
       Computational Logic, Inc.
       1717 West Sixth, Suite 290
       Austin, TX 78703-4776

CLI also requests, but does not require, that any improvements or extensions to
the Nqthm-1992 Software be returned to one of these addresses, so that they may
be  shared with other Nqthm-1992 users.  The Nqthm-1992 Software, including its
source, can be obtained by contacting one of the above addresses.

NO WARRANTY

BECAUSE THE  Nqthm-1992  SOFTWARE  IS  LICENSED  FREE  OF  CHARGE,  WE  PROVIDE
ABSOLUTELY  NO  WARRANTY.  THE SOFTWARE IS PROVIDED "AS IS" WITHOUT WARRANTY OF
ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, ANY IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.  THE ENTIRE
RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU.  SHOULD  THE
Nqthm-1992  SOFTWARE  PROVE  DEFECTIVE,  YOU  ASSUME  THE COST OF ALL NECESSARY
SERVICING, REPAIR OR CORRECTION.

IN NO EVENT WILL ROBERT S. BOYER, J STROTHER  MOORE,  OR  COMPUTATIONAL  LOGIC,
INC.  BE LIABLE TO YOU FOR ANY DAMAGES, ANY LOST PROFITS, LOST MONIES, OR OTHER
SPECIAL, INCIDENTAL  OR  CONSEQUENTIAL  DAMAGES  ARISING  OUT  OF  THE  USE  OR
INABILITY  TO USE THE Nqthm-1992 SOFTWARE (INCLUDING BUT NOT LIMITED TO LOSS OF
DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY  THIRD  PARTIES),
EVEN  IF  YOU  HAVE  ADVISED  US OF THE POSSIBILITY OF SUCH DAMAGES, OR FOR ANY
CLAIM BY ANY OTHER PARTY.

|#

(DEFPARAMETER *THM-DISCLAIMER* 

"

NQTHM Version 1992.  See the license agreement at the beginning
of the file \"basis.lisp\" for the terms and conditions on the
use and modification of this software.  To avoid this warning,
(SETQ *THM-SUPPRESS-DISCLAIMER-FLG* T).

Robert S. Boyer and J Strother Moore

")

(DEFVAR *THM-SUPPRESS-DISCLAIMER-FLG* NIL)

;                                  Nqthm-1992

;                       R. S. Boyer and J Strother Moore

;                                 Austin, Texas

;                                   circa 1992



;                          Computational Logic, Inc.
;                         1717 W. 6th St., Suite 290
;                             Austin, Texas 78703

;                               (512) 322-9951

;                            LANGUAGES AND MACHINES

;   We began working on this code in 1972 in Edinburgh at the Metamathematics
;   Unit of the University of Edinburgh.  The first version was written in
;   POP-2 for an ICL 4130.  In Palo Alto in 1974 we translated it into
;   Interlisp-10 for a Xerox MAXC and a DEC PDP10/BBN-TENEX.  We continued
;   developing it at Xerox PARC, SRI, and the University of Texas on two
;   DEC-2060s.  In 1983-4, we translated it into Maclisp for a DEC-2060 and a
;   Honeywell Multics, and into Zetalisp for a Symbolics 3600.  John Nagle made
;   it compatible with Franz Lisp for the VAX and SUNs.  In 1986 we further
;   modified it for PSL compatibility for use on Crays.  In 1987 we converted
;   it to Common Lisp, abandoning compatibility with all previous Lisps.  It
;   now runs under Kyoto, Symbolics, TI, and Lucid Common Lisps.  Via SLOOP,
;   compiler optimizers, type declarations, and improvements to KCL Bill
;   Schelter improved the speed of this system in Kyoto Common Lisp.


;                             CONTRIBUTIONS OF CODE

;   Over the years Nqthm has been in use, various users have coded extensions
;   or improvements to Nqthm programs.  With their permission we have included
;   some of these improvements in the 1992 release of Nqthm.  In all cases, we
;   have treated this code as though it were our own, modifying it as we felt
;   appropriate.  We take full responsibility for any bugs that we may have
;   introduced.  We are indebted to these people for their good ideas.

;   Bill Bevier introduced the notion of "theories" which permit the user to
;   enable and disable sets of names in a single act.

;   Bishop Brock implemented an improved clausifier that is substantially
;   faster than the one we originally coded for NQTHM.

;   Matt Wilding implemented a new version of our DISABLEDP which answers the
;   question "is this rewrite rule disabled?" in nearly constant time as
;   opposed to our old linear search through the list of all disabled names.

;   Matt Kaufmann has developed an extension to Nqthm, known as Pc-Nqthm, that
;   provides an interactive proof-checker for the Nqthm logic.  Pc-Nqthm is not
;   part of these sources but is built on top of them.  It may be obtained from
;   Computational Logic, Inc.  In the process of building PC-NQTHM Kaufmann has
;   scrutinized and revised the contributions of Bevier, Brock, and Wilding
;   mentioned above.  In addition, he has suggested many changes to Nqthm code
;   to facilitate his task of integrating the proof checker.

;   We would like to especially acknowledge Matt Kaufmann for his many
;   suggestions for improving Nqthm, his help in implementing many
;   improvements, his careful analysis of user complaints, and his scrutiny of
;   our code.  Matt's presence has increased our confidence that Nqthm is
;   sound.


;                                   OWNERSHIP

;   The development of this system has been primarily financed by the National
;   Science Foundation and the Office of Naval Research.  The NSF Grant Policy
;   Manual NSF-77-47, Revised October 1979, states in paragraph 754.2 "Data
;   banks and software, produced with the assistance of NSF grants, having
;   utility to others in addition to the grantee, shall be made available to
;   users, at no cost to the grantee, by publication or, on request, by
;   duplication or loan for reproduction by others. ... Any out of pocket
;   expenses incurred by the grantee in providing information to third parties
;   may be charged to the third party."  DARPA paid for the Common Lisp
;   conversion and the 1992 release.


;                                 DOCUMENTATION

;   The primary documentation for this system is the book "A Computational
;   Logic Handbook," Robert S. Boyer and J Strother Moore, Academic Press,
;   1988.  Additional documentation is in preparation.

;   The 1978 version of this system was carefully described in "A Computational
;   Logic," Academic Press, 1979.  But much has changed.  (1) An extensive
;   amount of "linear" arithmetic has been built-in, as described in
;   "Integrating Decision Procedures into Heuristic Theorem Provers: A Case
;   Study of Linear Arithmetic," R. S.  Boyer and J S. Moore, in Machine
;   Intelligence 11, Hayes, et. al, (editors), Oxford University Press, 1988.
;   (2) We have added the notion of metafunctions described in "Metafunctions:
;   Proving Them Correct and Using Them Efficiently as New Proof Procedures" in
;   "The Correctness Problem in Computer Science," R. S. Boyer and J S. Moore
;   (editors), Academic Press, 1981.  (3) Equality reasoning in the ground case
;   is complete.  (4) The mechanism for guessing well-founded relations at
;   definition time has been vastly simplified but now requires more explicit
;   guidance from the user in the nontrivial cases.  (5) A variety of hints can
;   be given to the theorem-prover.  (6) Bounded quantifiers and provision for
;   partial recursive functions were added, as described in "The Addition of
;   Bounded Quantification and Partial Functions to A Computational Logic and
;   Its Theorem Prover," R. S. Boyer and J S. Moore, Journal of Automated
;   Reasoning, Volume 4, pp. 117-172, 1988.  (7) Function instantiation
;   provides a means for instantiating function symbols in theorems under
;   certain conditions, and is described in "Functional Instantiation in First
;   Order Logic", Robert S.  Boyer, D. Goldschlag, M. Kaufmann, and J Moore, in
;   V. Lifschitz (editor), Artificial Intelligence and Mathematical Theory of
;   Computation: Papers in Honor of John McCarthy. Academic Press, 1991.  pp.
;   7-26.


;                             NUMERIC OPERATIONS

;   We never use floating point arithmetic in a way that could influence the
;   soundness of the theorem-prover.  We do use it for reporting time used
;   and for computing the "score" of an induction candidate.  The latter
;   helps us make a heuristic guess between several sound inductions.


;                                  LISP-CODE

;   Except during DEFN, all function symbols in the logic have a LISP-CODE
;   property.  The value of the property is the name of a Lisp function
;   that when applied to evgs returns the appropriate evg or else THROWs to
;   the tag REDUCE-TERM.  No LISP-CODE function should be applied unless
;   you are under an appropriate CATCH.  The LISP-CODE property for IF is a
;   function that causes an error because it is likely that you are making
;   a mistake if you casually eval the args to an IF and then apply the
;   LISP-CODE.  The LISP-CODE property for user DCLd functions always
;   THROWs.  During the proving done under DEFN, there is no LISP-CODE
;   property for the function symbol being defined so we are careful,
;   wherever we might be under DEFN, to check that the property is nonNIL.


;                               LISP PRIMITIVES

;   This file, BASIS, has all of the SPECIAL declarations for our
;   theorem-prover.  We load the compiled version of the file BASIS before we
;   compile the rest of the theorem-prover.


;                               SANITY CHECK

(EVAL-WHEN (LOAD EVAL COMPILE)

#|  

;   The following code is also found in nqthm.lisp.  It has been
;   commented out here to avoid duplicate definitions.  But we leave
;   the text in place so that the sources are complete even in the
;   absence of nqthm.lisp (which we think of as an addendum to the
;   system to help compile and load it).


(DEFMACRO ITERATE (&REST L) `(SLOOP::SLOOP ,@ L))

(DEFUN CHK-BASE-AND-PACKAGE-1992 (BASE PACK)

;  We have had some grief with Common Lisps that load files into the
;  wrong package or with the wrong base, so we check these things
;  every time that we load a file.

  (OR (AND (EQL BASE (+ 1 1 1 1 1 1 1 1 1 1))
           (EQ PACK (FIND-PACKAGE "USER")))
      (ERROR "Wrong package or base.")))

|#

(CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))


;                       SUITABILITY OF THIS COMMON LISP


;   The system is written for an Ascii-based Common Lisp, and we now
;   check that we are in one.

(EVAL-WHEN (COMPILE EVAL LOAD)

(DEFCONSTANT PRINTING-COMMON-LISP-CHARACTERS
  '(#\!
    #\"
    #\# #\$ #\% #\& #\' #\( #\) #\* #\+ #\, #\- #\. #\/
    #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
    #\: #\; #\< #\= #\> #\? #\@
    #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L
    #\M #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
    #\[ #\\ #\] #\^ #\_ #\`
    #\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l
    #\m #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
    #\{ #\|
    #\} #\~ ))

(DEFCONSTANT ASCII-CODES-FOR-PRINTING-COMMON-LISP-CHARACTERS
  '(33 34 35 36 37 38 39 40 41 42 43 44 45 46 47
       48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63
       64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79
       80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95
       96 97 98 99 100 101 102 103 104 105 106 107 108
       109 110 111 112 113 114 115 116 117 118 119 120
       121 122 123 124 125 126))

(DEFUN CHK-FOR-SUITABILITY-OF-THIS-COMMON-LISP ()
  #|
  (COND ((NOT (AND (TYPEP (1- (EXPT 2 31)) 'FIXNUM)
                   (TYPEP (- (EXPT 2 31)) 'FIXNUM)))
         (ERROR "THIS COMMON LISP DOES NOT SUPPORT FIXNUMS ~
                 IN THE RANGE 2^31-1 TO -2^31.")))|#
; The foregoing test, now deleted, insured that all our
; type sets and controller masks were fixnums.  Once upon
; a time we depended upon that because we used EQ to compare
; them.  We have since gone over to the use of =.  The test
; above excludes Lucid Common Lisp, where the boundary is
; 28.  We could speed the theorem prover up by leaving
; this test in and inserting a lot of declarations.  However,
; we were delighted by the speed of the un-annotated KCL
; version and are loathe to put in declarations.

; The theorem prover still checks that we have fewer than
; 31 shells.  That check must remain even if type sets are
; bignums.  The reason is that we use the "top bit" as
; the magic bit that means "all other types" and we had
; 32 shells then normal type sets would get interpreted
; incorrectly.  To remove the limitation on the number of
; types we must put the magic bit someplace else (like at
; the bottom).

  (ITERATE FOR CHAR IN PRINTING-COMMON-LISP-CHARACTERS
           AS N IN ASCII-CODES-FOR-PRINTING-COMMON-LISP-CHARACTERS
           DO
           (COND ((NOT (EQUAL N (CHAR-CODE CHAR)))
                  (ERROR "This is not an ASCII-based Common Lisp ~
                   because character ~A does not have code ~A."
                         CHAR N)))))

(CHK-FOR-SUITABILITY-OF-THIS-COMMON-LISP))

;                                   TYPES

(EVAL-WHEN (COMPILE EVAL LOAD)
(DEFCONSTANT *TYPE-SET-LENGTH* 31)
)

;  In order to obtain greater efficiency in KCL, Bill Schelter has introduced
;  the following types and operations for type-sets and for controllers.
;  This is pure Common Lisp, but not every compiler or implementation may be
;  able to take much advantage of these declarations.  It would be wrong to
;  think that merely setting *TYPE-SET-LENGTH* to a different integer would
;  be a reasonable thing to do.  31 is wired in several other places, sigh.
;  It is undoubtedly shocking to see such a gratuitous use of #. as follows.
;  However, the only alternative seems to be worse: actually putting in the
;  value of 2^32.  The problem is that some Common Lisps do not implement
;  DEFTYPE correctly.
(DEFTYPE TYPE-SET NIL
  `(INTEGER #.(- (EXPT 2 *TYPE-SET-LENGTH*))
            #.(- (EXPT 2 *TYPE-SET-LENGTH*) 1)))

;  We may wish to change controller length from type-set-length later.
(DEFTYPE CONTROLLER NIL
  `(INTEGER #.(- (EXPT 2 *TYPE-SET-LENGTH*))
            #.(- (EXPT 2 *TYPE-SET-LENGTH*) 1)))


(DEFMACRO TS= (A B) `(= (THE TYPE-SET ,A) (THE TYPE-SET ,B)))
(DEFMACRO CT= (A B) `(= (THE CONTROLLER ,A) (THE CONTROLLER ,B)))

(DEFMACRO TSLOGAND (A B)
  `(THE TYPE-SET (LOGAND (THE TYPE-SET ,A )(THE TYPE-SET ,B))))
(DEFMACRO CTLOGAND (A B)
  `(THE CONTROLLER (LOGAND (THE CONTROLLER ,A )(THE CONTROLLER ,B))))

(DEFMACRO TSLOGIOR (A B)
  `(THE TYPE-SET (LOGIOR (THE TYPE-SET ,A )(THE TYPE-SET ,B))))
(DEFMACRO CTLOGIOR (A B)
  `(THE CONTROLLER (LOGIOR (THE CONTROLLER ,A )(THE CONTROLLER ,B))))


(DEFMACRO TSLOGNOT (A)
  `(THE TYPE-SET (LOGNOT (THE TYPE-SET ,A ))))

(DEFMACRO TSLOGDIFF (X Y)
  `(THE TYPE-SET (BOOLE BOOLE-ANDC2 (THE TYPE-SET ,X)(THE TYPE-SET ,Y))))

(DEFMACRO TSLOGSUBSETP (X Y)
  (COND ((ATOM X)
         `(TS= (TSLOGAND ,X ,Y) (THE TYPE-SET ,X)))
        (T (LET ((XX (GENSYM)))
             `(LET ((,XX ,X))
                (DECLARE (TYPE TYPE-SET ,XX))
                (TSLOGSUBSETP ,XX ,Y))))))

(DEFMACRO TSLOGBIT (N)
  `(THE TYPE-SET (ASH 1 (THE (INTEGER 0 ,*TYPE-SET-LENGTH*) ,N))))

(DEFMACRO CTASH (A B)
  `(THE CONTROLLER (ASH ,A ,B)))

(DEFMACRO GLOBAL-DISABLED-HASHP (NAME)
  `(IF (EQ DISABLED-LEMMAS GLOBAL-DISABLEDP-HASH-LIST)
       (GETHASH ,NAME GLOBAL-DISABLEDP-HASH)
     (GETHASH ,NAME (MAKE-GLOBAL-DISABLEDP-HASH))))

;  The following macro should be used instead of =, EQL, or EQUAL for
;  comparing two objects known to be integers.  Much faster in KCL.
(DEFMACRO INT= (A B) `(EQL (THE INTEGER ,A) (THE INTEGER ,B)))


;                            VARIABLE DECLARATIONS

(DEFVAR *ALIST*)

(DEFVAR *ARGLIST*)

(DEFVAR *CONTROLLER-COMPLEXITIES*)

(DEFVAR *FILE*)

(DEFVAR *FNNAME*)

(DEFVAR *INDENT*)

(DEFVAR *TYPE-ALIST*)

;   Used by REWRITE-FNCALL to store the type-alist so that the lower level
;   jumpout can reach up and get it should it need to solidify before jumping.

;   The variables *1*BTM-OBJECTS, *1*F, *1*SHELL-QUOTE-MARK, and *1*T have
;   names that start with 1 because the built-in functions, such as
;   *1*COUNT, which could be called by some user's function *1*FOO, refer
;   to these variables.

(DEFVAR *1*BTM-OBJECTS)

;   This is just a list of all the bottom object function symbols.

(DEFCONSTANT *1*F (QUOTE *1*FALSE))

;   The explicit form of the term (FALSE).

(DEFCONSTANT *1*SHELL-QUOTE-MARK (QUOTE *1*QUOTE))

;   The mark that a constructor expression in an explicit object is represented
;   in the CADR.

(DEFCONSTANT *1*T (QUOTE *1*TRUE))

;   The explicit form of the term (TRUE).

(DEFVAR *COMPILE-FUNCTIONS-FLG* NIL)

;  If *COMPILE-FUNCTIONS-FLG* is not NIL, DEFN will compile each function as
;  it is defined.  The fact that this variable is DEFVARed but initialized
;  instead of DEFPARAMETERed is a sign that setting by the user is permitted.

#|

(DEFVAR *DEFAULT-NQTHM-PATH* NIL
  "IF not NIL, components from this will be used to extend pathnames.")

;  *DEFAULT-NQTHM-PATH* is also DEVARed in nqhtm.lisp, but is
;  duplicated here in case nqthm.lisp should be flushed.  It is
;  DEFVARed instead of DEFPARAMETERed so that the user can override
;  its value.


(DEFVAR *NQTHM-MAKE-PROCLAMATIONS* T)

;  *NQTHM-MAKE-PROCLAMATIONS* is also defined in nqthm.lisp.

|#

(DEFPARAMETER A-VERY-RARE-CONS (CONS NIL NIL))

;   This CONS should never be made part of any other Lisp object.  It is used
;   with the Common Lisp GET function as the default value returned when a
;   property is not actually present.

(DEFVAR ABBREVIATIONS-USED)

;   Used by EXPAND-ABBREVIATIONS and CLAUSIFY-INPUT to record which
;   abbreviations were applied.

(DEFVAR ADD-EQUATIONS-TO-DO)

;   The second answer returned by ADD-EQUATION consisting of new equations yet
;   to be added to the pot.

(DEFPARAMETER ADD-TERM-TO-POT-LST-TEMP (LIST NIL))

;   Used by ADD-TERM-TO-POT-LST.

(DEFVAR ALIST)

(DEFVAR ALISTS)

(DEFVAR ALL-FNS-FLG)

(DEFPARAMETER ALL-LEMMAS-USED NIL)

(DEFPARAMETER ALMOST-SUBSUMES-CONSTANT (CONS NIL NIL))

;   A special constant used by ALMOST-SUBSUMES.  ALMOST-SUBSUMES detects when
;   CL1 is almost subsumed by CL2, which means that either CL1 is subsumed by
;   CL2 or else it is except for one literal whose negation is in CL2.
;   ALMOST-SUBSUMES sets ALMOST-SUBSUMES-LITERAL to this literal.  When that
;   variable is set to this constant it is interpreted as the message that all
;   the literals were subsumed.

(DEFVAR ALMOST-SUBSUMES-LITERAL)

;   Used as an extra answer by ALMOST-SUBSUMES.

(DEFPARAMETER ANCESTORS NIL)

;   List of the negations of the hypotheses REWRITE is currently trying to
;   establish in order to apply lemmas.  This list is used by RELIEVE-HYPS and
;   RELIEVE-HYPS-NOT-OK to prevent infinite backwards chaining.  The list is
;   supposed to be bound whenever a new entry is added.  Like TYPE-ALIST it is
;   a free var only for convenience.

(DEFPARAMETER ANCESTORS-PROPERTY (GENSYM))

(DEFVAR ANS)

;   Used frequently in FOO, FOO1 constructions in which FOO initializes a
;   collection site and FOO1 repeatedly adds to it.

(DEFPARAMETER ARITY-ALIST NIL)

;   This is a list associating function names with their arities.  Once a
;   function has been defined or declared its arity is stored on its property
;   list encoded as the length of the CDR of its TYPE-PRESCRIPTION.  But it is
;   necessary to know the proposed arity of a function even before it has been
;   accepted as a legal function and its property list is set up.  Thus, this
;   list is used, by DEFN0, BOOT-STRAP, and ADD-SHELL0 to declare the arities
;   of certain functions during the act of creating them.

(DEFPARAMETER ASCII-CODES-FOR-LEGAL-SIGNS
  (ITERATE FOR CHAR IN (COERCE "$^&*_-+=~{}?<>"
                               'LIST)
           COLLECT (CHAR-CODE CHAR)))

;  ASCII-CODES-FOR-LEGAL-SIGNS does not change its value.  But
;  we don't use DEFCONSTANT because Genera 7 complains.

(DEFPARAMETER *BACKQUOTE-COUNTER* 0)

; READ causes an error upon reading a comma or comma-atsign unless there is a
; pending backquote that will eliminate the *COMMA* or *COMMA-ATSIGN*.  In the
; SPECIAL variable *BACKQUOTE-COUNTER* we keep track of the number of
; backquotes that are currently pending.  It is crucial that this variable be
; SPECIAL.

(DEFPARAMETER BOOT-STRAP-MACRO-FNS (QUOTE (GREATERP LEQ GEQ)))

;   Must be a list of function names defined nonrecursively in
;   BOOT-STRAP-INSTRS.  Expanded away in translate.

(DEFPARAMETER BREAK-LEMMA-COMMAND-HANDLER-ALIST
  '((NAME . "Print name of the broken rule.")
    (HYPS . "List the hypotheses of the broken rule.")
    (CONCL . "Print the conclusion of the broken rule.")
    (SUBST . "Print the substitution being applied to the broken rule.")
    (TARGET . "Print the term to which the rule is being applied.")))

;   The rewrite break package offers these standard commands.
;   This alist is used both to recognized commands fielded and
;   to display documentation to the user.  See BREAK-LEMMA-COMMAND-HANDLER.

(DEFVAR BREAK-REWRITE-COMMAND-HANDLER-STATE)

;   This variable is used by the break package to remember the state
;   as control passes from one function in the break sequence to another.
;   See BREAK-BEFORE-RELIEVE-HYPS for an explanation.

(DEFPARAMETER BROKEN-LEMMAS NIL)

;   This is the list of replacement and linear rules current
;   broken.  When the rewriter attempts to apply a name on
;   this list, the rewrite break package slogs into action.

(DEFVAR CHRONOLOGY)

;   The list of all event names, in reverse chronological order.

(DEFVAR CL2)

(DEFPARAMETER CLAUSE-ALIST NIL)

(DEFPARAMETER *COMMA* (MAKE-SYMBOL "COMMA"))

; *COMMA* is used by the backquote reader.  When the reader encounters <,foo>,
; while reading a backquoted expression, it returns (LIST *COMMA* READ:<foo>).

(DEFPARAMETER *COMMA-ATSIGN* (MAKE-SYMBOL "COMMA-ATSIGN"))

; *COMMA-ATSIGN* is used by the backquote reader.  When the reader encounters
; <,@foo> or <,.foo> while reading a backquoted expression, it returns (LIST
; *COMMA-ATSIGN* READ:<foo>).

(DEFPARAMETER COMMAND-STATUS-FLG NIL)

;   This flag is T when we are executing an event command.  Its purpose is to
;   implement the prohibition of recursive re-entry.

(DEFPARAMETER COMMENT-WINDOW NIL)

(DEFVAR COMMONSUBTERMS)

(DEFVAR COMPILED-FUNCTION-P-FN 'COMPILED-FUNCTION-P)

(DEFPARAMETER COMMUTED-EQUALITY-FLG NIL)

(DEFPARAMETER CULPRIT-FUNCTION NIL)

(DEFPARAMETER CURRENT-ATM 0)

;   Atom of CURRENT-LIT, set by SIMPLIFY-CLAUSE1 and used by
;   ADD-TERM-TO-POT-LST to avoid trying to use linear to add the negation of
;   CURRENT-LIT to the pot lst when we know we have already tried it.

(DEFVAR CURRENT-CL)

;   The clause whose subterms control which functions get opened up.

(DEFPARAMETER CURRENT-LIT 0)

;   During SIMPLIFY-CLAUSE1, CURRENT-LIT is the literal we are currently trying
;   to rewrite.  ADD-EQUATIONS avoids using any POLY that descends from this
;   literal and REWRITE-SOLIDIFY avoids using this literal.  Outside of
;   SIMPLIFY-CLAUSE1, this variable should not be a term.

(DEFVAR CURRENT-SIMPLIFY-CL)

(DEFVAR CURRENT-TYPE-NO)

;   Bound in ADD-SHELL0 for using during the creation of the axioms for a
;   shell.

(DEFVAR DECISIONS)

(DEFVAR DEFINED-FUNCTIONS-TOGGLED)

;   A list of pairs of the form (name . flg) where flg is T or NIL.  The
;   first flg on the list is the current state of the DEFINED-FUNCTIONS-TOGGLED
;   flag.  When the flag is T, then all defined *1*functions are disabled.

(DEFVAR DEFINITELY-FALSE)

;   If FALSE-NONFALSEP returns T then DEFINITELY-FALSE is T if the term is
;   equal to FALSE and is NIL if the term is not equal to FALSE.

(DEFVAR DEFN-FLG)

;   Used by REWRITE to keep track of whether the current term's value will
;   ultimately become either T, F, or -- most importantly -- part of the
;   expanded body of a recursive function.  If DEFN-FLG is on and the value of
;   the term violates REWRITE-FNCALLP, the recursive rewriting of the body can
;   be aborted in JUMPOUTP.

(DEFVAR DESCENDANTS)

(DEFVAR DISABLED-LEMMAS)

;   This list contains the names of those lemmas that are currently disabled.
;   No routine that uses a lemma will consider a lemma whose name is on this
;   list.

(DEFVAR DLHDFMLA)

(DEFPARAMETER DO-NOT-GENERALIZE-FLG NIL)

(DEFPARAMETER DO-NOT-USE-INDUCTION-FLG NIL)

;   If set to T then PROVE aborts with failure as soon as a clause has to be
;   pushed for induction.

(DEFPARAMETER DOTCONS (LIST NIL NIL))

(DEFVAR ELAPSED-TIME)

(DEFPARAMETER ELIM-VARIABLE-NAMES
  (QUOTE (X Z V W D C X1 Z1 V1 W1 D1 C1 X2 Z2 V2 W2 D2 C2)))

;   This is the list of variables that can be introduced by the elimination of
;   destructors -- provided they do not occur in the conjecture being
;   generalized.  It is important for us to be able to tell how a variable was
;   introduced in the theorem.  For example, such a question is asked to
;   control repeated destructor elimination which might otherwise loop.  We use
;   the "pretty" variables on this list rather than just GENSYMimg unique names
;   because we do not like to see funny variable names in our output.  IT IS
;   CRUCIAL THAT THIS LIST HAVE NO INTERSECTION WITH GEN-VARIABLE-NAMES -- the
;   list used to pick vars for GENERALIZE.

(DEFPARAMETER ELIM-VARIABLE-NAMES1 NIL)

(DEFVAR ENDLIST)

(DEFPARAMETER ERROR1-SET-FLG NIL)

(DEFVAR EVENT-LST)

(DEFCONSTANT EVENT-SEPARATOR-STRING #\Page)

(DEFPARAMETER EXECUTE-PROCESSES
  (QUOTE (SIMPLIFY-CLAUSE SETTLED-DOWN-CLAUSE FERTILIZE-CLAUSE
                          ELIMINATE-DESTRUCTORS-CLAUSE GENERALIZE-CLAUSE
                          ELIMINATE-IRRELEVANCE-CLAUSE STORE-SENT)))

;   This list is just used by the IO1 function to control such things as to
;   whether to indent and print the current goal before printing the process
;   specific information.

(DEFPARAMETER EXPAND-LST NIL)

(DEFPARAMETER *EXTRA-PROPERTYLESS-SYMBOLS-ALIST* NIL)

(DEFPARAMETER FAILED-EVENTS NIL)

;   List of all of the event commands which returned NIL in
;   a given session with the system.

(DEFVAR FAILURE-ACTION)

(DEFPARAMETER FAILURE-MSG
  (QUOTE |************** F  A  I  L  E  D **************|))

;   This is the value that is returned by PROVE should a proof fail.  It is a
;   distinctive message that is guaranteed to catch our eyes if it is ever
;   returned as the value of PROVE.  Since we often run with the I/O going to a
;   file and just the value of PROVE being printed to the terminal, we like for
;   failures to be brought to our attention.

(DEFPARAMETER FALSE (QUOTE (QUOTE *1*FALSE)))

;   This variable is just bound to the internal form of the term (FALSE) for
;   convenient coding.

(DEFVAR FALSE-COMPOUND-RECOGNIZER-ALIST)

;   See TRUE-COMPOUND-RECOGNIZER-ALIST.

(DEFVAR FALSE-TYPE-ALIST)

(DEFVAR FILE)

;  The fact that the following 5 variables are DEFVARed and
;  initialized instead of DEFPARAMETERed is a sign that
;  they may be set by the user.
(DEFVAR FILE-EXTENSION-PROOFS "proofs")

#|
;  The following code is also found in nqthm.lisp.  See comment above.

(DEFVAR FILE-EXTENSION-BIN NIL)

;  We have not found a mechanism that works across all Common Lisps
;  for both specifying the name for a compiled object file and for
;  loading that file.  In most Common Lisps we have tried, (load
;  "foo") will load the compiled form of foo if it is available and up
;  to date.  This seems to work for KCL, Symbolics, Lucid, and TI.
;  However, you may need to specify a value, e.g.  (SETQ
;  FILE-EXTENSION-BIN "fasl").  FILE-EXTENSION-BIN is DEFVARed instead
;  of DEFPARAMTERed so that the user can override its setting.

|#

(DEFVAR FILE-EXTENSION-ERR "err")

(DEFVAR FILE-EXTENSION-LIB "lib")

#|
;  The following code is also found in nqthm.lisp.  See comment above.

(DEFVAR FILE-EXTENSION-LISP "lisp")

;  FILE-EXTENSION-LISP is DEFVARed instead of DEFPARAMTERed so that
;  the user can override its setting.  FILE-EXTENSION-LISP is also
|#

(DEFVAR FILE-EXTENSION-FAIL "fail")

(DEFVAR FILE-EXTENSION-EVENTS "events")

; The default extension for a file to be processed by PROVE-FILE.

(DEFPARAMETER FILE-EXTENSION-PROVED "proved")

; Used by PROVE-FILE as the extension of a file that is created upon successful
; termination.

(DEFPARAMETER FILE-EXTENSION-STARTED "STARTED")

; Used by PROVE-FILE as the extension of a file that is created when processing
; is started.  The file is deleted if processing is successful.

(DEFVAR PPR-FLATSIZE)

(DEFVAR PROOF-START-TIME-IN-60THS)

(DEFVAR FMLA)

(DEFVAR FNS)

(DEFVAR FNSTACK)

(DEFPARAMETER FNS-TO-BE-IGNORED-BY-REWRITE NIL)

;   Terms beginning with function names on this list are not touched by
;   rewrite or expand abbreviations.  However, their arguments will have
;   already been worked on.

(DEFPARAMETER FORCE-OUTPUT-ON-STANDARD-OUTPUT T)

(DEFPARAMETER FORCEIN 38)

(DEFPARAMETER FOR-OPS
  (QUOTE (ADD-TO-SET ALWAYS APPEND COLLECT COUNT DO-RETURN EXISTS MAX MULTIPLY
                     SUM UNION)))

;   These are the quantifier names handled by the FOR function.

(DEFVAR FORM)

(DEFVAR FREE-VARS-IN-REWRITE-RHSS)

(DEFVAR FREE-VARS-IN-SIGHT)

;   During REWRITE this variable holds the list of variable symbols occurring
;   in the current clause.

(DEFPARAMETER GEN-VARIABLE-NAMES (QUOTE (Y A U B E G H P Q R S)))

;   List of variables that can be introduced by generalize.  See
;   ELIM-VARIABLE-NAMES.

(DEFVAR GEN-VARIABLE-NAMES1)

;   Those GEN-VARIABLE-NAMES not occurring in theorem being proved.

(DEFPARAMETER GENERALIZE-LEMMA-NAMES NIL)

(DEFVAR GENERALIZE-LEMMAS)

;   The list of GENERALIZE-LEMMA records representing all known GENERALIZE
;   lemmas.

(DEFPARAMETER GENERALIZING-SKOS NIL)

(DEFVAR GENRLTLIST)

(DEFPARAMETER HEURISTIC-TYPE-ALIST NIL)

;   This type alist is used under ADD-TERMS-TO-POT-LST to determine
;   heuristically which terms are numeric and should be linearized.  Soundness
;   and tail biting are not affected by its setting.

(DEFPARAMETER HINT NIL)

;   If nonNIL, then PROVE goes straight into induction.

(DEFVAR HINTS)

;   STORE-SENT looks at the HINTS argument of PROVE-LEMMA when deciding whether
;   an induction has been done.

(DEFPARAMETER HINT-VARIABLE-ALIST
  (QUOTE ((DISABLE TEMPORARILY-DISABLED-LEMMAS NIL NIL)
          (ENABLE TEMPORARILY-ENABLED-LEMMAS NIL NIL)
          (EXPAND HINTED-EXPANSIONS T NIL)
          (DO-NOT-INDUCT DO-NOT-USE-INDUCTION-FLG NIL NIL)
          (DO-NOT-GENERALIZE DO-NOT-GENERALIZE-FLG NIL NIL)
          (HANDS-OFF FNS-TO-BE-IGNORED-BY-REWRITE NIL NIL)
          (NO-BUILT-IN-ARITH NO-BUILT-IN-ARITH-FLG NIL NIL))))

;   This is a list of 4-tuples interpreted by APPLY-HINTS.  Each element of the
;   list is of the form:

;   (visible-name internal-variable-name translate-flg default-value).

;   Whenever there is a hint whose CAR is one of the visible-names, the
;   corresponding internal-variable-name is set by APPLY-HINTS to the CDR of
;   the hint.  If the translate-flg is T, the CDR of the hint is taken as a
;   list of terms and each element of it is TRANSLATEd and the internal
;   variable is set to the resulting list.  It is assumed that at the top level
;   of the system we have arranged -- e.g., by an appropriate DEFVAR -- for
;   each of the internal variables to have the value given by the
;   default-value.  The UNWIND-PROTECT in PROVE-LEMMA, in which hints are
;   processed, makes sure the internal variables are restored to their default
;   values after the PROVE-LEMMA has terminated.  Thus, if a variable is
;   DEFVARd to the default value in BASIS and is never set in our code then its
;   value is always the default value except when you are executing under a
;   PROVE-LEMMA containing a hint with the corresponding visible-name.  That
;   is, you can regard those variables as having been bound by PROVE-LEMMA to
;   the user specified values or to their global default values otherwise.

(DEFPARAMETER HINTED-EXPANSIONS NIL)

;   Used to pass information from APPLY-HINTS to SETUP regarding which terms
;   the user wants expanded.

(DEFVAR HIST-ENTRY)

(DEFVAR ID-IFF)

(DEFPARAMETER IN-ADD-SHELL0 NIL)

(DEFVAR INDENT)

(DEFPARAMETER INDICIAL-VARIABLE-NAMES (QUOTE (X Y Z U V W X1 Y1 Z1 U1 V1 W1)))

;   List of variables that can be introduced as indicials during
;   renaming.  We believe it is unimportant whether this list overlaps
;   with the GEN- and ELIM-VARIABLE-NAMES.

(DEFVAR INDUCTION-CONCL-TERMS)

(DEFPARAMETER INDUCTION-HYP-TERMS NIL)

(DEFVAR INST-HYP)

(DEFPARAMETER IN-ADD-AXIOM-FLG NIL)

(DEFPARAMETER IN-BOOT-STRAP-FLG NIL)

(DEFPARAMETER IN-PROVE-LEMMA-FLG NIL)

(DEFPARAMETER IO-FN (QUOTE IO1))

;   The name of the function called by IO to do the printing during a proof.
;   IO is called from several of the theorem proving routines.  By redefining
;   IO-FN we can alter the amount of IO1 we see.  We usually set IO-FN to
;   either IO1 or NO-OP.

(DEFPARAMETER IO-TIME 0)

;   Used to sum up the total amount of time spent in IO during PROVE.

(DEFPARAMETER IPOSITION-ALIST NIL)

(DEFVAR LAST-CLAUSE)

(DEFVAR LAST-EXIT)

;   When RELIEVE-HYPS1 fails, the value of LAST-EXIT encodes the reason we
;   failed.

(DEFVAR LAST-HYP)

;   When RELIEVE-HYPS1 fails, LAST-HYP is set to the HYP that was not relieved.

(DEFVAR LAST-PRIN5-WORD)

(DEFPARAMETER LAST-PRINEVAL-CHAR (QUOTE |.|))

;   Supposedly this is the last character printed under PRINEVAL, but actually
;   it is only accurate when the last character was a punctuation mark.
;   Otherwise, it is some arbitrary non-punctuation character.  The purpose
;   of this char is to decide how many spaces to put out in PRIN5* before
;   printing the next word.

(DEFVAR LAST-PRINT-CLAUSES)

(DEFPARAMETER LAST-PROCESS NIL)

(DEFPARAMETER LEFTMARGINCHAR NIL)

;   This is the character that IO1 and PPR will print along the left margin of
;   the proof tree.

(DEFPARAMETER LEGAL-PROVE-FILE-FNS
 (QUOTE (ADD-AXIOM ADD-SHELL COMMENT DCL DEFN DISABLE ENABLE PROVE-LEMMA
         TOGGLE TOGGLE-DEFINED-FUNCTIONS UBT
         CONSTRAIN FUNCTIONALLY-INSTANTIATE
         DEFTHEORY LEMMA AXIOM
         SET-STATUS DISABLE-THEORY ENABLE-THEORY)))

; PROVE-FILE checks that these are the only CARs of top-level forms that occur
; in a given file, save the first, which must be a NOTE-LIB or a BOOT-STRAP,
; and also save (COMPILE-UNCOMPILED-DEFNS "tmp") and (SETQ REDUCE-TERM-CLOCK
; integer) and (SETQ *COMPILE-FUNCTIONS-FLG* T/NIL).

(DEFPARAMETER LEMMA-DISPLAY-FLG NIL)

(DEFPARAMETER LEMMA-TYPES (QUOTE (REWRITE ELIM GENERALIZE META)))

;   For each lemma type x there must be a function CHK-ACCEPTABLE-x-LEMMA and
;   ADD-x-LEMMA.

(DEFPARAMETER LEMMA-STACK NIL)

(DEFVAR LEMMAS-USED-BY-LINEAR)

;   When ADD-TERMS-TO-POT-LST returns CONTRADICTION this list contains the
;   names of the lemmas used.

;   In between events, the user may save the state of the theorem-prover by
;   invoking MAKE-LIB.  The next five LIB- variables are the places from which
;   MAKE-LIB starts to trace out the current state.  Information about the
;   current state is found in (a) variables on LIB-VARS, (b) property lists of
;   symbols in LIB-ATOMS-WITH-PROPS under LIB-PROPS, and (c) in the definition
;   SEXPR properties of symbols in LIB-ATOMS-WITH-DEFS.

(DEFVAR LIB-ATOMS-WITH-PROPS)

(DEFVAR LIB-ATOMS-WITH-DEFS)

(DEFVAR LIB-FILE)

;   When a file is "noted," LIB-FILE is set to an open file object or pathname
;   to the noted file.

(DEFVAR LIB-PROPS)

;   LIB-PROPS is automatically set by ADD-SUB-FACT -- when called with INIT arg
;   = T -- to be a list all properties declared to be part of the state of the
;   system, except for the property SEXPR.

(DEFVAR LIB-VARS)

;   LIB-VARS is automatically set by ADD-SUB-FACT -- when called with INIT arg
;   = T -- to be a list of all of the variables that form part of the state
;   of the system.

;   Of considerably less significance than the foregoing LIB- variables are two
;   which are used to make consistency checks so that libararies are never
;   loaded into incompatible versions of the theorem-prover -- at least not
;   without warning:

(DEFVAR LIB-DATE)

;   This is the date of the creation of a library.

(DEFVAR LIB-VERSION)

;   The value of THEOREM-PROVER-LIBRARY-VERSION written to a library when
;   it is created.

(DEFPARAMETER LIB-VERSION-TROUBLE NIL)

;   The variable above is set to T when we note a library with an
;   inappropriate lib-version.  PROVE-FILE's final report on a run
;   advises you when this variable is non-NIL.  It is never reset to
;   NIL because we do not know what damage might have been caused by
;   noting an inappropriate lib.

(DEFVAR LINEAR-ASSUMPTIONS)

;   When ADD-TERMS-TO-POT-LST returns CONTRADICTION this list contains the
;   terms assumed true during the linearization.

(DEFPARAMETER LINEARIZE-ASSUMPTIONS-STACK NIL)

(DEFPARAMETER LINEL-VALUE 79)

(DEFPARAMETER LITATOM-FORM-COUNT-ALIST NIL)

(DEFPARAMETER LITS-THAT-MAY-BE-ASSUMED-FALSE NIL)

;   During the construction of the POT-LST in SIMPLIFY-CLAUSE0, we wish to
;   have available as hypotheses the negations of the literals in the
;   clause we are trying to prove.  This variable contains those lits
;   during that construction.  As lemmas, those lits get stored in POLYs.
;   Then, during SIMPLIFY-CLAUSE1's use of linear, we are careful, in
;   ADD-EQUATIONS, not to use any POLY that descends from the CURRENT-LIT,
;   by checking that CURRENT-LIT is not a MEMBer of the lemmas used to
;   produce the POLY.  During all calls of REWRITE except those under the
;   construction of the POT-LST in SIMPLIFY-CLAUSE0, this variable should
;   be NIL.

(DEFPARAMETER LITS-TO-BE-IGNORED-BY-LINEAR NIL)

;   Polys descending from the lits in this list are ignored by the linear
;   package.

(DEFVAR MAIN-EVENT-NAME)

;   All the undo information saved by ADD-FACT is saved on the property list of
;   this atom.  Thus, one of the main acts of creating an event is to bind this
;   name to the event name, so that subsequent ADD-FACTs know who is
;   responsible.

(DEFVAR MARG2)

;   The PPR variable specifying the righthand margin.

(DEFVAR MATCH-TEMP)

;   Smashed freely in our pattern matcher.

(DEFVAR MATCH-X)

(DEFVAR MINREM)

(DEFPARAMETER *MODS-ALIST* NIL)

(DEFPARAMETER MUST-BE-FALSE NIL)

(DEFPARAMETER MUST-BE-TRUE NIL)

(DEFVAR NAME)

(DEFVAR NAMES)

(DEFVAR NEW-VAR-INDEX)

(DEFVAR NEXTIND)

(DEFVAR NEXTNODE)

(DEFPARAMETER NILCONS (CONS NIL NIL))

(DEFPARAMETER NO-BUILT-IN-ARITH-FLG NIL)

;   If T the arithmetic package and the storage of arithmetic lemmas is
;   disabled.

(DEFVAR NONCONSTRUCTIVE-AXIOM-NAMES)

;   The names of all of the axioms added with ADD-AXIOM.  We can accept the
;   proof of correctness of a metafunction only when this list is empty.

(DEFPARAMETER NQTHM-READTABLE 'UNINITIALIZED)

; The Nqthm readtable is used by PROVE-FILE.  However, we always
; access it via the function NQTHM-READTABLE which builds it the first
; time it is needed and saves it in the variable above.

(DEFVAR NUMBER-OF-VARIABLES)

(DEFVAR OBJECTIVE)

(DEFPARAMETER OBVIOUS-RESTRICTIONS NIL)

(DEFPARAMETER ORIG-LEMMA-STACK NIL)

(DEFPARAMETER ORIG-LINEARIZE-ASSUMPTIONS-STACK NIL)

(DEFPARAMETER ORIGEVENT NIL)

(DEFVAR ORIGTHM)

(DEFCONSTANT PARAGRAPH-INDENT 5)

;   The number of spaces put out by PRIN5 when it sees the number sign token.

(DEFVAR PARENT)

(DEFVAR PARENT-HIST)

(DEFPARAMETER PERSISTENCE-RATIO 0.50)

;   The functions which print rewrite path frames note those
;   frames that have an unusually high persistence.  The
;   number above defines what we mean by "unusually."  See
;   HIGH-PERSISTENCEP.

(DEFPARAMETER PETITIO-PRINCIPII NIL)

;   When PETITIO-PRINCIPII is non-NIL, Nqthm is unsound.

(DEFVAR POS)

(DEFVAR PPR-REMAINDER)

(DEFVAR PPRFILE)

(DEFPARAMETER PPRFIRSTCOL 35)

(DEFCONSTANT PREFIX-FOR-FORMALS (QUOTE *3*))

(DEFCONSTANT PREFIX-FOR-FUNCTIONS (QUOTE *1*))

(DEFCONSTANT PREFIX-FOR-PROG-VARS (QUOTE *2*))

(DEFPARAMETER PRINEVAL-FNS
  (QUOTE (= AND EQUAL OR NOT EQ !CLAUSE !CLAUSE-SET !PPR
            LENGTH LENGTH-TO-ATOM !PPR-LIST !LIST1 !LIST PLURALP
            QUOTE !TERM !TERM-LIST CAR CDR FN-SYMB FFN-SYMB
            ARGN FARGN SARGS FARGS QUOTEP FQUOTEP)))

;   This is the list of LISP functions that PRINEVAL -- actually PEVAL -- can
;   evaluate.  Before adding a function to the list, make sure that the
;   function is essentially an EXPR -- rather than a FEXPR -- in that all of
;   its args get evald.  All of the functions in PRINEVAL-FNS are handled
;   specially in PEVAL.

(DEFVAR PROCESS)

(DEFVAR PROCESS-CLAUSES)

(DEFVAR PROCESS-HIST)

(DEFVAR PROP)

(DEFVAR PROPLIST)

(DEFVAR PROVEALL-FILENAME)

(DEFVAR PROVE-TERMINATION-CASES-TRIED)

(DEFVAR PROVE-TERMINATION-LEMMAS-USED)

(DEFPARAMETER PROVEALL-FLG NIL)

; This flag is NIL unless we are under PROVEALL.  The purpose of the flag is
; to permit us to close PROVE-FILE and ERR-FILE in any event command that is
; not called under PROVEALL.  The user is not supposed to know about PROVE-FILE
; and ERR-FILE, but aborted PROVEALLs can cause them to retain their values,
; causing subsequent output to be shipped to them.  CHK-COMMAND-STATUS, which
; every event command calls, insures that they are set correctly.

(DEFPARAMETER PROVE-FILE NIL)

; Theorem-prover output is sent to PROVE-FILE.  Warnings and error messages
; are also sent to ERR-FILE, if it is different from PROVE-FILE.  PROVE-FILE
; and ERR-FILE are initially set to NIL, which means that output goes to the
; default output, which is initially the terminal.

(DEFVAR PROVE-TIME)

(DEFPARAMETER R-ALIST NIL)

(DEFPARAMETER R-LOOP-TRACE-MODE NIL)

(DEFPARAMETER R-LOOP-UNTRANSLATE-MODE T)

(DEFPARAMETER *RANDOM-SEED* 0)

(DEFVAR RECOGNIZER-ALIST)

;   An alist that associates with each shell recognizer, e.g., NUMBERP, the
;   type set recognized by that predicate, e.g., the bit mask representing the
;   set whose only element is the type class for NUMBERs.  Obviously, the list
;   is used to help determine if recognizer expressions can be simplified to
;   TRUE (when the type set of the argument is the type set recognized) or
;   FALSE (when the type set of the argument does not intersect with the one
;   recognized).

(DEFVAR RECORD-DECLARATIONS)

(DEFVAR RECORD-TEMP)

;   Smashed repeatedly during our record package manipulations.

(DEFPARAMETER REDUCE-TERM-CLOCK 100)

(DEFVAR RELIEVE-HYPS-NOT-OK-ANS)

;   The REWRITE-PATH is maintained in an array used as a stack.  The
;   array is named REWRITE-PATH-STK and the top of stack pointer is
;   REWRITE-PATH-STK-PTR, which points at the most recently pushed
;   element and is -1 initially.  The length of the allocated array
;   is REWRITE-PATH-STK-LENGTH and is automatically extended
;   when necessary.  The items on the stack are record structures
;   of type REWRITE-PATH-FRAME.  See the declaration of that record.

(DEFPARAMETER REWRITE-PATH-STK-PTR NIL)

(DEFVAR REWRITE-PATH-STK-PTR0)

(DEFPARAMETER REWRITE-PATH-STK NIL)

(DEFVAR REWRITE-PATH-STK-LENGTH)

(DEFVAR REWRITE-PATH-FRAME-CNT)

(DEFPARAMETER REWRITE-PATH-PERSISTENCE-ALIST NIL)

(DEFVAR SCRIBE-FLG)

(DEFVAR SETQ-LST)

(DEFVAR SET-STATUS-DEPENDENTS)
(DEFVAR SET-STATUS-ENABLE-NAMES)
(DEFVAR SET-STATUS-DISABLE-NAMES)

(DEFVAR SHELL-ALIST)

;   An alist associating each shell name, e.g., CONS, with its type number.
;   The type set of the shell -- that is, the set containing only that type of
;   object -- is just the bit mask with one 1 in it, at the bit whose position
;   is the class's type no.  Thus, the type number for FALSE is 0, TRUE 1, etc.
;   The alist is used when determining the type of an expression beginning with
;   the shell name.

(DEFVAR SHELL-POCKETS)

;   A list of pockets consisting of a shell name and the list of its
;   destructors, with the shell name in the car.

(DEFVAR SIMPLIFY-CLAUSE-MAXIMALLY-CLAUSES)

(DEFVAR SIMPLIFY-CLAUSE-MAXIMALLY-HIST)

(DEFVAR SIMPLIFY-CLAUSE-POT-LST)

;   The ADD-EQUATIONS-WITH-LEMMAS of the top-level clause in SIMPLIFY-CLAUSE.

(DEFVAR SINGLETON-TYPE-SETS)

;   A list of type sets of shells with no components.  If a shell has no
;   components then an expression beginning with the shell name represents a
;   unique constant, e.g., (TRUE) or (FALSE) or other shells the user might
;   introduce such as (ERROR).  If an expression is known to have as its type
;   set one of the singleton type sets, the expression is known to be equal to
;   the corresponding object.

(DEFVAR SPACELEFT)

(DEFPARAMETER STACK NIL)

(DEFVAR STARTLIST)

(DEFVAR T2)

(DEFVAR TEMP-TEMP)

;   Used freely by anyone, but liable to be set by a call of any function.

(DEFVAR TEMP1)

(DEFPARAMETER TEMPORARILY-DISABLED-LEMMAS NIL)

(DEFPARAMETER TEMPORARILY-ENABLED-LEMMAS NIL)

(DEFPARAMETER TERMS-TO-BE-IGNORED-BY-REWRITE NIL)

(DEFVAR TEST-LST)

(DEFPARAMETER THEOREM-PROVER-LIBRARY-VERSION 7)

(DEFVAR *THM-SUPPRESS-UNDO-NAME-WARNING-FLG* NIL)

(DEFVAR THM)

(DEFPARAMETER TIME-LIMIT-IN-60THS NIL)

(DEFPARAMETER TOTAL-MISC-TIME 0.0)

;   These three variables are used to accumulate the times consumed by
;   the individual events.  The vars are incremented by STOP-STATS.
;   DO-EVENTS notes the initial and final totals to print the total
;   for its events.

(DEFPARAMETER TOTAL-PROVE-TIME 0.0)

(DEFPARAMETER TOTAL-IO-TIME 0.0)

(DEFCONSTANT TREE-INDENT 2)

;   The number of spaces IO1 indents when printing out the tree structure of
;   the proof.

(DEFCONSTANT TREE-LINES 2)

;   The number of lines IO1 skips between each node of the tree structure in a
;   proof.

(DEFPARAMETER TRUE (QUOTE (QUOTE *1*TRUE)))

;   A variable bound to internal form of the term (TRUE) to make coding more
;   convenient.

(DEFPARAMETER TRUE-CLAUSE (LIST TRUE))

;   The clause whose only literal is the (TRUE) literal.  This just makes
;   coding more convenient.

(DEFVAR TRUE-COMPOUND-RECOGNIZER-ALIST)

;   A list of triples of the form (fn type-set . name) encoding the fact
;   that the event named name establishes that when (fn X) is true,
;   x has type set type-set.  Used by SMART-ASSUME-TRUE-FALSE to forward
;   chain from (fn X) to typeset info about X.  See ACCEPTABLE-COMPOUND-
;   RECOGNIZER-LEMMAP for a discussion.

(DEFPARAMETER TRUE-TYPE-ALIST NIL)

(DEFPARAMETER ERR-FILE NIL)

;   The name of the file to which error and warning messages will be printed.

(DEFPARAMETER TYPE-ALIST NIL)

;   An alist used by TYPE-SET -- and hence almost every routine in the theorem
;   prover -- to associate with a term its type bits.  The list is always
;   protected by rebinding it when a new entry must be added.  However it has
;   become a GLOBAL free var out of convenience.  TYPE-SET cannot be trusted
;   unless TYPE-ALIST is accurately set.

(DEFCONSTANT TYPE-SET-BOOLEAN 3)

;   The bit pattern representing the set containing only the type classes TRUE
;   and FALSE.

(DEFCONSTANT TYPE-SET-CONS 16)

;   Type set of CONS exprs.

(DEFCONSTANT TYPE-SET-FALSE 1)

;   The bit pattern representing the set containing only the type class FALSE.

(DEFCONSTANT TYPE-SET-LITATOMS 8)

;   Type set of PACK exprs.

(DEFCONSTANT TYPE-SET-NEGATIVES 32)

;   Type set of MINUS exprs.

(DEFCONSTANT TYPE-SET-NUMBERS 4)

;   The bit pattern representing the set containing only the type class of 0
;   and ADD1 -- i.e., that set recognized by NUMBERP.

(DEFVAR TYPE-SET-TERM1)

(DEFCONSTANT TYPE-SET-TRUE 2)

;   The bit pattern representing the set containing only the type class TRUE.

(DEFCONSTANT TYPE-SET-UNKNOWN -1)

;   The bit pattern representing the set of all type classes.

(DEFPARAMETER UN-PRODUCTIVE-PROCESSES
  (QUOTE (SETTLED-DOWN-CLAUSE STORE-SENT POP SUBSUMED-ABOVE
                              SUBSUMED-BY-PARENT SUBSUMED-BELOW
                              FINISHED)))

;   Used by IO1 to determine if the descendants list of the current process
;   should be printed out.  Some processes, such as simplification, lead to n
;   new clauses, where n=0 means the parent was proved.  For unproductive
;   processes, such as SETUP, the list of descendants is meaningless since the
;   process does not change the current goal -- as far as the IO is concerned.

(DEFVAR UNDONE-EVENTS)

(DEFPARAMETER UNDONE-EVENTS-STACK NIL)

(DEFVAR UNIFY-SUBST)

(DEFVAR UNIVERSE)

(DEFPARAMETER USE-NO-LEMMAS-FLG NIL)

;   When non-NIL this flag prevents REWRITE from using rewrite lemmas, axioms,
;   and recursive definitions.  It is still free to use built in information
;   (e.g., about EQUAL) and the type set information through
;   TYPE-PRESCRIPTIONs, RECOGNIZER-ALIST, etc.  The option is used when PROVE
;   is first given a theorem and we want to eliminate the propositional
;   calculus stuff in it -- expanding the IMPLIES and NOTs etc -- without
;   wasting time trying to rewrite the interior recursive part of the theorem
;   until we have dug out all the hypotheses and put the thing into clausal
;   form.

(DEFVAR VAL)

(DEFVAR VAR-ALIST)

(DEFPARAMETER ZERO (QUOTE (QUOTE 0)))

;   Internal representation of (ZERO).

;                                   MACROS


(DEFMACRO *1*IF (X Y Z)

;   *1*IF is the only *1* function that is or may be a macro -- all the others
;   are likely to be APPLYed, for example in REWRITE or REDUCE-TERM.

  `(COND ((EQ ,X *1*F) ,Z) (T ,Y)))

(DEFMACRO ADD-NAME-TO-HASH (NAME HASH-TABLE)
  `(SETF (GETHASH ,NAME ,HASH-TABLE) T))

(DEFMACRO ASSOC-EQ (X Y)
  `(ASSOC ,X ,Y :TEST 'EQ))

(DEFMACRO ASSOC-EQUAL (X Y)
  `(ASSOC ,X ,Y :TEST 'EQUAL))

(DEFMACRO MEMBER-EQ (X Y)
  `(MEMBER ,X ,Y :TEST 'EQ))

(DEFMACRO MEMBER-EQUAL (X Y)
  `(MEMBER ,X ,Y :TEST 'EQUAL))

;  In AKCL there are special optimizers for ASSOC and MEMBER when the test is
;  EQ or EQUAL.  On other machines, it would probably be faster to use
;  specially coded functions.

(DEFMACRO ACCESS (RECORD-NAME FIELD RECORD)
  (COND ((CADDR (ASSOC-EQ RECORD-NAME RECORD-DECLARATIONS))
         `(CAR ,(CELL (GET-FIELD-NUMBER RECORD-NAME FIELD) RECORD)))
        (T `(COND ((AND (CONSP ,(COND ((CONSP RECORD)
                                       `(SETQ RECORD-TEMP ,RECORD))
                                      (T RECORD)))
                        (EQ (CAR ,(COND ((CONSP RECORD)
                                         (QUOTE RECORD-TEMP))
                                        (T RECORD)))
                            (QUOTE ,RECORD-NAME)))
                   (CAR ,(CELL (GET-FIELD-NUMBER RECORD-NAME FIELD)
                               (COND ((CONSP RECORD)
                                      (QUOTE RECORD-TEMP))
                                     (T RECORD)))))
                  (T (ACCESS-ERROR (QUOTE ,RECORD-NAME)))))))

(DEFMACRO ARGN (TERM ARG-NUM)
  (COND ((INTEGERP ARG-NUM)
         (COND ((ATOM TERM)
                `(COND ((FQUOTEP ,TERM)
                        (ARGN0 ,TERM ,ARG-NUM))
                       (T (CAR ,(CELL ARG-NUM TERM)))))
               (T (LET ((SYM (GENSYM)))
                    `(LET ((,SYM ,TERM))
                       (ARGN ,SYM ,ARG-NUM))))))
        (T `(ARGN0 ,TERM ,ARG-NUM))))

(DEFMACRO CHANGE (RECORD-NAME FIELD RECORD VALUE)
  (COND ((CADDR (ASSOC-EQ RECORD-NAME RECORD-DECLARATIONS))
         `(RPLACA
           ,(CELL (GET-FIELD-NUMBER RECORD-NAME FIELD) RECORD)
           ,VALUE))
        (T `(COND ((AND (CONSP ,(COND ((CONSP RECORD)
                                       `(SETQ RECORD-TEMP ,RECORD))
                                      (T RECORD)))
                        (EQ (CAR ,(COND ((CONSP RECORD)
                                         (QUOTE RECORD-TEMP))
                                        (T RECORD)))
                            (QUOTE ,RECORD-NAME)))
                   (RPLACA ,(CELL (GET-FIELD-NUMBER RECORD-NAME FIELD)
                                  (COND ((CONSP RECORD)
                                         (QUOTE RECORD-TEMP))
                                        (T RECORD)))
                           ,VALUE))
                  (T  (ACCESS-ERROR (QUOTE ,RECORD-NAME)))))))

(DEFMACRO DEF-NQTHM-RECORD (NAME FIELD-LST CHEAP)
  `(RECORD-DECLARATION (QUOTE ,NAME)
                       (QUOTE ,FIELD-LST)
                       (QUOTE ,CHEAP)))

(DEFMACRO DISABLEDP (NAME)

; Releases of Nqthm prior to Nqthm-1992 used "linear-time" disabling,
; which meant that the question "is this name disabled?" was answered
; by scanning a list of all the disabled names.  In Nqthm-1992 we use
; "constant-time" disabling, which uses hash tables.  This change was
; necessitated by the large size of Nqthm events files and the
; convention of "stacking" such files by disabling all the rules in
; one before going on to the next.  In such applications,
; constant-time disabling dramatically improves the performance of
; Nqthm, by a factor of 2 or more.

; This implementation of constant-time disabling was originally done
; by Matt Wilding.  It was inspected and refined by Matt Kaufmann
; before we adopted it with only minor improvements.  We now describe
; the basic design, which is entirely due to Wilding.

; We have two hash tables, GLOBAL-DISABLEDP-HASH and LOCAL-DISABLEDP-
; HASH.  Roughly speaking, the global hash table contains the globally
; disabled names.  However, global DISABLE and ENABLE events do not
; update that hash table; they merely add tuples to the
; DISABLED-LEMMAS list.  This makes it easier to implement undoing --
; indeed, undoing need not concern itself with the hash tables.  But
; every time we use the global table we first check that it reflects
; the then current DISABLED-LEMMAS list and if not we cleanse the
; table and load the DISABLED-LEMMAS into it.  If a PROVE-LEMMA event
; has no local enabling/disabling, then the global hash table is so
; used during the proof.

; So now we deal with local enables/disables.  If a PROVE-LEMMA does
; local status changes, APPLY-HINTS computes from the hints the set of
; disabled names and loads those names into the LOCAL-DISABLEDP-HASH.
; It sets the flag LOCAL-DISABLEDP-HASH-FLAG to T to indicate to
; DISABLEDP that the local hash array should be used instead of the
; global one.  This flag is unwind-protected in PROVE-LEMMA so that
; its top-level value is always NIL.  There is, however, one last
; twist.  Because of (DISABLE-THEORY T) it is possible to disable all
; names and then selectively enable others.  It is thought to be more
; efficient in this case to keep track of the enabled names rather
; than the disabled ones (because we think there are often fewer
; enabled names).  APPLY-HINTS handles this situation by leaving
; TEMPORARILY-DISABLED-LEMMAS with the value T (instead of its normal
; list of disabled names) and loading the LOCAL-DISABLEDP-HASH with
; just the opposite of what its name suggests!

; What with local ENABLE and DISABLE hints and ENABLE-THEORY and DISABLE-THEORY
; hints, it has become somewhat complicated to determine the status of a name.
; Here is the algorithm.  The following conditions are checked sequentially:

; 1. If the given name is included in an ENABLE hint, consider it enabled.

; 2. If the given name is included in a DISABLE hint, consider it disabled.

; 3. If the given name belongs to some theory named in an
; ENABLE-THEORY hint, consider it enabled.

; 4. If the given name belongs to some theory named in an
; DISABLE-THEORY hint, consider it disabled.

; 5. If there is an (ENABLE-THEORY T) hint (respectively, a (DISABLE-THEORY T)
; hint), consider it enabled (respectively, disabled).

; 6. Simply check whether it is enabled or disabled according to the
; global database.

  `(COND
    (LOCAL-DISABLEDP-HASH-FLAG
     (IF (EQ TEMPORARILY-DISABLED-LEMMAS T)
         (NOT (GETHASH ,NAME LOCAL-DISABLEDP-HASH))
       (GETHASH ,NAME LOCAL-DISABLEDP-HASH)))
    (T (GLOBAL-DISABLED-HASHP ,NAME))))

;   The following macro lets us protect against ERROR1's in a way
;   analogous to ERRSET's protection against errors.  The spec is that
;   if form causes no ERROR1s then (ERROR1-SET form) returns (LIST form)
;   if form causes a SOFT ERROR1, the ERROR1-SET returns NIL.  HARD ERROR1s
;   ignore ERROR1-SET and cause ERRORs, which may be a simple reset
;   in some lisps.

(DEFMACRO ERROR1-SET (FORM)
  `(LET ((ERROR1-SET-FLG T))
     (CATCH (QUOTE ERROR1-SET) (LIST ,FORM))))

;   In order to make invocations of ERROR1 less obtrusive in the code, we adopt
;   a macro convention such that (ER SOFT (X (Y A)) this is the message)
;   becomes (ERROR1 (PQUOTE (PROGN this is the message))
;                   `((X . ,X) (Y . ,A))
;                   (QUOTE SOFT))

(DEFMACRO ER (INTENSITY BINDINGS &REST X)
  `(ERROR1 (PQUOTE (PROGN ,@X))
           (LIST ,@(ITERATE FOR PAIR IN BINDINGS COLLECT
                            (COND ((ATOM PAIR)
                                   `(CONS (QUOTE ,PAIR) ,PAIR))
                                  (T `(CONS (QUOTE ,(CAR PAIR))
                                            ,(CADR PAIR))))))
           (QUOTE ,INTENSITY)))

(DEFMACRO EVAL-WITH-OUTPUT-TO-FILE (TO-FILE FORM)
  `(WITH-OPEN-STREAM
    (*STANDARD-OUTPUT*
     (OPEN ,TO-FILE :DIRECTION :OUTPUT :IF-EXISTS :RENAME-AND-DELETE))
    ,FORM))

(DEFMACRO EVENT-COMMAND (COMMAND-FORM &REST X)

;  This is the standard pre/postlude for event commands such as
;  DEFN and PROVE-LEMMA.  The COMMAND-FORM is the actual command
;  typed by the user and is not the "event form" stored in the
;  database.  The difference is that the event form has its term
;  components in translated form.  The COMMAND-FORM is used to
;  maintain the FAILED-EVENTS list.

  `(LET (EVENT-COMMAND-ANS (EVENT-COMMAND-FORM ,COMMAND-FORM))
     (SETQ FAILED-EVENTS
           (CONS EVENT-COMMAND-FORM FAILED-EVENTS))
     (CHK-COMMAND-STATUS (AND (CONSP EVENT-COMMAND-FORM)
                              (EQ (CAR EVENT-COMMAND-FORM)
                                  (QUOTE BOOT-STRAP))))
     (START-STATS)
     (SETQ EVENT-COMMAND-ANS
           (LET ((COMMAND-STATUS-FLG T) MAIN-EVENT-NAME)
             ,@X))
     (STOP-STATS)
     (SETQ FAILED-EVENTS (REMOVE EVENT-COMMAND-FORM FAILED-EVENTS
                                 :TEST #'EQUAL))
     EVENT-COMMAND-ANS))

(DEFMACRO FARGN (TERM ARG-NUM)
  (COND ((INTEGERP ARG-NUM)
         `(CAR ,(CELL ARG-NUM TERM)))
        (T `(LET ((TERM ,TERM) (ARG-NUM ,ARG-NUM))
              (NTH ARG-NUM TERM)))))

(DEFMACRO FARGS (X) `(CDR ,X))

(DEFMACRO FCONS-TERM (FN ARGS) `(CONS ,FN ,ARGS))

(DEFMACRO FCONS-TERM* (&REST TAIL) `(LIST ,@TAIL))

(DEFMACRO FFN-SYMB (X) `(CAR ,X))

(DEFMACRO FN-SYMB (TERM)
  (COND ((ATOM TERM)
         `(COND ((FQUOTEP ,TERM)
                 (FN-SYMB0 (CADR ,TERM)))
                (T (CAR ,TERM))))
        (T (LET ((SYM (GENSYM)))
             `(LET ((,SYM ,TERM))
                (FN-SYMB ,SYM))))))

(DEFMACRO FQUOTEP (X) `(EQ (CAR ,X) (QUOTE QUOTE)))

(DEFMACRO MAKE (RECORD &REST ARGLIST)
  (COND ((NOT (SETQ TEMP-TEMP (ASSOC-EQ RECORD RECORD-DECLARATIONS)))
         (ERROR "Undeclared record: ~A ~A" RECORD ARGLIST))
        ((INT= (LENGTH ARGLIST) (LENGTH (CADR TEMP-TEMP)))
         (COND ((CADDR TEMP-TEMP)
                `(LIST ,@ARGLIST))
               (T `(LIST (QUOTE ,RECORD) ,@ARGLIST))))
        (T (ERROR "Wrong number of args: ~A ~A" RECORD ARGLIST))))

(DEFMACRO MAKE-DISABLEDP-HASH ()
  `(MAKE-HASH-TABLE :SIZE 1000 :TEST #'EQ))

(DEFMACRO MATCH (TERM PATTERN) (MATCH-MACRO TERM PATTERN))

(DEFMACRO MATCH! (TERM PATTERN) (MATCH!-MACRO TERM PATTERN))

(DEFMACRO NVARIABLEP (X) `(CONSP ,X))

;   On the LISPM, the compiler generates warnings that the following functions
;   are obsolete:  EXPLODEC, EXPLODEN, GETCHAR, GETCHARN, and IMPLODE.  Hence
;   we define the following "OUR-" macros.  EXPLODEC, EXPLODEN, GETCHAR,
;   GETCHARN, and IMPLODE all assume that they are working on SYMBOLPs.

;   We never use EXPLODE because it slashes.

(DEFMACRO PQUOTE (X) `(QUOTE ,X))

(DEFMACRO PRIND (X FILE)
  `(LET ((TEMP ,X)
         (FL ,FILE))

; We use PRINC rather than PRIN1 on symbols because we are sure that
; everything we print (at least when we are printing terms) is in the
; USER package and prin1 is incredibly slow on arbitrary symbols.

     (COND ((SYMBOLP TEMP) (PRINC TEMP FL))
           ((STRINGP TEMP) (PRIN1 TEMP FL))
           ((CHARACTERP TEMP) (PRIN1 TEMP FL))
           (T (PRINC TEMP FL)))
     (SETQ POS (+ POS (COND ((SYMBOLP TEMP) (LENGTH (SYMBOL-NAME TEMP)))
                            (T (OUR-FLATC TEMP)))))))

(DEFMACRO PROVE-FILE-OUT (NAME &REST REST)

; We typically invoke PROVE-FILE via PROVE-FILE-OUT, invoking it from Unix,
; e.g., with the command:

;    % echo '(prove-file-out "goedel")' | nqthm > goedel.trans

; which means `run the program nqthm, feeding it the instruction, i.e., the
; Lisp form to run PROVE-FILE on the file goedel.events, while redirecting the
; standard output (e.g., the proofs and error messages) to the file
; goedel.proofs, and any other output that may incidentally arise to the file
; goedel.trans.'

; Here's an extra | to deal with an Emacs parsing problem above.

  `(LET ((FORCE-OUTPUT-ON-STANDARD-OUTPUT NIL))
     (EVAL-WITH-OUTPUT-TO-FILE (EXTEND-FILE-NAME ,NAME FILE-EXTENSION-PROOFS)
           (PROVE-FILE ,NAME ,@REST))))

(DEFMACRO QUOTEP (X)
  (COND ((ATOM X) `(AND (CONSP ,X) (EQ (CAR ,X) 'QUOTE)))
        (T (LET ((SYM (GENSYM)))
             `(LET ((,SYM ,X))
                (QUOTEP ,SYM))))))

(DEFMACRO OUR-SWAP (X Y) `(SETQ ,X (PROG1 ,Y (SETQ ,Y ,X))))

(DEFMACRO REMOVE-NAME-FROM-HASH (NAME HASH-TABLE)
  `(REMHASH ,NAME ,HASH-TABLE))

(DEFMACRO TOTALP (X)

;   The fundamental theorem about TOTALP is that if (TOTALP fn) then
;
;   (V&C-APPLY$ (QUOTE fn) args)
;      =
;   (IF (MEMBER F args)
;       F
;       (CONS (fn (CAAR args) ... (CAAD...DR args))
;             cost(fn,args)))
;
;   We are not interested in cost.

;   See the discussion of TAMEP.  In this implementation, TOTALP is
;   computed and stored on the property list of each fn by the
;   function PUT-TOTALP which uses the concept of SUPER-TAMEP.

  `(CDAR (GET ,X (QUOTE TOTALP-LST))))

(DEFMACRO WRITE-CHAR1 (X FILE)
  `(PROGN (WRITE-CHAR ,X ,FILE)
          (SETQ POS (1+ POS))))

(DEFMACRO TYPE-PRESCRIPTION (X)
  `(CDAR (GET ,X (QUOTE TYPE-PRESCRIPTION-LST))))

(DEFMACRO VARIABLEP (X) `(ATOM ,X))



(DEFUN CELL (N FIELD)
  (COND ((INT= N 0) FIELD)
        (T (LIST (QUOTE CDR)
                 (CELL (1- N) FIELD)))))

(DEFUN CREATE-LEMMA-STACK (N)
  (SETQ ORIG-LEMMA-STACK (SETQ LEMMA-STACK (CREATE-STACK1 N)))
  (RPLACA LEMMA-STACK (QUOTE TOP))
  NIL)

(DEFUN CREATE-LINEARIZE-ASSUMPTIONS-STACK (N)
  (SETQ ORIG-LINEARIZE-ASSUMPTIONS-STACK
        (SETQ LINEARIZE-ASSUMPTIONS-STACK (CREATE-STACK1 N)))
  (RPLACA LINEARIZE-ASSUMPTIONS-STACK (QUOTE TOP))
  NIL)

(DEFUN CREATE-STACK1 (N)
  (LET (STK)
    (SETQ STK (ITERATE FOR I FROM 1 TO (* 2 N) COLLECT NIL))
    (ITERATE FOR TAIL ON STK BY (QUOTE CDDR) UNTIL (NULL (CDDR TAIL))
             DO (RPLACA (CDDDR TAIL) TAIL))
    STK))

(DEFUN DEFEVENT-APPLY (X NAME FN MIN-ARGS MAX-ARGS)
  (COND ((OR (AND (ATOM X) X)
             (AND (CONSP X) (CDR (OUR-LAST X))))
         (ER SOFT NIL |Argument| |lists| |must| |end| |in|
             (!PPR NIL '|.|)))
        ((OR (< (LENGTH X) MIN-ARGS)
             (> (LENGTH X) MAX-ARGS))
         (COND ((INT= MIN-ARGS MAX-ARGS)
                (ER SOFT (NAME MIN-ARGS)
                    (!PPR NAME NIL) |takes| (!PPR MIN-ARGS NIL)
                    (PLURAL? MIN-ARGS |arguments| |argument|) |.|))
               (T (ER SOFT (NAME MIN-ARGS MAX-ARGS)
                      (!PPR NAME NIL) |takes| |from| (!PPR MIN-ARGS NIL)
                      |to| (!PPR MAX-ARGS NIL) |arguments| |.|))))
        (T (CONS FN
                 (APPEND (ITERATE FOR ARG IN X
                                  COLLECT (LIST (QUOTE QUOTE) ARG))
                         (ITERATE FOR I FROM 1
                                  TO (- MAX-ARGS (LENGTH X))
                                  COLLECT NIL))))))

(DEFUN GET-FIELD-NUMBER (RECORD-NAME LITATOM)
  (LET ((TEMP (ASSOC-EQ RECORD-NAME RECORD-DECLARATIONS)))
    (COND ((ITERATE FOR I FROM (COND ((CADDR TEMP) 0)
                                     (T 1))
                    AS FIELD IN (CADR TEMP) WHEN (EQ FIELD LITATOM)
                    DO (RETURN I)))
          (T (ERROR "Undeclared record name or illegal field name ~A ~A"
                    RECORD-NAME LITATOM)))))

(DEFUN KWOTE (X) `(QUOTE ,X))

(DEFUN MATCH-MACRO (TERM PAT)
  (COND ((ATOM TERM)
         (MATCH1-MACRO TERM PAT))
        (T (LET ((SYM (GENSYM "MATCH")))
             `(LET ((,SYM ,TERM))
                ,(MATCH1-MACRO SYM PAT))))))

(DEFUN MATCH!-MACRO (TERM PAT)
  (LIST (QUOTE OR)
        (MATCH-MACRO TERM PAT)
        (QUOTE (ERROR "MATCH! failed"))))

(DEFUN MATCH1-MACRO (TERM PAT)
  (LET (TEST-LST SETQ-LST)
    (MATCH2-MACRO TERM PAT)
    (LIST (QUOTE COND)
          (CONS
           (COND ((NULL TEST-LST) T)
                 ((NULL (CDR TEST-LST)) (CAR TEST-LST))
                 (T (CONS (QUOTE AND) TEST-LST)))
           (NCONC1 SETQ-LST T)))))

(DEFUN MATCH2-MACRO (TERM PAT)
  (COND ((ATOM PAT)
         (COND ((EQ PAT (QUOTE &)) NIL)
               ((OR (EQ PAT T) (EQ PAT NIL))
                (ERROR "Attempt to smash T or NIL."))
               ((SYMBOLP PAT)
                (SETQ SETQ-LST (NCONC1 SETQ-LST (LIST (QUOTE SETQ) PAT TERM))))
               (T (SETQ TEST-LST
                        (NCONC1 TEST-LST (LIST (QUOTE EQUAL) PAT TERM))))))
        ((EQ (QUOTE CONS) (CAR PAT))
         (SETQ TEST-LST (NCONC1 TEST-LST (LIST (QUOTE CONSP) TERM)))
         (MATCH2-MACRO (LIST (QUOTE CAR) TERM) (CADR PAT))
         (MATCH2-MACRO (LIST (QUOTE CDR) TERM) (CADDR PAT)))
        ((EQ (QUOTE QUOTE) (CAR PAT))
         (COND ((SYMBOLP (CADR PAT))
                (SETQ TEST-LST
                      (NCONC1 TEST-LST
                              (LIST (QUOTE EQ)
                                    (LIST (QUOTE QUOTE) (CADR PAT)) TERM))))
               (T (SETQ TEST-LST (NCONC1 TEST-LST
                                         (LIST (QUOTE EQUAL)
                                               (LIST (QUOTE QUOTE) (CADR PAT))
                                               TERM))))))
        (T (COND ((NOT (EQ (QUOTE LIST) (CAR PAT)))
                  (SETQ PAT (CONS (QUOTE LIST)
                                  (CONS (LIST (QUOTE QUOTE) (CAR PAT))
                                        (CDR PAT))))))
           (ITERATE FOR SUBPAT IN (CDR PAT) DO
                    (PROGN (SETQ TEST-LST
                                 (NCONC1 TEST-LST (LIST (QUOTE CONSP) TERM)))
                           (MATCH2-MACRO (LIST (QUOTE CAR) TERM) SUBPAT)
                           (SETQ TERM (LIST (QUOTE CDR) TERM))))
           (SETQ TEST-LST (NCONC1 TEST-LST (LIST (QUOTE EQ) TERM NIL))))))

(DEFUN NCONC1 (X Y) (NCONC X (LIST Y)))

(DEFUN OUR-LAST (L)

;   In Franz, (LAST '(0 1 . 2)) = 2, so we define our own last.

  (COND ((ATOM L) L)
        (T (ITERATE UNTIL (ATOM (CDR L)) DO (SETQ L (CDR L))
                    FINALLY (RETURN L)))))

(DEFUN PACK (L)

;  PACK returns a symbol interned in USER whose print name
;  consists of the characters that are printed by PRINCing
;  the members of L with *PRINT-BASE* 10.

  (LET ((*PRINT-PRETTY* NIL)
        (*PRINT-BASE* 10)
        (*PRINT-RADIX* NIL)
        (*PRINT-LEVEL* NIL)
        (*PRINT-LENGTH* NIL)
        (*PRINT-CASE* :UPCASE))
    (INTERN (FORMAT NIL "~{~A~}" L)
            'USER)))

(DEFUN SUB-PAIR (L1 L2 X)
  (COND ((ITERATE FOR Z IN L2 AS Y IN L1 WHEN (EQUAL Y X)
                  THEREIS (PROGN (SETQ TEMP-TEMP Z) T))
         TEMP-TEMP)
        ((ATOM X) X)
        (T (CONS (SUB-PAIR L1 L2 (CAR X)) (SUB-PAIR L1 L2 (CDR X))))))


;                             RECORD DECLARATIONS

(DEFUN RECORD-DECLARATION (RECORD-NAME FIELD-LST CHEAP)
  (LET (LST)
    (COND ((NOT (BOUNDP (QUOTE RECORD-DECLARATIONS)))
           (SETQ RECORD-DECLARATIONS NIL)))
    (COND ((NOT (OR (CONSP FIELD-LST) (EQ FIELD-LST NIL)))
           (ERROR "Illegal field list: ~A" FIELD-LST))
          ((NOT (OR (EQ CHEAP T) (EQ CHEAP NIL)))
           (ERROR "Illegal cheap flag: ~A" CHEAP)))
    (SETQ LST (LIST RECORD-NAME (COPY-TREE FIELD-LST) CHEAP))
    (COND ((MEMBER-EQUAL LST RECORD-DECLARATIONS) NIL)
          ((ASSOC-EQ (CAR LST) RECORD-DECLARATIONS)
           (SETQ RECORD-DECLARATIONS
                 (CONS LST (REMOVE (ASSOC-EQ (CAR LST) RECORD-DECLARATIONS)
                                   RECORD-DECLARATIONS :TEST #'EQUAL)))
           (FORMAT T "~A redefined.~%"
                   (CAR LST)))
          (T (SETQ RECORD-DECLARATIONS
                   (CONS LST RECORD-DECLARATIONS))))
    RECORD-NAME))

(DEF-NQTHM-RECORD CANDIDATE (SCORE CONTROLLERS CHANGED-VARS UNCHANGEABLE-VARS
                            TESTS-AND-ALISTS-LST JUSTIFICATION INDUCTION-TERM
                            OTHER-TERMS)
  NIL)

;   This record is used to represent one of the plausible inductions that must
;   be considered.  The SCORE represents some fairly artificial estimation of
;   how many terms in the conjecture want this induction.  CONTROLLERS is the
;   list of the controllers -- including unchanging controllers -- for all the
;   inductions merged to form this one.  The CHANGED-VARS is a list of all
;   those variables that will be instantiated (non-identically) in some
;   induction hypotheses.  Thus, CHANGED-VARS include both variables that
;   actually contribute to why some measure goes down and variables like
;   accumulators that are just along for the ride.  UNCHANGEABLE-VARS is a list
;   of all those vars which may not be changed by any substitution if this
;   induction is to be sound for the reasons specified.  TESTS-AND-ALISTS-LST
;   is a list of TESTS-AND-ALISTS which indicates the case analysis for the
;   induction and how the various induction hypotheses are obtained via
;   substitutions.  JUSTIFICATION is the JUSTIFICATION that justifies this
;   induction, and INDUCTION-TERM is the term that suggested this induction and
;   from which you obtain the actuals to substitute into the template.
;   OTHER-TERMS are terms whose induction candidates have been merged into this
;   one for heuristic reasons.

(DEF-NQTHM-RECORD GENERALIZE-LEMMA (NAME TERM) NIL)

;   This record records a GENERALIZE lemma with name NAME.  The TERM is just a
;   well-formed formula, assumed to be a theorem of course, translated but
;   possibly involving IMPLIES and the binary AND.  These records are collected
;   on the TYPE-NAME-AND-LEMMA-LST and used when a term, x, is generalized by
;   scanning the list for all formulas involving x -- modulo a unification of
;   course -- and adding to the hypothesis of the theorem, before it is
;   generalized, the appropriately instantiated formulas found.

(DEF-NQTHM-RECORD JUSTIFICATION (SUBSET MEASURE-TERM RELATION LEMMAS) NIL)

;   Consider the INDUCTION-MACHINE for some function.  This record gives one
;   justification for it.  In particular, MEASURE-TERM, which is a term on a
;   subset of the formals of the function, decreases according to the
;   well-founded relation RELATION in each hypothesis of the INDUCTION-MACHINE.
;   SUBSET is the measured subset of formals.  The fact that the measure
;   decreases can be proved using the lemmas in the list LEMMAS.

(DEF-NQTHM-RECORD LINEAR-LEMMA (NAME HYPS CONCL MAX-TERM) NIL)

;   Internal form of a LINEAR lemma.  NAME is the event name, HYPS is the list
;   of hypotheses, and POLY is the LINEARIZEd conclusion.

(DEF-NQTHM-RECORD LINEAR-POT (VAR POSITIVES NEGATIVES) T)

(DEF-NQTHM-RECORD POLY (CONSTANT ALIST ASSUMPTIONS LITERALS LEMMAS) T)

;   CONSTANT is a INTEGERP.  ALIST is an alist of pairs of the form (ti .
;   ki) where ti is a term and ki is a INTEGERP.  ASSUMPTIONS is a list of
;   terms.  LITERALS is a list of terms.  LEMMAS is a list of lemma names,
;   (LIST 'MARK)'s -- as constructed by ADD-TERMS-TO-POT-LST, or a term.  A
;   POLY represents an implication hyps -> concl, where hyps is the
;   conjunction of ASSUMPTIONS and concl is CONSTANT + k1*t1 + ... + kn*tn
;   <= 0, over the integers.  Every POLY in SIMPLIFY-CLAUSE-POT-LST is
;   being assumed.  See ADD-TERMS-TO-POT-LST for more details about
;   LITERALS and LEMMAS.

(DEF-NQTHM-RECORD REWRITE-RULE (NAME HYPS CONCL LOOP-STOPPER) NIL)

;   These records are used to represent rewrite rules.  The NAME field contains
;   the name of the lemma or axiom.  The HYPS is a list of terms whose
;   conjunction is the hypothesis of the lemma.  The CONCL is the term which is
;   the conclusion of the lemma.  The LOOP-STOPPER is an alist dotting vars to
;   vars and used to prevent infinite rewrite loops due to permutative rewrite
;   rules.  The rewrite cannot be performed if the instantiation of the CDR of
;   some pair is lexicographically bigger than or equal to -- see
;   LOOP-STOPPER-GTE -- the instantiation of the CAR.

(DEF-NQTHM-RECORD REWRITE-PATH-FRAME (PROG CNT LOC TERM ALIST) T)

;   PROG is the name of the theorem prover program that built the frame.
;   TERM and ALIST are suggestive misnomers whose actual interpretation
;   depends on prog.  Here is the table giving the possible values of PROG
;   and the interpretations of TERM and ALIST.

;   PROG                           TERM and ALIST

;   SIMPLIFY-CLAUSE                 CURRENT-CL and NIL

;   SET-SIMPLIFY-CLAUSE-POT-LST     CURRENT-CL and NIL

;   REWRITE                         TERM and ALIST -- TERM is always CONSP!

;   REWRITE-WITH-LEMMAS             LEMMA and UNIFY-SUBST

;   ADD-EQUATIONS-TO-POT-LST        LEMMA and UNIFY-SUBST

;   REWRITE-WITH-LINEAR             TERM and NIL

;   CNT is used to compute the "persistence" of the frame.  The
;   persistence of a frame is the number of frames pushed while
;   while that frame is active.  It is computed as follows.  Every
;   time a frame is pushed the variable REWRITE-PATH-FRAME-CNT is
;   incremented and its current value is stored in the cnt field of
;   the new frame.  Upon popping a frame we compute its persistence
;   by subtracting the stored cnt from the current frame cnt.  Then
;   we accumulate the persistence into the
;   REWRITE-PATH-PERSISTENCE-ALIST provided the frame is either a
;   REWRITE-WITH-LEMMAS or ADD-EQUATIONS-TO-POT-LST frame (in which
;   case we update the alist entry for the LEMMA-NAME) or is a
;   REWRITE frame with non-NIL loc (in which case we update the
;   alist entry for the top-fnname of the term).

;   The interpretation LOC depends on PROG also.  If PROG is REWRITE,
;   LOC is an object that indicates how the current TERM and ALIST
;   were derived from those in the previous frame.  Here are the possible
;   values of LOC for REWRITE frames:

;   NIL                 either this is a top level call or the TERM here
;                          is identical to the one in the previous frame.
;   n > 0               if prev frame is REWRITE, this TERM is the nth
;                          arg of that TERM;
;                       if prev frame is APPLY-LEMMA, this is nth hyp of the
;                          rewrite rule named by the prev frame;
;                       if prev frame is SIMPLIFY, this is the atom of the
;                          nth literal of the given clause.
;   BODY                the body of the top-function of the TERM in
;                          the previous frame.
;   REWRITTEN-BODY      the TERM being rewritten now is the result of rewriting
;                          the body of the function called in the prev frame.
;   RHS                 the right hand side of the conclusion of the rule
;                          in the prev frame.  This may be a rewrite rule but
;                          may also be the concl of a linear lemma.
;   META-RHS            the TERM is the result delivered by the application of
;                          a meta lemma.
;   (BUILTIN-RULE prog) progn is the name of some special purpose
;                          simplifier, like REWRITE-CAR-V&C-APPLY$ and the TERM
;                          being rewritten was manufactured by that rewriter.

;   If PROG is either REWRITE-WITH-LEMMAS or ADD-EQUATIONS-TO-POT-LST,
;   LOC is the term being rewritten with the lemma or unified with the
;   max-term of the linear rule.

;   Under the other PROGs, LOC is NIL.

(DEF-NQTHM-RECORD TESTS-AND-ALISTS (TESTS ALISTS) NIL)

;   A list of these records forms the TESTS-AND-ALISTS-LST component of a
;   CANDIDATE record.  The TESTS field contains a list of forms and the ALISTS
;   field a list of alists.  If the conjunction of the tests is true then some
;   measure goes down on the n-tuples produced by each alist.  The alist
;   contains explicitly pairs of the form (v . v) if v is an unchanging
;   controller.  The soundness of MERGE-CANDS rests on this fact.

(DEF-NQTHM-RECORD TESTS-AND-CASE (TESTS CASE) NIL)

;   This is like a TESTS-AND-CASES except that the CASE component contains
;   exactly one case.  A list of TESTS-AND-CASEs is a flattened machine.

(DEF-NQTHM-RECORD TESTS-AND-CASES (TESTS CASES) NIL)

;   A list of these compose a machine (see INDUCTION-MACHINE).  The TESTS field
;   contains a list of terms whose conjunction must be true before the machine
;   can "execute" the cases.  The CASES field contains a list of arglists of
;   the recursive calls governed by the tests.

(DEF-NQTHM-RECORD TYPE-PRESCRIPTION-NAME-AND-PAIR (NAME PAIR) NIL)

;   The TYPE-PRESCRIPTION-LST property is a list of these records.  The NAME is
;   the name of the rewrite lemma -- or definition -- that gave rise to the
;   type prescription pair (ts . args) PAIR for the function under which this
;   type prescription is hung.

(DEF-NQTHM-RECORD TYPE-RESTRICTION (TERM TYPE-SET DEFAULT) NIL)

;   This record is used to represent processed type restrictions as found on
;   the destructors of shells.  The TERM component is a normalized term
;   composed of recognizers applied to the variable X, possibly negated, and
;   possibly disjoined or conjoined with binary OR or AND.  The TYPE-SET
;   component is the corresponding bit mask.  The DEFAULT is the specified
;   default object satisfying the type set.  At prove time no one looks at
;   TERM.  It is examined during add shells and is used in the rewrite rules
;   added.

;                              BOOT-STRAP-INSTRS

;   We now build up BOOT-STRAP-INSTRS, which is the list of events used to
;   initialize the theorem-prover to its most ignorant state.  Instead of
;   merely setting the variable BOOT-STRAP-INSTRS to the value we want, we use
;   the macros DEFBOOT, DEFBOOT-NQTHM, and DEFBOOT-NOT-NQTHM to add things one
;   at a time.  The only reason we do it this way is so that the various "tags"
;   hacks can take us to the "events".

;   A user could not execute this sequence of commands because they necessarily
;   violate our new name conventions.  For example, axioms about SUB1 mention
;   LESSP before LESSP is defined.  But LESSP can't be defined first because it
;   recurses by SUB1, and before SUB1 were fully axiomatized LESSP wouldn't be
;   accepted as a total function.  Most of the names introduced here are
;   built-into the theorem prover in some sense.  For example, LESSP is on the
;   list of known well-founded relations, TRUE is referenced by name in many
;   routines, the axioms produced by ADD-SHELL use IMPLIES and the other
;   logical connectives, as well as LESSP and PLUS, and the read-time
;   translation routine uses PACK and CONS to translate QUOTE and LIST
;   expressions.  However, most of the logical properties of these names are
;   made known to the theorem prover in the usual way.  For example, TRUE,
;   FALSE, and ADD1 are just shells; the logical connectives are just defined
;   functions.  DIFFERENCE, TIMES, QUOTIENT and REMAINDER are in this list so
;   that efficient *1*Functions can be provided for them.

(DEFPARAMETER BOOT-STRAP-INSTRS NIL)

;   We have only one BOOT-STRAP-INSTRS list, even though we have both the NQTHM
;   mode BOOT-STRAP and the regular BOOT-STRAP.  The two modes are
;   distinguished internally by the flag:

(DEFVAR *1*THM-MODE$)

;   The mode is set to 'NQTHM if we are in NQTHM mode and to 'THM otherwise.
;   (It would have been nicer, perhaps, to make the mode be a flag but we can't
;   have library variables have the value NIL.)  The user has no business
;   setting this flag.  It is set by BOOT-STRAP.  Resetting it after the boot
;   will produce an impure mix of the two theories.  The mode flag is written
;   to the library.  It has the *1* prefix because it is used in some *1*fns.

;   The following macro is used as a fast check that we are in NQTHM mode.

(DEFMACRO CHK-NQTHM-MODE$ (FN)

;   Causes an error if we are not in NQTHM mode.  This function is called
;   by all the NQTHM functions that supposedly never get executed in THM
;   mode.

  `(OR (EQ *1*THM-MODE$ (QUOTE NQTHM))
       (CHK-NQTHM-MODE$-ERR (QUOTE ,FN))))

;   Events are added to BOOT-STRAP-INSTRS with DEFBOOT.  A typical call is:
;   (DEFBOOT name op . args), which adds to BOOT-STRAP-INSTRS the new element
;   (op name . args).  However, there are two special cases.  If op is
;   NQTHM-MODE then a typical call is (DEFBOOT name NQTHM-MODE op . args) and
;   if op is NOT-NQTHM-MODE the call is (DEFBOOT name NOT-NQTHM-MODE op . args)
;   In the first case, the element added to BOOT-STRAP-INSTRS is (IF-NQTHM-MODE
;   (op name . args)); analogous treatment is given the second case.


(DEFMACRO DEFBOOT (NAME OPERATION &REST OTHER-ARGS)
  `(PROGN
     (SETQ BOOT-STRAP-INSTRS
           (NCONC1 BOOT-STRAP-INSTRS
                  ,(COND
                    ((EQ OPERATION (QUOTE NQTHM-MODE))
                     `(QUOTE (IF-NQTHM-MODE
                              (,(CAR OTHER-ARGS) ,NAME ,@(CDR OTHER-ARGS)))))
                    ((EQ OPERATION (QUOTE NOT-NQTHM-MODE))
                     `(QUOTE (IF-NOT-NQTHM-MODE
                              (,(CAR OTHER-ARGS) ,NAME ,@(CDR OTHER-ARGS)))))
                    (T `(QUOTE (,OPERATION ,NAME ,@OTHER-ARGS))))))
     (QUOTE ,NAME)))

(DEFBOOT FALSE ADD-SHELL0 NIL FALSEP NIL)

(DEFBOOT TRUE ADD-SHELL0 NIL TRUEP NIL)

(DEFBOOT NOT DEFN0 (P)
  (IF P (FALSE) (TRUE))
  NIL T T)

(DEFBOOT AND DEFN0 (P Q)
  (IF P (IF Q (TRUE) (FALSE)) (FALSE))
  NIL T T)

(DEFBOOT OR DEFN0 (P Q)
  (IF P (TRUE) (IF Q (TRUE) (FALSE)))
  NIL T T)

(DEFBOOT IMPLIES DEFN0 (P Q)
  (IF P (IF Q (TRUE) (FALSE))
      (TRUE))
  NIL T T)

(DEFBOOT ADD1 ADD-SHELL0 ZERO NUMBERP ((SUB1 (ONE-OF NUMBERP) ZERO)))

(DEFBOOT LESSP DEFN0 (X Y)
  (IF (OR (EQUAL Y 0) (NOT (NUMBERP Y)))
      (FALSE)
      (IF (OR (EQUAL X 0) (NOT (NUMBERP X)))
          (TRUE)
          (LESSP (SUB1 X) (SUB1 Y))))
  NIL T T)

(DEFBOOT LESSP PUT1 0 LEVEL-NO)

(DEFBOOT GREATERP DEFN0 (X Y) (LESSP Y X) NIL T NIL)

(DEFBOOT LEQ DEFN0 (X Y) (NOT (LESSP Y X)) NIL T NIL)

(DEFBOOT GEQ DEFN0 (X Y) (NOT (LESSP X Y)) NIL T NIL)

(DEFBOOT ZEROP DEFN0 (X)
  (IF (EQUAL X 0)
      T
      (IF (NUMBERP X) F T))
  NIL T T)

(DEFBOOT FIX DEFN0 (X)
  (IF (NUMBERP X) X 0)
  NIL T T)

(DEFBOOT PLUS DEFN0 (X Y)
  (IF (ZEROP X)
      (FIX Y)
      (ADD1 (PLUS (SUB1 X) Y)))
  NIL T T)

(DEFBOOT COUNT-NUMBERP ADD-AXIOM1 (REWRITE)
  (IMPLIES (NUMBERP I)
           (EQUAL (COUNT I) I)))

(DEFBOOT COUNT-NOT-LESSP ADD-AXIOM1 (REWRITE)
  (NOT (LESSP (COUNT I) I)))

(DEFBOOT PACK ADD-SHELL0 NIL LITATOM ((UNPACK (NONE-OF) ZERO)))

(DEFBOOT CONS ADD-SHELL0 NIL LISTP ((CAR (NONE-OF) ZERO)
                                    (CDR (NONE-OF) ZERO)))

(DEFBOOT NLISTP DEFN0 (X)
  (NOT (LISTP X))
  NIL T T)

(DEFBOOT MINUS ADD-SHELL0 NIL NEGATIVEP
  ((NEGATIVE-GUTS (ONE-OF NUMBERP)
                  ZERO)))

(DEFBOOT DIFFERENCE DEFN0 (I J)
  (IF (ZEROP I)
      0
      (IF (ZEROP J)
          I
          (DIFFERENCE (SUB1 I) (SUB1 J))))
  NIL T T)

(DEFBOOT TIMES DEFN0 (I J)
  (IF (ZEROP I)
      0
      (PLUS J (TIMES (SUB1 I) J)))
  NIL T T)

(DEFBOOT QUOTIENT DEFN0 (I J)
  (IF (ZEROP J)
      0
      (IF (LESSP I J)
          0
          (ADD1 (QUOTIENT (DIFFERENCE I J) J))))
  NIL T T)

(DEFBOOT REMAINDER DEFN0 (I J)
  (IF (ZEROP J)
      (FIX I)
      (IF (LESSP I J)
          (FIX I)
          (REMAINDER (DIFFERENCE I J) J)))
  NIL T T)

(DEFBOOT MEMBER DEFN0 (X LST)                           
  (IF (NLISTP LST)
      F
      (IF (EQUAL X (CAR LST))
          T
          (MEMBER X (CDR LST))))
  NIL T NIL)

(DEFBOOT IFF DEFN0 (P Q)
  (IF P
      (IF Q (TRUE) (FALSE))
      (IF Q (FALSE) (TRUE)))
  NIL T NIL)

;   Now we do the NOT-NQTHM-MODE DEFBOOTS.  THM mode of NQTHM is not exactly
;   like the previously released theory.  The following functions exist in the
;   old theory and do not exist here:

;     FORM-LSTP
;     FORMP
;     ARITY
;     SYMBOLP
;     LEGAL-CHAR-CODE-SEQ
;     ILLEGAL-FIRST-CHAR-CODES
;     LEGAL-CHAR-CODES

;   I did not want to change what a meta lemma was, so I preserved NQTHM's
;   lenient treatment re non-terms and thus all the meta functions for
;   checking syntax have been eliminated.  I presume no user uses these
;   functions except to establish the old-style meta theorems, which is
;   now unnecessary.

;   In addition, THM mode is missing:

;     MEANING
;     MEANING-LST
;     APPLY

;   These have been replaced by EVAL$ (which takes a FLG argument to do
;   either the job of MEANING or of MEANING-LST) and APPLY$.  I claim
;   that the EVAL$ and APPLY$ that exist in THM mode are equal to the
;   MEANING (MEANING-LST) and APPLY in the release thm.

;   To achieve this partial reconstruction of the old released thm theory,
;   it is necessary to add certain defns that are not actually used in
;   the new theory, but which define commonly used functions in user
;   event lists, namely LENGTH, SUBSETP, and LAST.  In addition, we define
;   the two lexicographic relations LEX2 and LEX3 supported by THM.  To
;   define EVAL$ as in THM we also need to define LOOKUP, which in THM
;   differs from ASSOC in returning the CDR of the pair found, in not
;   looking at non-pairs on the alist, and in returning NIL at the end.


(DEFBOOT LEX2 NOT-NQTHM-MODE DEFN0 (L1 L2)
  (OR (LESSP (CAR L1) (CAR L2))
      (AND (EQUAL (CAR L1) (CAR L2))
           (LESSP (CADR L1) (CADR L2))))
  NIL T NIL)

(DEFBOOT LEX3 NOT-NQTHM-MODE DEFN0 (L1 L2)
  (OR (LESSP (CAR L1) (CAR L2))
      (AND (EQUAL (CAR L1) (CAR L2))
           (LEX2 (CDR L1) (CDR L2))))
  NIL T NIL)

(DEFBOOT LENGTH NOT-NQTHM-MODE DEFN0 (LST)
  (IF (LISTP LST)
      (ADD1 (LENGTH (CDR LST)))
      0)
  NIL T NIL)

(DEFBOOT SUBSETP NOT-NQTHM-MODE DEFN0 (X Y)
  (IF (NLISTP X)
      T
      (IF (MEMBER (CAR X) Y)
          (SUBSETP (CDR X) Y)
          F))
  NIL T NIL)

(DEFBOOT LAST NOT-NQTHM-MODE DEFN0 (L)
  (IF (LISTP L)
      (IF (LISTP (CDR L))
          (LAST (CDR L))
          L)
      L)
  NIL T NIL)

(DEFBOOT LOOKUP NOT-NQTHM-MODE DEFN0 (X ALIST)
  (IF (NLISTP ALIST)
      NIL
      (IF (AND (LISTP (CAR ALIST))
               (EQUAL X (CAAR ALIST)))
          (CDAR ALIST)
          (LOOKUP X (CDR ALIST))))
  NIL T NIL)

(DEFBOOT APPLY$ NOT-NQTHM-MODE DCL0 (FN ARGS) T)

(DEFBOOT EVAL$ NOT-NQTHM-MODE DEFN0 (FLG X A)
  (IF (EQUAL FLG (QUOTE LIST))
      (IF (NLISTP X)
          NIL
          (CONS (EVAL$ T (CAR X) A)
                (EVAL$ (QUOTE LIST) (CDR X) A)))
      (IF (LITATOM X)
          (LOOKUP X A)
          (IF (NLISTP X)
              X
              (IF (EQUAL (CAR X) (QUOTE QUOTE))
                  (CADR X)
                  (APPLY$ (CAR X)
                          (EVAL$ (QUOTE LIST) (CDR X) A))))))
  NIL T NIL)

;   Here are the NQTHM-MODE DEFBOOTS.


(DEFBOOT ORD-LESSP NQTHM-MODE DEFN0 (X Y)
  (IF (NOT (LISTP X))
      (IF (NOT (LISTP Y))
          (LESSP X Y)
          T)
      (IF (NOT (LISTP Y))
          F
          (IF (ORD-LESSP (CAR X) (CAR Y))
              T
              (AND (EQUAL (CAR X) (CAR Y))
                   (ORD-LESSP (CDR X) (CDR Y))))))
  NIL T NIL)

;  A proof of the well foundedness of ORD-LESSP may be found at
;  the end of this file.

(DEFBOOT ORDINALP NQTHM-MODE DEFN0 (X)
  (IF (LISTP X)
      (AND (ORDINALP (CAR X))
           (NOT (EQUAL (CAR X) 0))
           (ORDINALP (CDR X))
           (OR (NLISTP (CDR X))
               (NOT (ORD-LESSP (CAR X) (CADR X)))))
      (NUMBERP X))
  NIL T NIL)

;  See the notes near *1**APPLY-SUBR and *1**ASSOC for a warning regarding
;  the use of explictly provided LAMBDAs for LISP-CODE-FLG (as used below)
;  and an explanation of why we define some functions, such as *1*ASSOC,
;  in terms of "unnecessary" subroutines, such as *1**ASSOC.

(DEFBOOT ASSOC NQTHM-MODE DEFN0 (X L)
  (IF (NLISTP L)
      F
      (IF (EQUAL X (CAAR L))
          (CAR L)
          (ASSOC X (CDR L))))
  NIL T
  (LAMBDA (X L) (*1**ASSOC X L)))

(DEFBOOT PAIRLIST NQTHM-MODE DEFN0 (X Y)
  (IF (LISTP X)
      (CONS (CONS (CAR X) (CAR Y))
            (PAIRLIST (CDR X) (CDR Y)))
      NIL)
  NIL T NIL)

(DEFBOOT SUBRP NQTHM-MODE DCL0 (X)
  (LAMBDA (X) (*1**SUBRP X)))

(DEFBOOT SUBRP-BOOLEAN NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (OR (TRUEP (SUBRP X)) (FALSEP (SUBRP X))))

(DEFBOOT APPLY-SUBR NQTHM-MODE DCL0 (X LST)
  (LAMBDA (FN ARGS) (*1**APPLY-SUBR FN ARGS)))

(DEFBOOT FORMALS NQTHM-MODE DCL0 (FN)
  (LAMBDA (FN) (*1**FORMALS FN)))

(DEFBOOT BODY NQTHM-MODE DCL0 (FN)
  (LAMBDA (FN) (*1**BODY FN)))

(DEFBOOT FIX-COST NQTHM-MODE DEFN0 (X N)
  (IF X (CONS (CAR X) (PLUS N (CDR X))) F)
  NIL T NIL)

(DEFBOOT STRIP-CARS NQTHM-MODE DEFN0 (L)
  (IF (NLISTP L) NIL (CONS (CAAR L) (STRIP-CARS (CDR L))))
  NIL T NIL)

(DEFBOOT SUM-CDRS NQTHM-MODE DEFN0 (L)
  (IF (NLISTP L) 0 (PLUS (CDAR L) (SUM-CDRS (CDR L))))
  NIL T NIL)

(DEFBOOT V&C$ NQTHM-MODE DEFN0 (FLG X VA)

;  This DEFN0 has all of the normal effects of a DEFN0.  In particular,
;  we generate *1*V&C$ from the body below.  However, at SETUP-V&C$
;  below we smash the SDEFN to an equivalent one involving V&C-APPLY$
;  which makes the theorem proving easier but which is not suitable for
;  computation because it evals all the arguments of IFs.  Once we have
;  smashed the SDEFN, BODY would return the wrong answer were it not for
;  the special code in the definition of *1*BODY. 
  
;  If one attempts to determine the value of V&C$ on certain arguments
;  by rewriting in any of the standard ways, the rewriting process will
;  not terminate.  For example, consider (BODY 'LOOP) = '(LOOP).
;  It is possible to prove that (V&C$ T '(LOOP) NIL) = F, but rewriting
;  will not demonstrate that.  The phenomenon that "executing" our
;  *1*functions may not deliver the correct value by failing to terminate
;  is even more odd in the case of EVAL$.  In the case of V&C$, if
;  rewriting does not terminate, then the V&C$ value is F.  However,
;  there is more variety in the case of EVAL$.  For example, if
;  (V&C$ T '(ADD1 (LOOP)) NIL) = F, but (EVAL$ T '(ADD1 (LOOP)) NIL) =
;  (ADD1 (CAR F)) = (ADD1 0).

  (IF (EQUAL FLG (QUOTE LIST))
      (IF (NLISTP X)
          NIL
          (CONS (V&C$ T (CAR X) VA)
                (V&C$ (QUOTE LIST) (CDR X) VA)))
      (IF (LITATOM X) (CONS (CDR (ASSOC X VA)) 0)
          (IF (NLISTP X) (CONS X 0)
              (IF (EQUAL (CAR X) (QUOTE QUOTE)) (CONS (CADR X) 0)
                  (IF (EQUAL (CAR X) (QUOTE IF))
                      (IF (V&C$ T (CADR X) VA)
                          (FIX-COST (IF (CAR (V&C$ T (CADR X) VA))
                                        (V&C$ T (CADDR X) VA)
                                        (V&C$ T (CADDDR X) VA))
                                    (ADD1 (CDR (V&C$ T (CADR X) VA))))
                          F)
                      (IF (MEMBER F (V&C$ (QUOTE LIST) (CDR X) VA)) F
                          (IF (SUBRP (CAR X))
                              (CONS (APPLY-SUBR (CAR X)
                                                (STRIP-CARS
                                                 (V&C$ (QUOTE LIST)
                                                       (CDR X) VA)))
                                    (ADD1 (SUM-CDRS (V&C$ (QUOTE LIST)
                                                          (CDR X) VA))))
                              (FIX-COST (V&C$ T (BODY (CAR X))
                                              (PAIRLIST
                                               (FORMALS (CAR X))
                                               (STRIP-CARS
                                                (V&C$ (QUOTE LIST)
                                                      (CDR X)
                                                      VA))))
                                        (ADD1 (SUM-CDRS
                                               (V&C$ (QUOTE LIST)
                                                     (CDR X)
                                                     VA)))))))))))
  NIL T NIL)

(DEFBOOT V&C-APPLY$ NQTHM-MODE DEFN0 (FN ARGS)
  (IF (EQUAL FN (QUOTE IF))
      (IF (CAR ARGS)
          (FIX-COST (IF (CAAR ARGS) (CADR ARGS) (CADDR ARGS))
                    (ADD1 (CDAR ARGS)))
          F)
      (IF (MEMBER F ARGS)
          F
          (IF (SUBRP FN)
              (CONS (APPLY-SUBR FN (STRIP-CARS ARGS))
                    (ADD1 (SUM-CDRS ARGS)))
              (FIX-COST (V&C$ T (BODY FN) (PAIRLIST (FORMALS FN)
                                                    (STRIP-CARS ARGS)))
                        (ADD1 (SUM-CDRS ARGS))))))
  NIL T NIL)

;   Since both APPLY$ and EVAL$ are in THM mode and there we used handcoded
;   *1*fns, we must here too.

(DEFBOOT APPLY$ NQTHM-MODE DEFN0 (FN ARGS)    
  (CAR (V&C-APPLY$ FN (PAIRLIST ARGS 0)))
  NIL T T)

(DEFBOOT EVAL$ NQTHM-MODE DEFN0 (FLG X A)
  (IF (EQUAL FLG (QUOTE LIST))
      (IF (NLISTP X)
          NIL
          (CONS (EVAL$ T (CAR X) A)
                (EVAL$ (QUOTE LIST) (CDR X) A)))
      (IF (LITATOM X) (CDR (ASSOC X A))
          (IF (NLISTP X) X ;See comment in *1**EVAL$
              (IF (EQUAL (CAR X) (QUOTE QUOTE)) (CADR X)
                  (APPLY$ (CAR X) (EVAL$ (QUOTE LIST) (CDR X) A))))))
  NIL T
  (LAMBDA (FLG X VA)
    (COND ((EQ FLG (QUOTE LIST)) (*1**EVLIST$ X VA))
          (T (*1**EVAL$ X VA)))))

(DEFBOOT NIL NQTHM-MODE SETUP-V&C$)

(DEFBOOT NOT-LITATOM-SUBRP NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (NOT (LITATOM FN)) (EQUAL (SUBRP FN) F)))

(DEFBOOT NOT-LITATOM-FORMALS NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (NOT (LITATOM FN)) (EQUAL (FORMALS FN) F)))

(DEFBOOT NOT-LITATOM-BODY NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (NOT (LITATOM FN)) (EQUAL (BODY FN) F)))

(DEFBOOT SUBRP-FORMALS NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (SUBRP FN) (EQUAL (FORMALS FN) F)))

(DEFBOOT SUBRP-BODY NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (SUBRP FN) (EQUAL (BODY FN) F)))

(DEFBOOT NOT-SUBRP-APPLY-SUBR NQTHM-MODE ADD-AXIOM1 (REWRITE)
  (IMPLIES (NOT (SUBRP FN)) (EQUAL (APPLY-SUBR FN X) F)))

(DEFBOOT QUANTIFIER-INITIAL-VALUE NQTHM-MODE DEFN0 (FN)
  (CDR (ASSOC FN
              (QUOTE ((ADD-TO-SET . NIL)
                      (ALWAYS . *1*TRUE)
                      (APPEND . NIL)
                      (COLLECT . NIL)
                      (COUNT . 0)
                      (DO-RETURN . NIL)
                      (EXISTS . *1*FALSE)
                      (MAX . 0)
                      (SUM . 0)
                      (MULTIPLY . 1)
                      (UNION . NIL)))))
  NIL T NIL)

(DEFBOOT ADD-TO-SET NQTHM-MODE DEFN0 (X SET)
  (IF (MEMBER X SET)
      SET
      (CONS X SET))
  NIL T NIL)

(DEFBOOT APPEND NQTHM-MODE DEFN0 (X Y)
  (IF (LISTP X)
      (CONS (CAR X) (APPEND (CDR X) Y))
      Y)
  NIL T NIL)

(DEFBOOT MAX NQTHM-MODE DEFN0 (X Y)
  (IF (LESSP X Y) Y (FIX X))
  NIL T NIL)

(DEFBOOT NUMBERP-MAX NQTHM-MODE ADD-AXIOM1 (REWRITE) (NUMBERP (MAX X Y)))

(DEFBOOT UNION NQTHM-MODE DEFN0 (X Y)
  (IF (LISTP X)
      (IF (MEMBER (CAR X) Y)
          (UNION (CDR X) Y)
          (CONS (CAR X) (UNION (CDR X) Y))) Y)
  NIL T NIL)

(DEFBOOT QUANTIFIER-OPERATION NQTHM-MODE DEFN0 (FN ARG REST)
  (IF (EQUAL FN (QUOTE ADD-TO-SET))
      (ADD-TO-SET ARG REST)
      (IF (EQUAL FN (QUOTE ALWAYS))
          (AND ARG REST)
          (IF (EQUAL FN (QUOTE APPEND))
              (APPEND ARG REST)
              (IF (EQUAL FN (QUOTE COLLECT))
                  (CONS ARG REST)
                  (IF (EQUAL FN (QUOTE COUNT))
                      (IF ARG (ADD1 REST) REST)
                      (IF (EQUAL FN (QUOTE DO-RETURN))
                          ARG
                          (IF (EQUAL FN (QUOTE EXISTS))
                              (OR ARG REST)
                              (IF (EQUAL FN (QUOTE MAX))
                                  (MAX ARG REST)
                                  (IF (EQUAL FN (QUOTE SUM))
                                      (PLUS ARG REST)
                                      (IF (EQUAL FN (QUOTE MULTIPLY))
                                          (TIMES ARG REST)
                                          (IF (EQUAL FN
                                                     (QUOTE UNION))
                                              (UNION ARG REST)
                                              0)))))))))))
  NIL T NIL)

(DEFBOOT FOR NQTHM-MODE DEFN0 (VAR RANGE CONDITION OP BODY ALIST)
  (IF (NLISTP RANGE)
      (QUANTIFIER-INITIAL-VALUE OP)
      (IF (EVAL$ T CONDITION
                 (CONS (CONS VAR (CAR RANGE)) ALIST))
          (QUANTIFIER-OPERATION
           OP
           (EVAL$ T BODY
                  (CONS (CONS VAR (CAR RANGE)) ALIST))
           (FOR VAR (CDR RANGE) CONDITION OP BODY ALIST))
          (FOR VAR (CDR RANGE) CONDITION OP BODY ALIST)))
  NIL T NIL)

(DEFBOOT REWRITE-CAR-V&C-APPLY$  NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-APPLY$          NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-APPLY-SUBR      NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-V&C$            NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-V&C-APPLY$      NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-CAR-V&C$        NQTHM-MODE ADD-AXIOM1 NIL T)
(DEFBOOT REWRITE-EVAL$           NQTHM-MODE ADD-AXIOM1 NIL T)

(DEFBOOT IDENTITY DEFN0 (X) X NIL T NIL)

;                            STACK-INITIALIZATION

;  The LEMMA-STACK is circular, and we don't want it accidentally printed.
(PROGN (CREATE-LEMMA-STACK 10) (QUOTE LEMMA-STACK))

;  The LEMMA-STACK is circular, and we don't want it accidentally printed.
(PROGN (CREATE-LINEARIZE-ASSUMPTIONS-STACK 10) 
       (QUOTE LINEARIZE-ASSUMPTIONS-STACK))


;                         HASH TABLE INITIALIZATION

(DEFPARAMETER GLOBAL-DISABLEDP-HASH (MAKE-DISABLEDP-HASH))

(DEFPARAMETER GLOBAL-DISABLEDP-HASH-LIST T) 

; The above variable contains the DISABLED-LEMMAS list from which
; GLOBAL-DISABLEDP-HASH was constructed (if DISABLED-LEMMAS not eq
; GLOBAL-DISABLEDP-HASH-LIST, a new GLOBAL-DISABLEDP-HASH table needs
; to be constructed).  The significance of T is that it will force an
; initial hash table to be made, because T is not a list (so, any
; other non-NIL atom would do as well).

(DEFPARAMETER LOCAL-DISABLEDP-HASH (MAKE-DISABLEDP-HASH))

; See DISABLEP for a description of how these two hash tables are used.
; Warning:  the local table sometimes contains enabled names, not disabled
; names!

(DEFPARAMETER LOCAL-DISABLEDP-HASH-FLAG NIL)

; This variable must always be NIL at the top-level.  It is unwind-protected.


;                                   TRIVIA

;  As of February, 1984, this system contained about 15,500 lines of which
;  about 2000 were comments and 1700 were blank -- leaving about 12,000 lines
;  of "code".  There were about 550,000 characters in toto, which compiles
;  into about 400,000 bytes of compiled code in Maclisp for the 2060 but
;  only about 260,000 bytes in Zetalisp on a 3600.


;               Proof of ORD-LESSP's Well Foundedness

;  We first observe three facts about ord-lessp on ordinals that have been
;  proved by thm:
;  
;  (prove-lemma transitivity (rewrite)
;            (implies (and (ordinalp x)
;                          (ordinalp y)
;                          (ordinalp z)
;                          (ord-lessp x y)
;                          (ord-lessp y z))
;                     (ord-lessp x z)))
;  
;  
;  (prove-lemma non-circularity (rewrite)
;            (implies (and (ordinalp x)
;                          (ordinalp y)
;                          (ord-lessp x y))
;                     (not (ord-lessp y x))))
;                          
;  (prove-lemma trichotomy (rewrite)
;            (implies (and (ordinalp x)
;                          (ordinalp y))
;                     (or (equal x y)
;                         (ord-lessp x y)
;                         (ord-lessp y x))))
;  
;  These three properties establish that ord-lessp orders the ordinals.  To put
;  such a statement in the most standard mathematical nomenclature, we can
;  define the function:
;  
;  (defn ord-lesseqp (x y)
;    (or (equal x y) (ord-lessp x y)))
;  
;  and then establish that ord-lesseqp is a relation that is a simple,
;  complete, i.e., total order on ordinals by the following three
;  lemmas, which have been proved by thm:
;  
;  (prove-lemma antisymmetry nil
;            (implies (and (ordinalp x)
;                          (ordinalp y)
;                          (ord-lesseqp x y)
;                          (ord-lesseqp y x))
;                     (equal x y))
;            ((use (non-circularity))))
;  
;  (prove-lemma ord-lesseqp-transitivity nil
;            (implies (and (ordinalp x)
;                          (ordinalp y)
;                          (ordinalp z)
;                          (ord-lesseqp x y)
;                          (ord-lesseqp y z))
;                     (ord-lesseqp x z))
;            ((use (transitivity))))
;  
;  (prove-lemma trichotomy-of-ord-lessp nil
;            (implies (and (ordinalp x)
;                          (ordinalp y))
;                     (or (ord-lesseqp x y)
;                         (ord-lesseqp y x)))
;            ((use (trichotomy))))
;  
;  Crucially important to the proof of the well-foundedness of ord-lessp on
;  ordinals is the concept of ordinal-depth, abbreviated od:
;  
;  (defn od (l) (if (nlistp l) 0 (add1 (od (car l)))))
;  
;  If the od of an ordinal x is smaller than that of an ordinal y, then x is
;  ord-lessp y, as can be proved by thm:
;  
;  (prove-lemma od-implies-ordlessp (rewrite)
;    (implies (and (ordinalp x) (ordinalp y)
;                  (lessp (od x) (od y)))
;             (ord-lessp x y)))
;  
;  Remark.  A consequence of this lemma is the fact that if s = s(1), s(2), ...
;  is an infinite, ord-lessp descending sequence, then od(s(1)), od(s(2)), ...
;  is a "weakly" descending sequence of non-negative integers:  od(s(i)) is
;  greater than or equal to od(s(i+1)).
;  
;  Lemma Main.  For each non-negative integer N, ord-lessp well-orders the
;  set of ordinals with od less than or equal to N .
;  
;   Base Case.  N = 0.  The ordinals with 0 od are the non-negative integers.
;   On the non-negative integers, ord-lessp is the same as lessp.
;  
;   Induction Step.  N > 0.  We assume that ord-lessp well-orders the ordinals
;   with od less than N.
;  
;     If ord-lessp does not well-order the ordinals with od less than or equal
;     to N, we may let O be the ord-lessp-least ordinal which is the car of the
;     first member of an infinite, ord-lessp descending sequence of ordinals of
;     od less than or equal to N.  The od of O is N-1.
;  
;      Let K be the least integer > 0 such that for some infinite,
;      ord-lessp descending sequence s of ordinals with od less than
;      or equal to N, the first element of s begins with K occurrences
;      of O but not K+1 occurrences of O.
;
;        Having fixed O and K, let us let s = s(1), s(2), ... be an
;        infinite, ord-lessp descending sequence of ordinals with od
;        less than or equal to N such that O occurs exactly K times at
;        the beginning of s(1).
;  
;           O occurs exactly K times at the beinning of each s(i).
;           For suppose that s(j) is the first member of s with
;           exactly M occurrences of O at the beginning, M /= K.  If M
;           = 0, then the first member of s(j) must be ord-lessp O,
;           contradicting the minimality of O.  If 0 < M < K, then the
;           fact that the sequence beginning at s(j) is infinitely
;           descending contradicts the minimality of K.  If M > K,
;           then s(j) is greater than its predecessor, which has only
;           K occurrences of O at the beginning; but this contradicts
;           the fact that s is descending.
;             
;           Let t = t(1), t(2), ... be the sequence of ordinals that
;           is obtained by letting t(i) be the result of removing O
;           from the front of s(i) exactly K times.  t is infinitely
;           descending.  Furthermore, t(1) begins with an ordinal O' that
;           is ord-lessp O, and hence has od at most N-1 by the lemma
;           od-implies-ordlessp.  But this contradicts the minimality
;           of O. Q.E.D.
;  
;  
;  Theorem.  Ord-lessp well-orders the ordinals.  Proof.  Every infinite,
;  ord-lessp descending sequence of ordinals has the property that each member
;  has od less than or equal to the od, N, of the first member of the sequence.
;  This contradicts Lemma Main.

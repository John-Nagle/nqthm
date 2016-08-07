#| 

This file is in no way necessary for the correct operation of Nqthm-1992 but
merely serves as a convenience for the user wishing to automate the process of
running the more than one hundred Nqthm-1992 example files.

Unlike any of the other files distributed with Nqthm-1992, it is expected that
a user may well need to edit this file in order to indicate the directories
where Nqthm files are located.  In particular, the user may need to change the
three DEFPARAMETER forms below.

Nqthm-1992 works for a variety of Common Lisps and operating systems.  The
Nqthm-1992 code is Lisp implementation and operating system independent.
However, the organization of the more than one hundred Nqthm-1992 example files
into subdirectories has necessitated code for identifying subdirectories, which
code may introduce Lisp, operating system, and site specific information.  See
the file `driver.lisp' for further details.

The following three Lisp variable settings identify directory names and may
need to be different at different sites, especially at non-Unix sites.  The
particular settings below are relevant for a Unix process whose `connected'
directory is an `examples' directory that (1) contains the subdirectory `yu'
and that (2) has the Nqthm-1992 source directory as its superior.  On some
operating systems, such as the Macintosh native operating system, we recommend
that full, absolute pathnames be used below instead of Unix-style relative
pathnames.

|#

(SETQ *THM-SUPPRESS-DISCLAIMER-FLG* T)

(FORMAT *STANDARD-OUTPUT* "~%Loading dir.lisp.")

(IN-PACKAGE "USER")

; It is important that the strings end in the character that separates
; subdirectory components, e.g., / on Unix, > on Symbolics, and : on
; Macintosh.

(LET ((*PRINT-PRETTY* T)
      (FORM '(PROGN

; The examples subdirectory directory, for use in driver.lisp.

               (DEFPARAMETER *NQTHM-EXAMPLES-DIR* "./")

; The directory where defn-sk and the Nqthm-1992 sources are located, for use
; in driver-sk.lisp.

               (DEFPARAMETER *NQTHM-SOURCE-DIR*  "../")

; The directory where the defn-sk examples are, for use in driver-sk.lisp.

               (DEFPARAMETER *NQTHM-YU-DIR* "./yu/")

               (DEFPARAMETER *NQTHM-YOUNG-DIR* "./young/"))))
      
      (FORMAT *STANDARD-OUTPUT*
              "~%Evaluating this form: ~%")
      (PRINT FORM)
      (EVAL FORM))

(FORMAT *STANDARD-OUTPUT* "~%Finished loading dir.lisp.")

(FORCE-OUTPUT *STANDARD-OUTPUT*)

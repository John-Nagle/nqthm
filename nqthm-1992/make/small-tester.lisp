#|
Copyright (C) 1994 by Computational Logic, Inc.  All Rights Reserved.

Copying of this file is authorized to those who have read and agreed with the
terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE LICENSE" at the beginning of
the Nqthm file "basis.lisp".

|#

(SETQ *THM-SUPPRESS-DISCLAIMER-FLG* T)

(COND ((PROVE-FILE-OUT "proveall")
       (FORMAT *STANDARD-OUTPUT*
         "
=============================================================================
|                                                                           |
| It looks like the small test worked.                                      |
|                                                                           |
=============================================================================

        ")))

; Some Lisps quit when reading end of file, some don't.
#+CMU
(QUIT)
#+Allegro
(EXIT)



;;; -*-  Mode: Lisp; Package: USER; Syntax: Common-Lisp; Base: 10 -*- ;;;;

;  Copyright (C) 1989-1994 by Robert S. Boyer, J Strother Moore, and
;  Computational Logic, Inc. All Rights Reserved.

;  Copying of this file is authorized to those who have read and
;  agreed with the terms in the "Nqthm-1992 GENERAL PUBLIC SOFTWARE
;  LICENSE" at the beginning of the Nqthm file "basis.lisp".

;  NQTHM Version 1992

(IN-PACKAGE "USER")

(EVAL-WHEN (LOAD EVAL COMPILE)
           (CHK-BASE-AND-PACKAGE-1992 10 *PACKAGE*))

(DEFUN PPRIND (FMLA LEFTMARGIN RPARCNT PPRFILE)
  (PROG (MARG2 STARTLIST)
        (SETQ MARG2 (OUR-LINEL PPRFILE NIL))
        (COND ((ATOM FMLA) (IPRINC FMLA PPRFILE) (RETURN NIL)))
        (SETQ POS (COND ((SETQ TEMP-TEMP (ASSOC-EQ PPRFILE IPOSITION-ALIST))
                         (CDR TEMP-TEMP))
                        (T 0)))
        (SETQ SPACELEFT (- MARG2 LEFTMARGIN))
        (PPR1 FMLA (1+ RPARCNT))
        (SETQ NEXTNODE (CDAR STARTLIST))
        (SETQ NEXTIND (CAAR STARTLIST))
        (PPR2 FMLA LEFTMARGIN RPARCNT)
        (IPOSITION PPRFILE POS NIL)
        (RETURN NIL)))

(DEFUN PPRPACK NIL
  (CONS (COND ((< MINREM DLHDFMLA) (SETQ PPR-REMAINDER 0) (- (1+ MINREM)))
              (T (SETQ PPR-REMAINDER (- MINREM DLHDFMLA)) (1+ DLHDFMLA)))
        FMLA))

(DEFUN PPR1 (FMLA RPARCNT)
  (LET (DLHDFMLA RUNFLAT MINREM L RUNSTART RUNEND)
    (PROG NIL
          (COND
           ((ATOM FMLA)
            (SETQ PPR-FLATSIZE (+ RPARCNT
                                  (OUR-FLATC FMLA)))
            (SETQ PPR-REMAINDER (- SPACELEFT PPR-FLATSIZE))
            (RETURN NIL)))
          (COND
           ((ATOM (CAR FMLA))
            (COND ((AND (EQ (QUOTE QUOTE) (CAR FMLA))
                        (CONSP (CDR FMLA))
                        (NULL (CDDR FMLA)))
                   (PPR1 (CADR FMLA) RPARCNT)
                   (AND PPR-FLATSIZE (SETQ PPR-FLATSIZE (1+ PPR-FLATSIZE)))
                   (SETQ PPR-REMAINDER (1- PPR-REMAINDER))
                   (RETURN NIL)))
            (SETQ DLHDFMLA (1+ (OUR-FLATC (CAR FMLA))))
            (SETQ L FMLA))
           (T (SETQ DLHDFMLA 0)
              (SETQ L (RPLACD NILCONS FMLA))
              (GO OVER)))
          (COND
           ((NULL (CDR FMLA))
            (SETQ PPR-FLATSIZE (+ RPARCNT DLHDFMLA))
            (SETQ PPR-REMAINDER (- SPACELEFT PPR-FLATSIZE))
            (RETURN NIL)))
          OVER
          (SETQ RUNFLAT DLHDFMLA)
          (SETQ MINREM 1000)
          (SETQ SPACELEFT (1- SPACELEFT))
          LOOPFLAT
          (SETQ L (CDR L))
          (COND
           ((NULL L)
            (SETQ SPACELEFT (1+ SPACELEFT))
            (COND
             ((AND (NOT (> RUNFLAT SPACELEFT)) (NOT (> RUNFLAT FORCEIN)))
              (SETQ PPR-FLATSIZE RUNFLAT)
              (SETQ PPR-REMAINDER (- SPACELEFT RUNFLAT)))
             (T (SETQ STARTLIST (CONS (PPRPACK) NIL))
                (SETQ ENDLIST STARTLIST)
                (SETQ PPR-FLATSIZE NIL)))
            (RETURN NIL)))
          (COND
           ((ATOM L) (RPLACA (CDR DOTCONS) L) (SETQ L DOTCONS)))
          (COND
           ((ATOM (CAR L))
            (SETQ TEMP1 (OUR-FLATC (CAR L)))
            (SETQ RUNFLAT (+ TEMP1 (1+ RUNFLAT)))
            (SETQ TEMP1 (- SPACELEFT TEMP1))
            (COND ((NULL (CDR L))
                   (SETQ RUNFLAT (+ RPARCNT RUNFLAT))
                   (SETQ TEMP1 (- TEMP1 RPARCNT))))
            (COND
             ((< TEMP1 MINREM) (SETQ MINREM TEMP1)))
            (GO LOOPFLAT))
           (T (PPR1 (CAR L)
                    (COND
                     ((NULL (CDR L)) (1+ RPARCNT))
                     (T 1)))
              (COND
               ((< PPR-REMAINDER MINREM) (SETQ MINREM PPR-REMAINDER)))
              (COND
               (PPR-FLATSIZE (SETQ RUNFLAT (+ PPR-FLATSIZE (1+ RUNFLAT)))
                             (GO LOOPFLAT)))))
          (SETQ RUNSTART STARTLIST)
          (SETQ RUNEND ENDLIST)
          LOOPIND
          (SETQ L (CDR L))
          (COND
           ((NULL L)
            (SETQ STARTLIST (CONS (PPRPACK) RUNSTART))
            (SETQ ENDLIST RUNEND)
            (SETQ PPR-FLATSIZE NIL)
            (SETQ SPACELEFT (1+ SPACELEFT))
            (RETURN NIL)))
          (COND
           ((ATOM L) (RPLACA (CDR DOTCONS) L) (SETQ L DOTCONS)))
          (COND
           ((ATOM (CAR L))
            (SETQ TEMP1 (- SPACELEFT (OUR-FLATC (CAR L))))
            (COND ((NULL (CDR L)) (SETQ TEMP1 (- TEMP1 RPARCNT))))
            (COND ((< TEMP1 MINREM) (SETQ MINREM TEMP1)))
            (GO LOOPIND)))
          (PPR1 (CAR L) (COND ((NULL (CDR L)) (1+ RPARCNT)) (T 1)))
          (COND
           ((< PPR-REMAINDER MINREM) (SETQ MINREM PPR-REMAINDER)))
          (COND
           (PPR-FLATSIZE)
           (T (RPLACD RUNEND STARTLIST) (SETQ RUNEND ENDLIST)))
          (GO LOOPIND))))

(DEFUN PPR2 (FMLA MARG1 RPARCNT)
  (PROG (NONLFLAG TEMP)
        (COND
         ((ATOM FMLA) (PRIND FMLA PPRFILE) (RETURN NIL)))
        (COND ((AND (EQ (CAR FMLA) (QUOTE QUOTE))
                    (CONSP (CDR FMLA))
                    (NULL (CDDR FMLA)))
               (WRITE-CHAR1 #\' PPRFILE)
               (PPR2 (CADR FMLA) (1+ MARG1) RPARCNT)
               (RETURN NIL)))
        (COND
         ((EQ FMLA NEXTNODE)
          (SETQ MARG1 (+ MARG1 (ABS NEXTIND)))
          (SETQ NONLFLAG (> NEXTIND 0))
          (SETQ STARTLIST (CDR STARTLIST))
          (COND
           ((NULL STARTLIST))
           (T (SETQ NEXTNODE (CDAR STARTLIST))
              (SETQ NEXTIND (CAAR STARTLIST)))))
         (T (PPR22 FMLA)
            (RETURN NIL)))
        (WRITE-CHAR1 #\( PPRFILE)
        (COND
         ((ATOM (CAR FMLA))
          (PRIND (CAR FMLA) PPRFILE)
          (COND
           ((NULL (CDR FMLA))
            (WRITE-CHAR1 #\) PPRFILE)
            (RETURN NIL)))
          (COND
           ((AND (CONSP (CDR FMLA))
                 (OR (ATOM (SETQ TEMP (CADR FMLA)))
                     (AND (NOT (EQ (CADR FMLA) NEXTNODE))
                          (OR (ATOM TEMP)
                              (AND (EQ (CAR TEMP) (QUOTE QUOTE))
                                   (CONSP (CDR TEMP))
                                   (ATOM (CADR TEMP))
                                   (NULL (CDDR TEMP))))))
                 (< (+ POS (OUR-FLATC TEMP) RPARCNT)
                    MARG2))
            (WRITE-CHAR1 #\Space PPRFILE)
            (PPR2 (CADR FMLA) MARG1 RPARCNT)
            (SETQ FMLA (CDR FMLA))
            (GO LOOP1))
           (NONLFLAG (WRITE-CHAR1 #\Space PPRFILE))
           (T (TERPRISPACES MARG1 PPRFILE)))
          (SETQ FMLA (CDR FMLA))))
        LOOP(COND
             ((ATOM FMLA)
              (WRITE-CHAR1 #\. PPRFILE)
              (WRITE-CHAR1 #\Space PPRFILE)
              (PRIND FMLA PPRFILE)
              (WRITE-CHAR1 #\) PPRFILE)
              (RETURN NIL)))
        (PPR2 (CAR FMLA)
              MARG1
              (COND
               ((NULL (CDR FMLA)) (1+ RPARCNT))
               (T 1)))
        LOOP1
        (COND
         ((NULL (CDR FMLA))
          (WRITE-CHAR1 #\) PPRFILE)
          (RETURN NIL)))
        (COND
         ((AND (ATOM (CAR FMLA))
               (CONSP (CDR FMLA))
               (OR (ATOM (SETQ TEMP (CADR FMLA)))
                   (AND (NOT (EQ TEMP NEXTNODE))
                        (OR (ATOM TEMP)
                            (AND (EQ (CAR TEMP) (QUOTE QUOTE))
                                 (CONSP (CDR TEMP))
                                 (ATOM (CADR TEMP))
                                 (NULL (CDDR TEMP))))))
               (< (+ POS (OUR-FLATC TEMP) RPARCNT) MARG2))
          (WRITE-CHAR1 #\Space PPRFILE)
          (PPR2 (CADR FMLA) MARG2 RPARCNT)
          (SETQ FMLA (CDR FMLA))
          (GO LOOP1)))
        (TERPRISPACES MARG1 PPRFILE)
        (SETQ FMLA (CDR FMLA))
        (GO LOOP)))

(DEFUN PPR22 (X)
  (COND
   ((ATOM X) (PRIND X PPRFILE))
   (T (WRITE-CHAR1 #\( PPRFILE)
      (PROG NIL
            LOOP (COND
                  ((ATOM X)
                   (COND
                    ((NULL X) (WRITE-CHAR1 #\) PPRFILE))
                    (T (WRITE-CHAR1 #\. PPRFILE)
                       (WRITE-CHAR1 #\Space PPRFILE)
                       (PRIND X PPRFILE)
                       (WRITE-CHAR1 #\) PPRFILE)))
                   (RETURN NIL))
                  (T (PPR2 (CAR X) MARG2 0)
                     (SETQ X (CDR X))
                     (COND
                      ((NULL X))
                      (T (WRITE-CHAR1 #\Space PPRFILE)))
                     (GO LOOP)))))))

(DEFUN TERPRISPACES (N FILE)
  (TERPRI FILE)
  (ITERATE FOR I FROM 1 TO N
           DO (WRITE-CHAR #\Space FILE))
  (SETQ POS N))


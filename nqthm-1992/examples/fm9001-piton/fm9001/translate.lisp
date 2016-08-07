;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    TRANSLATE.LISP
;;;
;;;    A DUAL-EVAL HDL to LSI Logic NDL translator.
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "USER")

;;;
;;; The netlist arg to functions PRINT-NDL-FORM-TO-FILE and PRINT-NDL-FORM
;;; should look like (LISP-NETLIST <netlist>), where <netlist> is a well-formed
;;; netlist.  Recall that LISP-NETLIST changes (INDEX name num) names to
;;; 'name_num names. Make the netlist arg in r-loop by doing 
;;; 
;;;     (SETQ var (LISP-NETLIST <netlist>))
;;;
;;; Outside of r-loop, the netlist arg will be
;;;
;;;     (CDR (ASSOC 'var R-ALIST))
;;;
;;; 
;;; For example, to translate a the entire FM9001 netlist stored in Nqthm as
;;; (CHIP$NETLIST), do the following:
;;;
;;; > (r-loop)
;;; *(SETQ NETLIST (LISP-NETLIST (CHIP$NETLIST)))
;;; ... <r-loop prints the netlist> ..
;;; *OK
;;; > (PRINT-NDL-FORM-TO-FILE (CDR (ASSOC 'NETLIST R-ALIST)) "chip.ndl")
;;;
;;; The translated netlist will be written to "chip.ndl"
;;;
;;; This process defines certain modules that are assumed to be primitives of
;;; our netlist language.


;;;  PRINT-NDL-FORM-TO-FILE netlist file-name
;;;
;;;  This is the top-level call to the translator.  The NDL form of the NETLIST
;;;  will be written to file FILE-NAME.

(defun print-NDL-form-to-file (netlist file-name)
  (with-open-file (stream file-name :direction :output)
    (print-NDL-form netlist stream)))

(defconstant NDL-linelength 78)

(defun args-format (indent-column
                    &optional (extra-chars 1.)
                              (line-length NDL-linelength))
  (format nil "~~{~~<~~%~~~AT~~~A,~A:;~~A~~>~~^,~~}"
          indent-column extra-chars line-length))

;;;  PRINT-NDL-FORM (netlist &optional (stream *standard-output*))
;;;
;;;  Formats the netlist to a stream.

(defun print-NDL-form (netlist &optional (stream *standard-output*))
  (let ((m-ins-format (args-format 7))
        (m-outs-format (args-format 8)))
    (format stream "COMPILE;~%DIRECTORY MASTER;~%")
    (dolist (module netlist)
      (let ((m-name (car module))
            (m-ins  (cadr module))
            (m-outs (caddr module))
            (m-occs (cadddr module)))
        (format stream "~%MODULE ~A;~%INPUTS ~@?;~%OUTPUTS ~@?;~%~
                        LEVEL FUNCTION;~%DEFINE~%"
                m-name
                m-ins-format (NDL-name-list m-ins)
                m-outs-format (NDL-name-list m-outs))
        (dolist (occ m-occs)
          (multiple-value-bind (o-name o-outs o-fn o-ins)
            (NDL-occurrence occ)
            (let ((output (format nil
                                  "~A(~{~A~^,~}) = ~A(~{~A~^,~});"
                                  o-name o-outs o-fn o-ins)))
              (if (<= (length output) NDL-linelength)
                  (format stream "~A~%" output)
                (let ((o-name-length (length (princ-to-string o-name)))
                      (o-fn-length (length (princ-to-string o-fn))))
                  (format stream "~A(~@?)~%  = ~A(~@?);~%"
                          o-name
                          (args-format (1+ o-name-length)) o-outs
                          o-fn
                          (args-format (+ 5 o-fn-length) 2) o-ins))))))
        (format stream "END MODULE;~%")))
    (format stream "
MODULE RAM-ENABLE-CIRCUIT;
INPUTS CLK,TEST-REGFILE-,DISABLE-REGFILE-,WE;
OUTPUTS Z;
LEVEL FUNCTION;
DEFINE
G0(CLK-10) = DEL10(CLK);
G1(TEST-REGFILE) = IVA(TEST-REGFILE-);
G2(GATE-CLK) = OR2(CLK-10,TEST-REGFILE);
G3(Z) = ND3P(WE,DISABLE-REGFILE-,GATE-CLK);
END MODULE;

MODULE ID;
INPUTS A;
OUTPUTS Z;
LEVEL FUNCTION;
DEFINE
Z = (A);
END MODULE;

MODULE VDD;
OUTPUTS Z;
LEVEL FUNCTION;
DEFINE
G0(Z) = ID(NC/1/);
END MODULE;

MODULE VSS;
OUTPUTS Z;
LEVEL FUNCTION;
DEFINE
G0(Z) = ID(NC/0/);
END MODULE;

END COMPILE;
END;
")))
    
;;;  NDL-NAME x
;;;
;;;  NDL-NAME converts a name from a literal atom to a string, and substitutes
;;;  periods "." for underscores "_".

(defun NDL-name (x)
  (if (symbolp x)
      (substitute #\. #\_ (string x) :count 1 :from-end t)
      (progn (cerror "Return the argument."
                     "The argument ~A is not a symbol." x)
             x)))

(defun NDL-name-list (x)
  (if (consp x)
      (cons (NDL-name (car x))
            (NDL-name-list (cdr x)))
      x))

;;;  NDL-OCCURRENCE occ
;;;
;;;  Translates HDL occurrences to NDL, substituting NDL macrocell names for
;;;  HDL primitive names.

(defun NDL-occurrence (occ)
  (let* ((o-name (NDL-name (car occ)))
         (o-outs (NDL-name-list (cadr occ)))
         (o-fn (caddr  occ))
         (o-ins (NDL-name-list (cadddr occ)))
         (primp (assoc o-fn common-lisp-primp-database)))
    (if (consp primp)                   
        ;;  This is a primitive.  What these successive LET* forms are doing is
        ;;  checking for the case where the primitive macrocell has a
        ;;  different ordering on the inputs, in which case the generated
        ;;  macrocell call has to reorder the HDL inputs.  Also, LSI Logic pad
        ;;  macrocells are named "&<something>".  These are not legal Nqthm
        ;;  litatoms.  So, we add the "&" here.
        (let* ((lsi-entry (assoc 'lsi-name (cdr primp)))
               (lsi-value (if (consp lsi-entry) (cdr lsi-entry) o-fn))
               (o-fn2 (if (consp lsi-value) (car lsi-value) lsi-value))
               (o-ins2 (if (consp lsi-value)
                           (sublis (pairlis (cdr (assoc 'inputs (cdr primp)))
                                            o-ins)
                                   (cdr lsi-value))
                           o-ins))
               (o-fn3 (if (assoc 'pads (cdr primp))
                          (concatenate 'string "&" (string o-fn2))
                          o-fn2)))
          (values o-name o-outs o-fn3 o-ins2))
        (values o-name o-outs o-fn o-ins))))

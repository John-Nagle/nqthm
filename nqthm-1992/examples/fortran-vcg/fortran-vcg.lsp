; Record of changes from the Nqthm-1987 compatible version of the Fortran VCG
; code.

; 1.  Changed DEFRECORD to NQTHM-DEF-RECORD, for Nqthm-1992 compatibility.

; 2.  Change NOTE-LIB's arg to "fortran" from FORTRAN, for Nqthm-1992
; compatibility.

; 3.  Added greatly simplified DUMP functions from nqthm-1987 code to
;     end of this file, functions that were removed from Nqthm-1992.
;     We now dump all commands with PPR.  This not only looks nicer,
;     but it paves the way for possible use with the infix printers.
;     Furthermore, it would be a lot of trouble to try to make sure
;     that the Nqthm-1987 style dumper had been updated to handle
;     all events and hints correctly for 1992.

; 4.  Retargeted the undo in FORTRAN-NOTE-LIB, because of the movement
;     of INTEGER-SIZE in the file "fortran.events", from where it was
;     in the older xxxs.fortran.  (We moved INTEGER-SIZE only so that
;     we could show off CONSTRAIN.)

; 5.  Fixed error reporting in two places so that error messages from 
;     TRANSLATE that may occur while the VCG is running, under the
;     illusion we attempt to create of doing a PROVEALL, does not
;     crash in an ugly way but gives a reasonable error message.  This
;     bug in error reporting was exposed while tracking down the
;     problems that led to change 4, above.

; 6.  Flushed SCRIBE-FLG since few now use Scribe. Eliminating INDEXing
;     in DUMPING.  Something that could be done better with the
;     the infix printer anyway.

(EVAL-WHEN (LOAD EVAL COMPILE)
  
	   (DEF-NQTHM-RECORD COMMON-BLOCK (NAME VAR-DCLS) NIL)
  
	   (DEF-NQTHM-RECORD CONTEXT (TOKENS XXX COMMON-BLOCKS ROUTINES) NIL)
  
	   (DEF-NQTHM-RECORD FUNCTION (NAME TYPE ARGS BLOCK-NAMES KNOWN-BLOCK-NAMES VAR-DCLS 
				     CALLED-FNS STATEMENT-FUNCTION-PATTERNS INPUT-COND 
				     RESULT CLOCKS CODE) NIL)
  
	   (DEF-NQTHM-RECORD FUNCTION-PATTERN (NAME TYPE ARG-VAR-DCLS) NIL)
  
	   (DEF-NQTHM-RECORD STATEMENT-FUNCTION-PATTERN (NAME TYPE ARG-VAR-DCLS BODY) NIL)
  
	   (DEF-NQTHM-RECORD SUBROUTINE (NAME ARGS BLOCK-NAMES HIT-VARS KNOWN-BLOCK-NAMES VAR-DCLS 
				       CALLED-FNS STATEMENT-FUNCTION-PATTERNS INPUT-COND 
				       EFFECTS CLOCKS CODE) NIL)
  
	   (DEF-NQTHM-RECORD SUBROUTINE-PATTERN (NAME ARG-VAR-DCLS) NIL)
  
	   (DEF-NQTHM-RECORD VAR-DCL (NAME TYPE SIZES) NIL))

(DEFVAR ARRAY-PATTERNS)

(DEFVAR ASSERTION-LST)

(DEFVAR ASSERTION-NAME)

(DEFVAR BLOCK-NAMES)

(DEFVAR CALLED-FNS)

(DEFVAR CLOCKS)

(DEFPARAMETER COMMA-SPACE (QUOTE |, |))

(DEFVAR CONTEXT)

(DEFVAR CONTINUATION-LINE-CNT)

(DEFVAR EFFECTS)

(DEFVAR FORTRAN-ERROR-FLG)

(DEFVAR FORTRAN-CODE)

(DEFVAR FUNCTION-PATTERNS)

(DEFVAR FUNCTION-SPEC-ALIST)

(DEFVAR FUNCTION-TYPE)

(DEFVAR GLOBALS)

(DEFVAR HIT-VARS)

(DEFVAR INPUT-ASSERTION)

(DEFVAR INPUT-COND)

(DEFVAR INSTR-LST)

(DEFVAR INSTRS-SEEN)

(DEFPARAMETER INTEGER-SORT (QUOTE (INTEGER)))

(DEFVAR KNOWN-BLOCK-NAMES)

(DEFVAR KNOWN-DEFINED)

(DEFVAR KNOWN-VARS-ALIST)

(DEFVAR LABEL-VARIABLE-PATTERNS)

(DEFVAR LOCALS)

(DEFVAR ORIGINAL-CLOCKS)

(DEFVAR OUTPUT-ASSERTION)

(DEFPARAMETER PRINTING-A-COMMENT NIL)

(DEFVAR RESULT)

(DEFVAR ROUTINE-ARGS)

(DEFVAR ROUTINE-NAME)

(DEFVAR SKOLEM-CONSTANTS)

(DEFVAR STATE)

(DEFVAR STATEMENT-FUNCTION-PATTERNS)

(DEFVAR SUBROUTINE-FLG)

(DEFVAR SUBROUTINE-PATTERNS)

(DEFVAR SUBROUTINE-SPEC-ALIST)

(DEFVAR TO-BE-TRACED)

(DEFVAR TRACED)

(DEFVAR TRANS-EFFECTS)

(DEFVAR TRANS-INPUT-CLOCKS)

(DEFVAR TRANS-INPUT-COND)

(DEFVAR TRANS-INVARIANT-MAP)

(DEFVAR TRANS-RESULT)

(DEFVAR TRANSLATED-FORTRAN-CODE)

(DEFVAR UNSMASHED)

(DEFVAR VAR-DCLS)

(DEFVAR VARIABLE-PATTERNS)

(DEFVAR VCG-GEN-NAME-ALIST)

(DEFVAR VCG-PATH)

(DEFVAR VCS)

(DEFVAR XXX)

(DEFMACRO OUR-EXPLODEC (SYM)
	  `(LET ((S (SYMBOL-NAME ,SYM)))
		(ITERATE FOR I FROM 0 TO (1- (LENGTH S))
			 COLLECT (INTERN (STRING (CHAR S I)) 'USER))))

(DEFMACRO OUR-GETCHAR (X N)
	  `(INTERN (STRING (CHAR (SYMBOL-NAME ,X)
				 (1- ,N)))
		   'USER))

(DEFMACRO FORTRAN-COMMENT (NAME)
	  `(ADD-AXIOM ,NAME NIL T))

(DEFUN FORTRAN-ERROR (MSG CULPRIT)
       (SETQ FORTRAN-ERROR-FLG T)
       (IPRINC MSG NIL)
       (IPRINC (QUOTE |.|) NIL)
       (ITERPRI NIL)
       (IPRINC CULPRIT NIL)
       (ITERPRI NIL))

(DEFUN ADD-EVENT (COM NAME TERM)
       (OR (EQ COM (QUOTE UBT))
	   (EQ COM (QUOTE DEFN))
	   (SETQ NAME (VCG-GEN-NAME NAME)))
       (CASE COM
	     (FORTRAN-COMMENT (SETQ VCS (CONS (LIST (QUOTE FORTRAN-COMMENT)
						    NAME)
					      VCS)))
	     (ADD-AXIOM (SETQ VCS (CONS (LIST (QUOTE ADD-AXIOM)
					      NAME
					      (QUOTE (REWRITE))
					      (SKOLEMIZE-TERM TERM))
					VCS)))
	     (DEFN (SETQ VCS (CONS (LIST (QUOTE DEFN)
					 NAME NIL
					 (SKOLEMIZE-TERM TERM))
				   VCS)))
	     (PROVE-LEMMA
	      (COND
	       ((EQUAL TERM TRUE)
		NIL)
	       (T (SETQ VCS (CONS (CONS (QUOTE COMMENT)
					(REVERSE VCG-PATH))
				  (CONS (LIST (QUOTE PROVE-LEMMA)
					      NAME NIL
					      (SKOLEMIZE-TERM TERM))
					VCS))))))
	     (UBT (COND
		   ((OR (MEMBER-EQ (CAAR VCS)
				   (QUOTE (ADD-AXIOM FORTRAN-COMMENT)))
			(AND (EQ (CAAR VCS)
				 (QUOTE DEFN))
			     (NULL (CADDAR VCS))))

;   Skip over axioms, comments and defns of no args.		                                
		    (COND
		     ((EQ (CADR (CAR VCS))
			  NAME)
		      (SETQ VCS (CDR VCS)))
		     (T (SETQ VCS (CDR VCS))
			(ADD-EVENT (QUOTE UBT)
				   NAME NIL))))
		   ((EQ (CAAR VCS)
			(QUOTE UBT))
		    (SETQ VCS (CONS (LIST (QUOTE UBT)
					  NAME)
				    (CDR VCS))))
		   (T (SETQ VCS (CONS (LIST (QUOTE UBT)
					    NAME)
				      VCS)))))
	     (OTHERWISE (ERROR "SHOULDN'T")))
       NAME)

(DEFUN ADD-TO-CONTEXT (TOKENS XXX COMMON-BLOCKS ROUTINE CONTEXT)


;   Let us say that a FORTRAN triple consists of an XXX, a syntactically
;   correct context, and a specification of that context such that the context
;   is semantically correct with respect to the specification and the FORTRAN
;   theory that is produced by extending the basic FORTRAN theory with the XXX.
;   The XXX contains only DCLs, Definitions, ADD-SHELLS, ADD-AXIOMS and HINTs.
;   The latter are of the form (HINT name . xxx) and cause xxx to be spliced
;   into the final list of vcs.  xxx may not contain undoing or ADD-AXIOMs and
;   is used to permit the admission of DEFNs in the XXX.  If the last element
;   of XXX is a HINT it is laid down immediately before one starts the
;   consideration of paths.

;   ADD-TO-CONTEXT must be given a context that corresponds to a FORTRAN triple
;   and (b) some other junk. If ADD-TO-CONTEXT does not cause an error, it
;   returns a pair <VCS TRIP> such that if the VCS can be proved starting from
;   NOTE-LIBing FORTRAN-LIB, then TRIP will correspond to a FORTRAN triple,
;   which happily will be an extension of the input triple -- there will be one
;   more subroutine and the XXX will be an extension of the old, both taken
;   from the junk.  One piece of junk is a YYY. We check that YYY only contains
;   events suitable for inclusion in an XXX.  Another piece is a list of
;   parameters.



;   Before beginning to generate the VCS, O-CONTEXT NOTE-LIBs FORTRAN-LIB.  It
;   then processes the members of the XXX in the triple by DCLing DCLs and
;   Definitions, adding the ADD-SHELLS, and ignoring the axioms.  It then
;   processes the YYY by DCLing the DCLs and Definitions, adding the
;   ADD-SHELLS, and ignoring everthing else.


;   To assure that the 'real vcs ctually described in A Verification Condition
;   for FORTRAN can be proved in the alleged FORTRAN theory merely because the
;   VCS we produce can be proved from FORTRAN-LIB, we include in the VCS that
;   ADD-TO-CONTEXT produces many DCLs. These DCLs are placed after the new XXX
;   (the concatenation of the XXX in the input triple and the input XXX), and
;   thus assure that no axioms are added about certain function symbols by the
;   user. The functions DCLed are the parameters, START, BEGIN, NEXT, the names
;   of the variables, and the names of the functions called.



;   In the execution of ADD-TO-CONTEXT, we check that nput, output, clocks, and
;   invariants are formulas in the appropriate theory.  To this end, we
;   interleave the DCLing of various function symbols with TRANSLATE checks.
;   First, we DCL the parameters (after we have processed the XXX as above), we
;   DCL START and the globals and arguments.  We check input and output specs
;   and the clock.  Second, we DCL nonargument locals.  We check the invariants
;   and the loop clks.


       (LET ((PROVE-FILE (OPEN "VCG-TEMP" :DIRECTION :OUTPUT))
             (PROVEALL-FILENAME "VCG-TMP")
	     (PROVEALL-FLG T))
	    (PROG (NEW-CONTEXT NEW-TOKENS NEW-COMMON-BLOCKS OLD-TOKENS 
			       OLD-COMMON-BLOCKS OLD-ROUTINES OLD-XXX TEMP
			       ERROR1-IS-ERROR-FLG
			       VCS ARRAY-PATTERNS BLOCK-NAMES 
			       FUNCTION-PATTERNS LABEL-VARIABLE-PATTERNS 
			       STATEMENT-FUNCTION-PATTERNS 
			       SUBROUTINE-PATTERNS TRANSLATED-FORTRAN-CODE 
			       VARIABLE-PATTERNS)
		  (SETQ ERROR1-IS-ERROR-FLG T)
		  (SETQ FORTRAN-ERROR-FLG NIL)
		  (AND CONTEXT (MATCH! CONTEXT
				       (CONTEXT OLD-TOKENS OLD-XXX 
						OLD-COMMON-BLOCKS 
						OLD-ROUTINES)))
		  (ITERATE FOR P IN TOKENS
			   DO (OR (AND (NOT (ILLEGAL-NAME P))
				       (EQ (OUR-GETCHAR P (OUR-FLATC P))
					   (QUOTE &))
				       (NOT (= (OUR-FLATC P)
					       1))
				       (< (OUR-FLATC P)
					  8))
				  (FORTRAN-ERROR "Illegal token" P)))
		  (SETQ NEW-TOKENS (UNION-EQUAL TOKENS OLD-TOKENS))
		  (SETQ NEW-COMMON-BLOCKS
			(UNION-EQUAL COMMON-BLOCKS OLD-COMMON-BLOCKS))
		  (SETQ NEW-CONTEXT (MAKE CONTEXT NEW-TOKENS
					  (APPEND OLD-XXX XXX)
					  NEW-COMMON-BLOCKS OLD-ROUTINES))
		  (ITERATE FOR BLOCK IN COMMON-BLOCKS
			   UNLESS (MEMBER BLOCK OLD-COMMON-BLOCKS)
			   DO (CHK-BLOCK BLOCK NEW-TOKENS))
		  (COND
		   ((SETQ TEMP
			  (DUPLICATE-CADRS (APPEND NEW-COMMON-BLOCKS
						   (ITERATE FOR BLOCK
							    IN NEW-COMMON-BLOCKS
							    WITH ANS DO
							    (SETQ ANS (APPEND ANS
									      (ACCESS COMMON-BLOCK 
										      VAR-DCLS BLOCK)))
							    FINALLY (RETURN ANS))
						   (CONS (LIST 0 (CADR ROUTINE))
							 OLD-ROUTINES))))
		    (FORTRAN-ERROR "New block names-entries among routines" TEMP)))
		  (CHK-ROUTINE ROUTINE NEW-CONTEXT)
		  (SETQ TEMP (VCG ROUTINE NEW-CONTEXT))
		  (COND
		   (FORTRAN-ERROR-FLG (RETURN NIL))
		   (T (RETURN TEMP))))))

(DEFUN ADJUSTABLE-DIM (ARG)
       (AND (MEMBER-EQ ARG ROUTINE-ARGS)
	    (ITERATE FOR VDCL IN ARRAY-PATTERNS
		     THEREIS (MEMBER-EQ ARG (ACCESS VAR-DCL SIZES VDCL)))))

(DEFUN ADJUSTABLE-DIMS NIL
       (ITERATE FOR ARG IN ROUTINE-ARGS WHEN (ADJUSTABLE-DIM ARG) COLLECT ARG))

(DEFUN ALL-NAMES-POSSIBLY-SMASHED-THROUGH (INSTR)

;   Return the list of all long names possibly smashed through INSTR.

       (PROG (V SUB LST ST SUBR HIT-VARS-OF-SUBR)
	     (RETURN (COND
		      ((MATCH INSTR (ASSIGNMENT V &))
		       (LIST (LONG-NAME (REFERENCED-VARIABLE-OR-ARRAY
					 V))))
		      ((MATCH INSTR (ASSIGN-TO & V))
		       (LIST (LONG-NAME V)))
		      ((MATCH INSTR (CALL SUB LST))
		       (SETQ SUBR
			     (ASSOC-CADR SUB
					 (ACCESS CONTEXT ROUTINES CONTEXT)))
		       (SETQ HIT-VARS-OF-SUBR
			     (ACCESS SUBROUTINE HIT-VARS SUBR))
		       (UNION-EQUAL (ITERATE FOR NAME IN HIT-VARS-OF-SUBR
					     WHEN (COMMON-NAMEP NAME)
					     COLLECT NAME)
				    (ITERATE FOR ACTUAL IN LST AS FORMAL
					     IN (ACCESS SUBROUTINE ARGS SUBR)
					     WHEN (AND (MEMBER-EQ FORMAL HIT-VARS-OF-SUBR)
						       (OR (ASSOC-CADR ACTUAL 
								       VARIABLE-PATTERNS)
							   (ASSOC-CADR ACTUAL 
								       ARRAY-PATTERNS)))
					     COLLECT 

          
;  Officially, any local or common name in a hit var position is considered
;  possibly smashed.  But in a moment we will cause an error unless every such
;  actual is a variable or array name.  Thus, only such names are considered
;  possibly smashed by this CALL stmt. Should the user use something illegal in
;  a hit spot we will advise him later that only vars and arrays are permitted,
;  instead of advising him now to put it in the HIT-VARS of the new routine.


					     (LONG-NAME ACTUAL))))
		      ((MATCH INSTR (DO & V & & &))
		       (LIST (LONG-NAME V)))
		      ((MATCH INSTR (IF-LOGICAL & ST))
		       (ALL-NAMES-POSSIBLY-SMASHED-THROUGH ST))
		      (T NIL)))))

(DEFUN ALL-NAMES-USED-AS-SUBSCRIPTS (EXPR)
       (COND
	((ATOM EXPR)
	 NIL)
	((ASSOC-CADR (CAR EXPR)
		     ARRAY-PATTERNS)
	 (ITERATE FOR I IN (CDR EXPR) WITH ANS 
		  WHEN (AND (NOT (INTEGERP I))
			    (NOT (TOKENP I)))
		  DO (SETQ ANS (ADD-TO-SET I ANS))
		  FINALLY (RETURN ANS)))
	(T (ITERATE FOR ARG IN (CDR EXPR) WITH ANS
		    DO (SETQ ANS (UNION-EQUAL ANS (ALL-NAMES-USED-AS-SUBSCRIPTS
						   ARG)))
		    FINALLY (RETURN ANS)))))

(DEFUN ALL-NAMES-USED-ON-THE-SECOND-LEVEL (ST)
       (PROG (V EXP LST ST2)
	     (RETURN (COND
		      ((MATCH ST (ASSIGNMENT V EXP))
		       (UNION-EQUAL (ALL-NAMES-USED-AS-SUBSCRIPTS V)
				    (ALL-NAMES-USED-AS-SUBSCRIPTS EXP)))
		      ((MATCH ST (COMPUTED-GOTO & V))
		       (LIST V))
		      ((MATCH ST (IF-ARITHMETIC EXP & & &))
		       (ALL-NAMES-USED-AS-SUBSCRIPTS EXP))
		      ((MATCH ST (CALL & LST))
		       (ITERATE FOR ARG IN LST WITH ANS
				DO (SETQ ANS (UNION-EQUAL ANS
							  (ALL-NAMES-USED-AS-SUBSCRIPTS ARG)))
				FINALLY (RETURN ANS)))			    
		      ((MATCH ST (IF-LOGICAL EXP ST2))
		       (UNION-EQUAL (ALL-NAMES-USED-AS-SUBSCRIPTS EXP)
				    (ALL-NAMES-USED-ON-THE-SECOND-LEVEL ST2)))
		      (T NIL)))))

(DEFUN ASSOC-CADR (X LST)
       (ITERATE FOR Y IN LST WHEN (EQUAL X (CADR Y)) DO (RETURN Y)))

(DEFUN BUILT-IN-SPEC (X)
       (CASE
	X
	(TRUE (QUOTE (TRUE NIL NIL (QUOTE *1*TRUE)
			   (EQUAL ANS (QUOTE *1*TRUE)))))
	(FALSE (QUOTE (FALSE NIL NIL (QUOTE *1*TRUE)
			     (EQUAL ANS (QUOTE *1*FALSE)))))
	(ZPLUS (QUOTE (ZPLUS (I J)
			     NIL
			     (EXPRESSIBLE-ZNUMBERP (ZPLUS (I STATE)
							  (J STATE)))
			     (EQUAL ANS (ZPLUS (I STATE)
					       (J STATE))))))
	(RPLUS (QUOTE (RPLUS (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (RPLUS (I STATE)
					       (J STATE))))))
	(DPLUS (QUOTE (DPLUS (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DPLUS (I STATE)
					       (J STATE))))))
	(CPLUS (QUOTE (CPLUS (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (CPLUS (I STATE)
					       (J STATE))))))
	(ZDIFFERENCE (QUOTE (ZDIFFERENCE (I J)
					 NIL
					 (EXPRESSIBLE-ZNUMBERP
					  (ZDIFFERENCE (I STATE)
						       (J STATE)))
					 (EQUAL ANS
						(ZDIFFERENCE (I STATE)
							     (J STATE))))
			    ))
	(RDIFFERENCE (QUOTE (RDIFFERENCE (I J)
					 NIL
					 (QUOTE *1*FALSE)
					 (EQUAL ANS
						(RDIFFERENCE (I STATE)
							     (J STATE))))
			    ))
	(DDIFFERENCE (QUOTE (DDIFFERENCE (I J)
					 NIL
					 (QUOTE *1*FALSE)
					 (EQUAL ANS
						(DDIFFERENCE (I STATE)
							     (J STATE))))
			    ))
	(CDIFFERENCE (QUOTE (CDIFFERENCE (I J)
					 NIL
					 (QUOTE *1*FALSE)
					 (EQUAL ANS
						(CDIFFERENCE (I STATE)
							     (J STATE))))
			    ))
	(ZTIMES (QUOTE (ZTIMES (I J)
			       NIL
			       (EXPRESSIBLE-ZNUMBERP (ZTIMES (I STATE)
							     (J STATE)))
			       (EQUAL ANS (ZTIMES (I STATE)
						  (J STATE))))))
	(RTIMES (QUOTE (RTIMES (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (RTIMES (I STATE)
						  (J STATE))))))
	(DTIMES (QUOTE (DTIMES (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (DTIMES (I STATE)
						  (J STATE))))))
	(CTIMES (QUOTE (CTIMES (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (CTIMES (I STATE)
						  (J STATE))))))
	(ZQUOTIENT (QUOTE (ZQUOTIENT
			   (I J)
			   NIL
			   (AND (NOT (ZEQP (J STATE)
					   (QUOTE 0)))
				(EXPRESSIBLE-ZNUMBERP
				 (ZQUOTIENT (I STATE)
					    (J STATE))))
			   (EQUAL ANS (ZQUOTIENT (I STATE)
						 (J STATE))))))
	(RQUOTIENT (QUOTE (RQUOTIENT (I J)
				     NIL
				     (AND (QUOTE *1*FALSE)
					  (QUOTE (R--GATE (I STATE)
							  (J STATE))))
				     (EQUAL ANS (RQUOTIENT (I STATE)
							   (J STATE))))))
	(DQUOTIENT (QUOTE (DQUOTIENT (I J)
				     NIL
				     (AND (QUOTE *1*FALSE)
					  (QUOTE (D--GATE (I STATE)
							  (J STATE))))
				     (EQUAL ANS (DQUOTIENT (I STATE)
							   (J STATE))))))
	(CQUOTIENT (QUOTE (CQUOTIENT (I J)
				     NIL
				     (AND (QUOTE *1*FALSE)
					  (QUOTE (C--GATE (I STATE)
							  (J STATE))))
				     (EQUAL ANS (CQUOTIENT (I STATE)
							   (J STATE))))))
	(ZEXPTZ (QUOTE
		 (ZEXPTZ (I J)
			 NIL
			 (AND (NOT (AND (ZEQP (I STATE)
					      (QUOTE 0))
					(ZEQP (J STATE)
					      (QUOTE 0))))
			      (AND (ZLESSP (QUOTE -1)
					   (J STATE))
				   (EXPRESSIBLE-ZNUMBERP
				    (ZEXPTZ (I STATE)
					    (J STATE)))))
			 (EQUAL ANS (ZEXPTZ (I STATE)
					    (J STATE))))))
	(REXPTZ (QUOTE (REXPTZ (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (REXPTZ (I STATE)
						  (J STATE))))))
	(DEXPTZ (QUOTE (DEXPTZ (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (DEXPTZ (I STATE)
						  (J STATE))))))
	(CEXPTZ (QUOTE (CEXPTZ (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (CEXPTZ (I STATE)
						  (J STATE))))))
	(REXPTR (QUOTE (REXPTR (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (REXPTR (I STATE)
						  (J STATE))))))
	(REXPTD (QUOTE (REXPTD (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (REXPTD (I STATE)
						  (J STATE))))))
	(DEXPTR (QUOTE (DEXPTR (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (DEXPTR (I STATE)
						  (J STATE))))))
	(DEXPTD (QUOTE (DEXPTD (I J)
			       NIL
			       (AND (QUOTE *1*FALSE)
				    (QUOTE (-1 less than I and not 0 ^ 0)
					   ))
			       (EQUAL ANS (DEXPTD (I STATE)
						  (J STATE))))))
	(ZLESSP (QUOTE (ZLESSP (I J)
			       NIL
			       (QUOTE *1*TRUE)
			       (EQUAL ANS (ZLESSP (I STATE)
						  (J STATE))))))
	(RLESSP (QUOTE (RLESSP (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (RLESSP (I STATE)
						  (J STATE))))))
	(DLESSP (QUOTE (DLESSP (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (DLESSP (I STATE)
						  (J STATE))))))
	(ZLESSEQP (QUOTE (ZLESSEQP (I J)
				   NIL
				   (QUOTE *1*TRUE)
				   (EQUAL ANS (ZLESSEQP (I STATE)
							(J STATE))))))
	(RLESSEQP (QUOTE (RLESSEQP (I J)
				   NIL
				   (QUOTE *1*FALSE)
				   (EQUAL ANS (RLESSEQP (I STATE)
							(J STATE))))))
	(DLESSEQP (QUOTE (DLESSEQP (I J)
				   NIL
				   (QUOTE *1*FALSE)
				   (EQUAL ANS (DLESSEQP (I STATE)
							(J STATE))))))
	(ZEQP (QUOTE (ZEQP (I J)
			   NIL
			   (QUOTE *1*TRUE)
			   (EQUAL ANS (ZEQP (I STATE)
					    (J STATE))))))
	(REQP (QUOTE (REQP (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (REQP (I STATE)
					    (J STATE))))))
	(DEQP (QUOTE (DEQP (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DEQP (I STATE)
					    (J STATE))))))
	(CEQP (QUOTE (CEQP (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CEQP (I STATE)
					    (J STATE))))))
	(ZNEQP (QUOTE (ZNEQP (I J)
			     NIL
			     (QUOTE *1*TRUE)
			     (EQUAL ANS (ZNEQP (I STATE)
					       (J STATE))))))
	(RNEQP (QUOTE (RNEQP (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (RNEQP (I STATE)
					       (J STATE))))))
	(DNEQP (QUOTE (DNEQP (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DNEQP (I STATE)
					       (J STATE))))))
	(CNEQP (QUOTE (CNEQP (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (CNEQP (I STATE)
					       (J STATE))))))
	(ZGREATERP (QUOTE (ZGREATERP (I J)
				     NIL
				     (QUOTE *1*TRUE)
				     (EQUAL ANS (ZGREATERP (I STATE)
							   (J STATE))))))
	(RGREATERP (QUOTE (RGREATERP (I J)
				     NIL
				     (QUOTE *1*FALSE)
				     (EQUAL ANS (RGREATERP (I STATE)
							   (J STATE))))))
	(DGREATERP (QUOTE (DGREATERP (I J)
				     NIL
				     (QUOTE *1*FALSE)
				     (EQUAL ANS (DGREATERP (I STATE)
							   (J STATE))))))
	(ZGREATEREQP (QUOTE (ZGREATEREQP (I J)
					 NIL
					 (QUOTE *1*TRUE)
					 (EQUAL ANS
						(ZGREATEREQP (I STATE)
							     (J STATE))))
			    ))
	(RGREATEREQP (QUOTE (RGREATEREQP (I J)
					 NIL
					 (QUOTE *1*FALSE)
					 (EQUAL ANS
						(RGREATEREQP (I STATE)
							     (J STATE))))
			    ))
	(DGREATEREQP (QUOTE (DGREATEREQP (I J)
					 NIL
					 (QUOTE *1*FALSE)
					 (EQUAL ANS
						(DGREATEREQP (I STATE)
							     (J STATE))))
			    ))
	(NOT (QUOTE (NOT (I)
			 NIL
			 (QUOTE *1*TRUE)
			 (EQUAL ANS (NOT (I STATE))))))
	(AND (QUOTE (AND (I J)
			 NIL
			 (QUOTE *1*TRUE)
			 (EQUAL ANS (OR (I STATE)
					(J STATE))))))
	(OR (QUOTE (OR (I J)
		       NIL
		       (QUOTE *1*TRUE)
		       (EQUAL ANS (OR (I STATE)
				      (J STATE))))))
	(ABS (QUOTE (ABS (I)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (ABS (I STATE))))))
	(IABS (QUOTE (IABS (I)
			   NIL
			   (EXPRESSIBLE-ZNUMBERP (IABS (I STATE)))
			   (EQUAL ANS (IABS (I STATE))))))
	(DABS (QUOTE (DABS (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DABS (I STATE))))))
	(AINT (QUOTE (AINT (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (AINT (I STATE))))))
	(INT (QUOTE (INT (I)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (INT (I STATE))))))
	(IDINT (QUOTE (IDINT (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (IDINT (I STATE))))))
	(AMOD (QUOTE (AMOD (I J)
			   NIL
			   (AND (QUOTE *1*FALSE)
				(QUOTE (J not 0)))
			   (EQUAL ANS (AMOD (I STATE)
					    (J STATE))))))
	(MOD (QUOTE (MOD (I J)
			 NIL
			 (AND (NOT (ZEQP (J STATE)
					 (QUOTE 0)))
			      (EXPRESSIBLE-ZNUMBERP (MOD (I STATE)
							 (J STATE))))
			 (EQUAL ANS (MOD (I STATE)
					 (J STATE))))))
	(AMAX0 (QUOTE (AMAX0 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (AMAX0 (I STATE)
					       (J STATE))))))
	(AMAX1 (QUOTE (AMAX1 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (AMAX1 (I STATE)
					       (J STATE))))))
	(MAX0 (QUOTE (MAX0 (I J)
			   NIL
			   (QUOTE *1*TRUE)
			   (EQUAL ANS (MAX0 (I STATE)
					    (J STATE))))))
	(MAX1 (QUOTE (MAX1 (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (MAX1 (I STATE)
					    (J STATE))))))
	(DMAX1 (QUOTE (DMAX1 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DMAX1 (I STATE)
					       (J STATE))))))
	(AMIN0 (QUOTE (AMIN0 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (AMIN0 (I STATE)
					       (J STATE))))))
	(AMIN1 (QUOTE (AMIN1 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (AMIN1 (I STATE)
					       (J STATE))))))
	(MIN0 (QUOTE (MIN0 (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (MIN0 (I STATE)
					    (J STATE))))))
	(MIN1 (QUOTE (MIN1 (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (MIN1 (I STATE)
					    (J STATE))))))
	(DMIN1 (QUOTE (DMIN1 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DMIN1 (I STATE)
					       (J STATE))))))
	(FLOAT (QUOTE (FLOAT (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (FLOAT (I STATE))))))
	(IFIX (QUOTE (IFIX (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (IFIX (I STATE))))))
	(SIGN (QUOTE (SIGN (I J)
			   NIL
			   (AND (QUOTE *1*FALSE)
				(QUOTE (J not 0)))
			   (EQUAL ANS (SIGN (I STATE)
					    (J STATE))))))
	(ISIGN (QUOTE (ISIGN (I J)
			     NIL
			     (AND (NOT (ZEQP (J STATE)
					     (QUOTE 0)))
				  (EXPRESSIBLE-ZNUMBERP (ISIGN (I STATE)
							       (J STATE))
							))
			     (EQUAL ANS (ISIGN (I STATE)
					       (J STATE))))))
	(DSIGN (QUOTE (DSIGN (I J)
			     NIL
			     (AND (QUOTE *1*FALSE)
				  (QUOTE (J not 0)))
			     (EQUAL ANS (DSIGN (I STATE)
					       (J STATE))))))
	(DIM (QUOTE (DIM (I J)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (DIM (I STATE)
					 (J STATE))))))
	(IDIM (QUOTE (IDIM (I J)
			   NIL
			   (EXPRESSIBLE-ZNUMBERP (IDIM (I STATE)
						       (J STATE)))
			   (EQUAL ANS (IDIM (I STATE)
					    (J STATE))))))
	(SNGL (QUOTE (SNGL (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (SNGL (I STATE))))))
	(REAL (QUOTE (REAL (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (REAL (I STATE))))))
	(AIMAG (QUOTE (AIMAG (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (AIMAG (I STATE))))))
	(DBLE (QUOTE (DBLE (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DBLE (I STATE))))))
	(CMPLX (QUOTE (CMPLX (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (CMPLX (I STATE)
					       (J STATE))))))
	(CONJG (QUOTE (CONJG (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (CONJG (I STATE))))))
	(EXP (QUOTE (EXP (I)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (EXP (I STATE))))))
	(DEXP (QUOTE (DEXP (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DEXP (I STATE))))))
	(CEXP (QUOTE (CEXP (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CEXP (I STATE))))))
	(ALOG (QUOTE (ALOG (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (ALOG (I STATE))))))
	(DLOG (QUOTE (DLOG (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DLOG (I STATE))))))
	(CLOG (QUOTE (CLOG (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CLOG (I STATE))))))
	(ALOG10 (QUOTE (ALOG10 (I)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (ALOG10 (I STATE))))))
	(DLOG10 (QUOTE (DLOG10 (I)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (DLOG10 (I STATE))))))
	(SIN (QUOTE (SIN (I)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (SIN (I STATE))))))
	(DSIN (QUOTE (DSIN (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DSIN (I STATE))))))
	(CSIN (QUOTE (CSIN (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CSIN (I STATE))))))
	(COS (QUOTE (COS (I)
			 NIL
			 (QUOTE *1*FALSE)
			 (EQUAL ANS (COS (I STATE))))))
	(DCOS (QUOTE (DCOS (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DCOS (I STATE))))))
	(CCOS (QUOTE (CCOS (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CCOS (I STATE))))))
	(TANH (QUOTE (TANH (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (TANH (I STATE))))))
	(SQRT (QUOTE (SQRT (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (SQRT (I STATE))))))
	(DSQRT (QUOTE (DSQRT (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DSQRT (I STATE))))))
	(CSQRT (QUOTE (CSQRT (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (CSQRT (I STATE))))))
	(ATAN (QUOTE (ATAN (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (ATAN (I STATE))))))
	(DATAN (QUOTE (DATAN (I)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (DATAN (I STATE))))))
	(ATAN2 (QUOTE (ATAN2 (I J)
			     NIL
			     (QUOTE *1*FALSE)
			     (EQUAL ANS (ATAN2 (I STATE)
					       (J STATE))))))
	(DATAN2 (QUOTE (DATAN2 (I J)
			       NIL
			       (QUOTE *1*FALSE)
			       (EQUAL ANS (DATAN2 (I STATE)
						  (J STATE))))))
	(DMOD (QUOTE (DMOD (I J)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (DMOD (I STATE)
					    (J STATE))))))
	(CABS (QUOTE (CABS (I)
			   NIL
			   (QUOTE *1*FALSE)
			   (EQUAL ANS (CABS (I STATE))))))
	(OTHERWISE NIL)))

(DEFUN CHK-BLOCK (BLOCK LST)
       (PROG (NAME VDCLS)
	     (MATCH! BLOCK (COMMON-BLOCK NAME VDCLS))
	     (CHK-FORTRAN-NAME NAME)
	     (OR (> (LENGTH VDCLS)
		    0)
		 (FORTRAN-ERROR "Empty block" BLOCK))
	     (ITERATE FOR X IN VDCLS DO (CHK-VAR-DCL X LST))
	     (RETURN NIL)))

(DEFUN CHK-DEFINEDP (EXPR)
       (PROG (VDCL)
	     (RETURN
	      (COND
	       ((OR (VARIABLEP EXPR)
		    (FQUOTEP EXPR)
		    (MEMBER-EQ (FFN-SYMB EXPR)
			       KNOWN-DEFINED))
		NIL)
	       ((MEMBER-EQ (FFN-SYMB EXPR)
			   (QUOTE (ELT1 ELT2 ELT3)))
		(SETQ VDCL (ASSOC-CADR (SHORT-NAME
					(FFN-SYMB (FARGN EXPR 1)))
				       ARRAY-PATTERNS))
		(ADD-EVENT (QUOTE PROVE-LEMMA)
			   (QUOTE DEFINEDNESS)
			   (IMPLICATE
			    (CONJOIN TEST-LST NIL)
			    (FCONS-TERM* (FORTRAN-RECOGNIZER (ACCESS 
							      VAR-DCL 
							      TYPE 
							      VDCL))
					 EXPR))))
	       ((SETQ VDCL (ASSOC-CADR (SHORT-NAME (FFN-SYMB EXPR))
				       VARIABLE-PATTERNS))
		(ADD-EVENT (QUOTE PROVE-LEMMA)
			   (QUOTE DEFINEDNESS)
			   (IMPLICATE
			    (CONJOIN TEST-LST NIL)
			    (FCONS-TERM* (FORTRAN-RECOGNIZER (ACCESS 
							      VAR-DCL 
							      TYPE 
							      VDCL))
					 EXPR)))
		(SETQ KNOWN-DEFINED (CONS (FFN-SYMB EXPR)
					  KNOWN-DEFINED)))))))

(DEFUN CHK-DO-NESTING-AND-JUMPS NIL

;   Return the list of all long names possibly smashed through INSTR.  This
;   function checks that the DO's are ested, that each terminal statement is of
;   the correct kind, and the restrictions on jumping around in ranges are
;   obeyed.


       (PROG (LABEL-STACK CONTAINING-DOS LABEL RHS LHS)
	     (SETQ LABEL-STACK NIL)
	     (SETQ CONTAINING-DOS NIL)
	     (ITERATE FOR TAIL ON FORTRAN-CODE WITH INSTR AND INSTR2
		      DO (PROGN (SETQ INSTR (CAR TAIL)) 

;   CONTAINING-DOS is a stack of tails of FORTRAN.CODE. The first stmt of each
;   tail is a DO statement and each of the DO's in the stack contains the
;   current INSTR being processed.  LABEL-STACK is just the stack of terminal
;   labels for each DO in CONTAINING-DOS.


				(COND
				 ((ATOM INSTR)
				  (COND
				   ((MEMBER INSTR LABEL-STACK)
			   

;   Confirm that the last statement in the range of the DO meets our
;   restrictions.  We know, from the CHK-OK-LABEL check in
;   CHK-SYNTACTICALLY-OK-STATEMENTS, that there is a statement after this
;   label.


				    (SETQ INSTR2 (CADR TAIL))
				    (OR (MATCH INSTR2 (ASSIGNMENT & &))
					(MATCH INSTR2 (ASSIGN-TO & &))
					(MATCH INSTR2 (CONTINUE))
					(MATCH INSTR2 (IF-LOGICAL
						       &
						       (ASSIGNMENT & &)))
					(MATCH INSTR2 (IF-LOGICAL &
								  (ASSIGN-TO & &)))
					(MATCH INSTR2 (IF-LOGICAL & (CONTINUE)))
					(FORTRAN-ERROR "Illegal DO terminal stmt" INSTR2))
			   

;   Pop the label stack and containing DO's until the active DO terminates at a
;   label different from this one.


				    (ITERATE WHILE (AND (CONSP LABEL-STACK)
							(EQUAL INSTR (CAR LABEL-STACK)))
					     DO (SETQ LABEL-STACK (CDR LABEL-STACK))
					     (SETQ CONTAINING-DOS (CDR CONTAINING-DOS))
					     )

;   Now confirm that no other DO terminates here.

				    (OR (NOT (MEMBER INSTR LABEL-STACK))
					(FORTRAN-ERROR "Illegal DO nesting"
						       (LIST (LIST (QUOTE DO)
								   (CAR LABEL-STACK)
								   (QUOTE --))
							     (QUOTE vs)
							     (LIST (QUOTE DO)
								   INSTR
								   (QUOTE --))))))))
				 ((MATCH INSTR (DO LABEL & & & &))
				  (SETQ LABEL-STACK (CONS LABEL LABEL-STACK))
				  (SETQ CONTAINING-DOS (CONS TAIL CONTAINING-DOS)))
				 ((MATCH INSTR (GOTO LABEL))
				  (CHK-LEGAL-JUMP LABEL CONTAINING-DOS INSTR))
				 ((MATCH INSTR (IF-ARITHMETIC & & & &))
				  (ITERATE FOR LABEL IN (CDDR INSTR)
					   DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS INSTR)))
				 ((MATCH INSTR (ASSIGNED-GOTO & RHS))
				  (ITERATE FOR LABEL IN RHS
					   DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS INSTR)))
				 ((MATCH INSTR (COMPUTED-GOTO LHS &))
				  (ITERATE FOR LABEL IN LHS
					   DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS INSTR)))
				 ((MATCH INSTR (IF-LOGICAL & INSTR2))
				  (COND
				   ((MATCH INSTR2 (GOTO LABEL))
				    (CHK-LEGAL-JUMP LABEL CONTAINING-DOS INSTR))
				   ((MATCH INSTR2 (IF-ARITHMETIC & & & &))
				    (ITERATE FOR LABEL IN (CDDR INSTR2)
					     DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS 
								INSTR)))
				   ((MATCH INSTR2 (ASSIGNED-GOTO & RHS))
				    (ITERATE FOR LABEL IN RHS
					     DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS 
								INSTR)))
				   ((MATCH INSTR2 (COMPUTED-GOTO LHS &))
				    (ITERATE FOR LABEL IN LHS
					     DO (CHK-LEGAL-JUMP LABEL CONTAINING-DOS 
								INSTR))))))))
	     (OR (NULL LABEL-STACK)
		 (FORTRAN-ERROR 
		  "Illegal DO nesting.  Terminal DO statement not found."
		  LABEL-STACK))
	     (RETURN NIL)))

(DEFUN CHK-FORMULAS NIL

;   Now check that each of the formulas in the specification of ROUTINE is
;   indeed a formula in the right theory and that it incarcerates the right
;   things, using the theorem-prover's TRANSLATE routine to do the checking.


       (FORTRAN-NOTE-LIB)

;   In theory, a FORTRAN theory already has all tokens declared. So declare all
;   the ones used.  Note that no member of the XXX can refer to any of the
;   tokens. Add the axiom that each parameter is positive, just in case a
;   little bit of theorem-proving comes up.


       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR P
					IN (ACCESS CONTEXT TOKENS CONTEXT)
					COLLECT (LIST (QUOTE DCL)
						      P NIL)))
       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR P
					IN (ACCESS CONTEXT TOKENS CONTEXT)
					COLLECT
					(LIST (QUOTE ADD-AXIOM)
					      (PACK (LIST P (QUOTE -POSITIVE)))
					      (QUOTE (REWRITE))
					      (FCONS-TERM* (QUOTE LESSP)
							   0
							   (FCONS-TERM* P)))))
       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR P
					IN (QUOTE (PATH-HYPS GLOBAL-HYPS))
					COLLECT (LIST (QUOTE DCL)
						      P NIL)))
       (VCG-REDO-UNDONE-EVENTS
	(ITERATE FOR P IN (QUOTE (PATH-HYPS GLOBAL-HYPS))
		 COLLECT (LIST (QUOTE ADD-AXIOM)
			       (PACK (LIST P (QUOTE -BOOLEAN)))
			       (QUOTE (REWRITE))
			       (FCONS-TERM* (QUOTE OR)
					    (FCONS-TERM* (QUOTE TRUEP)
							 (FCONS-TERM* P))
					    (FCONS-TERM* (QUOTE FALSEP)
							 (FCONS-TERM* P))))))
       (ITERATE FOR EV IN XXX
		DO (OR (AND (CONSP EV)
			    (PLISTP EV)
			    (MEMBER-EQ (CAR EV)
				       (QUOTE (ADD-AXIOM DCL DEFN FORTRAN-COMMENT ADD-SHELL))))
		       (AND (CONSP EV)
			    (EQ (CAR EV)
				(QUOTE HINT))
			    (SYMBOLP (CADR EV))
			    (ITERATE FOR X IN (CDDR EV)
				     ALWAYS (MEMBER-EQ (CAR X)
						       (QUOTE (DEFN DCL ADD-SHELL TOGGLE 
								    DISABLE ENABLE 
								    PROVE-LEMMA FORTRAN-COMMENT))))
			    )
		       (FORTRAN-ERROR "Illegal event" EV)))

;   To avoid the work involved in proving that functions terminate, merely DCL
;   defined function symbols. Ignore axioms.


       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR EV IN XXX
					UNLESS (MEMBER-EQ (CAR EV)
							  (QUOTE (ADD-AXIOM HINT)))
					COLLECT (COND
						 ((EQ (CAR EV)
						      (QUOTE DEFN))
						  (LIST (QUOTE DCL)
							(CADR EV)
							(CADDR EV)))
						 (T EV))))
       (VCG-REDO-UNDONE-EVENTS (QUOTE ((DCL START NIL))))
       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR ARG IN ROUTINE-ARGS
					COLLECT (LIST (QUOTE DCL)
						      ARG
						      (QUOTE (STATE)))))
       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR G IN GLOBALS
					COLLECT (LIST (QUOTE DCL)
						      G
						      (QUOTE (STATE)))))

;   The theorem-prover is now in the primary extension.

       (SETQ TRANS-INPUT-COND (CHK-TRANSLATE INPUT-COND))
       (OR (INCARCERATES TRANS-INPUT-COND (QUOTE (STATE))
			 (APPEND ROUTINE-ARGS GLOBALS))
	   (FORTRAN-ERROR "Incarceration error" TRANS-INPUT-COND))
       (COND
	(SUBROUTINE-FLG (SETQ TRANS-EFFECTS (CHK-TRANSLATE EFFECTS))
			(OR (INCARCERATES TRANS-EFFECTS
					  (QUOTE (STATE NEWSTATE))
					  (APPEND ROUTINE-ARGS GLOBALS))
			    (FORTRAN-ERROR "Incarceration error." TRANS-EFFECTS))
			(OR (ITERATE FOR X IN (SUBTERMS-THAT-USE
					       (QUOTE (NEWSTATE))
					       TRANS-EFFECTS)
				     ALWAYS (MEMBER-EQ (FFN-SYMB X)
						       HIT-VARS))
			    (FORTRAN-ERROR "Incarceration error." TRANS-EFFECTS))
			)
	(T (SETQ TRANS-RESULT (CHK-TRANSLATE RESULT))
	   (OR (SUBSETP-EQ (ALL-VARS TRANS-RESULT)
			   (QUOTE (STATE ANS)))
	       (FORTRAN-ERROR "Illegal var in result" TRANS-RESULT))
	   (OR (INCARCERATES TRANS-RESULT (QUOTE (STATE))
			     (APPEND ROUTINE-ARGS GLOBALS))
	       (FORTRAN-ERROR "Incarceration error" TRANS-RESULT))))
       (SETQ TRANS-INPUT-CLOCKS (CHK-TRANSLATE (CONS (QUOTE LIST)
						     CLOCKS)))
       (OR (INCARCERATES TRANS-INPUT-CLOCKS (QUOTE ((START)))
			 (APPEND ROUTINE-ARGS GLOBALS))
	   (FORTRAN-ERROR "Incarceration error" TRANS-INPUT-CLOCKS))
       (OR (NULL (ALL-VARS TRANS-INPUT-CLOCKS))
	   (FORTRAN-ERROR "Illegal var in clock" TRANS-INPUT-CLOCKS))
       (VCG-REDO-UNDONE-EVENTS (ITERATE FOR V IN LOCALS
					UNLESS (MEMBER-EQ V ROUTINE-ARGS)
					COLLECT (LIST (QUOTE DCL)
						      V
						      (QUOTE (STATE)))))
;   We are now in the secondary extension.

       (ITERATE FOR INSTR IN TRANSLATED-FORTRAN-CODE WITH XXX
		WHEN (MATCH INSTR (CONS (QUOTE COMMENT)
					(CONS (QUOTE XXX)
					      (CONS & (CONS & XXX)))))
		DO (ITERATE FOR X IN XXX
			    DO (OR (AND (CONSP X)
					(MEMBER-EQ (CAR X)
						   (QUOTE (PROVE-LEMMA DEFN TOGGLE ENABLE 
								       DISABLE))))
				   (FORTRAN-ERROR "Illegal XXX member" X))))
       (OR (AND (NOT (MATCH (CAR TRANSLATED-FORTRAN-CODE)
			    (COMMENT (QUOTE ASSERTION)
				     & & &)))
		(ITERATE FOR TAIL ON TRANSLATED-FORTRAN-CODE
			 ALWAYS (COND
				 ((AND (CONSP (CDR TAIL))
				       (MATCH (CADR TAIL)
					      (COMMENT (QUOTE ASSERTION)
						       & & &)))
				  (EQUAL (CAAR TAIL)
					 (QUOTE CONTINUE)))
				 (T T))))
	   (FORTRAN-ERROR "Invariants must follow CONTINUEs" NIL))

;   As we check each invariant and its clock, we set up an alist for use in
;   vcg.


       (SETQ TRANS-INVARIANT-MAP NIL)
       (ITERATE FOR INSTR IN TRANSLATED-FORTRAN-CODE
		WITH ASSN-NAME AND ASSN AND CLKS AND TRANS-INVRNT AND TRANS-CLKS
		WHEN (MATCH INSTR (COMMENT (QUOTE ASSERTION)
					   ASSN-NAME ASSN CLKS))
		DO (PROGN (OR (SYMBOLP ASSN-NAME)
			      (FORTRAN-ERROR "Illegal assertion name" ASSN-NAME))
			  (SETQ TRANS-INVRNT (CHK-TRANSLATE ASSN))
			  (OR (INCARCERATES TRANS-INVRNT (QUOTE (STATE (START)))
					    (APPEND LOCALS GLOBALS))
			      (FORTRAN-ERROR "Incarceration error" TRANS-INVRNT))
			  (OR (EQUAL (LENGTH CLKS) (LENGTH CLOCKS))
			      (FORTRAN-ERROR "Wrong length clock" CLOCKS))
			  (SETQ TRANS-CLKS (CHK-TRANSLATE (CONS (QUOTE LIST)
								CLKS)))
			  (OR (INCARCERATES TRANS-CLKS (QUOTE (STATE (START)))
					    (APPEND LOCALS GLOBALS))
			      (FORTRAN-ERROR "Incarceration error" TRANS-CLKS))
			  (OR (SUBSETP-EQ (ALL-VARS TRANS-CLKS)
					  (QUOTE (STATE)))
			      (FORTRAN-ERROR "Illegal var" TRANS-CLKS))
			  (OR (NOT (ASSOC-EQ ASSN-NAME TRANS-INVARIANT-MAP))
			      (FORTRAN-ERROR "Two invariants with same name" ASSN-NAME))
			  (SETQ TRANS-INVARIANT-MAP
				(CONS (LIST ASSN-NAME TRANS-INVRNT TRANS-CLKS)
				      TRANS-INVARIANT-MAP))))
       (VCG-REDO-UNDONE-EVENTS (QUOTE ((DCL BEGIN NIL)
				       (DCL NEXT (STATE))))))

(DEFUN CHK-FORTRAN-NAME (X)
       (PROG (TEMP)
	     (OR (AND (SYMBOLP X)
		      (< (LENGTH (SETQ TEMP (OUR-EXPLODEC X)))
			 7)
		      TEMP
		      (>= (OUR-GETCHARN (CAR TEMP) 1)
			  65)
		      (< (OUR-GETCHARN (CAR TEMP) 1)
			 91)
		      (SUBSETP-EQ TEMP
				  (QUOTE (A B C D E F G H I J K L M N O P Q R 
					    S T U V W X Y Z |0| |1| |2| |3| |4| |5| |6|
					    |7| |8| |9|))))
		 (FORTRAN-ERROR "Illegal FORTRAN name" X))
	     (RETURN NIL)))

(DEFUN CHK-FORTRAN-SUBSCRIPT (X EXPR)
       (OR (AND (INTEGERP X)
		(< 0 X))
	   (TOKENP X)
	   (AND (SETQ TEMP-TEMP (ASSOC-CADR X VARIABLE-PATTERNS))
		(EQ (QUOTE INTEGER)
		    (ACCESS VAR-DCL TYPE TEMP-TEMP)))
	   (FORTRAN-ERROR "Illegal subscript" (LIST (QUOTE sub)
						    X
						    (QUOTE expr)
						    EXPR))))

(DEFUN CHK-FORTRAN-TYPE (X)
       (OR (MEMBER-EQ X (QUOTE (INTEGER REAL DOUBLE COMPLEX LOGICAL)))
	   (FORTRAN-ERROR "Illegal FORTRAN type" X)))

(DEFUN CHK-INTRINSIC-USAGE NIL

;   Check that the name of each intrinsic member of the function patterns is
;   called.


       (ITERATE FOR X IN FUNCTION-PATTERNS WITH FN
		WHEN (INTRINSIC-FUNCTIONP X)
		DO (PROGN (SETQ FN (ACCESS FUNCTION-PATTERN NAME X)) 

;   Now consider the statements in the prettyprinted version of the routine and
;   look for a reference to FN. The statements appear in the following order:
;   FUNCTION or SUBROUTINE, type, DIMENSION, COMMON, EXTERNAL, statement
;   functions, and executable code.  The only place we may find a call is in
;   the statement functions or executable code.


			  (OR (ITERATE FOR PAT IN STATEMENT-FUNCTION-PATTERNS
				       THEREIS (REFERENCED-AS-A-FUNCTION
						FN
						(ACCESS 
						 STATEMENT-FUNCTION-PATTERN 
						 BODY PAT)))
			      (ITERATE FOR INSTR IN FORTRAN-CODE
				       THEREIS (REFERENCED-AS-A-FUNCTION-IN-STMT FN INSTR))
			      (FORTRAN-ERROR "Intrinsic fn not referenced" FN)))))

(DEFUN CHK-KNOWN-BLOCK-NAMES NIL

;   KNOWN-BLOCK-NAMES should contain the prefix of every global name of the
;   routine.  The global names are the long names of every var in every common
;   block of the routine plus the global names of each nonintrinsic function
;   pattern and subroutine pattern. So the KNOWN-BLOCK-NAMES should be a
;   permutation of the BLOCK-NAMES of the routine unioned with the
;   KNOWN-BLOCK-NAMES of every nonintrinsic FUNCTION-PATTERN and every
;   SUBROUTINE-PATTERN.


       (PROG (KNOWN-BLOCK-NAMES-OF-SUBPROGRAMS)
	     (SETQ KNOWN-BLOCK-NAMES-OF-SUBPROGRAMS
		   (ITERATE FOR X IN (ACCESS CONTEXT ROUTINES CONTEXT) WITH ANS
			    WHEN (OR (ASSOC-CADR (CADR X)
						 SUBROUTINE-PATTERNS)
				     (ASSOC-CADR (CADR X)
						 FUNCTION-PATTERNS))
			    DO (SETQ ANS
				     (UNION-EQUAL ANS
						  (COND
						   ((EQ (CAR X)
							(QUOTE SUBROUTINE))
						    (ACCESS
						     SUBROUTINE KNOWN-BLOCK-NAMES X))
						   (T (ACCESS
						       FUNCTION KNOWN-BLOCK-NAMES X)))))
			    FINALLY (RETURN ANS)))
	     (OR (PERM KNOWN-BLOCK-NAMES
		       (UNION-EQUAL BLOCK-NAMES
				    KNOWN-BLOCK-NAMES-OF-SUBPROGRAMS))
		 (FORTRAN-ERROR "KNOWN-BLOCK-NAMES should be a permutation of"
				(UNION-EQUAL BLOCK-NAMES 
					     KNOWN-BLOCK-NAMES-OF-SUBPROGRAMS)))
	     (RETURN NIL)))

(DEFUN CHK-LABEL (X INSTR)
       (OR (AND (INTEGERP X)
		(MEMBER-EQUAL X FORTRAN-CODE))
	   (FORTRAN-ERROR "Nonlabel used as label" (LIST (QUOTE nonlabel)
							 X
							 (QUOTE instr)
							 INSTR))))

(DEFUN CHK-LEGAL-JUMP (LABEL CONTAINING-DOS INSTR)
       (PROG (TAIL L)
	     (SETQ TAIL FORTRAN-CODE)
	     LOOP(COND
		  ((ATOM TAIL)
		   (FORTRAN-ERROR "Illegal jump into DO" INSTR)
		   (RETURN NIL))
		  ((EQUAL LABEL (CAR TAIL))
		   (RETURN T))
		  ((AND (MATCH (CAR TAIL)
			       (DO L & & & &))
			(NOT (MEMBER-EQ TAIL CONTAINING-DOS)))
		   (SETQ TAIL (CDDR (MEMBER-EQUAL L TAIL))))
		  (T (SETQ TAIL (CDR TAIL))))
	     (GO LOOP)))

(DEFUN CHK-NO-ALIASING (INSTR)

;   INSTR is assumed to be a CALL.  Check that it exhibits neither form of
;   aliasing.  We check four things. Every possibly smashed formal is occupied
;   by a var or array reference.  No such formal is occupied by a reference to
;   a known common var of the called routine.  No such formal is occupied by an
;   actual also passed in another formal slot. No common name of the caller
;   that is possibly smashed by the called routine is passed in any formal.


       (PROG (SUBR HIT-VARS-OF-SUBR SUB LST)
	     (MATCH! INSTR (CALL SUB LST))
	     (COND
	      ((EQ SUB (QUOTE UNDEFINER))
	       (RETURN NIL)))
	     (SETQ SUBR (ASSOC-CADR SUB (ACCESS CONTEXT ROUTINES CONTEXT)))
	     (SETQ HIT-VARS-OF-SUBR (ACCESS SUBROUTINE HIT-VARS SUBR))
	     (ITERATE FOR ACTUAL IN LST AS FORMAL IN (ACCESS SUBROUTINE ARGS SUBR)
		      WHEN (MEMBER-EQ FORMAL HIT-VARS-OF-SUBR)
		      DO (PROGN (OR (ASSOC-CADR ACTUAL VARIABLE-PATTERNS)
				    (ASSOC-CADR ACTUAL ARRAY-PATTERNS)
				    (FORTRAN-ERROR
				     "Smashed actual must be variable or array"
				     (LIST (QUOTE actual)
					   ACTUAL
					   (QUOTE instr)
					   INSTR)))
				(OR (NOT (COMMON-NAMEP (LONG-NAME ACTUAL)))
				    (NOT (MEMBER-EQ (COMMON-BLOCK-CONTAINING ACTUAL)
						    (ACCESS
						     SUBROUTINE KNOWN-BLOCK-NAMES SUBR)))
				    (FORTRAN-ERROR 
				     "Known COMMON name passed as smashed actual"
				     (LIST (QUOTE actual)
					   ACTUAL
					   (QUOTE instr)
					   INSTR)))
				(ITERATE FOR ACTUAL2 IN LST AS FORMAL2
					 IN (ACCESS SUBROUTINE ARGS SUBR)
					 WHEN (NOT (EQ FORMAL2 FORMAL))
					 DO 

;   we here check that no other actual is ACTUAL or an array element ref to
;   ACTUAL.


					 (COND
					  ((AND (VARIABLE-ARRAY-OR-ELEMENT-REFERENCE
						 ACTUAL2)
						(EQ (REFERENCED-VARIABLE-OR-ARRAY ACTUAL2)
						    ACTUAL))
					   (FORTRAN-ERROR "Smashed actual passed twice"
							  (LIST (QUOTE actual)
								ACTUAL
								(QUOTE instr)
								INSTR)))))))
	     (ITERATE FOR NAME IN HIT-VARS-OF-SUBR WHEN (COMMON-NAMEP NAME)
		      DO
		      (ITERATE FOR ACTUAL IN LST
			       DO
			       (COND
				((AND (VARIABLE-ARRAY-OR-ELEMENT-REFERENCE ACTUAL)
				      (EQ (LONG-NAME (REFERENCED-VARIABLE-OR-ARRAY
						      ACTUAL))
					  NAME))
				 (FORTRAN-ERROR "Smashed global of subr passed as actual"
						(LIST (QUOTE actual)
						      ACTUAL
						      (QUOTE instr)
						      INSTR))))))
	     (RETURN NIL)))

(DEFUN CHK-OK-LABEL (L)

;   We check that L meets the syntactic requirements on a label and also that
;   it occurs exactly once in FORTRAN-CODE and labels an executable statement.
;   Thus, if CHK-OK-LABEL has approved every ATOM member of FORTRAN-CODE then
;   we can conclude that the implicit function from labels to positions of
;   members of FORTRAN-CODE is a label function.


       (OR (AND (INTEGERP L)
		(< 0 L)
		(< L 100000))
	   (FORTRAN-ERROR "Illegal label" L))
       (OR (CONSP (CDR (MEMBER-EQUAL L FORTRAN-CODE)))
	   (FORTRAN-ERROR "Label labels END" L))
       (OR (NOT (MEMBER-EQUAL L (CDR (MEMBER-EQUAL L FORTRAN-CODE))))
	   (FORTRAN-ERROR "Label occurs twice" L))
       (OR (CONSP (CADR (MEMBER-EQUAL L FORTRAN-CODE)))
	   (FORTRAN-ERROR "Label labels label" L))
       (OR (NOT (EQ (CAR (CADR (MEMBER-EQUAL L FORTRAN-CODE)))
		    (QUOTE COMMENT)))
	   (FORTRAN-ERROR "Label labels comment" L)))

(DEFUN CHK-POSSIBLY-SMASHED NIL

;   HIT-VARS is supposed to be the set of all names possibly smashed by a call
;   of the new routine.  Thus, it should be the set containing every global
;   name or argument that is possibly smashed by some statement in
;   FORTRAN-CODE. We will verify that by computing every long name that is
;   smashed by some stmt and remembering those that are not nonarg locals. At
;   the end we will require HIT-VARS to be a permutation of that list. To make
;   the error messages a little more helpful in the case where a name is
;   omitted from HIT-VARS we will check for each statement that the nonarg
;   locals it possibly smashes are in HIT-VARS In the same pass we will enforce
;   the prohibition on smashing the variables controlling DO loops. We will
;   also make sure that no name used on the second level is possibly smashed by
;   any CALL stmt.


       (PROG (DO-VARIABLE-POCKETS NECESSARY-HIT-VARS 
				  USED-ON-THE-SECOND-LEVEL)

;   At the conclusion of this computation NECESSARY-HIT-VARS will be set to the
;   list of all COMMON names and arguments of this routine that are possibly
;   smashed. It had better be a permutation of HIT-VARS then.


	     (SETQ USED-ON-THE-SECOND-LEVEL
		   (ITERATE FOR INSTR IN FORTRAN-CODE WITH ANS
			    DO (SETQ ANS
				     (UNION-EQUAL
				      ANS
				      (ITERATE FOR NAME IN (ALL-NAMES-USED-ON-THE-SECOND-LEVEL
							    INSTR)
					       COLLECT (LONG-NAME NAME))))
			    FINALLY (RETURN ANS)))
	     (ITERATE FOR TAIL ON FORTRAN-CODE WITH INSTR
		      DO
		      (PROGN (SETQ INSTR (CAR TAIL)) 

;   DO-VARIABLE-POCKETS is a stack of pairs.  The CAR of each pair is the
;   terminating label of a DO containing the current INSTR.  The CDR of each
;   pair is a list of all the DO control variables that may not smashed by any
;   statement in the range of the DO.


			     (COND
			      ((ATOM INSTR)
			       (COND
				((EQUAL INSTR (CAAR DO-VARIABLE-POCKETS))
			

;   If we are at the terminating label of the most recent active DO, then
;   splice into the TAIL after the next stmt a secret instruction to pop the
;   DO-VARIABLE-POCKETS


				 (SETQ TAIL
				       (CONS NIL (CONS (CADR TAIL)
						       (CONS (LIST (QUOTE POP)
								   INSTR)
							     (CDDR TAIL))))))))
			      ((EQ (CAR INSTR)
				   (QUOTE POP))
		      

;   If we have just processed the last stmt in the range of the most recent
;   active DO then pop the DO-VARIABLE-POCKETS until we've removed all DO's
;   terminating with the just processed labeled stmt.


			       (ITERATE WHILE (EQUAL (CADR INSTR)
						     (CAAR DO-VARIABLE-POCKETS))
					DO (SETQ DO-VARIABLE-POCKETS
						 (CDR DO-VARIABLE-POCKETS))))
			      (T 

;   For all other statements check that every smashed variable is either a
;   nonarg local of the routine or else is on HIT-VARS and that no protected
;   var is smashed. If we are processing a CALL make sure it doesn't smash any
;   name used on the second level.  Add to NECESSARY-HIT-VARS each possibly
;   smashed arg and global name. Finally, if we are processing a DO statement,
;   push another entry onto DO-VARIABLE-POCKETS.


			       (ITERATE FOR NAME IN (ALL-NAMES-POSSIBLY-SMASHED-THROUGH
						     INSTR)
					DO
					(PROGN
					 (OR (MEMBER-EQ NAME HIT-VARS)
					     (NONARG-LOCAL-NAMEP NAME)
					     (FORTRAN-ERROR "Undeclared HIT-VAR" NAME))
					 (OR (ITERATE FOR POCKET IN DO-VARIABLE-POCKETS
						      NEVER (MEMBER-EQ NAME (CDR POCKET)))
					     (FORTRAN-ERROR "DO variable smashed in range" 
							    NAME))
					 (COND
					  ((EQ (CAR INSTR)
					       (QUOTE CALL))
					   (COND
					    ((MEMBER-EQ NAME USED-ON-THE-SECOND-LEVEL)
					     (FORTRAN-ERROR "Second level var smashed"
							    (LIST (QUOTE var)
								  NAME
								  (QUOTE instr)
								  INSTR))))))
					 (COND
					  ((NOT (NONARG-LOCAL-NAMEP NAME))
					   (SETQ NECESSARY-HIT-VARS
						 (ADD-TO-SET NAME NECESSARY-HIT-VARS))))))
			       (COND
				((EQ (CAR INSTR)
				     (QUOTE DO))
				 (SETQ DO-VARIABLE-POCKETS
				       (CONS (CONS (CADR INSTR)
						   (ITERATE FOR V IN (CDDR INSTR)
							    WHEN (FORTRAN-VARIABLEP V)
							    COLLECT (LONG-NAME V)))
					     DO-VARIABLE-POCKETS))))))))
	     (OR (PERM NECESSARY-HIT-VARS HIT-VARS)
		 (FORTRAN-ERROR "HIT-VARS should be a permutation of" 
				NECESSARY-HIT-VARS))
	     (RETURN NIL)))

(DEFUN CHK-ROUTINE (ROUTINE CONTEXT)

;   This function checks that ROUTINE is a FUNCTION or SUBROUTINE subprogram.
;   It also checks that adding ROUTINE to CONTEXT produces a syntactically
;   correct context, assuming CONTEXT is syntactically correct.  If this
;   function does not cause an error then the syntactic environment of ROUTINE
;   is given by the values of the following 7 global variables:
;   ARRAY-PATTERNS, VARIABLE-PATTERNS, LABEL-VARIABLE-PATTERNS,
;   STATEMENT-FUNCTION-PATTERNS, FUNCTION-PATTERNS, SUBROUTINE-PATTERNS, and
;   BLOCK-NAMES.  In addition, the global variable TRANSLATED-FORTRAN-CODE will
;   contain the result of translating the CODE of ROUTINE to remove the DO's.


       (PROG (ROUTINE-NAME ROUTINE-ARGS HIT-VARS KNOWN-BLOCK-NAMES 
			   VAR-DCLS CALLED-FNS FORTRAN-CODE FUNCTION-TYPE 
			   SUBROUTINE-FLG)
	     (COND
	      ((MATCH ROUTINE
		      (SUBROUTINE ROUTINE-NAME ROUTINE-ARGS BLOCK-NAMES 
				  HIT-VARS KNOWN-BLOCK-NAMES VAR-DCLS 
				  CALLED-FNS STATEMENT-FUNCTION-PATTERNS 
				  & & & FORTRAN-CODE))
	       (SETQ SUBROUTINE-FLG T))
	      ((MATCH ROUTINE
		      (FUNCTION ROUTINE-NAME FUNCTION-TYPE ROUTINE-ARGS 
				BLOCK-NAMES KNOWN-BLOCK-NAMES VAR-DCLS 
				CALLED-FNS STATEMENT-FUNCTION-PATTERNS & 
				& & FORTRAN-CODE))
	       (SETQ VAR-DCLS
		     (CONS (MAKE VAR-DCL ROUTINE-NAME FUNCTION-TYPE NIL)
			   VAR-DCLS))
	       (SETQ SUBROUTINE-FLG NIL)
	       (SETQ HIT-VARS NIL))
	      (T (FORTRAN-ERROR "ROUTINE must be SUBROUTINE or FUNCTION record" NIL)
		 (SETQ TRANSLATED-FORTRAN-CODE NIL)
		 (RETURN NIL)))

;   The members of BLOCK-NAMES are supposed to be the names of the common
;   blocks to be declared in this routine, whereas the KNOWN-BLOCK-NAMES are
;   supposed to be the block names declared here and in any routine called
;   somehow from here.  HIT-VARS is supposed to contain every name that is
;   possibly smashed by this routine.  VAR-DCLS is supposed to contain the
;   variable patterns and the array patterns for this routine.  CALLED-FNS
;   contains the names of the routine's function patterns.


	     (GUESS-SYNTACTIC-ENVIRONMENT)
	     (CHK-SYNTACTIC-ENVIRONMENT)

;   We now know that we have a syntactic environment.  We next check that every
;   statement generated by the pretty printer on this routine will be a FORTRAN
;   statement in our subset.


	     (CHK-SYNTACTICALLY-OK-STATEMENTS)

;   Now we confirm that we have a legal subprogram and that when added to the
;   CONTEXT we get a superficial context.


	     (CHK-SUBPROGRAM)
	     (CHK-SUPERFICIAL-CONTEXT)

;   According to the specs, we want to check next that the context is
;   syntactically correct.  To do that we have to do the possibly smashed
;   analysis, which requires knowing that the KNOWN-BLOCK-NAMES are correctly
;   set.


	     (CHK-KNOWN-BLOCK-NAMES)

;   We now do the possibly smashed analysis.  We check three things. First,
;   that HIT-VARS is correctly set. Second that DO variables are not smashed in
;   the range of the DO.  Third that variables used on the second level in the
;   routine are not possibly smashed by any CALL.  The first -- aside from
;   being necessary to maintain the invariant for the HIT-VARS component of a
;   verified routine -- is used in our check for syntactic correctness. The
;   second completes the checks necessary for DO loop removal.  The third is
;   actually a part of the definition of syntactic correctness but is being
;   done here since all the necessary information is available.


	     (CHK-POSSIBLY-SMASHED)

;   We now know that KNOWN-BLOCK-NAMES and HIT-VARS are correctly set. We also
;   know that all requirements on the DO statements and their ranges are met.
;   So we are ready to translate away the DO statements and check syntactic
;   correctness.


	     (SETQ TRANSLATED-FORTRAN-CODE (TRANSLATE-DO-STATEMENTS 
					    FORTRAN-CODE))
	     (CHK-SYNTACTICALLY-CORRECT)
	     (RETURN NIL)))

(DEFUN CHK-SUBPROGRAM NIL

;   we now check that the syntactic environment, ROUTINE, and implicit label
;   function together form a subprogram. We include the check that the DO loops
;   are well-nested, have proper terminating statements, and observe the
;   restrictions on jumps since those 3 of the 4 DO loop restrictions are
;   purely syntactic.  We do not check that the control vars are not possibly
;   smashed, as that requires a more global view of things and more properly
;   belongs in the syntactic correctness rather than subprogram part.


       (PROG (NEXT-TO-LAST-STMT TEMP)

;   We know that we have a syntactic environment, a sequence of statements, and
;   a label function.  We know the first statement to be printed will be a
;   SUBROUTINE or FUNCTION statement and that no other such statement will be
;   printed.  We must check that every adjustable array and every adjustable
;   dimension is a formal.


	     (ITERATE FOR PAT IN ARRAY-PATTERNS
		      DO (OR (ITERATE FOR DIM IN (ACCESS VAR-DCL SIZES PAT)
				      UNLESS (OR (INTEGERP DIM)
						 (TOKENP DIM))
				      ALWAYS (AND (MEMBER-EQ (ACCESS VAR-DCL NAME PAT)
							     ROUTINE-ARGS)
						  (MEMBER-EQ DIM ROUTINE-ARGS)))
			     (FORTRAN-ERROR "Nonformal adjustable array or dimension" 
					    PAT)))

;   We must check that each array, variable, label variable, statement
;   function, and function pattern will be declared exactly once.  Since the
;   statement function patterns and function patterns of the syntactic
;   environment are in 1:1 correspondence with the corresponding fields of the
;   routine -- from which the type stmts are generated -- and since we know
;   those components of the syntactic environment have no duplications, we are
;   okay for the latter two classes.  To conclude that each of the other three
;   types of patterns will be declared at least once note that the declarations
;   are printed from the BLOCK-NAMES and the VAR-DCLS and that every array,
;   variable, or label variable pattern is from one of those two.  Furthermore,
;   each of the patterns among these three types is from one of those two.
;   Thus, if there are no duplicates among the vars declared in the blocks
;   concatenated with VAR-DCLS, then it is obvious that each pattern is
;   declared exactly once. It is possible to do better than this, but the proof
;   is tedious, being complicated by the fact that duplications in the VAR-DCLS
;   or between them and the common patterns may be masked by the SET-DIFF used
;   to compute VARIABLE-PATTERNS.  So I'll just do the brute force check here.
;   In the case of a FUNCTION we know the name of the function will not be
;   re-declared because it is not among the VAR-DCLS initially -- because if it
;   were then we would have gotten a duplication after adding it.


	     (COND
	      ((SETQ TEMP (DUPLICATE-CADRS
			   (APPEND (ITERATE FOR NAME IN BLOCK-NAMES WITH ANS
					    DO (SETQ ANS
						     (APPEND ANS (VAR-DCLS-OF-BLOCK NAME)))
					    FINALLY (RETURN ANS))
				   VAR-DCLS)))
	       (FORTRAN-ERROR "Vars declared twice" TEMP)))

;   Observe that each nonintrinsic CALLED-FN is declared EXTERNAL exactly once
;   since there are no duplicates among CALLED-FNS -- since there are no
;   duplicates among the function patterns.  Each block name is declared
;   exactly once and no name is in two blocks, by the ADD-TO-CONTEXT checks.
;   We must check that no formal argument is in any common block.


	     (ITERATE FOR ARG IN ROUTINE-ARGS
		      DO (COND
			  ((ITERATE FOR BLK IN BLOCK-NAMES
				    THEREIS (ASSOC-CADR ARG (VAR-DCLS-OF-BLOCK BLK)))
			   (FORTRAN-ERROR "Formal var in COMMON" ARG))))

;   We must check that if we are processing a FUNCTION then the name of the
;   function is not in any common block.


	     (COND
	      ((NOT SUBROUTINE-FLG)
	       (COND
		((ITERATE FOR BLK IN BLOCK-NAMES
			  THEREIS (ASSOC-CADR ROUTINE-NAME
					      (VAR-DCLS-OF-BLOCK BLK)))
		 (FORTRAN-ERROR "FUNCTION name in COMMON" ROUTINE-NAME)))))

;   Each statement fn is defined exactly once since the statement function
;   patterns have no duplications. Each array pattern is dimensioned exactly
;   once since VAR-DCLS has no duplicates.  Every label used in the
;   FORTRAN-CODE is a CHK-LABEL and hence in the domain of the implicit label
;   function. By construction, each subroutine pattern is called at least once.
;   By construction, each label variable is so used at least once.  We must
;   check that at least one member of the code is a RETURN.


	     (COND
	      ((ITERATE FOR STMT IN FORTRAN-CODE
			NEVER (OR (MATCH STMT (RETURN))
				  (MATCH STMT (IF-LOGICAL & (RETURN)))))
	       (FORTRAN-ERROR "No RETURN stmt" NIL)))

;   We print the statements of a subprogram in the correct order, given that no
;   nonexecutable statements are hidden in FORTRAN-CODE.  We have already
;   checked that the statement functions are defined in the proper order --
;   that was done prematurely but somewhate naturally by
;   CHK-SYNTACTICALLY-OK-STATEMENTS.  We must check that the next to last
;   statement printed will be a transfer of control.


	     (SETQ NEXT-TO-LAST-STMT (CAR (OUR-LAST FORTRAN-CODE)))
	     (COND
	      ((OR (ATOM NEXT-TO-LAST-STMT)
		   (NOT (MEMBER-EQ (CAR NEXT-TO-LAST-STMT)
				   (QUOTE (GOTO ASSIGNED-GOTO COMPUTED-GOTO 
						IF-ARITHMETIC RETURN STOP)))))
	       (FORTRAN-ERROR "Illegal last stmt" NEXT-TO-LAST-STMT)))

;   * We know the last statement printed is an END stmt.



;   The name of each member of the variable patterns must be used as a variable
;   -- other than as an actual -- in some statement other than a type or
;   FUNCTION statement. Furthermore each argument of the routine must be used
;   as a variable -- other than as an actual in a function reference -- in some
;   statement of seq other than a type, CALL, FUNCTION, or SUBROUTINE
;   statement.


	     (CHK-VARIABLE-USAGE)

;   We now check that the name of each intrinsic member of the function
;   patterns is called.


	     (CHK-INTRINSIC-USAGE)

;   now we check that each DO terminates with the correct kind of stmt, that
;   the DO's are well nested, and that nobody jumps into the range of a lower
;   DO.


	     (CHK-DO-NESTING-AND-JUMPS)
	     (RETURN T)))

(DEFUN CHK-SUPERFICIAL-CONTEXT NIL

;   Now we confirm that we have a superficial context. We assume that CONTEXT
;   itself is superficial.

;   We know by construction that the SUBROUTINE-PATTERNS and the nonintrinsic
;   FUNCTION-PATTERNS of our routine are consistent with those of the CONTEXT.
;   That is, we know each pattern corresponds to a previously verified routine
;   because we constructed the subroutine and function patterns from the
;   routines in CONTEXT.  We know the type and number of args are right from
;   that construction. We know that each of the ARG-VAR-DCLS is in the array or
;   variable patterns of the verified routine because we checked that in
;   CHK-SYNTACTICALLY-OK-STATEMENTS when we were dealing with the old routine.

;   We must check that the NAME of our new routine is not among the routines of
;   the context and is not the name of any intrinsic. The former is guaranteed
;   by the DUPLICATE-CADRS in ADD-TO-CONTEXT.  The latter can be proved: if our
;   new routine is a SUBROUTINE then its name is not intrinsic by the syntactic
;   requirements on SUBROUTINE statements; if our new routine is a FUNCTION
;   then its name is among the variable patterns by construction and thus
;   cannot be intrinsic by the definition of a syntactic environment.

;   We know that the NAME of our new routine is not among the block names of
;   any old routine because of the DUPLICATE-CADRS check in ADD-TO-CONTEXT.

;   We know that the layout of every common block in our new routine is
;   consistent with that of the block in any old routine, since the CONTEXT
;   contains the only description of the blocks.  By construction of the
;   ARRAY-PATTERNS and VARIABLE-PATTERNS, every component of every common block
;   in our routine is in the array or variable patterns.

;   We know -- from the DUPLICATE-CADRS check in ADD-TO-CONTEXT -- that no
;   component of any block is in a different block or is a block name, the name
;   of our new routine, or the name of any old routine.

       T)

(DEFUN CHK-SYNTACTIC-ENVIRONMENT NIL

;   We now check that we have a syntactic environment consisting of
;   ARRAY-PATTERNS, VARIABLE-PATTERNS, LABEL-VARIABLE-PATTERNS,
;   STATEMENT-FUNCTION-PATTERNS, FUNCTION-PATTERNS, SUBROUTINE-PATTERNS,
;   BLOCK-NAMES.  In principle we have to make one CHECK for each clause in the
;   definition of a syntactic environment.  However, in fact we use some facts
;   about GUESS-SYNTACTIC-ENVIRONMENT -- for example, that the
;   SUBROUTINE-PATTERNS are all distinct by construction. Roughly speaking
;   however, our checks below follow exactly the definition of syntactic
;   environment.


       (PROG (TEMP)

;   We start with a top-level no duplication check that not only guarantees
;   that the individual components of the proposed syntactic environment have
;   no duplicates but also that there are no intersections between components.


	     (COND
	      ((SETQ TEMP
		     (DUPLICATE-CADRS (APPEND ARRAY-PATTERNS 
					      VARIABLE-PATTERNS 
					      LABEL-VARIABLE-PATTERNS 
					      STATEMENT-FUNCTION-PATTERNS 
					      FUNCTION-PATTERNS 
					      SUBROUTINE-PATTERNS
					      (ITERATE FOR BLK IN BLOCK-NAMES
						       COLLECT (LIST 0 BLK)))))
	       (FORTRAN-ERROR "Duplicate names in syntactic environment" TEMP)))
	     (ITERATE FOR ARRAY-PATTERN IN ARRAY-PATTERNS
		      WITH INTEGER-VARS = (APPEND (ACCESS CONTEXT TOKENS CONTEXT)
						  (ITERATE FOR VDCL
							   IN VARIABLE-PATTERNS
							   WHEN (EQ (ACCESS VAR-DCL TYPE 
									    VDCL)
								    (QUOTE INTEGER))
							   COLLECT (ACCESS VAR-DCL NAME 
									   VDCL)))

		      DO (CHK-VAR-DCL ARRAY-PATTERN INTEGER-VARS))
	     (ITERATE FOR VDCL IN VARIABLE-PATTERNS DO (CHK-VAR-DCL VDCL NIL))
	     (ITERATE FOR VDCL IN LABEL-VARIABLE-PATTERNS
		      DO (PROGN (CHK-VAR-DCL VDCL NIL)
				(OR (EQ (ACCESS VAR-DCL TYPE VDCL)
					(QUOTE INTEGER))
				    (FORTRAN-ERROR "Non-INTEGER label var" VDCL))))

;   We not only check that each statement function pattern is well-formed, we
;   check that the args are among the variable patterns, knowing that that will
;   be required later in the check that the statement function statements are
;   well-formed.


	     (ITERATE FOR STMT-FN IN STATEMENT-FUNCTION-PATTERNS
		      WITH NAME AND TYPE AND ARGS
		      DO
		      (PROGN
		       (OR (MATCH STMT-FN (STATEMENT-FUNCTION-PATTERN NAME 
								      TYPE 
								      ARGS &))
			   (FORTRAN-ERROR 
			    "Ill-formed STATEMENT-FUNCTION-PATTERN record"
			    STMT-FN))
		       (CHK-FORTRAN-NAME NAME)
		       (CHK-FORTRAN-TYPE TYPE)
		       (ITERATE FOR ARG IN ARGS
				DO (OR (MEMBER-EQUAL ARG VARIABLE-PATTERNS)
				       (FORTRAN-ERROR
					"Stmt fn arg not in var patterns" ARG)))
		       (OR (NO-DUPLICATE-CADRSP (CONS STMT-FN ARGS))
			   (FORTRAN-ERROR "Duplicates among stmt fn name and args" 
					  STMT-FN))))

;   * We know that FUNCTION-PATTERNS is a list of FUNCTION-PATTERNS by
;   construction.



;   We know that SUBROUTINE-PATTERNS is a list of SUBROUTINE-PATTERNS without
;   duplication by construction.


	     (ITERATE FOR BLK IN BLOCK-NAMES DO (CHK-FORTRAN-NAME BLK))
	     (COND
	      ((ITERATE FOR X IN (APPEND ARRAY-PATTERNS VARIABLE-PATTERNS 
					 LABEL-VARIABLE-PATTERNS 
					 STATEMENT-FUNCTION-PATTERNS 
					 SUBROUTINE-PATTERNS
					 (ITERATE FOR BLK IN BLOCK-NAMES
						  COLLECT (LIST 0 BLK)))
			WHEN (INTRINSIC-FUNCTIONP (CADR X))
			DO (FORTRAN-ERROR "Nonintrinsic use of intrinsic names" X))))

;   We know that if a member of the FUNCTION-PATTERNS has and instrinsic name,
;   that the pattern is a member of INTRINSIC-FUNCTION-PATTERNS by
;   construction.


	     (RETURN T)))

(DEFUN CHK-SYNTACTICALLY-CORRECT NIL

;   check that the result of adding the routine to CONTEXT is syntactically
;   correct.



;   If the new routine is a FUNCTION we know its HIT-VARS are NIL because we
;   set them to that and have just checked it.



;   * Next we check no adjustable dimension is smashed


       (ITERATE FOR VDCL IN ARRAY-PATTERNS
		DO (ITERATE FOR X IN (ACCESS VAR-DCL SIZES VDCL)
			    WHEN (AND (FORTRAN-VARIABLEP X)
				      (MEMBER-EQ X HIT-VARS))
			    DO (FORTRAN-ERROR "Smashed adjustable dimension" X)))

;   Now make sure that no CALL stmt exhibits either form of aliasing. We check
;   four things.  Every possibly smashed formal is occupied by a var or array
;   reference. No such formal is occupied by a reference to a known common var
;   of the called routine. No such formal is occupied by an actual also passed
;   in another formal slot.  No possibly smashed common name of the called
;   routine is passed in any formal.


       (ITERATE FOR INSTR IN TRANSLATED-FORTRAN-CODE WHEN (MATCH INSTR
								 (CALL & &))
		DO (CHK-NO-ALIASING INSTR))

;   In CHK-POSSIBLY-SMASHED we verified that no var used on the second level is
;   possibly smashed by a CALL.


       T)

(DEFUN CHK-SYNTACTICALLY-OK-COMMENT (INSTR)
       (PROG (NAME)
	     (OR (ITERATE FOR WORD
			  IN (MC-FLATTEN (COND
					  ((MATCH (CDR INSTR)
						  (ASSERTION NAME & &))
					   NAME)
					  ((MATCH (CDR INSTR)
						  (CONS (QUOTE DOJUNK)
							(CONS NAME &)))
					   NAME)
					  ((MATCH (CDR INSTR)
						  (CONS (QUOTE XXX)
							(CONS NAME (CONS & &))))
					   NAME)
					  (T (CDR INSTR)))
					 NIL)
			  UNLESS (TOKENP WORD)
			  ALWAYS (ITERATE FOR C IN
					  (COND ((NUMBERP WORD) NIL)
						((SYMBOLP WORD)(OUR-EXPLODEC WORD))
						(T (FORTRAN-ERROR
						    "Illegal member of comment." WORD)
						   NIL))
					  ALWAYS (MEMBER-EQ C
							    `(/
							      A B C D E F G H I J K L M N O P Q R S T U 
							      V W X Y Z |0| |1| |2| |3| |4| 
							      |5| |6| |7| |8| |9| | |  = + - * 
							      |(| |)| |.| |,| $))))
		 (FORTRAN-ERROR "Non-ASSERTION comment contains illegal chars" 
				INSTR))
	     (COND
	      ((AND (CONSP (CDR INSTR))
		    (EQ (CAR INSTR)
			(QUOTE DOJUNK)))
	       (OR
		(ITERATE FOR PAIR IN (CDDDR INSTR)
			 ALWAYS
			 (AND
			  (CONSP PAIR)
			  (MEMBER-EQ (CAR PAIR)
				     (QUOTE (OKDO INIT TEST BUMP JUMP UNDEF)))
			  (ITERATE FOR X IN (CDR PAIR)
				   ALWAYS
				   (OR (MATCH X (CONTINUE))
				       (MATCH X (COMMENT (QUOTE ASSERTION)
							 & & &))
				       (MATCH X (CONS (QUOTE COMMENT)
						      (CONS (QUOTE XXX)
							    (CONS & (CONS & &))))
					      )))))
		(FORTRAN-ERROR "Bad DO Junk" INSTR))))
	     (RETURN NIL)))

(DEFUN CHK-SYNTACTICALLY-OK-EXECUTABLE-STMT (INSTR)
       (PROG (V EXP LAB I J K STMT SUB LST PAT)
	     (COND
	      ((MATCH INSTR (ASSIGNMENT V EXP))
	       (OR (COND
		    ((ATOM V)
		     (FORTRAN-VARIABLEP V))
		    (T (ASSOC-CADR (CAR V)
				   ARRAY-PATTERNS)))
		   (FORTRAN-ERROR "lhs not variable or array element" INSTR))
	       (OR (EQUAL (SORT-OF V)
			  (SORT-OF EXP))
		   (FORTRAN-ERROR "Sort of lhs not sort of rhs" INSTR)))
	      ((MATCH INSTR (ASSIGN-TO LAB I))
	       (OR (ASSOC-CADR I LABEL-VARIABLE-PATTERNS)
		   (FORTRAN-ERROR "rhs not label var" INSTR))
	       (CHK-LABEL LAB INSTR))
	      ((MATCH INSTR (GOTO LAB))
	       (CHK-LABEL LAB INSTR))
	      ((MATCH INSTR (ASSIGNED-GOTO I LST))
	       (OR (ASSOC-CADR I LABEL-VARIABLE-PATTERNS)
		   (FORTRAN-ERROR "lhs not label var" INSTR))
	       (OR (CONSP LST)
		   (FORTRAN-ERROR "rhs empty list" INSTR))
	       (ITERATE FOR X IN LST DO (CHK-LABEL X INSTR)))
	      ((MATCH INSTR (COMPUTED-GOTO LST I))
	       (OR (AND (FORTRAN-VARIABLEP I)
			(INTEGER-EXPRP I))
		   (FORTRAN-ERROR "lhs not integer variable" INSTR))
	       (OR (CONSP LST)
		   (FORTRAN-ERROR "rhs empty list" INSTR))
	       (ITERATE FOR X IN LST DO (CHK-LABEL X INSTR)))
	      ((MATCH INSTR (IF-ARITHMETIC EXP I J K))
	       (CHK-LABEL I INSTR)
	       (CHK-LABEL J INSTR)
	       (CHK-LABEL K INSTR)
	       (OR (MEMBER-EQUAL (SORT-OF EXP)
				 (QUOTE ((INTEGER)
					 (REAL)
					 (DOUBLE))))
		   (FORTRAN-ERROR "Tested expr has wrong type" INSTR)))
	      ((MATCH INSTR (CALL SUB LST))
	       (OR (SETQ PAT (ASSOC-CADR SUB SUBROUTINE-PATTERNS))
		   (FORTRAN-ERROR "Undefined subr called" INSTR))
	       (OR (EQUAL (LENGTH LST)
			  (LENGTH (ACCESS SUBROUTINE-PATTERN ARG-VAR-DCLS 
					  PAT)))
		   (FORTRAN-ERROR "Wrong number of args" INSTR))
	       (ITERATE FOR ARG IN LST AS VDCL
			IN (ACCESS SUBROUTINE-PATTERN ARG-VAR-DCLS PAT)
			WITH SORT
			DO
			(PROGN
			 (SETQ SORT (SORT-OF ARG))
			 (OR (EQUAL (ACCESS VAR-DCL TYPE VDCL)
				    (CAR SORT))
			     (FORTRAN-ERROR "Actual of wrong type"
					    (LIST (QUOTE actual)
						  ARG
						  (QUOTE instr)
						  INSTR)))
			 (OR (EQUAL (LENGTH (CDR SORT))
				    (LENGTH (ACCESS VAR-DCL SIZES VDCL)))
			     (FORTRAN-ERROR "Actual of wrong number of dimensions"
					    (LIST (QUOTE actual)
						  ARG
						  (QUOTE instr)
						  INSTR)))
			 (OR
			  (ITERATE FOR ADIM IN (CDR SORT) AS FDIM
				   IN (ACCESS VAR-DCL SIZES VDCL)
				   ALWAYS
				   (COND
				    ((OR (INTEGERP FDIM)
					 (TOKENP FDIM))
				     (EQUAL FDIM ADIM))
				    (T (EQUAL ADIM
					      (ITERATE FOR ACT IN LST AS FORMAL
						       IN (ACCESS SUBROUTINE-PATTERN 
								  ARG-VAR-DCLS PAT)
						       WHEN (EQUAL (ACCESS VAR-DCL NAME FORMAL)
								   FDIM)
						       DO (RETURN ACT))))))
			  (FORTRAN-ERROR "Actual has wrong size"
					 (LIST (QUOTE actual)
					       ARG
					       (QUOTE instr)
					       INSTR))))))
	      ((MEMBER-EQUAL INSTR (QUOTE ((RETURN)
					   (CONTINUE)
					   (STOP)
					   (PAUSE))))
	       T)
	      ((OR (MATCH INSTR (PAUSE I))
		   (MATCH INSTR (STOP I)))
	       (OR (AND (INTEGERP I)
			(< -1 I)
			(< I 32768))
		   (FORTRAN-ERROR "Illegal STOP-PAUSE number" INSTR)))
	      ((MATCH INSTR (IF-LOGICAL EXP STMT))
	       (OR (EQUAL (SORT-OF EXP)
			  (QUOTE (LOGICAL)))
		   (FORTRAN-ERROR "Tested expr not logical" INSTR))
	       (CHK-SYNTACTICALLY-OK-EXECUTABLE-STMT STMT)
	       (OR (MEMBER-EQ (CAR STMT)
			      (QUOTE (ASSIGNMENT ASSIGN-TO GOTO 
						 ASSIGNED-GOTO COMPUTED-GOTO 
						 IF-ARITHMETIC CALL RETURN 
						 CONTINUE STOP PAUSE)))
		   (FORTRAN-ERROR "Logical IF contains wrong kind of stmt" 
				  INSTR)))
	      ((MATCH INSTR (DO LAB V I J K))
	       (CHK-LABEL LAB INSTR)
	       (OR (AND (INTEGER-EXPRP V)
			(FORTRAN-VARIABLEP V))
		   (FORTRAN-ERROR "DO control not integer var" INSTR))
	       (ITERATE FOR I IN (LIST I J K)
			DO (OR (AND (INTEGER-EXPRP I)
				    (OR (FORTRAN-VARIABLEP I)
					(AND (INTEGERP I)
					     (< 0 I))
					(TOKENP I)))
			       (FORTRAN-ERROR "Illegal DO max-min-incrt" INSTR))))
	      (T (FORTRAN-ERROR "Unrecognized instr" INSTR)))
	     (RETURN NIL)))

(DEFUN CHK-SYNTACTICALLY-OK-STATEMENTS NIL

;   Check that every statement that will be printed for the ROUTINE of
;   CHK-ROUTINE is a statement wrt the syntactic environment in CHK-ROUTINE.
;   We make our checks in the order in which the statements of the routine will
;   be printed.  We first check that the FUNCTION or SUBROUTINE statement will
;   be properly printed.


       (PROG (NAME TYPE BODY TEMP)
	     (CHK-FORTRAN-NAME ROUTINE-NAME)
	     (COND
	      (SUBROUTINE-FLG (COND
			       ((SETQ TEMP
				      (ASSOC-CADR
				       ROUTINE-NAME
				       (APPEND ARRAY-PATTERNS 
					       VARIABLE-PATTERNS 
					       LABEL-VARIABLE-PATTERNS 
					       STATEMENT-FUNCTION-PATTERNS 
					       FUNCTION-PATTERNS 
					       SUBROUTINE-PATTERNS
					       (ITERATE FOR NAME IN BLOCK-NAMES
							COLLECT
							(LIST (QUOTE 
							       COMMON-BLOCK)
							      NAME
							      (QUOTE &))))))
				(FORTRAN-ERROR 
				 "Routine name in own syntactic environment"
				 TEMP)))
			      (COND
			       ((INTRINSIC-FUNCTIONP ROUTINE-NAME)
				(FORTRAN-ERROR "Subroutine name is intrinsic" 
					       ROUTINE-NAME)))
			      (OR (NO-DUPLICATESP ROUTINE-ARGS)
				  (FORTRAN-ERROR "Duplicate formals" 
						 ROUTINE-ARGS))
			      (ITERATE FOR ARG IN ROUTINE-ARGS
				       DO (OR (ASSOC-CADR ARG ARRAY-PATTERNS)
					      (ASSOC-CADR ARG VARIABLE-PATTERNS)
					      (FORTRAN-ERROR 
					       "Formal not array or variable"
					       ARG))))
	      (T (CHK-FORTRAN-TYPE FUNCTION-TYPE)
		 (OR (CONSP ROUTINE-ARGS)
		     (FORTRAN-ERROR "Function with no args" ROUTINE-NAME))
		 (OR (NOT (MEMBER-EQ ROUTINE-NAME ROUTINE-ARGS))
		     (FORTRAN-ERROR "Function name among formals" ROUTINE-NAME))
		 (OR (NO-DUPLICATESP ROUTINE-ARGS)
		     (FORTRAN-ERROR "Duplicate formals" ROUTINE-ARGS))
		 (ITERATE FOR ARG IN ROUTINE-ARGS
			  DO (OR (ASSOC-CADR ARG ARRAY-PATTERNS)
				 (ASSOC-CADR ARG VARIABLE-PATTERNS)
				 (FORTRAN-ERROR "Formal not array or variable" ARG)))))

;   We now check that all the type stmts are in our subset. That means that
;   each name declared is in the array, variable, label variable, stmt fns, or
;   function patterns. We know by construction that that statement holds of the
;   type statements generated from the BLOCK-NAMES, CALLED-FNS, STATEMENT-FNS,
;   and VAR-DCLS. So we are finished with the type statements.



;   We know the DIMENSION stmts are all ok because they are generated from the
;   BLOCK-NAMES and VAR-DCLS that have SIZES and all those names are in the
;   array patterns.



;   We now check the COMMON statements.  We only print them for BLOCK-NAMES,
;   the printing is driven from the COMMON-BLOCKs in the context, and
;   ADD-TO-CONTEXT checked that all the names were distinct. Each entry in each
;   COMMON block is either in the variable or array or label variable patterns
;   by construction. Thus, we must only check that every block name names a
;   member of the COMMON-BLOCKS of the CONTEXT and that no entry in any block
;   is in the label variable patterns.


	     (ITERATE FOR BLOCK IN BLOCK-NAMES
		      DO
		      (PROGN
		       (OR (ASSOC-CADR BLOCK
				       (ACCESS CONTEXT COMMON-BLOCKS CONTEXT))
			   (FORTRAN-ERROR "Block name not contained in CONTEXT" BLOCK))
		       (ITERATE FOR VDCL IN (VAR-DCLS-OF-BLOCK BLOCK)
				DO (COND
				    ((MEMBER-EQ (ACCESS VAR-DCL NAME VDCL)
						LABEL-VARIABLE-PATTERNS)
				     (FORTRAN-ERROR "Label var in COMMON" VDCL))))))

;   The EXTERNAL statements are ok because we only EXTERNAL the CALLED-FNS not
;   in the intrinsics.



;   We now check that each statement function statement comes out legally.  We
;   actually do a little more here than required to check that each individual
;   one comes out legally: we check that they come out in the correct order, as
;   per the definition of a subprogram.  To do this latter we set
;   STATEMENT-FUNCTION-PATTERNS to NIL in the following FOR and add each
;   blessed pattern to it, thereby permitting its use by SORT-OF in subsequent
;   bodies.


	     (SETQ TEMP-TEMP STATEMENT-FUNCTION-PATTERNS)
	     (SETQ STATEMENT-FUNCTION-PATTERNS NIL)
	     (ITERATE FOR FN IN TEMP-TEMP
		      DO
		      (PROGN
		       (MATCH! FN (STATEMENT-FUNCTION-PATTERN NAME TYPE & BODY))
		       (OR (EQUAL (CONS TYPE NIL)
				  (SORT-OF BODY))
			   (FORTRAN-ERROR "Sort of stmt fn disagrees with body" NAME))
		       (OR (INTEGERP BODY)
			   (TOKENP BODY)
			   (CONSP BODY)
			   (FORTRAN-ERROR "Stmt fn with var body" NAME))
		       (OR (CONTAINS-NO-ARRAYS BODY)
			   (FORTRAN-ERROR "Stmt fn body contains arrays" NAME))
		       (SETQ STATEMENT-FUNCTION-PATTERNS
			     (CONS FN STATEMENT-FUNCTION-PATTERNS))))

;   We now check that every executable statement is a statement wrt our
;   syntactic environment.  We also check that the ATOM members of FORTRAN-CODE
;   are labels and that the characters printed in comments are all legal
;   FORTRAN characters.


	     (ITERATE FOR INSTR IN FORTRAN-CODE
		      DO (COND
			  ((ATOM INSTR)
		    

;   We not only check syntactic well-formedness of the labels but enough to
;   guarantee that they specify a label function.


			   (CHK-OK-LABEL INSTR))
			  ((EQ (CAR INSTR)
			       (QUOTE COMMENT))
			   (CHK-SYNTACTICALLY-OK-COMMENT INSTR))
			  (T (CHK-SYNTACTICALLY-OK-EXECUTABLE-STMT INSTR))))
	     (RETURN NIL)))

(DEFUN CHK-TRANSLATE (TERM)
  (LET ((UNDONE-EVENTS (LIST (LIST 'TRANSLATE TERM))))
    (TRANSLATE TERM)))

(DEFUN CHK-VAR-DCL (DCL LST)
       (PROG (NAME TYPE SIZES)
	     (MATCH! DCL (VAR-DCL NAME TYPE SIZES))
	     (CHK-FORTRAN-NAME NAME)
	     (CHK-FORTRAN-TYPE TYPE)
	     (OR (< (LENGTH SIZES)
		    4)
		 (FORTRAN-ERROR "Too many dimensions" DCL))
	     (ITERATE FOR SIZE IN SIZES
		      DO (OR (COND
			      ((NUMBERP SIZE)
			       (AND (INTEGERP SIZE)
				    (NOT (< SIZE 1))))
			      (T (MEMBER-EQ SIZE LST)))
			     (FORTRAN-ERROR "Illegal dimension" (LIST (QUOTE dim)
								      SIZE
								      (QUOTE var-dcl)
								      DCL))))
	     (RETURN NIL)))

(DEFUN CHK-VARIABLE-USAGE NIL

;   The name of each member of the variable patterns must be used as a variable
;   -- other than as an actual -- in some statement other than a type or
;   FUNCTION statement. Furthermore each argument of the routine must be used
;   as a variable -- other than as an actual in a function reference -- in some
;   statement of seq other than a type, CALL, FUNCTION, or SUBROUTINE
;   statement. Note that the requirement on args implies the general
;   requirement on all variables. Thus, we wish to check that for each variable
;   pattern either the var is an arg and occurs in one class of stmts or is not
;   an arg and occurs in another.


    (PROG (VDCL VAR ARGP TAIL)

;   we use a PROG here only to permit the blow by blow commenting of the
;   program.  The check is natually a FOR VDCL IN VARIABLE-PATTERNS EXISTS a
;   big OR checking for each acceptable use of the VDCL. But I wanted to
;   comment the disjuncts. So the form I chose is to iterate in a PROG, to
;   check each disjunct in a separate COND preceded by an appropriate comment
;   relating the test to what is prettyprinted. In the event that any test
;   succeeds I jump to FOUND, which is where we consider the next VDCL. If no
;   test succeeds I print a CHECK message.


          (SETQ TAIL VARIABLE-PATTERNS)
      LOOP(COND
	    ((ATOM TAIL)
	      (RETURN T)))
          (SETQ VDCL (CAR TAIL))
          (SETQ VAR (ACCESS VAR-DCL NAME VDCL))
          (SETQ ARGP (MEMBER-EQ VAR ROUTINE-ARGS))

;   Now consider the statements in the prettyprinted version of the routine and
;   look for a suitable occurrence of VAR. First consider the FUNCTION or
;   SUBROUTINE stmt. If VAR is an arg an occurrence there wouldn't count, so we
;   needn't look.  If VAR is not an arg then we might look in the SUBROUTINE
;   stmt but we wouldn't find it because the only vars that occur there are
;   args.  So next we consider the type statements.  Neither case accepts an
;   occurrence in a type statement. So next we consider the DIMENSION stmts.
;   Both cases would accept an occurrence there.  Of course, we don't have to
;   consider the possibility that the occurrence is as the array name, since
;   VAR is in the VARIABLE-PATTERNS.


          (COND
	    ((OR (ITERATE FOR BLK IN BLOCK-NAMES
		    THEREIS (ITERATE FOR VDCL IN (VAR-DCLS-OF-BLOCK BLK)
			      THEREIS (MEMBER-EQ VAR (ACCESS VAR-DCL SIZES VDCL))))
		 (ITERATE FOR VDCL IN VAR-DCLS
		    THEREIS (MEMBER-EQ VAR (ACCESS VAR-DCL SIZES VDCL))))
	      (GO FOUND)))

;   Next consider the COMMON statements.  Both cases accept occurrences there,
;   though we know we won't find any if VAR is an arg because formals are not
;   in COMMON.


          (COND
	    ((AND (NOT ARGP)
		  (ITERATE FOR BLK IN BLOCK-NAMES
		     THEREIS (ASSOC-CADR VAR (VAR-DCLS-OF-BLOCK BLK))))
	      (GO FOUND)))

;   Next come the EXTERNAL stmts, but VAR won't be found there. Next come the
;   statement function statements. We want to find an occurrence of VAR either
;   as a formal of the stmt fn or somewhere in the body, except as an actual in
;   a function ref.

          (COND
	    ((ITERATE FOR FN IN STATEMENT-FUNCTION-PATTERNS
		THEREIS (OR (MEMBER-EQUAL VDCL
				   (ACCESS STATEMENT-FUNCTION-PATTERN 
				      ARG-VAR-DCLS FN))
			   (USED-AS-A-NON-ACTUAL-VARIABLE VAR
							  (ACCESS 
					 STATEMENT-FUNCTION-PATTERN 
							     BODY FN))))
	     (GO FOUND)))

;   Finally comes the code.

          (COND
	    ((ITERATE FOR INSTR IN FORTRAN-CODE
		THEREIS (USED-AS-A-NON-ACTUAL-VARIABLE-IN-STMT VAR INSTR ARGP))
	     (GO FOUND)))

;   Then VAR was never used appropriately and we should scream.

          (FORTRAN-ERROR "Var not used as var" VAR)
      FOUND
          (SETQ TAIL (CDR TAIL))
          (GO LOOP)))

(DEFUN COMMON-BLOCK-CONTAINING (X)

;   If the long name of X is blk-X, then return blk; else return 0 which is not
;   a block name.


       (PROG (BLK)
	     (RETURN (COND
		      ((ITERATE FOR NAME IN BLOCK-NAMES
				THEREIS (COND
					 ((ASSOC-CADR X
						      (VAR-DCLS-OF-BLOCK NAME))
					  (SETQ BLK NAME)
					  T)
					 (T NIL)))
		       BLK)
		      (T 0)))))

(DEFUN COMMON-NAMEP (X)

;   assuming X is either local or common name, this function returns T if its a
;   common name.


       (MEMBER-EQ (QUOTE -) (OUR-EXPLODEC X)))

(DEFUN CONTAINS-NO-ARRAYS (X)
       (COND
	((ATOM X)
	 (OR (INTEGERP X)
	     (TOKENP X)
	     (ASSOC-CADR X VARIABLE-PATTERNS)))
	((ASSOC-CADR (CAR X)
		     ARRAY-PATTERNS)
	 NIL)
	(T (ITERATE FOR ARG IN (CDR X) ALWAYS (CONTAINS-NO-ARRAYS ARG)))))

(DEFUN DO-TEST (J K L INSTR)

;   Either we cause an error, or we return a FORTRAN expresion equivalent to J
;   .GT.  K OR J .LT. 1 OR L .LT. 1


       (PROG (T1 T2 T3)
	     (SETQ T1 (COND
		       ((AND (INTEGERP J)
			     (INTEGERP K))
			(COND
			 ((> J K)
			  (FORTRAN-ERROR "DO parameter error" INSTR)))
			NIL)
		       ((AND (EQUAL J 1)
			     (OR (ADJUSTABLE-DIM K)
				 (TOKENP K)))
			NIL)
		       (T (LIST (QUOTE ZGREATERP)
				J K))))
	     (SETQ T2 (COND
		       ((INTEGERP J)
			(COND
			 ((< J 1)
			  (FORTRAN-ERROR "DO parameter error" INSTR)))
			NIL)
		       ((OR (ADJUSTABLE-DIM J)
			    (TOKENP J))
			NIL)
		       (T (LIST (QUOTE ZLESSP)
				J 1))))
	     (SETQ T3 (COND
		       ((INTEGERP L)
			(COND
			 ((< L 1)
			  (FORTRAN-ERROR "DO parameter error" INSTR)))
			NIL)
		       ((OR (ADJUSTABLE-DIM L)
			    (TOKENP L))
			NIL)
		       (T (LIST (QUOTE ZLESSP)
				L 1))))
	     (RETURN (COND
		      (T1 (COND
			   (T2 (COND
				(T3 (LIST (QUOTE OR)
					  T1
					  (LIST (QUOTE OR)
						T2 T3)))
				(T (LIST (QUOTE OR)
					 T1 T2))))
			   (T (COND
			       (T3 (LIST (QUOTE OR)
					 T1 T3))
			       (T T1)))))
		      (T2 (COND
			   (T3 (LIST (QUOTE OR)
				     T2 T3))
			   (T T2)))
		      (T3 T3)
		      (T (LIST (QUOTE FALSE)))))))

(DEFUN DUPLICATE-CADRS (X)
       (COND
	((ATOM X)
	 NIL)
	((ASSOC-CADR (CADR (CAR X))
		     (CDR X))
	 (CONS (CADR (CAR X))
	       (DUPLICATE-CADRS (CDR X))))
	(T (DUPLICATE-CADRS (CDR X)))))

(DEFUN FAKE (LST)
       (PROG (DCL ANS)
	     (OR (CONSP LST)
		 (ERROR "~A is not a list." LST))
	     (SETQ DCL (ASSOC-EQ (CAR LST)
				 RECORD-DECLARATIONS))
	     (OR DCL (ERROR "~A is not the name of a record." (CAR LST)))
	     (SETQ ANS (ITERATE FOR FIELD IN (CADR DCL)
				COLLECT
				(CADR (ITERATE FOR TAIL
					       ON (ITERATE FOR X IN (CDR LST) 
							   COLLECT X)
					       BY 'CDDR
					       WHEN (EQ FIELD (CAR TAIL))
					       DO (RETURN TAIL)))))
	     (COND
	      ((NULL (CADDR DCL))
	       (SETQ ANS (CONS (CAR LST)
			       ANS))))
	     (RETURN ANS)))

(DEFUN FLATTEN-AND-OR (X FN)
       (COND
	((AND (EQ FN (QUOTE AND))
	      (EQUAL X TRUE))
	 NIL)
	((AND (EQ FN (QUOTE OR))
	      (EQUAL X FALSE))
	 NIL)
	((OR (VARIABLEP X)
	     (FQUOTEP X))
	 (LIST X))
	((EQ FN (FFN-SYMB X))
	 (ITERATE FOR X IN (FARGS X) WITH ANS
		  DO (SETQ ANS (APPEND ANS (FLATTEN-AND-OR X FN)))
		  FINALLY (RETURN ANS)))
	(T (LIST X))))

(DEFUN FLATTEN-ANDS (X)
       (PROG (LHS RHS)
	     (RETURN (COND
		      ((MATCH X (AND LHS RHS))
		       (UNION-EQUAL (FLATTEN-ANDS LHS)
				    (FLATTEN-ANDS RHS)))
		      (T (LIST X))))))

(DEFUN GENERATE-SKOLEM-CONSTANT (FN-SYMB ARG)
       (FCONS-TERM* (COND
		     ((MEMBER-EQ FN-SYMB UNSMASHED)
		      (PACK (LIST FN-SYMB (QUOTE $) (QUOTE |0|))))
		     (T (PACK (LIST FN-SYMB (QUOTE $)
				    (NEXT-DEPTH ARG)))))))

(DEFUN GENERATE-SPEC-ALISTS NIL

;   We now set up an alist of the translations of the input and output
;   conditions of all of the called functions. This is a delicate business
;   because for each function we must first declare as functions of one
;   argument each of the arguments of each such function in order to perform
;   the translation.  But then we must undo those declarations because those
;   arguments might be the names of other functions.


       (SETQ FUNCTION-SPEC-ALIST
	     (ITERATE FOR FN IN CALLED-FNS WITH FORMALS AND INPUT
		      AND OUTPUT AND KNOWN-BLOCK-NAMES
		      UNLESS (BUILT-IN-SPEC FN)
		      COLLECT (PROGN (MATCH! (ASSOC-CADR FN
							 (ACCESS CONTEXT ROUTINES CONTEXT))
					     (FUNCTION & & FORMALS & KNOWN-BLOCK-NAMES & & 
						       & INPUT OUTPUT & &))
				     (VCG-REDO-UNDONE-EVENTS
				      (CONS (QUOTE (FORTRAN-COMMENT DCL-START))
					    (ITERATE FOR ARG IN FORMALS
						     WHEN (NOT (MEMBER-EQ ARG (APPEND LOCALS GLOBALS))
							       )
						     COLLECT (LIST (QUOTE DCL)
								   ARG
								   (QUOTE (STATE))))))
				     (PROG1 (LIST FN FORMALS KNOWN-BLOCK-NAMES
						  (CHK-TRANSLATE INPUT)
						  (CHK-TRANSLATE OUTPUT))
					    (VCG-REDO-UNDONE-EVENTS
					     (QUOTE ((UNDO-BACK-THROUGH (QUOTE DCL-START)))))))))
       (SETQ SUBROUTINE-SPEC-ALIST
	     (ITERATE FOR PAT IN SUBROUTINE-PATTERNS WITH FORMALS AND INPUT AND OUTPUT
		      COLLECT (PROGN (MATCH! (ASSOC-CADR (ACCESS SUBROUTINE-PATTERN NAME PAT)
							 (ACCESS CONTEXT ROUTINES CONTEXT))
					     (SUBROUTINE & FORMALS & & & & & & INPUT OUTPUT 
							 & &))
				     (VCG-REDO-UNDONE-EVENTS
				      (CONS (QUOTE (FORTRAN-COMMENT DCL-START))
					    (ITERATE FOR ARG IN FORMALS
						     WHEN (NOT (MEMBER-EQ ARG (APPEND LOCALS GLOBALS))
							       )
						     COLLECT (LIST (QUOTE DCL)
								   ARG
								   (QUOTE (STATE))))))
				     (PROG1 (LIST (ACCESS SUBROUTINE-PATTERN NAME PAT)
						  (CHK-TRANSLATE INPUT)
						  (CHK-TRANSLATE OUTPUT))
					    (VCG-REDO-UNDONE-EVENTS
					     (QUOTE ((UNDO-BACK-THROUGH (QUOTE DCL-START)))))))))
       (VCG-REDO-UNDONE-EVENTS
	(ITERATE FOR FN IN CALLED-FNS UNLESS (INTRINSIC-FUNCTIONP FN)
		 COLLECT
		 (LIST (QUOTE DCL)
		       (PACK (LIST FN (QUOTE $)))
		       (APPEND (ITERATE FOR ARG
					IN (ACCESS FUNCTION-PATTERN ARG-VAR-DCLS
						   (ASSOC-CADR FN FUNCTION-PATTERNS))
					COLLECT (ACCESS VAR-DCL NAME ARG))
			       (OUR-STABLE-SORT
				(ITERATE
				 FOR BLOCK-NAME
				 IN (ACCESS FUNCTION KNOWN-BLOCK-NAMES
					    (ASSOC-CADR FN
							(ACCESS CONTEXT ROUTINES 
								CONTEXT)))
				 NCONC (ITERATE
					FOR VAR-DCL
					IN (VAR-DCLS-OF-BLOCK 
					    BLOCK-NAME)
					COLLECT (PACK (LIST BLOCK-NAME
							    (QUOTE -)
							    (ACCESS VAR-DCL NAME 
								    VAR-DCL)))))
				#'ALPHORDER))
		       ))))

(DEFUN GENERATE-VCS NIL
       (PROG (INSTR TEMP KNOWN-DEFINED EVENT-NAME VCG-PATH UNSMASHED 
		    SKOLEM-CONSTANTS VDCL)
	     (SETQ INPUT-ASSERTION
		   (SUBST-VAR
		    (QUOTE (START))
		    (QUOTE STATE)
		    (COND
		     (SUBROUTINE-FLG
		      (CONJOIN
		       (CONS TRANS-INPUT-COND
			     (ITERATE FOR VAR IN (ADJUSTABLE-DIMS)
				      COLLECT (FCONS-TERM*
					       (QUOTE NUMBERP)
					       (FCONS-TERM* VAR (QUOTE STATE))))
			     )
		       NIL))
		     (T
		      (CONJOIN
		       (CONS TRANS-INPUT-COND
			     (ITERATE FOR VAR IN ROUTINE-ARGS
				      WHEN (SETQ VDCL
						 (ASSOC-CADR VAR VARIABLE-PATTERNS))
				      COLLECT
				      (FCONS-TERM*
				       (FORTRAN-RECOGNIZER (ACCESS VAR-DCL TYPE 
								   VDCL))
				       (FCONS-TERM* VAR (QUOTE STATE)))))
		       NIL)))))
	     (SETQ OUTPUT-ASSERTION
		   (SUBST-VAR
		    (QUOTE (START))
		    (QUOTE STATE)
		    (COND
		     (SUBROUTINE-FLG TRANS-EFFECTS)
		     (T (CONJOIN2 (FCONS-TERM* (FORTRAN-RECOGNIZER
						(ACCESS VAR-DCL TYPE
							(ASSOC-CADR ROUTINE-NAME 
								    VARIABLE-PATTERNS)))
					       (FCONS-TERM* ROUTINE-NAME
							    (QUOTE NEWSTATE))
					       )
				  (SUBST-VAR (FCONS-TERM* ROUTINE-NAME
							  (QUOTE NEWSTATE))
					     (QUOTE ANS)
					     TRANS-RESULT)
				  NIL)))))
	     (SETQ ORIGINAL-CLOCKS TRANS-INPUT-CLOCKS)
	     (SETQ KNOWN-DEFINED
		   (ITERATE FOR V IN ROUTINE-ARGS
			    WHEN (AND (ASSOC-CADR V VARIABLE-PATTERNS)
				      (NOT (MEMBER-EQ V HIT-VARS)))
			    COLLECT V))
	     (SETQ UNSMASHED
		   (APPEND (ITERATE FOR ARG IN ROUTINE-ARGS
				    WHEN (NOT (MEMBER-EQ ARG HIT-VARS)) COLLECT ARG)
			   (ITERATE FOR BLOCK
				    IN (ACCESS CONTEXT COMMON-BLOCKS CONTEXT)
				    WHEN (MEMBER-EQ (ACCESS COMMON-BLOCK NAME BLOCK)
						    KNOWN-BLOCK-NAMES)
				    NCONC (ITERATE FOR VDCL
						   IN (ACCESS COMMON-BLOCK VAR-DCLS BLOCK)
						   WITH LONG-NAME
						   UNLESS (MEMBER-EQ (SETQ LONG-NAME
									   (PACK (LIST (ACCESS COMMON-BLOCK 
											       NAME BLOCK)
										       (QUOTE -)
										       (ACCESS VAR-DCL NAME 
											       VDCL))))
								     HIT-VARS)
						   COLLECT LONG-NAME))))
	     (SETQ KNOWN-VARS-ALIST
		   (APPEND (ITERATE FOR X IN VAR-DCLS
				    UNLESS (AND (MEMBER-EQ (ACCESS VAR-DCL NAME X)
							   ROUTINE-ARGS)
						(NOT (MEMBER-EQ (ACCESS VAR-DCL NAME X)
								HIT-VARS)))
				    COLLECT (CONS (ACCESS VAR-DCL NAME X)
						  (CONS (ACCESS VAR-DCL TYPE X)
							(LENGTH (ACCESS VAR-DCL SIZES X)))
						  ))
			   (ITERATE FOR BLOCK
				    IN (ACCESS CONTEXT COMMON-BLOCKS CONTEXT)
				    WHEN (MEMBER-EQ (ACCESS COMMON-BLOCK NAME BLOCK)
						    KNOWN-BLOCK-NAMES)
				    NCONC (ITERATE FOR VDCL
						   IN (ACCESS COMMON-BLOCK VAR-DCLS BLOCK)
						   WITH LONG-NAME
						   WHEN (MEMBER-EQ (SETQ LONG-NAME
									 (PACK (LIST (ACCESS COMMON-BLOCK NAME 
											     BLOCK)
										     (QUOTE -)
										     (ACCESS VAR-DCL NAME VDCL)
										     )))
								   HIT-VARS)
						   COLLECT (CONS LONG-NAME
								 (CONS (ACCESS VAR-DCL TYPE VDCL)
								       (LENGTH (ACCESS VAR-DCL 
										       SIZES 
										       VDCL))))))
			   ))
	     (SETQ VCS
		   (REVERSE
		    (APPEND
		     (QUOTE ((FORTRAN-COMMENT FORTRAN)))
		     (ITERATE FOR P IN (ACCESS CONTEXT TOKENS CONTEXT)
			      NCONC (LIST (LIST (QUOTE DCL)
						P NIL)
					  (LIST (QUOTE ADD-AXIOM)
						(PACK (LIST P (QUOTE -NUMBERP)))
						(QUOTE (REWRITE))
						(FCONS-TERM* (QUOTE NUMBERP)
							     (FCONS-TERM* P)))))
		     (ITERATE FOR TAIL ON XXX
			      WITH EV AND ANS
			      DO (PROGN 
				  (SETQ EV (CAR TAIL))
				  (SETQ ANS (APPEND ANS (COND
							 ((EQ (CAR EV)
							      (QUOTE HINT))
							  (COND
							   ((CONSP (CDR TAIL))
							    (CDDR EV))
							   (T NIL)))
							 (T (LIST EV))))))
			      FINALLY (RETURN ANS))
		     (ITERATE FOR FN IN CALLED-FNS
			      UNLESS (INTRINSIC-FUNCTIONP FN)
			      COLLECT
			      (LIST
			       (QUOTE DCL)
			       (PACK (LIST FN (QUOTE $)))
			       (APPEND
				(ITERATE FOR ARG
					 IN (ACCESS FUNCTION-PATTERN ARG-VAR-DCLS
						    (ASSOC-CADR FN FUNCTION-PATTERNS))
					 COLLECT (ACCESS VAR-DCL NAME ARG))
				(OUR-STABLE-SORT (ITERATE FOR BLOCK-NAME
							  IN (ACCESS FUNCTION KNOWN-BLOCK-NAMES
								     (ASSOC-CADR FN
										 (ACCESS CONTEXT ROUTINES 
											 CONTEXT)))
							  NCONC (ITERATE FOR VAR-DCL
									 IN (ACCESS COMMON-BLOCK VAR-DCLS
										    (ASSOC-CADR BLOCK-NAME
												(ACCESS CONTEXT 
													COMMON-BLOCKS 
													CONTEXT)))
									 COLLECT (PACK (LIST BLOCK-NAME
											     (QUOTE -)
											     (ACCESS VAR-DCL NAME 
												     VAR-DCL)))))
						 #'ALPHORDER))
			       ))
		     (GLOBAL-ASSUMPTIONS INPUT-ASSERTION)
		     (COND
		      ((EQ (CAAR (OUR-LAST XXX))
			   (QUOTE HINT))
		       (CDDR (CAR (OUR-LAST XXX))))
		      (T NIL)))))
	     (COND
	      (SUBROUTINE-FLG
	      

;   In order to reduce the number of vcs that make us prove that things that
;   obviously should be defined are in fact defined, we special case the
;   definedness vcs. The variable KNOWN-DEFINED is set above to all of the
;   variable args that are not hit.  Those variables will never occur in a
;   definedness check. Furthermore, in the input condition, in the case of a
;   FUNCTION, we assume that all of the variable args are always defined.
;   Finally, we assume, in the input condition, that all of the adjustable
;   array dimensions are always defined.


	      

;   How are these hypotheses relieved? Whenever a FUNCTION is called, all the
;   args must be defined.  And when a SUBROUTINE is called, the adjustable
;   array dimensions are known to be defined by syntactic considerations. That
;   leaves the non-array-dimension, non-hit, variable, SUBROUTINE args to be
;   handled, and we do it here.


	       (ADD-EVENT
		(QUOTE PROVE-LEMMA)
		(QUOTE INPUT-DEFINEDNESS)
		(FCONS-TERM*
		 (QUOTE IMPLIES)
		 (FCONS-TERM* (QUOTE GLOBAL-HYPS))
		 (CONJOIN (ITERATE FOR V IN (SET-DIFF KNOWN-DEFINED
						      (ADJUSTABLE-DIMS))
				   COLLECT
				   (FCONS-TERM*
				    (FORTRAN-RECOGNIZER
				     (ACCESS VAR-DCL TYPE
					     (ASSOC-CADR V VARIABLE-PATTERNS)))
				    (FCONS-TERM* V (QUOTE (START)))))
			  NIL)))))

;   We will depend upon the fact that except for labels, no two instructions we
;   process are EQ.  We also depend upon the fact that no label occurs twice.


	     (SETQ INSTR-LST (COPY-TREE TRANSLATED-FORTRAN-CODE))
	     (SETQ ASSERTION-NAME (QUOTE INPUT))
	     (SETQ INSTRS-SEEN NIL)
	     (SETQ EVENT-NAME (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					 (QUOTE INPUT)
					 NIL))
	     (VCG1 (LIST (FCONS-TERM* (QUOTE GLOBAL-HYPS)))
		   (CAR INSTR-LST)
		   (QUOTE (START))
		   NIL TRANS-INPUT-CLOCKS KNOWN-DEFINED (QUOTE (INPUT)))
	     (ADD-EVENT (QUOTE UBT)
			EVENT-NAME NIL)
	     (ITERATE WHILE TO-BE-TRACED WITH ASSERTION-NAME AND ASSN AND CLKS
		      DO (PROGN (SETQ INSTR (CAR TO-BE-TRACED))
				(SETQ TO-BE-TRACED (CDR TO-BE-TRACED))
				(SETQ TRACED (CONS INSTR TRACED))
				(MATCH! INSTR (COMMENT (QUOTE ASSERTION)
						       ASSERTION-NAME & &))
				(SETQ TEMP (ASSOC-EQ ASSERTION-NAME TRANS-INVARIANT-MAP))
				(SETQ ASSN (CADR TEMP))
				(SETQ CLKS (CADDR TEMP))
				(SETQ TEMP (FLATTEN-ANDS (SUBST-VAR (QUOTE (BEGIN))
								    (QUOTE STATE)
								    ASSN)))
				(SETQ EVENT-NAME
				      (ADD-EVENT (QUOTE ADD-AXIOM)
						 (PACK (LIST (QUOTE PATHS-FROM-)
							     ASSERTION-NAME))
						 (CONJOIN
						  (ITERATE FOR X IN TEMP
							   WHEN (OR (FREE-VARSP X NIL)
								    (MATCH X
									   (EQUAL & &)))
							   COLLECT X)
						  NIL)
						 ))
				(ADD-EVENT
				 (QUOTE DEFN)
				 (QUOTE PATH-HYPS)
				 (CONJOIN (CONS (FCONS-TERM* (QUOTE GLOBAL-HYPS))
						(ITERATE FOR X IN TEMP
							 UNLESS (OR (FREE-VARSP X NIL)
								    (MATCH X (EQUAL & &)))
							 COLLECT X))
					  NIL)
				 )
				(VCG1 (LIST (FCONS-TERM* (QUOTE PATH-HYPS)))
				      (NEXT-INSTR INSTR)
				      (QUOTE (BEGIN))
				      NIL
				      (SUBST-VAR (QUOTE (BEGIN))
						 (QUOTE STATE)
						 CLKS)
				      KNOWN-DEFINED
				      (LIST ASSERTION-NAME))
				(ADD-EVENT (QUOTE UBT)
					   EVENT-NAME NIL)))
	     (ITERATE FOR INSTR IN INSTR-LST WHEN (AND (CONSP INSTR)
						       (NOT (EQ (CAR INSTR)
								(QUOTE COMMENT))))
		      DO (OR (MEMBER-EQ INSTR INSTRS-SEEN)
			     (FORTRAN-ERROR "Inaccessible instruction" INSTR)))
	     (SETQ VCS (CONS (QUOTE (UBT FORTRAN))
			     VCS))
	     (SETQ VCS (REVERSE VCS))
	     (COND
	      ((OR (ATOM VCS)
		   (NOT (EQUAL (CAR VCS)
			       (QUOTE (FORTRAN-COMMENT FORTRAN))))))
	      (T (SETQ VCS (CONS (CAR VCS)
				 (APPEND (ITERATE FOR SKO
						  IN (OUR-STABLE-SORT SKOLEM-CONSTANTS
								      #'ALPHORDER)
						  COLLECT (LIST (QUOTE DCL)
								SKO NIL))
					 (CDR VCS))))))
	     (RETURN NIL)))

(DEFUN GLOBAL-ASSUMPTIONS (INPUT-ASSERTION)
       (PROG (TERM GROUND FREE)
	     (SETQ TERM (SKOLEMIZE-TERM INPUT-ASSERTION))
	     (ITERATE FOR X IN (FLATTEN-ANDS TERM)
		      DO (COND
			  ((OR (FREE-VARSP X NIL)
			       (MATCH X (EQUAL & &)))
			   (SETQ FREE (NCONC1 FREE X)))
			  (T (SETQ GROUND (NCONC1 GROUND X)))))
	     (RETURN
	      (LIST
	       (LIST (QUOTE ADD-AXIOM)
		     (QUOTE INPUT-CONDITIONS)
		     (QUOTE (REWRITE))
		     (CONJOIN FREE NIL))
	       (LIST
		(QUOTE DEFN)
		(QUOTE GLOBAL-HYPS)
		NIL
		(CONJOIN
		 (APPEND (ITERATE FOR P IN (ACCESS CONTEXT TOKENS CONTEXT)
				  COLLECT
				  (FCONS-TERM*
				   (QUOTE NOT)
				   (FCONS-TERM* (QUOTE EQUAL)
						(FCONS-TERM* P)
						ZERO)))
			 GROUND)
		 NIL))))))

(DEFUN GUESS-SYNTACTIC-ENVIRONMENT NIL

;   Guess the syntactic environment implicit in the ROUTINE argument of
;   CHK-ROUTINE.  When this function has been executed the following seven
;   variables are supposed to be set to the obvious components of the candidate
;   syntactic environment: ARRAY-PATTERNS VARIABLE-PATTERNS
;   LABEL-VARIABLE-PATTERNS STATEMENT-FUNCTION-PATTERNS FUNCTION-PATTERNS
;   SUBROUTINE-PATTERNS and BLOCK-NAMES. It may be the case that the settings
;   do not define a syntactic environment -- so they must be checked by
;   CHK-SYNTACTIC-ENVIRONMENT.  The only reason the code in this program has
;   been separated from CHK-ROUTINE is to reduce the size of that function and
;   to make it obvious what we are doing here.


       (SETQ ARRAY-PATTERNS (APPEND
			     (ITERATE FOR VDCL IN VAR-DCLS
				      WHEN (ACCESS VAR-DCL SIZES VDCL) COLLECT VDCL)
			     (ITERATE FOR NAME IN BLOCK-NAMES WITH ANS
				      DO (SETQ ANS (APPEND ANS (ITERATE FOR VDCL IN (VAR-DCLS-OF-BLOCK NAME)
									WHEN (ACCESS VAR-DCL SIZES VDCL)
									COLLECT VDCL
									)))
				      FINALLY (RETURN ANS))))
       (SETQ LABEL-VARIABLE-PATTERNS
	     (ITERATE FOR INSTR IN FORTRAN-CODE WITH TEMP AND ANS
		      WHEN (OR (MATCH INSTR (ASSIGN-TO & TEMP))
			       (MATCH INSTR (ASSIGNED-GOTO TEMP &))
			       (MATCH INSTR (IF-LOGICAL & (ASSIGN-TO & TEMP)))
			       (MATCH INSTR (IF-LOGICAL & (ASSIGNED-GOTO TEMP &))))
		      DO (SETQ ANS (ADD-TO-SET (ASSOC-CADR TEMP VAR-DCLS) ANS))
		      FINALLY (RETURN ANS)))
       (SETQ VARIABLE-PATTERNS
	     (SET-DIFF (APPEND (ITERATE FOR VDCL IN VAR-DCLS
					UNLESS (ACCESS VAR-DCL SIZES VDCL)
					COLLECT VDCL)
			       (ITERATE FOR NAME IN BLOCK-NAMES WITH ANS
					DO (SETQ ANS (APPEND ANS
							     (ITERATE FOR VDCL
								      IN (VAR-DCLS-OF-BLOCK NAME)
								      UNLESS (ACCESS VAR-DCL SIZES VDCL)
								      COLLECT VDCL)))
					FINALLY (RETURN ANS)))
		       LABEL-VARIABLE-PATTERNS))

;   Observe the theorem: entities in the blocks named by BLOCK-NAMES + those
;   declared in VAR-DCLS = ARRAY-PATTERNS + VARIABLE-PATTERNS +
;   LABEL-VARIABLE-PATTERNS.


       (SETQ FUNCTION-PATTERNS
	     (ITERATE FOR NAME IN CALLED-FNS WITH TEMP
		      COLLECT (COND
			       ((INTRINSIC-FUNCTION-PATTERN NAME))
			       ((AND (SETQ TEMP (ASSOC-CADR NAME
							    (ACCESS CONTEXT ROUTINES 
								    CONTEXT)))
				     (EQ (CAR TEMP)
					 (QUOTE FUNCTION)))
				(MAKE FUNCTION-PATTERN NAME (ACCESS FUNCTION TYPE TEMP)
				      (ITERATE FOR ARG IN (ACCESS FUNCTION ARGS TEMP)
					       COLLECT (ASSOC-CADR ARG
								   (ACCESS FUNCTION VAR-DCLS 
									   TEMP)))))
			       (T (FORTRAN-ERROR "Unrecognized fn in CALLED-FNS" NAME)))))
       (SETQ SUBROUTINE-PATTERNS
	     (ITERATE FOR NAME IN (ITERATE FOR INSTR IN FORTRAN-CODE WITH TEMP AND ANS
					   WHEN (OR (MATCH INSTR (CALL TEMP &))
						    (MATCH INSTR (IF-LOGICAL & (CALL TEMP &))
							   ))
					   DO (SETQ ANS (ADD-TO-SET TEMP ANS))
					   FINALLY (RETURN ANS))
		      WITH TEMP
		      COLLECT (PROGN (SETQ TEMP (ASSOC-CADR NAME
							    (ACCESS CONTEXT ROUTINES CONTEXT)))
				     (OR (AND TEMP (EQ (CAR TEMP)
						       (QUOTE SUBROUTINE)))
					 (FORTRAN-ERROR "Unrecognized subr called" NAME))
				     (MAKE SUBROUTINE-PATTERN NAME
					   (ITERATE FOR ARG IN (ACCESS SUBROUTINE ARGS TEMP)
						    COLLECT (ASSOC-CADR ARG
									(ACCESS SUBROUTINE VAR-DCLS 
										TEMP))))))))

(DEFUN IMPLICATE (HYP CONCL)
       (COND
	((FALSE-NONFALSEP CONCL)
	 (COND
	  (DEFINITELY-FALSE (NEGATE HYP))
	  (T TRUE)))
	((FALSE-NONFALSEP HYP)
	 (COND
	  (DEFINITELY-FALSE TRUE)
	  (T CONCL)))
	(T (FCONS-TERM*(QUOTE IMPLIES)
		       HYP CONCL))))

(DEFUN INCARCERATES (TERM SET FNS)
       (AND (NOT (MEMBER-EQUAL TERM SET))
	    (ITERATE FOR T1 IN (SUBTERMS-THAT-USE SET TERM)
		     ALWAYS (COND
			     ((MEMBER-EQ (FFN-SYMB T1)
					 FNS)
			      T)
			     (T (FORTRAN-ERROR "First not in second:"
					       (LIST (FFN-SYMB T1)
						     FNS))
				NIL)))
	    (ITERATE FOR T1 IN (SUBTERMS-THAT-CALL FNS TERM)
		     ALWAYS (COND
			     ((MEMBER-EQUAL (FARGN T1 1)
					    SET)
			      T)
			     (T (FORTRAN-ERROR "First not in second:"
					       (LIST (FARGN T1 1)
						     SET))
				NIL)))))

(DEFUN INFIX-FUNCTION-PATTERN (X)
       (CASE X
	     (ZPLUS (QUOTE (FUNCTION-PATTERN ZPLUS INTEGER
					     ((VAR-DCL I INTEGER NIL)
					      (VAR-DCL J INTEGER NIL)))
			   ))
	     (RPLUS (QUOTE (FUNCTION-PATTERN RPLUS REAL
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (DPLUS (QUOTE (FUNCTION-PATTERN DPLUS DOUBLE
					     ((VAR-DCL I DOUBLE NIL)
					      (VAR-DCL J DOUBLE NIL))))
		    )
	     (CPLUS (QUOTE (FUNCTION-PATTERN CPLUS COMPLEX
					     ((VAR-DCL I COMPLEX NIL)
					      (VAR-DCL J COMPLEX NIL)))
			   ))
	     (ZDIFFERENCE (QUOTE (FUNCTION-PATTERN ZDIFFERENCE INTEGER
						   ((VAR-DCL I INTEGER 
							     NIL)
						    (VAR-DCL J INTEGER 
							     NIL)))))
	     (RDIFFERENCE (QUOTE (FUNCTION-PATTERN RDIFFERENCE REAL
						   ((VAR-DCL I REAL 
							     NIL)
						    (VAR-DCL J REAL 
							     NIL)))))
	     (DDIFFERENCE (QUOTE (FUNCTION-PATTERN DDIFFERENCE DOUBLE
						   ((VAR-DCL I DOUBLE 
							     NIL)
						    (VAR-DCL J DOUBLE 
							     NIL)))))
	     (CDIFFERENCE (QUOTE (FUNCTION-PATTERN CDIFFERENCE COMPLEX
						   ((VAR-DCL I COMPLEX 
							     NIL)
						    (VAR-DCL J COMPLEX 
							     NIL)))))
	     (ZTIMES (QUOTE (FUNCTION-PATTERN ZTIMES INTEGER
					      ((VAR-DCL I INTEGER NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (RTIMES (QUOTE (FUNCTION-PATTERN RTIMES REAL
					      ((VAR-DCL I REAL NIL)
					       (VAR-DCL J REAL NIL)))))
	     (DTIMES (QUOTE (FUNCTION-PATTERN DTIMES DOUBLE
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J DOUBLE NIL)))
			    ))
	     (CTIMES (QUOTE (FUNCTION-PATTERN CTIMES COMPLEX
					      ((VAR-DCL I COMPLEX NIL)
					       (VAR-DCL J COMPLEX NIL))
					      )))
	     (ZQUOTIENT (QUOTE (FUNCTION-PATTERN ZQUOTIENT INTEGER
						 ((VAR-DCL I INTEGER 
							   NIL)
						  (VAR-DCL J INTEGER 
							   NIL)))))
	     (RQUOTIENT (QUOTE (FUNCTION-PATTERN RQUOTIENT REAL
						 ((VAR-DCL I REAL NIL)
						  (VAR-DCL J REAL NIL))
						 )))
	     (DQUOTIENT (QUOTE (FUNCTION-PATTERN DQUOTIENT DOUBLE
						 ((VAR-DCL I DOUBLE 
							   NIL)
						  (VAR-DCL J DOUBLE 
							   NIL)))))
	     (CQUOTIENT (QUOTE (FUNCTION-PATTERN CQUOTIENT COMPLEX
						 ((VAR-DCL I COMPLEX 
							   NIL)
						  (VAR-DCL J COMPLEX 
							   NIL)))))
	     (ZEXPTZ (QUOTE (FUNCTION-PATTERN ZEXPTZ INTEGER
					      ((VAR-DCL I INTEGER NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (REXPTZ (QUOTE (FUNCTION-PATTERN REXPTZ REAL
					      ((VAR-DCL I REAL NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (DEXPTZ (QUOTE (FUNCTION-PATTERN DEXPTZ DOUBLE
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (CEXPTZ (QUOTE (FUNCTION-PATTERN CEXPTZ COMPLEX
					      ((VAR-DCL I COMPLEX NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (REXPTR (QUOTE (FUNCTION-PATTERN REXPTR REAL
					      ((VAR-DCL I REAL NIL)
					       (VAR-DCL J REAL NIL)))))
	     (REXPTD (QUOTE (FUNCTION-PATTERN REXPTD DOUBLE
					      ((VAR-DCL I REAL NIL)
					       (VAR-DCL J DOUBLE NIL)))
			    ))
	     (DEXPTR (QUOTE (FUNCTION-PATTERN DEXPTR DOUBLE
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J REAL NIL)))))
	     (DEXPTD (QUOTE (FUNCTION-PATTERN DEXPTD DOUBLE
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J DOUBLE NIL)))
			    ))
	     (TRUE (QUOTE (FUNCTION-PATTERN TRUE LOGICAL NIL)))
	     (FALSE (QUOTE (FUNCTION-PATTERN FALSE LOGICAL NIL)))
	     (ZLESSP (QUOTE (FUNCTION-PATTERN ZLESSP LOGICAL
					      ((VAR-DCL I INTEGER NIL)
					       (VAR-DCL J INTEGER NIL))
					      )))
	     (RLESSP (QUOTE (FUNCTION-PATTERN RLESSP LOGICAL
					      ((VAR-DCL I REAL NIL)
					       (VAR-DCL J REAL NIL)))))
	     (DLESSP (QUOTE (FUNCTION-PATTERN DLESSP LOGICAL
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J DOUBLE NIL)))
			    ))
	     (ZLESSEQP (QUOTE (FUNCTION-PATTERN ZLESSEQP LOGICAL
						((VAR-DCL I INTEGER 
							  NIL)
						 (VAR-DCL J INTEGER 
							  NIL)))))
	     (RLESSEQP (QUOTE (FUNCTION-PATTERN RLESSEQP LOGICAL
						((VAR-DCL I REAL NIL)
						 (VAR-DCL J REAL NIL)))
			      ))
	     (DLESSEQP (QUOTE (FUNCTION-PATTERN DLESSEQP LOGICAL
						((VAR-DCL I DOUBLE NIL)
						 (VAR-DCL J DOUBLE NIL)
						 ))))
	     (ZEQP (QUOTE (FUNCTION-PATTERN ZEQP LOGICAL
					    ((VAR-DCL I INTEGER NIL)
					     (VAR-DCL J INTEGER NIL))))
		   )
	     (REQP (QUOTE (FUNCTION-PATTERN REQP LOGICAL
					    ((VAR-DCL I REAL NIL)
					     (VAR-DCL J REAL NIL)))))
	     (DEQP (QUOTE (FUNCTION-PATTERN DEQP LOGICAL
					    ((VAR-DCL I DOUBLE NIL)
					     (VAR-DCL J DOUBLE NIL)))))
	     (CEQP (QUOTE (FUNCTION-PATTERN CEQP LOGICAL
					    ((VAR-DCL I COMPLEX NIL)
					     (VAR-DCL J COMPLEX NIL))))
		   )
	     (ZNEQP (QUOTE (FUNCTION-PATTERN ZNEQP LOGICAL
					     ((VAR-DCL I INTEGER NIL)
					      (VAR-DCL J INTEGER NIL)))
			   ))
	     (RNEQP (QUOTE (FUNCTION-PATTERN RNEQP LOGICAL
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (DNEQP (QUOTE (FUNCTION-PATTERN DNEQP LOGICAL
					     ((VAR-DCL I DOUBLE NIL)
					      (VAR-DCL J DOUBLE NIL))))
		    )
	     (CNEQP (QUOTE (FUNCTION-PATTERN CNEQP LOGICAL
					     ((VAR-DCL I COMPLEX NIL)
					      (VAR-DCL J COMPLEX NIL)))
			   ))
	     (ZGREATERP (QUOTE (FUNCTION-PATTERN ZGREATERP LOGICAL
						 ((VAR-DCL I INTEGER 
							   NIL)
						  (VAR-DCL J INTEGER 
							   NIL)))))
	     (RGREATERP (QUOTE (FUNCTION-PATTERN RGREATERP LOGICAL
						 ((VAR-DCL I REAL NIL)
						  (VAR-DCL J REAL NIL))
						 )))
	     (DGREATERP (QUOTE (FUNCTION-PATTERN DGREATERP LOGICAL
						 ((VAR-DCL I DOUBLE 
							   NIL)
						  (VAR-DCL J DOUBLE 
							   NIL)))))
	     (ZGREATEREQP (QUOTE (FUNCTION-PATTERN ZGREATEREQP LOGICAL
						   ((VAR-DCL I INTEGER 
							     NIL)
						    (VAR-DCL J INTEGER 
							     NIL)))))
	     (RGREATEREQP (QUOTE (FUNCTION-PATTERN RGREATEREQP LOGICAL
						   ((VAR-DCL I REAL 
							     NIL)
						    (VAR-DCL J REAL 
							     NIL)))))
	     (DGREATEREQP (QUOTE (FUNCTION-PATTERN DGREATEREQP LOGICAL
						   ((VAR-DCL I DOUBLE 
							     NIL)
						    (VAR-DCL J DOUBLE 
							     NIL)))))
	     (NOT (QUOTE (FUNCTION-PATTERN NOT LOGICAL
					   ((VAR-DCL I LOGICAL NIL)))))
	     (AND (QUOTE (FUNCTION-PATTERN
			  AND LOGICAL ((VAR-DCL I LOGICAL NIL)
				       (VAR-DCL J LOGICAL NIL)))))
	     (OR (QUOTE (FUNCTION-PATTERN
			 OR LOGICAL ((VAR-DCL I LOGICAL NIL)
				     (VAR-DCL J LOGICAL NIL)))))
	     (OTHERWISE NIL)))

(DEFUN INFIX-OP (X)
       (CASE X
	     (ZLESSP (QUOTE .LT.))
	     (RLESSP (QUOTE .LT.))
	     (DLESSP (QUOTE .LT.))
	     (ZLESSEQP (QUOTE .LE.))
	     (RLESSEQP (QUOTE .LE.))
	     (DLESSEQP (QUOTE .LE.))
	     (ZEQP (QUOTE .EQ.))
	     (REQP (QUOTE .EQ.))
	     (DEQP (QUOTE .EQ.))
	     (CEQP (QUOTE .EQ.))
	     (ZNEQP (QUOTE .NE.))
	     (RNEQP (QUOTE .NE.))
	     (DNEQP (QUOTE .NE.))
	     (CNEQP (QUOTE .NE.))
	     (ZGREATERP (QUOTE .GT.))
	     (RGREATERP (QUOTE .GT.))
	     (DGREATERP (QUOTE .GT.))
	     (ZGREATEREQP (QUOTE .GE.))
	     (RGREATEREQP (QUOTE .GE.))
	     (DGREATEREQP (QUOTE .GE.))
	     (OR (QUOTE .OR.))
	     (AND (QUOTE .AND.))
	     (ZPLUS (QUOTE +))
	     (RPLUS (QUOTE +))
	     (DPLUS (QUOTE +))
	     (CPLUS (QUOTE +))
	     (ZDIFFERENCE (QUOTE -))
	     (RDIFFERENCE (QUOTE -))
	     (DDIFFERENCE (QUOTE -))
	     (CDIFFERENCE (QUOTE -))
	     (ZTIMES (QUOTE *))
	     (RTIMES (QUOTE *))
	     (DTIMES (QUOTE *))
	     (CTIMES (QUOTE *))
	     (ZQUOTIENT '/)
	     (RQUOTIENT '/)
	     (DQUOTIENT '/)
	     (CQUOTIENT '/)
	     (ZEXPTZ (QUOTE **))
	     (REXPTZ (QUOTE **))
	     (DEXPTZ (QUOTE **))
	     (CEXPTZ (QUOTE **))
	     (REXPTR (QUOTE **))
	     (REXPTD (QUOTE **))
	     (DEXPTR (QUOTE **))
	     (DEXPTD (QUOTE **))
	     (OTHERWISE NIL)))

(DEFUN INTEGER-EXPRP (X)
       (EQUAL (SORT-OF X)
	      INTEGER-SORT))

(DEFUN INTERSECTION-CADR (X Y)
       (ITERATE FOR A IN X  WHEN (ASSOC-CADR (CADR A)
					     Y)
		COLLECT (CADR A)))

(DEFUN INTRINSIC-FUNCTION-PATTERN (X)
       (CASE X
	     (ABS (QUOTE (FUNCTION-PATTERN ABS REAL
					   ((VAR-DCL I REAL NIL)))))
	     (IABS (QUOTE (FUNCTION-PATTERN IABS INTEGER
					    ((VAR-DCL I INTEGER NIL))))
		   )
	     (DABS (QUOTE (FUNCTION-PATTERN DABS DOUBLE
					    ((VAR-DCL I DOUBLE NIL)))))
	     (AINT (QUOTE (FUNCTION-PATTERN AINT REAL
					    ((VAR-DCL I REAL NIL)))))
	     (INT (QUOTE (FUNCTION-PATTERN INT INTEGER
					   ((VAR-DCL I REAL NIL)))))
	     (IDINT (QUOTE (FUNCTION-PATTERN IDINT INTEGER
					     ((VAR-DCL I DOUBLE NIL))))
		    )
	     (AMOD (QUOTE (FUNCTION-PATTERN AMOD REAL
					    ((VAR-DCL I REAL NIL)
					     (VAR-DCL J REAL NIL)))))
	     (MOD (QUOTE (FUNCTION-PATTERN MOD INTEGER
					   ((VAR-DCL I INTEGER NIL)
					    (VAR-DCL J INTEGER NIL)))))
	     (AMAX0 (QUOTE (FUNCTION-PATTERN AMAX0 REAL
					     ((VAR-DCL I INTEGER NIL)
					      (VAR-DCL J INTEGER NIL)))
			   ))
	     (AMAX1 (QUOTE (FUNCTION-PATTERN AMAX1 REAL
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (MAX0 (QUOTE (FUNCTION-PATTERN MAX0 INTEGER
					    ((VAR-DCL I INTEGER NIL)
					     (VAR-DCL J INTEGER NIL))))
		   )
	     (MAX1 (QUOTE (FUNCTION-PATTERN MAX1 INTEGER
					    ((VAR-DCL I REAL NIL)
					     (VAR-DCL J REAL NIL)))))
	     (DMAX1 (QUOTE (FUNCTION-PATTERN DMAX1 DOUBLE
					     ((VAR-DCL I DOUBLE NIL)
					      (VAR-DCL J DOUBLE NIL))))
		    )
	     (AMIN0 (QUOTE (FUNCTION-PATTERN AMIN0 REAL
					     ((VAR-DCL I INTEGER NIL)
					      (VAR-DCL J INTEGER NIL)))
			   ))
	     (AMIN1 (QUOTE (FUNCTION-PATTERN AMIN1 REAL
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (MIN0 (QUOTE (FUNCTION-PATTERN MIN0 INTEGER
					    ((VAR-DCL I INTEGER NIL)
					     (VAR-DCL J INTEGER NIL))))
		   )
	     (MIN1 (QUOTE (FUNCTION-PATTERN MIN1 INTEGER
					    ((VAR-DCL I REAL NIL)
					     (VAR-DCL J REAL NIL)))))
	     (DMIN1 (QUOTE (FUNCTION-PATTERN DMIN1 DOUBLE
					     ((VAR-DCL I DOUBLE NIL)
					      (VAR-DCL J DOUBLE NIL))))
		    )
	     (FLOAT (QUOTE (FUNCTION-PATTERN FLOAT REAL
					     ((VAR-DCL I INTEGER NIL)))
			   ))
	     (IFIX (QUOTE (FUNCTION-PATTERN IFIX INTEGER
					    ((VAR-DCL I REAL NIL)))))
	     (SIGN (QUOTE (FUNCTION-PATTERN SIGN REAL
					    ((VAR-DCL I REAL NIL)
					     (VAR-DCL J REAL NIL)))))
	     (ISIGN (QUOTE (FUNCTION-PATTERN ISIGN INTEGER
					     ((VAR-DCL I INTEGER NIL)
					      (VAR-DCL J INTEGER NIL)))
			   ))
	     (DSIGN (QUOTE (FUNCTION-PATTERN DSIGN DOUBLE
					     ((VAR-DCL I DOUBLE NIL)
					      (VAR-DCL J DOUBLE NIL))))
		    )
	     (DIM (QUOTE (FUNCTION-PATTERN DIM REAL
					   ((VAR-DCL I REAL NIL)
					    (VAR-DCL J REAL NIL)))))
	     (IDIM (QUOTE (FUNCTION-PATTERN IDIM INTEGER
					    ((VAR-DCL I INTEGER NIL)
					     (VAR-DCL J INTEGER NIL))))
		   )
	     (SNGL (QUOTE (FUNCTION-PATTERN SNGL REAL
					    ((VAR-DCL I DOUBLE NIL)))))
	     (REAL (QUOTE (FUNCTION-PATTERN REAL REAL
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (AIMAG (QUOTE (FUNCTION-PATTERN AIMAG REAL
					     ((VAR-DCL I COMPLEX NIL)))
			   ))
	     (DBLE (QUOTE (FUNCTION-PATTERN DBLE DOUBLE
					    ((VAR-DCL I REAL NIL)))))
	     (CMPLX (QUOTE (FUNCTION-PATTERN CMPLX COMPLEX
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (CONJG (QUOTE (FUNCTION-PATTERN CONJG COMPLEX
					     ((VAR-DCL I COMPLEX NIL)))
			   ))
	     (EXP (QUOTE (FUNCTION-PATTERN EXP REAL
					   ((VAR-DCL I REAL NIL)))))
	     (DEXP (QUOTE (FUNCTION-PATTERN DEXP DOUBLE
					    ((VAR-DCL I DOUBLE NIL)))))
	     (CEXP (QUOTE (FUNCTION-PATTERN CEXP COMPLEX
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (ALOG (QUOTE (FUNCTION-PATTERN ALOG REAL
					    ((VAR-DCL I REAL NIL)))))
	     (DLOG (QUOTE (FUNCTION-PATTERN DLOG DOUBLE
					    ((VAR-DCL I DOUBLE NIL)))))
	     (CLOG (QUOTE (FUNCTION-PATTERN CLOG COMPLEX
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (ALOG10 (QUOTE (FUNCTION-PATTERN ALOG10 REAL
					      ((VAR-DCL I REAL NIL)))))
	     (DLOG10 (QUOTE (FUNCTION-PATTERN DLOG10 DOUBLE
					      ((VAR-DCL I DOUBLE NIL)))
			    ))
	     (SIN (QUOTE (FUNCTION-PATTERN SIN REAL
					   ((VAR-DCL I REAL NIL)))))
	     (DSIN (QUOTE (FUNCTION-PATTERN DSIN DOUBLE
					    ((VAR-DCL I DOUBLE NIL)))))
	     (CSIN (QUOTE (FUNCTION-PATTERN CSIN COMPLEX
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (COS (QUOTE (FUNCTION-PATTERN COS REAL
					   ((VAR-DCL I REAL NIL)))))
	     (DCOS (QUOTE (FUNCTION-PATTERN DCOS DOUBLE
					    ((VAR-DCL I DOUBLE NIL)))))
	     (CCOS (QUOTE (FUNCTION-PATTERN CCOS COMPLEX
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (TANH (QUOTE (FUNCTION-PATTERN TANH REAL
					    ((VAR-DCL I REAL NIL)))))
	     (SQRT (QUOTE (FUNCTION-PATTERN SQRT REAL
					    ((VAR-DCL I REAL NIL)))))
	     (DSQRT (QUOTE (FUNCTION-PATTERN DSQRT DOUBLE
					     ((VAR-DCL I DOUBLE NIL))))
		    )
	     (CSQRT (QUOTE (FUNCTION-PATTERN CSQRT COMPLEX
					     ((VAR-DCL I COMPLEX NIL)))
			   ))
	     (ATAN (QUOTE (FUNCTION-PATTERN ATAN REAL
					    ((VAR-DCL I REAL NIL)))))
	     (DATAN (QUOTE (FUNCTION-PATTERN DATAN DOUBLE
					     ((VAR-DCL I DOUBLE NIL))))
		    )
	     (ATAN2 (QUOTE (FUNCTION-PATTERN ATAN2 REAL
					     ((VAR-DCL I REAL NIL)
					      (VAR-DCL J REAL NIL)))))
	     (DATAN2 (QUOTE (FUNCTION-PATTERN DATAN2 DOUBLE
					      ((VAR-DCL I DOUBLE NIL)
					       (VAR-DCL J DOUBLE NIL)))
			    ))
	     (DMOD (QUOTE (FUNCTION-PATTERN DMOD DOUBLE
					    ((VAR-DCL I DOUBLE NIL)
					     (VAR-DCL J DOUBLE NIL)))))
	     (CABS (QUOTE (FUNCTION-PATTERN CABS REAL
					    ((VAR-DCL I COMPLEX NIL))))
		   )
	     (OTHERWISE NIL)))

(DEFUN INTRINSIC-FUNCTIONP (X)
       (MEMBER-EQ X
		  (QUOTE (ABS IABS DABS AINT INT IDINT AMOD MOD AMAX0 AMAX1 
			      MAX0 MAX1 DMAX1 AMIN0 AMIN1 MIN0 MIN1 DMIN1 
			      FLOAT IFIX SIGN ISIGN DSIGN DIM IDIM SNGL REAL 
			      AIMAG DBLE CMPLX CONJG EXP DEXP CEXP ALOG DLOG 
			      CLOG ALOG10 DLOG10 SIN DSIN CSIN COS DCOS CCOS 
			      TANH SQRT DSQRT CSQRT ATAN DATAN ATAN2 DATAN2 
			      DMOD CABS))))

(DEFUN LONG-NAME (X)
       (PROG (BLK)
	     (RETURN (COND
		      ((ITERATE FOR NAME IN BLOCK-NAMES
				THEREIS (COND
					 ((ASSOC-CADR X
						      (VAR-DCLS-OF-BLOCK NAME))
					  (SETQ BLK NAME)
					  T)
					 (T NIL)))
		       (PACK (LIST BLK (QUOTE -)
				   X)))
		      (T X)))))

(DEFUN MC-FLATTEN (X ANS)
       (COND
	((CONSP X)
	 (MC-FLATTEN (CAR X)
		     (MC-FLATTEN (CDR X)
				 ANS)))
	(T (CONS X ANS))))

(DEFUN NEXT-DEPTH (TERM)
       (CASE (FFN-SYMB TERM)
	     (START 0)
	     (BEGIN 1)
	     (OTHERWISE (1+ (NEXT-DEPTH (FARGN TERM 1))))))

(DEFUN NEXT-INSTR (X)
       (SETQ TEMP-TEMP (MEMBER-EQ X INSTR-LST))
       (COND
	(TEMP-TEMP (OR (CONSP (CDR TEMP-TEMP))
		       (FORTRAN-ERROR 
			"Each path must end with a STOP or RETURN."
			X))
		   (CADR TEMP-TEMP))
	((SETQ TEMP-TEMP (ITERATE FOR I IN INSTR-LST WHEN (CONSP I)
				  WHEN (AND (EQ (CAR I)
						(QUOTE IF-LOGICAL))
					    (EQ (CADDR I)
						X))
				  DO (RETURN I)))
	 (SETQ TEMP-TEMP (MEMBER-EQ TEMP-TEMP INSTR-LST))
	 (OR (CONSP (CDR TEMP-TEMP))
	     (FORTRAN-ERROR "Each path must end with a RETURN or STOP." X))
	 (CADR TEMP-TEMP))
	(T (ERROR ""))))

(DEFUN NO-DUPLICATE-CADRSP (LST)
       (ITERATE FOR TAIL ON LST NEVER (ASSOC-CADR (CADR (CAR TAIL))
						  (CDR TAIL))))

(DEFUN NONARG-LOCAL-NAMEP (X)
       (AND (ASSOC-CADR X VAR-DCLS)
	    (NOT (MEMBER-EQ X ROUTINE-ARGS))))

(DEFUN PERM (X Y)
       (COND
	((ATOM X)
	 (ATOM Y))
	(T (AND (MEMBER-EQUAL (CAR X)
			      Y)
		(PERM (CDR X)
		      (REMOVE (CAR X)
			      Y :TEST #'EQUAL))))))

(DEFUN PLISTP (X)
       (COND
	((ATOM X)
	 (NULL X))
	(T (PLISTP (CDR X)))))

(DEFUN PP-AS-COMMENT (FORMULA)
       (IPRINC (QUOTE C) NIL)
       (PSPACES 5)
       (PPRIND FORMULA 6 0 NIL)
       (ITERPRI NIL))

(DEFUN PRE-COLON (X)
       (PACK (ITERATE FOR C IN (OUR-EXPLODEC X) UNTIL (EQ C (QUOTE $))
		      COLLECT C)))

(DEFUN PRIN (X)
       (SETQ X (PACK (LIST X)))
       (ITERATE FOR I FROM 1 TO (OUR-FLATC X)
		DO (PROGN (COND
			   ((> (IPOSITION NIL NIL NIL)
			       71)
			    (COND ((NOT PRINTING-A-COMMENT)
				   (SETQ CONTINUATION-LINE-CNT (1+ CONTINUATION-LINE-CNT))
				   (COND ((= CONTINUATION-LINE-CNT 20)
					  (FORTRAN-ERROR
					   "Won't fit in 20 continuation lines." NIL)))
				   (ITERPRI NIL)
				   (ISPACES 5 NIL)
				   (IPRINC "." NIL))
				  (T (ITERPRI NIL)
				     (IPRINC "C" NIL)
				     (ISPACES 5 NIL)))))
			  (IPRINC (OUR-GETCHAR X I) NIL))))

(DEFUN PRIN-CODE (INSTRS)
       (ITERATE FOR INSTR IN INSTRS
		DO (COND
		    ((ATOM INSTR)
		     (PRIN INSTR))
		    (T (OR (EQ (CAR INSTR)
			       (QUOTE COMMENT))
			   (PSPACES (- 6 (IPOSITION NIL NIL NIL))))
		       (PRIN-INSTR INSTR)))))

(DEFUN PRIN-COMMON-BLOCK (BLOCK)
       (PSPACES 6)
       (PRIN (QUOTE COMMON))
       (PSPACES 1)
       (PRIN '/)
       (PRIN (ACCESS COMMON-BLOCK NAME BLOCK))
       (PRIN '/)
       (ITERATE FOR TAIL ON (ACCESS COMMON-BLOCK VAR-DCLS BLOCK)
		DO (PROGN (PRIN (ACCESS VAR-DCL NAME (CAR TAIL)))
			  (COND
			   ((CDR TAIL)
			    (PRIN COMMA-SPACE)))))
       (ITERPRI NIL))

(DEFUN PRIN-DIMENSION-STMTS (VAR-DCLS)
       (ITERATE FOR VDCL IN VAR-DCLS WHEN (ACCESS VAR-DCL SIZES VDCL)
		DO (PROGN (PSPACES 6)
			  (PRIN (QUOTE DIMENSION))
			  (PSPACES 1)
			  (PRIN (ACCESS VAR-DCL NAME VDCL))
			  (PRIN (QUOTE |(|))
			  (ITERATE FOR TAIL ON (ACCESS VAR-DCL SIZES VDCL)
				   DO (PROGN (PRIN (CAR TAIL))
					     (COND
					      ((CDR TAIL)
					       (PRIN COMMA-SPACE)))))
			  (PRIN (QUOTE |)|))
			  (ITERPRI NIL))))

(DEFUN PRIN-EXPR (EXPR)
       (PROG (TEMP DIGITS)
	     (COND
	      ((ATOM EXPR)
	       (PRIN EXPR))
	      ((OR (EQ (CAR EXPR)
		       (QUOTE ^))
		   (EQ (CAR EXPR)
		       (QUOTE ^^)))
	       (SETQ DIGITS (OUR-EXPLODEC (CADR EXPR)))
	       (COND
		((EQ (CAR DIGITS)
		     (QUOTE -))
		 (PRIN (QUOTE -))
		 (SETQ DIGITS (CDR DIGITS))))
	       (COND
		((< (CADDR EXPR)
		    0)
		 (ITERATE WHILE (<= (LENGTH DIGITS)
				    (- (CADDR EXPR)))
			  DO (SETQ DIGITS (CONS 0 DIGITS)))
		 (ITERATE FOR DIGIT IN DIGITS AS I FROM 1
			  DO (PROGN (COND
				     ((EQUAL (- I (CADDR EXPR))
					     (1+ (LENGTH DIGITS)))
				      (PRIN (QUOTE -))))
				    (PRIN DIGIT))))
		(T (PRIN (CADR EXPR))
		   (ITERATE FOR I FROM 1 TO (CADDR EXPR) DO (PRIN 0))
		   (PRIN (QUOTE -))
		   (PRIN 0)))
	       (PRIN (COND
		      ((EQ (CAR EXPR)
			   (QUOTE ^))
		       (QUOTE E))
		      (T (QUOTE D))))
	       (PRIN (CADDDR EXPR)))
	      ((EQ (CAR EXPR)
		   (QUOTE |^,^|))
	       (PRIN (QUOTE |(|))
	       (PRIN-EXPR (CADR EXPR))
	       (PRIN COMMA-SPACE)
	       (PRIN-EXPR (CADDR EXPR))
	       (PRIN (QUOTE |)|)))
	      ((EQ (CAR EXPR)
		   (QUOTE NOT))
	       (PRIN ".NOT.")
	       (PRIN (QUOTE |(|))
	       (PRIN-EXPR (CADR EXPR))
	       (PRIN (QUOTE |)|)))
	      ((EQ (CAR EXPR)
		   (QUOTE TRUE))
	       (PRIN ".TRUE."))
	      ((EQ (CAR EXPR)
		   (QUOTE FALSE))
	       (PRIN ".FALSE."))
	      ((SETQ TEMP (INFIX-OP (CAR EXPR)))
	       (PRIN (QUOTE |(|))
	       (PRIN-EXPR (CADR EXPR))
	       (PSPACES 1)
	       (PRIN TEMP)
	       (PSPACES 1)
	       (PRIN-EXPR (CADDR EXPR))
	       (PRIN (QUOTE |)|)))
	      (T (PRIN (CAR EXPR))
		 (PRIN (QUOTE |(|))
		 (ITERATE FOR TAIL ON (CDR EXPR)
			  DO (PROGN (PRIN-EXPR (CAR TAIL))
				    (COND
				     ((CDR TAIL)
				      (PRIN COMMA-SPACE)))))
		 (PRIN (QUOTE |)|))))
	     (RETURN NIL)))

(DEFUN PRIN-EXTERNALS (FNS)
       (ITERATE FOR FN IN FNS DO (PROGN (PSPACES 6)
					(PRIN (QUOTE EXTERNAL))
					(PSPACES 1)
					(IPRINC FN NIL)
					(ITERPRI NIL))))

(DEFUN PRIN-INSTR (INSTR)
       (PROG (ETC- VAR EXPR LABEL V1 V2 V3 V4 L1 L2 L3 NAME ARGLIST 
		   LABEL-LST CONTINUATION-LINE-CNT)
	     (SETQ CONTINUATION-LINE-CNT 0)
	     (COND
	      ((MATCH INSTR (CONS (QUOTE COMMENT)
				  ETC-))
	       (PRINT-COMMENT ETC-)
	       (RETURN NIL))
	      ((MATCH INSTR (ASSIGNMENT VAR EXPR))
	       (PRIN-EXPR VAR)
	       (PSPACES 1)
	       (PRIN (QUOTE =))
	       (PSPACES 1)
	       (PRIN-EXPR EXPR))
	      ((MATCH INSTR (DO LABEL V1 V2 V3 V4))
	       (PRIN (QUOTE DO))
	       (PSPACES 1)
	       (PRIN LABEL)
	       (PSPACES 1)
	       (PRIN V1)
	       (PSPACES 1)
	       (PRIN (QUOTE =))
	       (PSPACES 1)
	       (PRIN V2)
	       (PRIN COMMA-SPACE)
	       (PRIN V3)
	       (COND
		((NOT (EQUAL V4 1))
		 (PRIN COMMA-SPACE)
		 (PRIN V4))))
	      ((MATCH INSTR (GOTO LABEL))
	       (PRIN (QUOTE GOTO))
	       (PSPACES 1)
	       (PRIN LABEL))
	      ((MATCH INSTR (IF-ARITHMETIC EXPR L1 L2 L3))
	       (PRIN (QUOTE IF))
	       (PSPACES 1)
	       (PRIN (QUOTE |(|))
	       (PRIN-EXPR EXPR)
	       (PRIN (QUOTE |)|))
	       (PSPACES 1)
	       (PRIN L1)
	       (PRIN COMMA-SPACE)
	       (PRIN L2)
	       (PRIN COMMA-SPACE)
	       (PRIN L3))
	      ((MATCH INSTR (IF-LOGICAL EXPR INSTR))
	       (PRIN (QUOTE IF))
	       (PSPACES 1)
	       (PRIN (QUOTE |(|))
	       (PRIN-EXPR EXPR)
	       (PRIN (QUOTE |)|))
	       (PSPACES 1)
	       (PRIN-INSTR INSTR)
	       (RETURN NIL))
	      ((MATCH INSTR (CALL NAME ARGLIST))
	       (PRIN (QUOTE CALL))
	       (PSPACES 1)
	       (PRIN NAME)
	       (COND
		(ARGLIST (PRIN (QUOTE |(|))
			 (ITERATE FOR TAIL ON ARGLIST
				  DO (PROGN (PRIN-EXPR (CAR TAIL))
					    (COND
					     ((CDR TAIL)
					      (PRIN COMMA-SPACE)))))
			 (PRIN (QUOTE |)|)))))
	      ((MEMBER-EQ (CAR INSTR)
			  (QUOTE (RETURN PAUSE STOP CONTINUE)))
	       (PRIN (CAR INSTR))
	       (COND
		((CDR INSTR)
		 (PSPACES 1)
		 (LET ((*PRINT-BASE* 8))
		      (PRIN (CADR INSTR))))))
	      ((MATCH INSTR (ASSIGNED-GOTO VAR LABEL-LST))
	       (PRIN (QUOTE GOTO))
	       (PSPACES 1)
	       (PRIN VAR)
	       (PRIN COMMA-SPACE)
	       (PRIN (QUOTE |(|))
	       (ITERATE FOR TAIL ON LABEL-LST DO (PROGN (PRIN (CAR TAIL))
							(COND
							 ((CDR TAIL)
							  (PRIN COMMA-SPACE)))))
	       (PRIN (QUOTE |)|)))
	      ((MATCH INSTR (COMPUTED-GOTO LABEL-LST VAR))
	       (PRIN (QUOTE GOTO))
	       (PSPACES 1)
	       (PRIN (QUOTE |(|))
	       (ITERATE FOR TAIL ON LABEL-LST DO (PROGN (PRIN (CAR TAIL))
							(COND
							 ((CDR TAIL)
							  (PRIN COMMA-SPACE)))))
	       (PRIN (QUOTE |)|))
	       (PRIN COMMA-SPACE)
	       (PRIN VAR))
	      ((MATCH INSTR (ASSIGN-TO LABEL VAR))
	       (PRIN (QUOTE ASSIGN))
	       (PSPACES 1)
	       (PRIN LABEL)
	       (PSPACES 1)
	       (PRIN (QUOTE TO))
	       (PSPACES 1)
	       (PRIN VAR)))
	     (ITERPRI NIL)
	     (RETURN NIL)))

(DEFUN PRIN-STATEMENT-FNS (FNS)
       (ITERATE FOR STMNT-FN IN FNS
		DO
		(PROGN (PRIN (ACCESS STATEMENT-FUNCTION-PATTERN NAME STMNT-FN))
		       (PRIN (QUOTE |(|))
		       (ITERATE FOR TAIL ON (ACCESS STATEMENT-FUNCTION-PATTERN
						    ARG-VAR-DCLS 
						    STMNT-FN)
				DO (PROGN (PRIN (CAR TAIL))
					  (COND
					   ((CDR TAIL)
					    (PRIN COMMA-SPACE)))))
		       (PRIN (QUOTE |)|))
		       (PSPACES 1)
		       (PRIN (QUOTE =))
		       (PSPACES 1)
		       (PRIN-EXPR (ACCESS STATEMENT-FUNCTION-PATTERN BODY STMNT-FN))
		       (ITERPRI NIL))))

(DEFUN PRIN-TYPE-STMTS (VAR-DCLS)
       (ITERATE FOR VDCL IN VAR-DCLS
		DO (PROGN (PSPACES 6)
			  (PRIN (CASE (ACCESS VAR-DCL TYPE VDCL)
				      (DOUBLE "DOUBLE PRECISION")
				      (OTHERWISE (ACCESS VAR-DCL TYPE VDCL))))
			  (PSPACES 1)
			  (IPRINC (ACCESS VAR-DCL NAME VDCL) NIL)
			  (ITERPRI NIL))))

(DEFUN IPRINCC (X)
       (SETQ X (PACK (LIST X)))
       (COND
	((> (+ (IPOSITION NIL NIL NIL)
	       (OUR-FLATC X))
	    71)
	 (ITERPRI NIL)
	 (IPRINC (QUOTE C) NIL)
	 (PSPACES 5)))
       (ITERATE FOR I FROM 1 TO  (OUR-FLATC X)
		DO (PROGN (COND
			   ((> (IPOSITION NIL NIL NIL)
			       71)
			    (ITERPRI NIL)
			    (IPRINC (QUOTE C) NIL)
			    (PSPACES 5)))
			  (IPRINC (OUR-GETCHAR X I) NIL))))

(DEFUN PRINT-COMMENT (LST)
       (PROG (N NAME PRINTING-A-COMMENT)
	     (SETQ PRINTING-A-COMMENT T)
	     (IPRINC (QUOTE C) NIL)
	     (PSPACES 5)
	     (COND
	      ((OR (MATCH LST (ASSERTION NAME & &))
		   (MATCH LST (CONS (QUOTE XXX)
				    (CONS NAME (CONS & &))))
		   (MATCH LST (CONS (QUOTE DOJUNK)
				    (CONS NAME &))))
	       (PRIN (CAR LST))
	       (PSPACES 1)
	       (PRINC NAME)
	       (ITERPRI NIL))
	      (T (ITERATE FOR L IN LST
			  DO (COND
			      ((EQ L '/)
			       (ITERPRI NIL)
			       (IPRINC (QUOTE C) NIL)
			       (PSPACES 5))
			      ((MATCH L (COL N))
			       (PSPACES (- (MIN N 70)
					   (IPOSITION NIL NIL NIL))))
			      (T (PRIN L)
				 (PSPACES 1))))
		 (ITERPRI NIL)))
	     (RETURN NIL)))

(DEFUN PRINT-CONTEXT (CONTEXT FILE TOKEN-ALIST)
       (SETQ FILE (OPEN FILE :DIRECTION :OUTPUT))
       (OUR-LINEL 72 NIL)
       (LET ((*STANDARD-OUTPUT* FILE))
	    (PROG (STATEMENT-FNS CODE TYPE TOKENS COMMON-BLOCKS ARGS NAME 
				 ROUTINES)
		  (SETQ TOKENS (ACCESS CONTEXT TOKENS CONTEXT))
		  (ITERATE FOR PAIR IN TOKEN-ALIST
			   DO (COND
			       ((OR (NOT (CONSP PAIR))
				    (NOT (MEMBER-EQ (CAR PAIR)
						    TOKENS))
				    (NOT (INTEGERP (CDR PAIR)))
				    (< (CDR PAIR)
				       1))
				(ERROR "~%The second argument must be an alist ~
                               from tokens to nonnegative integers, ~A"
				       TOKEN-ALIST))))
		  (PRINT-SPECIFICATIONS CONTEXT TOKEN-ALIST)
		  (MATCH (SUBLIS TOKEN-ALIST CONTEXT)
			 (CONTEXT & & COMMON-BLOCKS ROUTINES))
		  (ITERPRI NIL)
		  (WRITE-CHAR #\Page)
		  (ITERPRI NIL)
		  (ITERATE FOR BLOCK IN COMMON-BLOCKS
			   DO (PRIN-TYPE-STMTS (ACCESS COMMON-BLOCK VAR-DCLS BLOCK)))
		  (ITERATE FOR BLOCK IN COMMON-BLOCKS
			   DO (PRIN-DIMENSION-STMTS (ACCESS COMMON-BLOCK VAR-DCLS 
							    BLOCK)))
		  (ITERATE FOR BLOCK IN COMMON-BLOCKS
			   DO (PRIN-COMMON-BLOCK BLOCK))
		  (ISPACES 6 NIL)
		  (PRIN (QUOTE END))
		  (ITERPRI NIL)
		  (ITERATE FOR SUB IN ROUTINES
			   DO
			   (PROGN
			    (COND
			     ((EQ (CAR SUB)
				  (QUOTE SUBROUTINE))
			      (SETQ SUBROUTINE-FLG T)
			      (MATCH SUB
				     (SUBROUTINE NAME ARGS BLOCK-NAMES & & 
						 VAR-DCLS CALLED-FNS 
						 STATEMENT-FNS & & & CODE)))
			     (T (SETQ SUBROUTINE-FLG NIL)
				(MATCH SUB
				       (FUNCTION NAME TYPE ARGS BLOCK-NAMES & 
						 VAR-DCLS CALLED-FNS 
						 STATEMENT-FNS & & & CODE))))
			    (COND
			     (SUBROUTINE-FLG
			      (ISPACES 6 NIL)
			      (PRIN (QUOTE SUBROUTINE))
			      (PSPACES 1)
			      (PRIN NAME)
			      (COND
			       (ARGS (PRIN (QUOTE |(|))
				     (ITERATE FOR TAIL ON ARGS
					      DO (PROGN (PRIN (CAR TAIL))
							(COND
							 ((NULL (CDR TAIL))
							  NIL)
							 (T (PRIN COMMA-SPACE)))))
				     (PRIN (QUOTE |)|))))
			      (ITERPRI NIL))
			     (T (ISPACES 6 NIL)
				(PRIN (COND
				       ((EQ TYPE (QUOTE DOUBLE))
					"DOUBLE PRECISION")
				       (T TYPE)))
				(PSPACES 1)
				(PRIN (QUOTE FUNCTION))
				(PSPACES 1)
				(PRIN NAME)
				(PRIN (QUOTE |(|))
				(ITERATE FOR TAIL ON ARGS
					 DO (PROGN (PRIN (CAR TAIL))
						   (COND
						    ((NULL (CDR TAIL))
						     NIL)
						    (T (PRIN COMMA-SPACE)))))
				(PRIN (QUOTE |)|))
				(ITERPRI NIL)))
			    (ITERATE FOR NAME IN BLOCK-NAMES
				     DO (PRIN-TYPE-STMTS
					 (ACCESS COMMON-BLOCK VAR-DCLS
						 (ASSOC-CADR NAME 
							     COMMON-BLOCKS))))
			    (PRIN-TYPE-STMTS
			     (ITERATE FOR NAME IN CALLED-FNS WITH TEMP
				      COLLECT (COND
					       ((SETQ TEMP
						      (INTRINSIC-FUNCTION-PATTERN
						       NAME))
						(MAKE VAR-DCL NAME
						      (ACCESS FUNCTION-PATTERN TYPE 
							      TEMP)
						      NIL))
					       (T (SETQ TEMP
							(ASSOC-CADR NAME ROUTINES))
						  (MAKE VAR-DCL NAME
							(ACCESS FUNCTION TYPE TEMP)
							NIL)))))
			    (PRIN-TYPE-STMTS (ITERATE FOR FN IN STATEMENT-FNS
						      COLLECT (MAKE VAR-DCL
								    (ACCESS 
								     STATEMENT-FUNCTION-PATTERN 
								     NAME FN)
								    (ACCESS 
								     STATEMENT-FUNCTION-PATTERN 
								     TYPE FN)
								    NIL)))
			    (PRIN-TYPE-STMTS VAR-DCLS)
			    (ITERATE FOR NAME IN BLOCK-NAMES
				     DO (PRIN-DIMENSION-STMTS
					 (ACCESS COMMON-BLOCK 
						 VAR-DCLS
						 (ASSOC-CADR NAME 
							     COMMON-BLOCKS))))
			    (PRIN-DIMENSION-STMTS VAR-DCLS)
			    (ITERATE FOR NAME IN BLOCK-NAMES
				     DO (PRIN-COMMON-BLOCK (ASSOC-CADR NAME 
								       COMMON-BLOCKS)))
			    (PRIN-EXTERNALS (ITERATE FOR FN IN CALLED-FNS
						     UNLESS
						     (INTRINSIC-FUNCTIONP FN)
						     COLLECT FN))
			    (PRIN-STATEMENT-FNS STATEMENT-FNS)
			    (PRIN-CODE CODE)
			    (PSPACES 6)
			    (PRIN (QUOTE END))
			    (ITERPRI NIL)))
		  (PRINT-HINTS CONTEXT)
		  (RETURN NIL)))
       (CLOSE FILE))

(DEFUN PRINT-HINTS (CONTEXT)
       (PROG (XXX ROUTINES CLOCKS CODE SUBROUTINE-FLG FORTRAN-COMMENTS)
	     (MATCH CONTEXT (CONTEXT & XXX & ROUTINES))
	     (ITERATE FOR X IN XXX WHEN (EQ (CAR X)
					    (QUOTE HINT))
		      DO (IPRINC "

The XXX at " NIL)
		      (PRIN (CADR X))
		      (IPRINC ".
" NIL)
		      (DUMP (CDDR X)
			    NIL 8 (OUR-LINEL NIL NIL)))
	     (ITERATE FOR ROUTINE IN ROUTINES
		      DO
		      (ITERPRI NIL)
		      (WRITE-CHAR #\Page)
		      (ITERPRI NIL)
		      (IPRINC "Hints for routine " NIL)
		      (IPRINC (CADR ROUTINE) NIL)
		      (ITERPRI NIL)
		      (COND
		       ((EQ (CAR ROUTINE)
			    (QUOTE SUBROUTINE))
			(SETQ SUBROUTINE-FLG T)
			(SETQ CLOCKS (ACCESS SUBROUTINE CLOCKS ROUTINE))
			(SETQ CODE (ACCESS SUBROUTINE CODE ROUTINE)))
		       (T (SETQ SUBROUTINE-FLG NIL)
			  (SETQ CLOCKS (ACCESS FUNCTION CLOCKS ROUTINE))
			  (SETQ CODE (ACCESS FUNCTION CODE ROUTINE))))
		      (IPRINC "
			      

The input clock:
" NIL)
		      (ISPACES 8 NIL)
		      (PPRIND (CONS (QUOTE LIST)
				    CLOCKS)
			      8 0 NIL)
		      (SETQ FORTRAN-COMMENTS
			    (ITERATE FOR INSTR IN CODE WITH ANS
				     DO (SETQ ANS (APPEND ANS
							  (COND
							   ((MATCH INSTR (COMMENT (QUOTE ASSERTION)
										  & & &))
							    (LIST INSTR))
							   ((MATCH INSTR (CONS (QUOTE COMMENT)
									       (CONS (QUOTE XXX)
										     (CONS & (CONS & &)))))
							    (LIST INSTR))
							   ((MATCH INSTR (CONS (QUOTE COMMENT)
									       (CONS (QUOTE DOJUNK)
										     (CONS & &))))
							    (CONS
							     (CONS
							      (QUOTE COMMENT)
							      (CONS
							       (QUOTE DOJUNK)
							       (CONS (CADDR INSTR)
								     (ITERATE FOR PAIR IN (CDDDR INSTR)
									      COLLECT
									      (CONS (CAR PAIR)
										    (ITERATE FOR X IN (CDR PAIR)
											     WHEN (EQ (CAR X)
												      (QUOTE 
												       COMMENT))
											     COLLECT (CADDR X)))))))
							     (ITERATE FOR PAIR IN (CDDDR INSTR) WITH ANS
								      DO (SETQ ANS (APPEND ANS
											   (ITERATE FOR X IN (CDR PAIR)
												    WHEN (EQ (CAR X)
													     (QUOTE COMMENT))
												    COLLECT X)))
								      FINALLY (RETURN ANS))))
							   (T NIL))))
				     FINALLY (RETURN ANS)))
		      (ITERATE FOR COM IN FORTRAN-COMMENTS WITH ASSN-NAME AND
			       ASSN AND CLKS AND FLAGS AND XXX
			       DO (COND
				   ((MATCH COM (COMMENT (QUOTE ASSERTION)
							ASSN-NAME ASSN CLKS))
				    (IPRINC 
				     "

The invariant and clock named " NIL)
				    (IPRINC ASSN-NAME NIL)
				    (IPRINC ".

" NIL)
				    (ISPACES 8 NIL)
				    (PPRIND ASSN 8 0 NIL)
				    (ITERPRI NIL)
				    (ITERPRI NIL)
				    (ISPACES 8 NIL)
				    (PPRIND (CONS (QUOTE LIST)
						  CLKS)
					    8 0 NIL))
				   ((MATCH COM (CONS (QUOTE COMMENT)
						     (CONS (QUOTE XXX)
							   (CONS ASSN-NAME
								 (CONS FLAGS XXX)))))
				    (IPRINC "

The XXX named " NIL)
				    (IPRINC ASSN-NAME NIL)
				    (IPRINC ":
" NIL)
				    (COND
				     (FLAGS (ISPACES 8 NIL)
					    (IPRINC 
					     "Path encryption:
" NIL)
					    (ISPACES 8 NIL)
					    (PPRIND FLAGS 8 0 NIL)
					    (ITERPRI NIL)))
				    (DUMP XXX NIL 8 (OUR-LINEL NIL NIL)))
				   ((MATCH COM (CONS (QUOTE COMMENT)
						     (CONS (QUOTE DOJUNK)
							   (CONS ASSN-NAME ALIST))))
				    (IPRINC "

The DO junk named " NIL)
				    (IPRINC ASSN-NAME NIL)
				    (IPRINC ":
" NIL)
				    (ISPACES 8 NIL)
				    (PPRIND ALIST 8 0 NIL))
				   (T (ERROR "SHOULDN'T")))))
	     (RETURN NIL)))

(DEFUN PRINT-SPECIFICATIONS (CONTEXT TOKEN-ALIST)
       (PROG (XXX ROUTINES INPUT-CONDITION EFFECTS SUBROUTINE-FLG)
	     (COND
	      (TOKEN-ALIST (IPRINC 
			    "In the following FORTRAN program tokens were instantiated thus:


" NIL)
			   (ITERATE FOR PAIR IN TOKEN-ALIST
				    DO (ISPACES 10 NIL)
				    (IPRINC (CAR PAIR) NIL)
				    (ISPACES (- 30 (IPOSITION NIL NIL NIL))
					     NIL)
				    (IPRINC (CDR PAIR) NIL)
				    (ITERPRI NIL))))
	     (MATCH CONTEXT (CONTEXT & XXX & ROUTINES))
	     (IPRINC 
	      "

The correctness of the program depends upon the following events:

" NIL)
	     (DUMP (ITERATE FOR X IN XXX COLLECT (COND
						  ((EQ (CAR X)
						       (QUOTE HINT))
						   (LIST (QUOTE FORTRAN-COMMENT)
							 (CADR X)))
						  (T X)))
		   NIL 8 NIL)
	     (ITERATE FOR ROUTINE IN ROUTINES
		      DO (ITERPRI NIL)
		      (WRITE-CHAR #\Page)
		      (ITERPRI NIL)
		      (IPRINC "Specification for routine " NIL)
		      (IPRINC (CADR ROUTINE) NIL)
		      (ITERPRI NIL)
		      (COND
		       ((EQ (CAR ROUTINE)
			    (QUOTE SUBROUTINE))
			(SETQ SUBROUTINE-FLG T)
			(SETQ INPUT-CONDITION
			      (ACCESS SUBROUTINE INPUT-COND ROUTINE))
			(SETQ EFFECTS (ACCESS SUBROUTINE EFFECTS ROUTINE))
			(SETQ CLOCKS (ACCESS SUBROUTINE CLOCKS ROUTINE)))
		       (T (SETQ SUBROUTINE-FLG NIL)
			  (SETQ INPUT-CONDITION
				(ACCESS FUNCTION INPUT-COND ROUTINE))
			  (SETQ EFFECTS (ACCESS FUNCTION RESULT ROUTINE))
			  (SETQ CLOCKS (ACCESS FUNCTION CLOCKS ROUTINE))))
		      (IPRINC "
The input assertion:
" NIL)
		      (ISPACES 8 NIL)
		      (PPRIND INPUT-CONDITION 8 0 NIL)
		      (IPRINC "


The output assertion:
" NIL)
		      (ISPACES 8 NIL)
		      (PPRIND EFFECTS 8 0 NIL))
	     (RETURN NIL)))

(DEFUN PSPACES (I)
       (ITERATE FOR J FROM 1 TO I DO (PRIN (QUOTE | |))))

(DEFUN REFERENCED-AS-A-FUNCTION (FN EXPR)

;   Assume FN is the name of a function pattern and EXPR is an expression.
;   Return T iff FN is used as a function in EXPR. That just means it occurs in
;   the CAR of some subexpression.


       (COND
	((ATOM EXPR)
	 NIL)
	((EQ (CAR EXPR)
	     FN)
	 T)
	(T (ITERATE FOR ARG IN (CDR EXPR) THEREIS (REFERENCED-AS-A-FUNCTION FN ARG)
		    ))))

(DEFUN REFERENCED-AS-A-FUNCTION-IN-STMT (FN INSTR)

;   FN is the name of a function pattern.  INSTR is an executable instruction.
;   Return T iff FN is referenced as a function symbol in some expr of INSTR.


       (PROG (V EXP ST2 LST)
	     (RETURN (COND
		      ((MATCH INSTR (ASSIGNMENT V EXP))
		       (OR (REFERENCED-AS-A-FUNCTION FN V)
			   (REFERENCED-AS-A-FUNCTION FN EXP)))
		      ((MATCH INSTR (IF-ARITHMETIC EXP & & &))
		       (REFERENCED-AS-A-FUNCTION FN EXP))
		      ((MATCH INSTR (IF-LOGICAL EXP ST2))
		       (OR (REFERENCED-AS-A-FUNCTION FN EXP)
			   (REFERENCED-AS-A-FUNCTION-IN-STMT FN ST2)))
		      ((MATCH INSTR (CALL & LST))
		       (ITERATE FOR ARG IN LST
				THEREIS (REFERENCED-AS-A-FUNCTION FN ARG)))
		      (T 

;   The only remaining statments are labels, COMMENT, DO, GOTO, RETURN,
;   CONTINUE, STOP, PAUSE, ASSIGNED-GOTO, COMPUTED-GOTO, and ASSIGN-TO.  None
;   of those statements could possibly contain a fn call.


		       NIL)))))

(DEFUN REFERENCED-VARIABLE-OR-ARRAY (EXPR)

;   Assuming EXPR is a variable reference, an array reference, or an array
;   element reference, return the name of the referenced variable or array


       (COND
	((CONSP EXPR)
	 (CAR EXPR))
	(T EXPR)))

(DEFUN SHORT-NAME (X)
       (COND
	((COMMON-NAMEP X)
	 (PACK (REVERSE (ITERATE FOR C IN (REVERSE (OUR-EXPLODEC X))
				 UNTIL (EQ C (QUOTE -))
				 COLLECT C))))
	(T X)))
(DEFUN SKOLEMIZE-TERM (TERM)
       (PROG (TEMP)
	     (RETURN (COND
		      ((OR (VARIABLEP TERM)
			   (FQUOTEP TERM))
		       TERM)
		      ((AND (NOT (VARIABLEP (FARGN TERM 1)))
			    (NOT (FQUOTEP (FARGN TERM 1)))
			    (MEMBER-EQ (FFN-SYMB (FARGN TERM 1))
				       (QUOTE (START BEGIN NEXT))))
		       (SETQ TEMP (GENERATE-SKOLEM-CONSTANT
				   (FFN-SYMB TERM)
				   (FARGN TERM 1)))
		       (SETQ SKOLEM-CONSTANTS
			     (ADD-TO-SET (FFN-SYMB TEMP)
					 SKOLEM-CONSTANTS))
		       TEMP)
		      (T (CONS-TERM (FFN-SYMB TERM)
				    (ITERATE FOR ARG IN (FARGS TERM)
					     COLLECT (SKOLEMIZE-TERM ARG))))))))

(DEFUN SORT-OF (EXPR)
       (PROG (L1 L2 L3 R1 R2 R3 PAT)
	     (RETURN
	      (COND
	       ((ATOM EXPR)
		(COND
		 ((INTEGERP EXPR)
		  (OR (< -1 EXPR)
		      (FORTRAN-ERROR "Illegal INTEGER constant" EXPR))
		  (QUOTE (INTEGER)))
		 ((TOKENP EXPR)
		  (QUOTE (INTEGER)))
		 (T (SORT-OF1 EXPR))))
	       ((EQ (CAR EXPR)
		    (QUOTE ^))
		(OR (AND (MATCH EXPR (^ L1 L2 L3))
			 (INTEGERP L1)
			 (< -1 L1)
			 (INTEGERP L2)
			 (INTEGERP L3))
		    (FORTRAN-ERROR "Illegal REAL constant" EXPR))
		(QUOTE (REAL)))
	       ((EQ (CAR EXPR)
		    (QUOTE ^^))
		(OR (AND (MATCH EXPR (^^ L1 L2 L3))
			 (INTEGERP L1)
			 (< -1 L1)
			 (INTEGERP L2)
			 (INTEGERP L3))
		    (FORTRAN-ERROR "Illegal DOUBLE constant" EXPR))
		(QUOTE (DOUBLE)))
	       ((EQ (CAR EXPR)
		    (QUOTE |^,^|))
		(OR (AND (MATCH EXPR (|^,^| (^ L1 L2 L3)
					    (^ R1 R2 R3)))
			 (INTEGERP L1)
			 (INTEGERP L2)
			 (INTEGERP L3)
			 (INTEGERP R1)
			 (INTEGERP R2)
			 (INTEGERP R3))
		    (FORTRAN-ERROR "Illegal COMPLEX constant" EXPR))
		(QUOTE (COMPLEX)))
	       ((SETQ PAT (ASSOC-CADR (CAR EXPR)
				      STATEMENT-FUNCTION-PATTERNS))
		(OR (EQUAL (LENGTH (CDR EXPR))
			   (LENGTH (ACCESS STATEMENT-FUNCTION-PATTERN 
					   ARG-VAR-DCLS PAT)))
		    (FORTRAN-ERROR "Wrong number of args" EXPR))
		(ITERATE FOR ARG IN (CDR EXPR) AS VDCL
			 IN (ACCESS STATEMENT-FUNCTION-PATTERN ARG-VAR-DCLS PAT)
			 WITH SORT
			 DO (SETQ SORT (SORT-OF ARG)) 

;   The sort of a VAR-DCL used as an arg of a statement function will always be
;   a type CONSed onto NIL because the ARG-VAR-DCLS are each members of the
;   variable patterns. We thus need only check that shown below, and not worry
;   about the correctness of actual array dimensions.


			 (OR (AND (EQUAL (ACCESS VAR-DCL TYPE VDCL)
					 (CAR SORT))
				  (NULL (CDR SORT)))
			     (FORTRAN-ERROR "Actual of wrong sort"
					    (LIST (QUOTE actual)
						  ARG
						  (QUOTE expr)
						  EXPR))))
		(CONS (ACCESS STATEMENT-FUNCTION-PATTERN TYPE PAT)
		      NIL))
	       ((SETQ PAT (OR (ASSOC-CADR (CAR EXPR)
					  FUNCTION-PATTERNS)
			      (INFIX-FUNCTION-PATTERN (CAR EXPR))))
		(OR (EQUAL (LENGTH (CDR EXPR))
			   (LENGTH (ACCESS FUNCTION-PATTERN ARG-VAR-DCLS 
					   PAT)))
		    (FORTRAN-ERROR "Wrong number of args" EXPR))
		(ITERATE FOR ARG IN (CDR EXPR) AS VDCL
			 IN (ACCESS FUNCTION-PATTERN ARG-VAR-DCLS PAT)
			 WITH SORT
			 DO
			 (SETQ SORT (SORT-OF ARG))
			 (OR (EQUAL (ACCESS VAR-DCL TYPE VDCL)
				    (CAR SORT))
			     (FORTRAN-ERROR "Actual of wrong type"
					    (LIST (QUOTE actual)
						  ARG
						  (QUOTE expr)
						  EXPR)))
			 (OR (EQUAL (LENGTH (CDR SORT))
				    (LENGTH (ACCESS VAR-DCL SIZES VDCL)))
			     (FORTRAN-ERROR "Actual of wrong number of dimensions"
					    (LIST (QUOTE actual)
						  ARG
						  (QUOTE expr)
						  EXPR)))
			 (ITERATE FOR ADIM IN (CDR SORT) AS FDIM
				  IN (ACCESS VAR-DCL SIZES VDCL)
				  DO
				  (OR
				   (COND
				    ((OR (INTEGERP FDIM)
					 (TOKENP FDIM))
				     (EQUAL FDIM ADIM))
				    (T
				     (EQUAL ADIM
					    (ITERATE FOR ACT IN (CDR EXPR) AS FORMAL
						     IN (ACCESS FUNCTION-PATTERN 
								ARG-VAR-DCLS PAT)
						     WHEN
						     (EQUAL (ACCESS VAR-DCL NAME FORMAL)
							    FDIM)
						     DO (RETURN ACT)))))
				   (FORTRAN-ERROR "Actual of wrong size"
						  (LIST (QUOTE actual)
							ARG
							(QUOTE expr)
							EXPR)))))
		(CONS (ACCESS FUNCTION-PATTERN TYPE PAT)
		      NIL))
	       ((SETQ PAT (ASSOC-CADR (CAR EXPR)
				      ARRAY-PATTERNS))
		(OR (EQUAL (LENGTH (CDR EXPR))
			   (LENGTH (ACCESS VAR-DCL SIZES PAT)))
		    (FORTRAN-ERROR "Wrong number of subscripts" EXPR))
		(ITERATE FOR ARG IN (CDR EXPR)
			 DO (CHK-FORTRAN-SUBSCRIPT ARG EXPR))
		(CONS (ACCESS VAR-DCL TYPE PAT)
		      NIL))
	       (T (FORTRAN-ERROR "Unrecognized function" EXPR))))))

(DEFUN SORT-OF1 (ATM)
       (PROG (TEMP)
	     (OR (CONSP (SETQ TEMP (OR (ASSOC-CADR ATM VARIABLE-PATTERNS)
				       (ASSOC-CADR ATM ARRAY-PATTERNS))))
		 (FORTRAN-ERROR "Unrecognized var" ATM))
	     (RETURN (CONS (ACCESS VAR-DCL TYPE TEMP)
			   (ACCESS VAR-DCL SIZES TEMP)))))

;  ?? is this the same as Interlisps?  Is it the one we need?

(DEFUN SUBPAIR (OLDLST NEWLST X)
       (COND ((ATOM X)
	      (COND ((ITERATE FOR O IN OLDLST AS N IN NEWLST
			      WHEN (EQUAL X O)
			      DO (SETQ TEMP-TEMP N) (RETURN T))
		     TEMP-TEMP)
		    (T X)))
	     (T (CONS (SUBPAIR OLDLST NEWLST (CAR X))
		      (COND ((NULL X) NIL)
			    (T (SUBPAIR OLDLST NEWLST (CDR X))))))))

(DEFUN SUBTERMS-THAT-CALL (FNS TERM)

;   Returns a list of the subterms of TERM that are calls of some member of FN.
;   We assume that no member of FN is a constructor or bottom object.


       (PROG (ANS)
	     (SUBTERMS-THAT-CALL1 FNS TERM)
	     (RETURN ANS)))

(DEFUN SUBTERMS-THAT-CALL1 (FNS TERM)
       (COND
	((VARIABLEP TERM))
	((FQUOTEP TERM))
	(T (COND
	    ((MEMBER-EQ (FFN-SYMB TERM)
			FNS)
	     (SETQ ANS (ADD-TO-SET TERM ANS))))
	   (ITERATE FOR ARG IN (FARGS TERM) DO (SUBTERMS-THAT-CALL1 FNS ARG)))))

(DEFUN SUBTERMS-THAT-USE (ARGS TERM)

;   Returns a list of all subterms of TERM that have a member of ARGS as an
;   argument.  We assume that ARG is not an explicit value.


       (PROG (ANS)
	     (SUBTERMS-THAT-USE1 ARGS TERM)
	     (RETURN ANS)))

(DEFUN SUBTERMS-THAT-USE1 (ARGS TERM)
       (COND
	((VARIABLEP TERM))
	((FQUOTEP TERM))
	(T (COND
	    ((INTERSECTP (FARGS TERM)
			 ARGS)
	     (SETQ ANS (ADD-TO-SET TERM ANS))))
	   (ITERATE FOR ARG IN (FARGS TERM) DO (SUBTERMS-THAT-USE1 ARGS ARG)))))

(DEFUN TOKENP (X)
       (MEMBER-EQ X (ACCESS CONTEXT TOKENS CONTEXT)))

(DEFUN TRANSLATE-DO-STATEMENTS (CODE)
       (PROG (INSTR LABEL-STACK BACK DONE I J K L LABEL NEXT-INSTR ALIST)
	     (RETURN
	      (ITERATE FOR TAIL ON CODE WITH ANS
		       DO 
		       (SETQ INSTR (CAR TAIL))
		       (SETQ ANS (APPEND ANS
					 (COND
					  ((ATOM INSTR)
					   (COND
					    ((NOT (EQUAL INSTR (CAAR LABEL-STACK)))
					     (LIST INSTR))
					    (T (SETQ NEXT-INSTR (CADR TAIL))
					       (SETQ TAIL (CDR TAIL))
					       (CONS INSTR
						     (CONS NEXT-INSTR
							   (ITERATE WITH ANS WHILE (EQUAL INSTR
											  (CAAR LABEL-STACK))
								    DO (SETQ ANS (APPEND ANS
											 (PROG1 (CDAR LABEL-STACK)
												(SETQ LABEL-STACK
												      (CDR LABEL-STACK)))))
								    FINALLY (RETURN ANS)))))))
					  ((MATCH INSTR (DO LABEL I J K L))
					   (SETQ BACK (PACK (LIST LABEL (QUOTE |$BACK|)
								  (ITERATE FOR X IN LABEL-STACK
									   COUNT (EQUAL (CAR X)
											LABEL)))))
					   (SETQ DONE (PACK (LIST LABEL (QUOTE |$DONE|)
								  (ITERATE FOR X IN LABEL-STACK
									   COUNT (EQUAL (CAR X)
											LABEL)))))
					   (COND
					    ((AND (CONSP (CADR TAIL))
						  (EQ (CAR (CADR TAIL))
						      (QUOTE COMMENT))
						  (EQ (CADR (CADR TAIL))
						      (QUOTE DOJUNK)))
					     (SETQ ALIST (CDDDR (CADR TAIL)))
					     (SETQ TAIL (CDR TAIL)))
					    (T (SETQ ALIST NIL)))
					   (SETQ LABEL-STACK
						 (CONS
						  (CONS LABEL
							(APPEND (CDR (ASSOC-EQ (QUOTE BUMP)
									       ALIST))
								(LIST (LIST (QUOTE ASSIGNMENT)
									    I
									    (LIST (QUOTE ZPLUS)
										  I L)))
								(CDR (ASSOC-EQ (QUOTE JUMP)
									       ALIST))
								(LIST (LIST (QUOTE GOTO)
									    BACK)
								      DONE)
								(CDR (ASSOC-EQ (QUOTE UNDEF)
									       ALIST))
								(LIST (LIST (QUOTE CALL)
									    (QUOTE UNDEFINER)
									    (LIST I)))))
						  LABEL-STACK))
					   (APPEND (CDR (ASSOC-EQ (QUOTE OKDO)
								  ALIST))
						   (LIST (LIST (QUOTE IF-LOGICAL)
							       (DO-TEST J K L INSTR)
							       (QUOTE (STOP))))
						   (CDR (ASSOC-EQ (QUOTE INIT)
								  ALIST))
						   (LIST (LIST (QUOTE ASSIGNMENT)
							       I J)
							 BACK)
						   (CDR (ASSOC-EQ (QUOTE TEST)
								  ALIST))
						   (LIST (LIST (QUOTE IF-LOGICAL)
							       (LIST (QUOTE ZGREATERP)
								     I K)
							       (LIST (QUOTE GOTO)
								     DONE)))))
					  (T (LIST INSTR)))))
		       FINALLY (RETURN ANS)))))

(DEFUN USED-AS-A-LABEL-VARIABLE (X ST)
       (OR (AND (MATCH ST (ASSIGNED-GOTO & &))
		(EQUAL X (CADR ST)))
	   (AND (MATCH ST (ASSIGN-TO & &))
		(EQUAL X (CADDR ST)))
	   (AND (MATCH ST (IF-LOGICAL & &))
		(USED-AS-A-LABEL-VARIABLE X (CADDR ST)))))

(DEFUN USED-AS-A-NON-ACTUAL-VARIABLE (VAR EXPR)

;   Assume VAR is the name of a variable pattern and EXPR is an expression.
;   Return T iff VAR occupies a slot in EXPR reserved for a variable pattern
;   name -- other than an actual argument slot for a function reference.


       (COND
	((ATOM EXPR)
	 (EQ VAR EXPR))
	((OR (ASSOC-CADR (CAR EXPR)
			 STATEMENT-FUNCTION-PATTERNS)
	     (ASSOC-CADR (CAR EXPR)
			 FUNCTION-PATTERNS))
	 (ITERATE FOR ARG IN (CDR EXPR) WHEN (NOT (EQ VAR ARG))
		  THEREIS (USED-AS-A-NON-ACTUAL-VARIABLE VAR ARG)))
	(T (ITERATE FOR ARG IN (CDR EXPR) THEREIS (USED-AS-A-NON-ACTUAL-VARIABLE
						   VAR ARG)))))

(DEFUN USED-AS-A-NON-ACTUAL-VARIABLE-IN-STMT (VAR INSTR ARGP)

;   VAR is the name of a variable pattern and ARGP is T iff VAR is an argument
;   of the routine being processed. INSTR is an executable instruction.  If
;   ARGP is T, return T iff VAR is used as a variable -- other than as an
;   actual in a function reference -- in INSTR and INSTR is not a CALL
;   statement.  If ARGP is NIL, return T iff VAR is used as a variable -- other
;   than as an actual in a function reference or an actual in a CALL stmt -- in
;   INSTR.


       (PROG (V EXP ST2 LST)
	     (RETURN (COND
		      ((MATCH INSTR (ASSIGNMENT V EXP))
		       (OR (USED-AS-A-NON-ACTUAL-VARIABLE VAR V)
			   (USED-AS-A-NON-ACTUAL-VARIABLE VAR EXP)))
		      ((MATCH INSTR (DO & & & & &))
		       (MEMBER-EQ VAR (CDDR INSTR)))
		      ((MATCH INSTR (IF-ARITHMETIC EXP & & &))
		       (USED-AS-A-NON-ACTUAL-VARIABLE VAR EXP))
		      ((MATCH INSTR (IF-LOGICAL EXP ST2))
		       (OR (USED-AS-A-NON-ACTUAL-VARIABLE VAR EXP)
			   (USED-AS-A-NON-ACTUAL-VARIABLE-IN-STMT VAR 
								  ST2 
								  ARGP)))
		      ((MATCH INSTR (CALL & LST))
		      

;   If ARGP is set, then we must ignore CALLs.  If ARGP is nil, we return T if
;   VAR is used as a variable other than an actual in one of the actuals of the
;   CALL.


		       (COND
			(ARGP NIL)
			(T (ITERATE FOR ARG IN LST UNLESS (EQ ARG VAR)
				    THEREIS (USED-AS-A-NON-ACTUAL-VARIABLE
					     VAR ARG)))))
		      ((MATCH INSTR (COMPUTED-GOTO & V))
		       (EQUAL V VAR))
		      (T 

;   The only remaining statments are labels, COMMENT, GOTO, RETURN, CONTINUE,
;   STOP, PAUSE, ASSIGNED-GOTO, and ASSIGN-TO. None of those statements could
;   possibly use VAR -- a member of the variable patterns.


		       NIL)))))

(DEFUN VAR-DCLS-OF-BLOCK (BLKNAME)

;   return the VAR-DCLs component of the COMMON-BLOCK named BLKNAME in the
;   current CONTEXT


       (ACCESS COMMON-BLOCK VAR-DCLS
	       (ASSOC-CADR BLKNAME (ACCESS CONTEXT COMMON-BLOCKS CONTEXT))))

(DEFUN VARIABLE-ARRAY-OR-ELEMENT-REFERENCE (EXPR)

;   Assuming EXPR is an expression, return T iff it is a variable reference, an
;   array reference, or an array element reference


       (COND
	((ATOM EXPR)
	 (AND (NOT (INTEGERP EXPR))
	      (NOT (TOKENP EXPR))))
	((ASSOC-CADR (CAR EXPR)
		     ARRAY-PATTERNS)
	 T)
	(T NIL)))

(DEFUN FORTRAN-NOTE-LIB NIL
       (COND
	((AND (BOUNDP (QUOTE CHRONOLOGY))
	      (MEMBER-EQ (QUOTE ALMOST-EQUAL1)
			 CHRONOLOGY))
	 (ITERATE UNTIL (EQ (CAR CHRONOLOGY)
			    (QUOTE ALMOST-EQUAL1))
		  DO (UNDO-NAME (CAR CHRONOLOGY))))
	(T (NOTE-LIB "fortran"))))

(DEFUN FORTRAN-RECOGNIZER (TYPE)
       (CASE TYPE
	     (INTEGER (QUOTE ZNUMBERP))
	     (REAL (QUOTE RNUMBERP))
	     (DOUBLE (QUOTE DNUMBERP))
	     (COMPLEX (QUOTE CNUMBERP))
	     (OTHERWISE (QUOTE LOGICALP))))

(DEFUN FORTRAN-VARIABLEP (X)
       (ASSOC-CADR X VARIABLE-PATTERNS))

(DEFUN VCG (ROUTINE CONTEXT)
       (PROG (ROUTINE-ARGS ROUTINE-NAME HIT-VARS KNOWN-BLOCK-NAMES 
			   VAR-DCLS CALLED-FNS INPUT-COND EFFECTS CLOCKS 
			   RESULT TRANS-RESULT GLOBALS LOCALS 
			   SUBROUTINE-FLG FUNCTION-TYPE TRANS-INPUT-COND 
			   TRANS-EFFECTS TRANS-INPUT-CLOCKS 
			   TRANS-INVARIANT-MAP FUNCTION-SPEC-ALIST 
			   SUBROUTINE-SPEC-ALIST OUTPUT-ASSERTION 
			   ORIGINAL-CLOCKS KNOWN-VARS-ALIST INSTRS-SEEN 
			   TO-BE-TRACED TRACED VCG-GEN-NAME-ALIST XXX 
			   INPUT-ASSERTION)

;   We have now checked that ROUTINE is a subprogram with respect to the
;   syntactic environment constructed in CHK-ROUTINE. We have also checked that
;   the result of appending ROUTINE to the routines in CONTEXT produces a
;   syntactically correct context.  Finally, we have checked that the HIT-VARS
;   field of ROUTINE is the set of things possibly smashed by ROUTINE and that
;   the KNOWN-BLOCK field of ROUTINE is the set of prefixes of the global names
;   of ROUTINE.


	     (SETQ XXX (ACCESS CONTEXT XXX CONTEXT))

;   We will make reference to the variables holding the members of the
;   syntactic environment previously computed. We also make reference to
;   TRANSLATED-FORTRAN-CODE.


	     (COND
	      ((MATCH ROUTINE
		      (SUBROUTINE ROUTINE-NAME ROUTINE-ARGS & HIT-VARS 
				  KNOWN-BLOCK-NAMES VAR-DCLS CALLED-FNS & 
				  INPUT-COND EFFECTS CLOCKS &))
	       (SETQ SUBROUTINE-FLG T))
	      (T (MATCH! ROUTINE
			 (FUNCTION ROUTINE-NAME FUNCTION-TYPE 
				   ROUTINE-ARGS & KNOWN-BLOCK-NAMES 
				   VAR-DCLS CALLED-FNS & INPUT-COND 
				   RESULT CLOCKS &))
		 (SETQ VAR-DCLS
		       (CONS (MAKE VAR-DCL ROUTINE-NAME FUNCTION-TYPE NIL)
			     VAR-DCLS))
		 (SETQ SUBROUTINE-FLG NIL)
		 (SETQ HIT-VARS NIL)))

;   Here are the local nam of ROUTINE.

	     (SETQ LOCALS (ITERATE FOR X IN VAR-DCLS COLLECT (ACCESS VAR-DCL NAME X)))

;   Here are the global names of ROUTINE.

	     (SETQ GLOBALS
		   (ITERATE FOR BLOCK IN (ACCESS CONTEXT COMMON-BLOCKS CONTEXT)
			    WHEN (MEMBER-EQ (ACCESS COMMON-BLOCK NAME BLOCK)
					    KNOWN-BLOCK-NAMES)
			    NCONC (ITERATE FOR VDCL
					   IN (ACCESS COMMON-BLOCK VAR-DCLS BLOCK)
					   COLLECT (PACK (LIST (ACCESS COMMON-BLOCK NAME BLOCK)
							       (QUOTE -)
							       (ACCESS VAR-DCL NAME VDCL))))))
	     (CHK-FORMULAS)
	     (GENERATE-SPEC-ALISTS)
	     (GENERATE-VCS)
	     (RETURN (CONS VCS
			   (MAKE CONTEXT (ACCESS CONTEXT TOKENS CONTEXT)
				 XXX
				 (ACCESS CONTEXT COMMON-BLOCKS CONTEXT)
				 (APPEND (ACCESS CONTEXT ROUTINES CONTEXT)
					 (LIST ROUTINE)))))))

(DEFUN VCG-EXPR (EXPR)
       (PROG (AC-SIZES TEMP OUTPUT-CONDITIONS KNOWN-BLOCKS TRANS-INPUT 
		       TRANS-OUTPUT ACTUALS FN FORMALS INPUT LHS RHS SKO 
		       SPEC)
	     (RETURN
	      (COND
	       ((ATOM EXPR)
		(COND
		 ((INTEGERP EXPR)
		  (COND
		   ((AND (<= EXPR 200)
			 (>= EXPR -200))
		    NIL)
		   (T (ADD-EVENT
		       (QUOTE PROVE-LEMMA)
		       (PACK (LIST (QUOTE INPUT-COND-OF-)
				   EXPR))
		       (IMPLICATE (CONJOIN TEST-LST NIL)
				  (FCONS-TERM* (QUOTE 
						EXPRESSIBLE-ZNUMBERP)
					       (LIST (QUOTE QUOTE)
						     EXPR))))))
		  (CONS (LIST (QUOTE QUOTE)
			      EXPR)
			NIL))
		 ((SYMBOLP EXPR)
		  (COND
		   ((TOKENP EXPR)
		    (CONS (FCONS-TERM* EXPR)
			  NIL))
		   (T (CONS (FCONS-TERM* (LONG-NAME EXPR)
					 STATE)
			    NIL))))
		 (T (ERROR ""))))
	       ((MEMBER-EQ (CAR EXPR)
			   (QUOTE (^ ^^ |^,^|)))
		(ERROR "%Since we have not yet figured out how to present ~
  		        REALS, DOUBLES, or COMPLEXES as formulas, we cannot ~
		        proceed with ~A"
		       EXPR))
	       ((SETQ SPEC (ASSOC-CADR (CAR EXPR)
				       STATEMENT-FUNCTION-PATTERNS))
		(SETQ TEMP (ITERATE FOR X IN (CDR EXPR)
				    COLLECT (VCG-EXPR X)))
		(SETQ ACTUALS (ITERATE FOR X IN TEMP COLLECT (CAR X)))
		(ITERATE FOR ACTUAL IN ACTUALS DO (CHK-DEFINEDP ACTUAL))
		

;   Note: the following nasty SUBPAIR is used because we are substituting into
;   a FORTRAN expression, not a term.


		(VCG-EXPR (SUBPAIR (ITERATE FOR VDCL
					    IN (ACCESS STATEMENT-FUNCTION-PATTERN 
						       ARG-VAR-DCLS SPEC)
					    COLLECT (ACCESS VAR-DCL NAME VDCL))
				   (CDR EXPR)
				   (ACCESS STATEMENT-FUNCTION-PATTERN BODY 
					   SPEC))))
	       ((SETQ SPEC (OR (ASSOC-EQ (CAR EXPR)
					 FUNCTION-SPEC-ALIST)
			       (BUILT-IN-SPEC (CAR EXPR))))
		(SETQ TEMP (ITERATE FOR X IN (CDR EXPR)
				    COLLECT (VCG-EXPR X)))
		(SETQ ACTUALS (ITERATE FOR X IN TEMP COLLECT (CAR X)))
		(SETQ OUTPUT-CONDITIONS (ITERATE FOR X IN TEMP WITH ANS DO
						 (SETQ ANS (UNION-EQUAL ANS (CDR X)))
						 FINALLY (RETURN ANS)))
		(ITERATE FOR ACTUAL IN ACTUALS DO (CHK-DEFINEDP ACTUAL))
		(MATCH! SPEC (LIST FN FORMALS KNOWN-BLOCKS TRANS-INPUT 
				   TRANS-OUTPUT))
		(COND
		 ((NOT (EQUAL INPUT TRUE))
		  (SETQ INPUT
			(SUB-PAIR-EXPR
			 (CONS (QUOTE STATE)
			       (ITERATE FOR FORMAL IN FORMALS
					COLLECT (FCONS-TERM* FORMAL
							     (QUOTE STATE))))
			 (CONS STATE ACTUALS)
			 TRANS-INPUT))
		  (ADD-EVENT (QUOTE PROVE-LEMMA)
			     (PACK (LIST (QUOTE INPUT-COND-OF-)
					 FN))
			     (IMPLICATE (CONJOIN (APPEND 
						  OUTPUT-CONDITIONS 
						  TEST-LST)
						 NIL)
					INPUT))))
		(COND
		 ((AND (MATCH TRANS-OUTPUT (EQUAL LHS RHS))
		       (EQUAL LHS (QUOTE ANS))
		       (NOT (MEMBER-EQ (QUOTE ANS)
				       (ALL-VARS RHS))))
		  (CONS
		   (SUB-PAIR-EXPR
		    (CONS (QUOTE STATE)
			  (ITERATE FOR FORMAL IN FORMALS
				   COLLECT (FCONS-TERM* FORMAL
							(QUOTE STATE))))
		    (CONS STATE ACTUALS)
		    RHS)
		   OUTPUT-CONDITIONS))
		 (T
		  (SETQ SKO
			(FCONS-TERM
			 (PACK (LIST FN (QUOTE $)))
			 (APPEND
			  ACTUALS
			  (ITERATE FOR NAME
				   IN
				   (OUR-STABLE-SORT
				    (ITERATE FOR BLOCK-NAME IN KNOWN-BLOCKS
					     NCONC (ITERATE FOR VAR-DCL
							    IN (ACCESS COMMON-BLOCK VAR-DCLS
								       (ASSOC-CADR BLOCK-NAME
										   (ACCESS CONTEXT 
											   COMMON-BLOCKS 
											   CONTEXT)))
							    COLLECT (PACK (LIST BLOCK-NAME
										(QUOTE -)
										(ACCESS VAR-DCL 
											NAME 
											VAR-DCL)))))
				    #'ALPHORDER)
				   COLLECT (FCONS-TERM* NAME STATE)))))
		  (CONS
		   SKO
		   (CONS
		    (SUB-PAIR-EXPR
		     (CONS
		      (QUOTE ANS)
		      (CONS (QUOTE STATE)
			    (ITERATE FOR FORMAL IN FORMALS
				     COLLECT (FCONS-TERM* FORMAL
							  (QUOTE STATE))
				     )))
		     (CONS SKO (CONS STATE ACTUALS))
		     TRANS-OUTPUT)
		    OUTPUT-CONDITIONS)))))
	       (T
		(SETQ TEMP (ITERATE FOR X IN (CDR EXPR)
				    COLLECT (VCG-EXPR X)))
		(SETQ ACTUALS (ITERATE FOR X IN TEMP COLLECT (CAR X)))
		(SETQ OUTPUT-CONDITIONS (ITERATE FOR X IN TEMP WITH ANS
						 DO (SETQ ANS (UNION-EQUAL ANS
									   (CDR X)))
						 FINALLY (RETURN ANS)))
		(SETQ AC-SIZES (ACCESS VAR-DCL SIZES (ASSOC-CADR (CAR EXPR)
							    
								 ARRAY-PATTERNS)))
		(ADD-EVENT
		 (QUOTE PROVE-LEMMA)
		 (PACK (LIST (QUOTE ARRAY-BOUNDS-CHECK-FOR-)
			     (CAR EXPR)))
		 (IMPLICATE
		  (CONJOIN (APPEND OUTPUT-CONDITIONS TEST-LST)
			   NIL)
		  (CONJOIN
		   (ITERATE FOR ACTUAL IN ACTUALS AS SIZE IN AC-SIZES
			    COLLECT
			    (CONJOIN
			     (LIST
			      (FCONS-TERM* (QUOTE LESSP)
					   (QUOTE (QUOTE 0))
					   ACTUAL)
			      (NEGATE (FCONS-TERM*
				       (QUOTE LESSP)
				       (COND
					((INTEGERP SIZE)
					 (LIST (QUOTE QUOTE)
					       SIZE))
					((TOKENP SIZE)
					 (FCONS-TERM* SIZE))
					(T (FCONS-TERM* SIZE STATE)))
				       ACTUAL)))
			     NIL))
		   NIL)))
		(SETQ KNOWN-DEFINED (UNION-EQUAL (ITERATE FOR I IN (CDR EXPR) WITH ANS
							  UNLESS (OR (INTEGERP I)
								     (TOKENP I))
							  DO
							  (SETQ ANS (ADD-TO-SET I ANS))
							  FINALLY (RETURN ANS))
						 KNOWN-DEFINED))
		(CONS (FCONS-TERM (PACK (LIST (QUOTE ELT)
					      (LENGTH ACTUALS)))
				  (CONS (FCONS-TERM*
					 (LONG-NAME (CAR EXPR))
					 STATE)
					ACTUALS))
		      OUTPUT-CONDITIONS))))))

(DEFUN VCG-GEN-NAME (ROOT)
       (COND
	((VCG-NEW-NAMEP ROOT VCS)
	 ROOT)
	(T (PACK (LIST ROOT
		       (ITERATE FOR I FROM 1 WHEN  (VCG-NEW-NAMEP
						    (PACK (LIST ROOT I))
						    VCS)
				DO (RETURN I)))))))

(DEFUN VCG-NEW-NAMEP (NAME XXX)
       (COND
	((ATOM XXX)
	 T)
	((EQ (CAAR XXX)
	     (QUOTE UBT))
	 (VCG-NEW-NAMEP NAME (CDR (ITERATE FOR TAIL ON (CDR XXX)
					   WHEN (EQ (CADR (CAR TAIL))
						    (CADR (CAR XXX)))
					   DO (RETURN TAIL)))))
	((EQ (CADR (CAR XXX))
	     NAME)
	 NIL)
	(T (VCG-NEW-NAMEP NAME (CDR XXX)))))

(DEFUN VCG-REDO-UNDONE-EVENTS (EVENTS)
       (DO-EVENTS EVENTS))

(DEFUN VCG1 (TEST-LST INSTR STATE LABELS CLOCKS KNOWN-DEFINED VCG-PATH)
       (PROG (OUTPUT-CONDITIONS OUTPUT-CONDITIONS-RHS 
				OUTPUT-CONDITIONS-LHS ACTUAL-ARGS ACTUALS 
				ARGS2 ASSN ASSN-NAME CLKS EFFECTS2 EXPR 
				HIT-VARS2 INPUT-COND2 L1 LHS NEWLHS 
				NEWSTATE RHS SPEC STMT SUBR TYPE 
				INST-INPUT-COND2 INST-EFFECTS2 TEMP 
				EVENT-NAME XXX FLAGS SIZE 
				ALMOST-EQUAL-HYPS)
	     (SETQ INSTRS-SEEN (CONS INSTR INSTRS-SEEN))
	     (RETURN
	      (COND
	       ((ATOM INSTR)
		(OR (NOT (MEMBER-EQUAL INSTR LABELS))
		    (FORTRAN-ERROR "Loop not cut" LABELS))
		(VCG1 TEST-LST (NEXT-INSTR INSTR)
		      STATE
		      (CONS INSTR LABELS)
		      CLOCKS KNOWN-DEFINED VCG-PATH))
	       ((MATCH INSTR (RETURN))
		(COND
		 ((NOT SUBROUTINE-FLG)
		  (CHK-DEFINEDP (FCONS-TERM* ROUTINE-NAME STATE))))
		(ADD-EVENT (QUOTE PROVE-LEMMA)
			   (QUOTE OUTPUT)
			   (IMPLICATE (CONJOIN TEST-LST NIL)
				      (SUBST-VAR STATE
						 (QUOTE NEWSTATE)
						 OUTPUT-ASSERTION))))
	       ((MATCH INSTR (GOTO L1))
		(VCG1 TEST-LST L1 STATE LABELS CLOCKS KNOWN-DEFINED 
		      VCG-PATH))
	       ((MATCH INSTR (COMMENT (QUOTE ASSERTION)
				      ASSN-NAME & &))
		(SETQ TEMP (ASSOC-EQ ASSN-NAME TRANS-INVARIANT-MAP))
		(SETQ ASSN (CADR TEMP))
		(SETQ CLKS (CADDR TEMP))
		(ADD-EVENT
		 (QUOTE PROVE-LEMMA)
		 ASSN-NAME
		 (IMPLICATE (CONJOIN TEST-LST NIL)
			    (CONJOIN2 (SUBST-VAR STATE (QUOTE STATE)
						 ASSN)
				      (FCONS-TERM*
				       (QUOTE LEX)
				       (SUBST-VAR STATE
						  (QUOTE STATE)
						  CLKS)
				       CLOCKS)
				      NIL)))
		(COND
		 ((EQUAL ASSN FALSE)
		  NIL)
		 ((MEMBER-EQ INSTR TRACED)
		  NIL)
		 ((MEMBER-EQ INSTR TO-BE-TRACED)
		  NIL)
		 (T (SETQ TO-BE-TRACED (CONS INSTR TO-BE-TRACED)))))
	       ((MATCH INSTR (CONS (QUOTE COMMENT)
				   (CONS (QUOTE XXX)
					 (CONS ASSN-NAME
					       (CONS FLAGS XXX)))))
		(COND
		 ((OR (NULL FLAGS)
		      (MEMBER-EQUAL (REVERSE VCG-PATH)
				    FLAGS))
		  (SETQ VCS (APPEND (REVERSE XXX)
				    VCS))))
		(VCG1 TEST-LST (NEXT-INSTR INSTR)
		      STATE LABELS CLOCKS KNOWN-DEFINED VCG-PATH))
	       ((EQ (CAR INSTR)
		    (QUOTE COMMENT))
		(VCG1 TEST-LST (NEXT-INSTR INSTR)
		      STATE LABELS CLOCKS KNOWN-DEFINED VCG-PATH))
	       ((MATCH INSTR (IF-ARITHMETIC EXPR & & &))
		(SETQ TYPE (CAR (SORT-OF EXPR)))
		(SETQ TEMP (VCG-EXPR EXPR))
		(SETQ EXPR (CAR TEMP))
		(SETQ OUTPUT-CONDITIONS (CDR TEMP))
		(CHK-DEFINEDP EXPR)
		(ITERATE FOR LABEL IN (CDDR INSTR) AS OP
			 IN (QUOTE (LESSP EQUAL GREATERP)) AS SIGN
			 IN (QUOTE (< = >))
			 DO
			 (SETQ EVENT-NAME
			       (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					  (PACK (LIST (QUOTE ARITHMETIC-IF-)
						      OP))
					  NIL))
			 (VCG1
			  (ADD-TO-SET
			   (CASE TYPE
				 (INTEGER (FCONS-TERM*
					   (PACK (LIST (QUOTE Z)
						       OP))
					   EXPR
					   (QUOTE (QUOTE 0))))
				 (REAL (FCONS-TERM*
					(PACK (LIST (QUOTE R)
						    OP))
					EXPR
					(QUOTE (RZERO))))
				 (DOUBLE (FCONS-TERM*
					  (PACK (LIST (QUOTE D)
						      OP))
					  EXPR
					  (QUOTE (DZERO))))
				 (OTHERWISE (ERROR NIL)))
			   (APPEND OUTPUT-CONDITIONS TEST-LST))
			  LABEL STATE LABELS CLOCKS KNOWN-DEFINED
			  (CONS SIGN VCG-PATH))
			 (ADD-EVENT (QUOTE UBT)
				    EVENT-NAME NIL)))
	       ((MATCH INSTR (IF-LOGICAL EXPR STMT))
		(SETQ TEMP (VCG-EXPR EXPR))
		(SETQ EXPR (CAR TEMP))
		(SETQ OUTPUT-CONDITIONS (CDR TEMP))
		(CHK-DEFINEDP EXPR)
		(SETQ EVENT-NAME (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					    (QUOTE LOGICAL-IF-T)
					    NIL))
		(VCG1 (ADD-TO-SET EXPR
				  (APPEND OUTPUT-CONDITIONS TEST-LST))
		      STMT STATE LABELS CLOCKS KNOWN-DEFINED
		      (CONS T VCG-PATH))
		(ADD-EVENT (QUOTE UBT)
			   EVENT-NAME NIL)
		(SETQ EVENT-NAME (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					    (QUOTE LOGICAL-IF-F)
					    NIL))
		(VCG1 (COND
		       ((EQ (CAR STMT)
			    (QUOTE STOP))
			  

;   If the STMT is STOP then the previous vc established that EXPR is always false.


			TEST-LST)
		       (T (ADD-TO-SET (NEGATE EXPR)
				      (APPEND OUTPUT-CONDITIONS 
					      TEST-LST))))
		      (NEXT-INSTR INSTR)
		      STATE LABELS CLOCKS KNOWN-DEFINED
		      (CONS (QUOTE F)
			    VCG-PATH))
		(ADD-EVENT (QUOTE UBT)
			   EVENT-NAME NIL))
	       ((OR (MATCH INSTR (ASSIGNMENT LHS RHS))
		    (MATCH INSTR (ASSIGN-TO RHS LHS)))
		(SETQ TEMP (COND
			    ((EQ (CAR INSTR)
				 (QUOTE ASSIGN-TO))
			     (CONS (LIST (QUOTE QUOTE)
					 RHS)
				   NIL))
			    (T (VCG-EXPR RHS))))
		(SETQ OUTPUT-CONDITIONS-RHS (CDR TEMP))
		(SETQ RHS (CAR TEMP))
		(CHK-DEFINEDP RHS)
		(SETQ NEWSTATE (FCONS-TERM* (QUOTE NEXT)
					    STATE))
		(COND
		 ((NOT (CONSP LHS))
		  (SETQ NEWLHS (FCONS-TERM* (LONG-NAME LHS)
					    NEWSTATE))
		  (ADD-EVENT
		   (QUOTE ADD-AXIOM)
		   (QUOTE ASSIGNMENT)
		   (CONJOIN
		    (ITERATE FOR X IN KNOWN-VARS-ALIST
			     COLLECT
			     (COND
			      ((EQ (CAR X)
				   (FFN-SYMB NEWLHS))
			       (FCONS-TERM* (QUOTE EQUAL)
					    NEWLHS RHS))
			      (T (FCONS-TERM* (QUOTE EQUAL)
					      (FCONS-TERM* (CAR X)
							   NEWSTATE)
					      (FCONS-TERM* (CAR X)
							   STATE)))))
		    NIL))
		  (VCG1 (APPEND OUTPUT-CONDITIONS-RHS TEST-LST)
			(NEXT-INSTR INSTR)
			NEWSTATE LABELS CLOCKS
			(ADD-TO-SET (CAR NEWLHS)
				    KNOWN-DEFINED)
			VCG-PATH))
		 (T
		  (SETQ TEMP (VCG-EXPR LHS))
		  (SETQ NEWLHS (CAR TEMP))
		  (SETQ OUTPUT-CONDITIONS-LHS (CDR TEMP))
		  (ADD-EVENT
		   (QUOTE ADD-AXIOM)
		   (QUOTE ASSIGNMENT)
		   (CONJOIN
		    (ITERATE FOR X IN KNOWN-VARS-ALIST
			     COLLECT
			     (COND
			      ((EQ (CAR X)
				   (FFN-SYMB (FARGN NEWLHS 1)))
			       (SETQ ALMOST-EQUAL-HYPS
				     (COND
				      ((NOT (= (CDDR X)
					       1))

;  We haven't thought how to add ALMOST-EQUAL2 and 3 yet.)

				       NIL)
				      (T
				       (LIST
					(FCONS-TERM*
					 (QUOTE ALMOST-EQUAL1)
					 (FCONS-TERM*
					  (FFN-SYMB (FARGN NEWLHS 1))
					  STATE)
					 (FCONS-TERM*
					  (FFN-SYMB (FARGN NEWLHS 1))
					  NEWSTATE)
					 (QUOTE (QUOTE 1))
					 (COND
					  ((INTEGERP
					    (SETQ SIZE
						  (CAR
						   (ACCESS
						    VAR-DCL SIZES
						    (ASSOC-CADR
						     (CAR LHS)
						     ARRAY-PATTERNS))
						   )))
					   (LIST (QUOTE QUOTE)
						 SIZE))
					  ((TOKENP SIZE)
					   (FCONS-TERM* SIZE))
					  (T (FCONS-TERM* SIZE STATE))
					  )
					 (FARGN NEWLHS 2)
					 RHS)))))
			       (FCONS-TERM*
				(QUOTE EQUAL)
				(FCONS-TERM
				 (PACK (LIST  (QUOTE ELT)
					      (CDDR X)))
				 (CONS
				  (FCONS-TERM*
				   (FFN-SYMB (FARGN NEWLHS 1))
				   NEWSTATE)
				  (ITERATE FOR I FROM 1 TO (CDDR X)
					   AS V IN (QUOTE (I J K))
					   COLLECT
					   V)))
				(FCONS-TERM*
				 (QUOTE IF)
				 (CONJOIN
				  (ITERATE FOR AC IN (CDR (FARGS NEWLHS))
					   AS V IN (QUOTE (I J K))
					   COLLECT
					   (FCONS-TERM* (QUOTE EQUAL)
							V AC))
				  NIL)
				 RHS
				 (FCONS-TERM
				  (PACK (LIST (QUOTE ELT)
					      (CDDR X)))
				  (CONS
				   (FCONS-TERM*
				    (FFN-SYMB (FARGN NEWLHS 1))
				    STATE)
				   (ITERATE FOR I FROM 1 TO (CDDR X)
					    AS V IN (QUOTE (I J K))
					    COLLECT
					    V))))))
			      (T (FCONS-TERM* (QUOTE EQUAL)
					      (FCONS-TERM* (CAR X)
							   NEWSTATE)
					      (FCONS-TERM* (CAR X)
							   STATE)))))
		    NIL))
		  (VCG1 (APPEND ALMOST-EQUAL-HYPS 
				OUTPUT-CONDITIONS-LHS 
				OUTPUT-CONDITIONS-RHS TEST-LST)
			(NEXT-INSTR INSTR)
			NEWSTATE LABELS CLOCKS KNOWN-DEFINED VCG-PATH)
		  )))
	       ((MATCH INSTR (CALL SUBR ACTUAL-ARGS))
		(SETQ TEMP (ITERATE FOR X IN ACTUAL-ARGS
				    COLLECT (VCG-EXPR X)))
		(SETQ OUTPUT-CONDITIONS (ITERATE FOR X IN TEMP WITH ANS
						 DO (SETQ ANS (UNION-EQUAL ANS (CDR X)))
						 FINALLY (RETURN X)))
		(SETQ ACTUALS (ITERATE FOR X IN TEMP COLLECT (CAR X)))
		(COND
		 ((SETQ SPEC (ASSOC-CADR SUBR
					 (ACCESS CONTEXT ROUTINES CONTEXT)))
		  (MATCH! SPEC
			  (SUBROUTINE & ARGS2 & HIT-VARS2 & & & & & & 
				      & &))
		  (MATCH! (ASSOC-EQUAL SUBR SUBROUTINE-SPEC-ALIST)
			  (LIST & INPUT-COND2 EFFECTS2)))
		 (T (MATCH! SUBR (QUOTE UNDEFINER))
		    (SETQ ARGS2 (QUOTE (VAR)))
		    (SETQ HIT-VARS2 ARGS2)
		    (SETQ INPUT-COND2 TRUE)
		    (SETQ EFFECTS2 TRUE)))
		(SETQ INST-INPUT-COND2
		      (SUB-PAIR-EXPR
		       (CONS (QUOTE STATE)
			     (ITERATE FOR FORMAL IN ARGS2
				      COLLECT (FCONS-TERM* FORMAL (QUOTE STATE)))
			     )
		       (CONS STATE ACTUALS)
		       INPUT-COND2))
		(ADD-EVENT (QUOTE PROVE-LEMMA)
			   (PACK (LIST (QUOTE CALL-OF-)
				       SUBR))
			   (IMPLICATE (CONJOIN (APPEND 
						OUTPUT-CONDITIONS 
						TEST-LST)
					       NIL)
				      INST-INPUT-COND2))
		(SETQ NEWSTATE (FCONS-TERM* (QUOTE NEXT)
					    STATE))
		(SETQ INST-EFFECTS2
		      (SUB-PAIR-EXPR
		       (CONS
			(QUOTE NEWSTATE)
			(CONS (QUOTE STATE)
			      (APPEND (ITERATE FOR FORMAL IN ARGS2
					       COLLECT
					       (FCONS-TERM* FORMAL
							    (QUOTE STATE)))
				      (ITERATE FOR FORMAL IN ARGS2
					       WHEN (MEMBER-EQ FORMAL HIT-VARS2)
					       COLLECT
					       (FCONS-TERM* FORMAL
							    (QUOTE NEWSTATE))))
			      ))
		       (CONS
			NEWSTATE
			(CONS STATE
			      (APPEND
			       ACTUALS
			       (ITERATE FOR FORMAL IN ARGS2 AS ACTUAL
					IN ACTUALS
					WHEN (MEMBER-EQ FORMAL HIT-VARS2)
					COLLECT (FCONS-TERM* (FFN-SYMB ACTUAL)
							     NEWSTATE)))))
		       EFFECTS2))
		(SETQ TEMP
		      (FLATTEN-ANDS
		       (CONJOIN
			(CONS
			 INST-EFFECTS2
			 (ITERATE FOR X IN KNOWN-VARS-ALIST
				  UNLESS
				  (OR (AND (MEMBER-EQ (QUOTE -)
						      (OUR-EXPLODEC (CAR X)))
					   (MEMBER-EQ (CAR X)
						      HIT-VARS2))
				      (ITERATE FOR ARG2 IN ARGS2 AS ACTUAL
					       IN ACTUALS
					       THEREIS
					       (AND (MEMBER-EQ ARG2 HIT-VARS2)
						    (EQUAL (CAR X)
							   (FFN-SYMB ACTUAL)))))
				  COLLECT (FCONS-TERM*
					   (QUOTE EQUAL)
					   (FCONS-TERM* (CAR X)
							NEWSTATE)
					   (FCONS-TERM* (CAR X)
							STATE))))
			NIL)))
		(ADD-EVENT (QUOTE ADD-AXIOM)
			   (PACK (LIST (QUOTE EFFECTS-OF-)
				       SUBR))
			   (CONJOIN (ITERATE FOR X IN TEMP
					     WHEN (OR (FREE-VARSP X NIL)
						      (MATCH X (EQUAL & &)))
					     COLLECT X)
				    NIL))
		(VCG1 (APPEND (ITERATE FOR X IN TEMP
				       UNLESS (OR (FREE-VARSP X NIL)
						  (MATCH X (EQUAL & &)))
				       COLLECT X)
			      OUTPUT-CONDITIONS TEST-LST)
		      (NEXT-INSTR INSTR)
		      NEWSTATE LABELS CLOCKS
		      (ITERATE FOR X IN KNOWN-DEFINED 
			       UNLESS
			       (OR (AND (MEMBER-EQ (QUOTE -)
						   (OUR-EXPLODEC X))
					(MEMBER-EQ X HIT-VARS2))
				   (ITERATE FOR ARG2 IN ARGS2 AS ACTUAL IN ACTUALS
					    THEREIS (AND (MEMBER-EQ ARG2 HIT-VARS2)
							 (EQUAL X (FFN-SYMB ACTUAL))
							 )))
			       COLLECT X)
		      VCG-PATH))
	       ((MEMBER-EQ (CAR INSTR)
			   (QUOTE (CONTINUE PAUSE)))
		(VCG1 TEST-LST (NEXT-INSTR INSTR)
		      STATE LABELS CLOCKS KNOWN-DEFINED VCG-PATH))
	       ((EQ (CAR INSTR)
		    (QUOTE STOP))
		(ADD-EVENT (QUOTE PROVE-LEMMA)
			   (QUOTE STOP)
			   (IMPLICATE (CONJOIN TEST-LST NIL)
				      (QUOTE (FALSE)))))
	       ((MATCH INSTR (ASSIGNED-GOTO LHS RHS))
		(ADD-EVENT
		 (QUOTE PROVE-LEMMA)
		 (QUOTE ASSIGNED-GOTO-IN-RANGE)
		 (IMPLICATE
		  (CONJOIN TEST-LST NIL)
		  (DISJOIN (ITERATE FOR LABEL IN RHS
				    COLLECT (FCONS-TERM*
					     (QUOTE EQUAL)
					     (FCONS-TERM* LHS STATE)
					     (LIST (QUOTE QUOTE)
						   LABEL)))
			   NIL)))
		(ITERATE FOR LABEL IN RHS AS I FROM 1
			 DO (SETQ EVENT-NAME
				  (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					     (PACK (LIST (QUOTE ARITHMETIC-GOTO-)
							 LABEL))
					     NIL))
			 (VCG1 (ADD-TO-SET (FCONS-TERM*
					    (QUOTE EQUAL)
					    (FCONS-TERM* LHS STATE)
					    (LIST (QUOTE QUOTE)
						  LABEL))
					   TEST-LST)
			       LABEL STATE LABELS CLOCKS KNOWN-DEFINED
			       (CONS I VCG-PATH))
			 (ADD-EVENT (QUOTE UBT)
				    EVENT-NAME NIL)))
	       ((MATCH INSTR (COMPUTED-GOTO LHS RHS))
		(SETQ RHS (FCONS-TERM* (LONG-NAME RHS)
				       STATE))
		(ADD-EVENT
		 (QUOTE PROVE-LEMMA)
		 (QUOTE COMPUTED-GOTO-IN-RANGE)
		 (IMPLICATE
		  (CONJOIN TEST-LST NIL)
		  (FCONS-TERM* (QUOTE AND)
			       (FCONS-TERM* (QUOTE LESSP)
					    (QUOTE (QUOTE 0))
					    RHS)
			       (NEGATE (FCONS-TERM*
					(QUOTE LESSP)
					(LIST (QUOTE QUOTE)
					      (LENGTH LHS))
					RHS)))))
		(ITERATE FOR LABEL IN LHS AS I FROM 1
			 DO (SETQ EVENT-NAME
				  (ADD-EVENT (QUOTE FORTRAN-COMMENT)
					     (PACK (LIST (QUOTE COMPUTED-GOTO-)
							 LABEL))
					     NIL))
			 (VCG1 (ADD-TO-SET (FCONS-TERM*
					    (QUOTE EQUAL)
					    RHS
					    (LIST (QUOTE QUOTE)
						  I))
					   TEST-LST)
			       LABEL STATE LABELS CLOCKS KNOWN-DEFINED
			       (CONS I VCG-PATH))
			 (ADD-EVENT (QUOTE UBT)
				    EVENT-NAME NIL)))
	       (T (ERROR "Unrecognized instr: ~A" INSTR))))))

; Added from Nqthm-1987 code-b-d.lisp.  Greatly simplified.

(DEFUN DUMP (LST FILE INDENT WIDTH)
  (LET (WE-OPENED-IT)
    (OR INDENT (SETQ INDENT 5))
    (OR WIDTH (SETQ WIDTH 68))
    (COND ((MAYBE-OPENABLE FILE)
           (SETQ FILE (OPEN (EXTEND-FILE-NAME FILE NIL) :DIRECTION :OUTPUT))
           (SETQ WE-OPENED-IT T)))
    (OUR-LINEL FILE WIDTH)
    (ITERATE FOR L IN LST AS I FROM 1 DO
             (PROGN
               (COND ((SYMBOLP L) (SETQ L (GET L (QUOTE EVENT)))))
               (DUMP-OTHER L)
               (CONS (NTH 1 L) I)))
    (COND (WE-OPENED-IT (CLOSE FILE)))
    FILE))

(DEFUN DUMP-OTHER (X)
  (ITERPRI FILE)
  (ISPACES INDENT FILE)
  (PPRIND X (IPOSITION FILE NIL NIL) 0 FILE)
  (ITERPRI FILE))



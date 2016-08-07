; Date: Sun, 22 Aug 93 14:19:25 +0200
; From: schelter@posso.ibp.fr (William Schelter)
; Apparently-To: mksmith@cli.com

; Here is a patch to fix the bug, which you found.   Thanks again
; for finding this.   The problem was in the way the interpreter
; was invoking the function. 

(in-package 'compiler)
(defun vararg-p (x)
  (and (equal (get x 'proclaimed-return-type) t)
       (do ((v (get x 'proclaimed-arg-types) (cdr v)))
	   ((null v) t)
	   (or (consp v) (return nil))
	   (or (eq (car v) t)
	       (eq (car v) '*)
	       (return nil)))))


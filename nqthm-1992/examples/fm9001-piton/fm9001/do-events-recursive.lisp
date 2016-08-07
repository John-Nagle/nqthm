;;;  Copyright (C) 1990-1994 Computational Logic, Inc.  All Rights
;;;  Reserved.  See the file LICENSE in this directory for the
;;;  complete license agreement.

(in-package "USER")

(defun do-events-recursive (ev)
  (let (undone-events)
    (do-events ev)))

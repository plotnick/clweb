;;;; Initialization forms for CLWEB with Allegro Common -*-Lisp-*-

(require "CLWEB")

(defun filename (x)
  "Try to coerce X into a pathname."
  (etypecase x
    (string (parse-namestring x))
    ;; FIXME: We need to do better with case here.
    (symbol (parse-namestring (string-downcase (string x))))
    (pathname x)))

(defmacro make-cached-command (command &aux (cached-args (gensym)))
  `(let ((,cached-args nil))
     (lambda (&rest args)
       (when args (setq ,cached-args args))
       (apply ,command ,cached-args))))

(defmacro alias-cached-command (name command &optional doc-string &aux
                                (symbol (gensym)) name-string abbr arg-mode)
  ;; Parse the NAME argument in the same way that TOP-LEVEL:ALIAS does.
  (etypecase name
    (string (setq name-string name))
    (list (setq name-string (pop name))
          (dolist (x name)
            (etypecase x
              (integer (setq abbr x))
              (keyword (setq arg-mode x))))))
  `(progn
     (setf (symbol-function ',symbol)
           (make-cached-command (symbol-function ',command))
           (documentation ',symbol 'function)
           (documentation ',command 'function))
     ;; Yes, Virginia, we're using an internal symbol of the TOP-LEVEL
     ;; package. But the public API doesn't allow us to set a doc-string
     ;; for a command programmatically, so we're forced to resort to this.
     (top-level::add-alias ,name-string (or ,abbr (1- (length ,name-string)))
                           ',symbol ,doc-string ,arg-mode)))

(defun tex-command (file)
  "Run TeX on FILE."
  (excl:shell (format nil "tex ~A" (file-namestring (filename file)))))

(defun load-web-command (file &rest args)
  "Load the web in FILE."
  (handler-bind ((warning #'muffle-warning))
    (apply 'clweb:load-web (filename file) args)))

(defun tangle-file-command (file &rest args)
  "Tangle the web in FILE."
  (handler-bind ((warning #'muffle-warning))
    (apply 'clweb:tangle-file (filename file) args)))

(defun weave-command (file &rest args)
  "Weave the web in FILE."
  (apply 'clweb:weave (filename file) args))

(alias-cached-command "tex" tex-command "run TeX")
(alias-cached-command "tf" tangle-file-command "tangle file")
(alias-cached-command "lw" load-web-command "load web")
(alias-cached-command ("weave" 1) weave-command "weave web")

;;; Testing aliases.

(require "RT")

(top-level:alias "dt" () "do tests" (rt:do-tests))
(top-level:alias "ct" () "continue testing" (rt:continue-testing))

(defun tangle-test-command (file &rest args &aux (file (filename file)))
  "Tangle FILE, load the compiled file, and run the tests."
  (and (load (apply #'tangle-file-command file args))
       (progn
         (rt:rem-all-tests)
         (load (clweb::tests-file-pathname file nil)))
       (rt:do-tests)))

(alias-cached-command "tt" tangle-test-command "tangle & test")

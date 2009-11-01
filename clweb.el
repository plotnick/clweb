;;;; A major-mode for editing CLWEB programs.

(defvar *start-section-regexp* "@ \\|@\\*\\|@\n\\|@t\\*?")

(defun forward-section (arg)
  "Move forward to the beginning of the next web section.
With argument, do this that many times."
  (interactive "p")
  (when (looking-at *start-section-regexp*)
    (setq arg (1+ arg)))
  (while (> arg 0)
    (condition-case nil
        (re-search-forward *start-section-regexp*)
      (search-failed (signal 'end-of-buffer nil)))
    (setq arg (1- arg)))
  (goto-char (match-beginning 0)))

(defun backward-section (arg)
  "Move backward to the beginning of a web section.
With argument, do this that many times."
  (interactive "p")
  (while (> arg 0)
    (condition-case nil
        (re-search-backward *start-section-regexp*)
      (search-failed (signal 'beginning-of-buffer nil)))
    (setq arg (1- arg)))
  (point))

(defun eval-section (arg)
  "Evaluate the (named or unnamed) section around point.
If an argument is supplied, code for named sections will be appended to
any existing code for that section; otherwise, it will be replaced."
  (interactive "P")
  (save-excursion
    (let* ((start (condition-case nil
                      (if (looking-at *start-section-regexp*)
                          (point)
                          (backward-section 1))
                    (beginning-of-buffer (error "In limbo"))))
           (end (condition-case nil
                    (forward-section 1)
                  (end-of-buffer (point-max))))
           (temp-file (make-temp-file "clweb")))
      (write-region start end temp-file t 'nomsg)
      (comint-simple-send (inferior-lisp-proc)
                          (format "(load-sections-from-temp-file %S %S)"
                                  temp-file (not (null arg)))))))

(define-derived-mode clweb-mode lisp-mode "CLWEB"
  "Major mode for editing CLWEB programs.
\\{clweb-mode-map}"
  (setq fill-paragraph-function nil)
  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  (setq font-lock-defaults
	'((lisp-font-lock-keywords
	   lisp-font-lock-keywords-1
           lisp-font-lock-keywords-2)
	  nil
          nil
          (("+-/.!?$%_&~^:" . "w"))
          nil
	  (font-lock-mark-block-function . mark-defun)
	  (font-lock-syntactic-face-function
	   . lisp-font-lock-syntactic-face-function)
          (font-lock-syntactic-keywords
           . (("\\(^\\|[^@,]\\)\\(@\\)[ *Tt]" 2 "< b")
              ("\\(^\\|[^@]\\)@\\([LlPp]\\)" 2 "> b")
              ("\\(^\\|[^@]\\)\\(@\\)[<^.]" 2 "< bn")
              ("\\(^\\|[^@]\\)@\\(>\\)[^=]" 2 "> bn")
              ("\\(^\\|[^@]\\)@\\(>\\)\\+?\\(=\\)" (2 "> bn") (3 "> b")))))))

(define-key clweb-mode-map "\M-n" 'forward-section)
(define-key clweb-mode-map "\M-p" 'backward-section)
(define-key clweb-mode-map "\C-c\C-s" 'eval-section)

(add-to-list 'auto-mode-alist '("\\.clw" . clweb-mode))

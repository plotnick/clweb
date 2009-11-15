;;;; A major-mode for editing CLWEB programs.

(defvar *start-section-regexp* "^@[ *\nTt]")
(defvar *start-non-test-section-regexp* "^@[ *\n]")

(defun move-by-sections (arg &optional skip-test-sections)
  "Move forward or backward ARG sections."
  (let ((regexp (if skip-test-sections
                    *start-non-test-section-regexp*
                    *start-section-regexp*)))
    (cond ((> arg 0)
           (condition-case nil
               (re-search-forward regexp nil nil
                                  (if (looking-at *start-section-regexp*)
                                      (1+ arg)
                                      arg))
             (search-failed (signal 'end-of-buffer nil)))
           (goto-char (match-beginning 0)))
          ((< arg 0)
           (condition-case nil
               (re-search-backward regexp nil nil (- arg))
             (search-failed (signal 'beginning-of-buffer nil)))
           (point)))))

(defun forward-section (arg)
  "Move forward to the beginning of the next web section.
With argument, do this that many times."
  (interactive "p")
  (move-by-sections arg))

(defun backward-section (arg)
  "Move backward to the beginning of a web section.
With argument, do this that many times."
  (interactive "p")
  (move-by-sections (- arg)))

(defun goto-section (arg)
  "Move to the section whose number is the given argument."
  (interactive "NSection number: ")
  (goto-char 1)
  (condition-case nil
      (move-by-sections arg t)
    (end-of-buffer (goto-char (point-max)))))

(defun what-section ()
  "Print the section number containing point."
  (interactive)
  (let ((p (point))
        (n -1))
    (save-excursion
      (goto-char 1)
      (condition-case nil
          (while (<= (point) p)
            (setq n (1+ n))
            (move-by-sections 1 t))
        (end-of-buffer)))
    (message "%d" n)))

(defun eval-section (arg)
  "Evaluate the (named or unnamed) section around point.
If an argument is supplied, code for named sections will be appended to
any existing code for that section; otherwise, it will be replaced."
  (interactive "P")
  (save-excursion
    (let* ((start (condition-case nil
                      (if (looking-at *start-section-regexp*)
                          (point)
                          (move-by-sections -1))
                    (beginning-of-buffer (error "In limbo"))))
           (end (condition-case nil
                    (move-by-sections 1)
                  (end-of-buffer (point-max))))
           (temp-file (make-temp-file "clweb")))
      (write-region start end temp-file t 'nomsg)
      (let ((string (format "(clweb:load-sections-from-temp-file %s %s)"
                            temp-file (not (null arg)))))
        (cond ((fboundp 'slime-interactive-eval)
               (slime-interactive-eval string))
              ((fboundp 'inferior-lisp-proc)
               (comint-simple-send (inferior-lisp-proc) string))
              (t (error "Unable to find superior or inferior Lisp")))))))

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

(define-key clweb-mode-map "\C-c\C-n" 'forward-section)
(define-key clweb-mode-map "\C-c\C-p" 'backward-section)
(define-key clweb-mode-map "\C-c\C-s" 'eval-section)

(add-to-list 'auto-mode-alist '("\\.clw" . clweb-mode))

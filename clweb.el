;;;; A simple minor-mode for editing CLWEB programs.

(defvar *start-section-regexp* "@ \\|@\\*\\|@\n")

(defun move-to-section (arg)
  (condition-case nil
      (progn
        (while (> arg 0)
          (re-search-forward *start-section-regexp*)
          (setq arg (1- arg)))
        (while (< arg 0)
          (re-search-backward *start-section-regexp*)
          (setq arg (1+ arg))))
    (search-failed (message "Can't find section boundary"))))

(defun forward-section (arg)
  "Advance past next WEB section beginning; with ARG, repeat ARG times."
  (interactive "p")
  (move-to-section (if (looking-at *start-section-regexp*) (1+ arg) arg)))

(defun backward-section (arg)
  "Advance to previous WEB section beginning; with ARG, repeat ARG times."
  (interactive "p")
  (move-to-section (- arg)))

(defun eval-section (arg)
  "Evaluate the (named or unnamed) section around point.  If ARG is supplied,
code for named sections will be appended to any existing code for that section;
otherwise, it will be replaced."
  (interactive "P")
  (let ((tmp (make-temp-file "clweb"))
        (start (save-excursion
                 (unless (looking-at *start-section-regexp*)
                   (move-to-section -1))
                 (point)))
        (end (save-excursion
               (move-to-section 1)
               (- (point) 2))))
    (write-region start end tmp t 'nomsg)
    (comint-simple-send (inferior-lisp-proc)
                        (format "(load-sections-from-temp-file %S %S)"
                                tmp (not (null arg))))))

(define-minor-mode clweb-mode
  "A minor mode for editing CLWEB programs."
  :lighter " CLWEB"
  :keymap '(("\C-\M-n" . forward-section)
            ("\C-\M-p" . backward-section)
            ("\C-c\C-s" . eval-section)))


;; Emacs mode for Fuzz
;; http://privacy.cis.upenn.edu/
;;
;; (C) 2012 The University of Pennsylvania


;;;###autoload
(add-to-list 'auto-mode-alist '("\\.fz\\'" . fuzz-mode))

(defconst fuzz-font-lock-defaults
  '((fuzz-font-lock-keywords fuzz-font-lock-keywords-1 fuzz-font-lock-keywords-2)
    nil nil

    ))

(define-derived-mode fuzz-mode prog-mode "Fuzz"
  "Mode for editing Fuzz Programs"
  (setq fuzz-interpreter "")
  (setq font-lock-defaults fuzz-font-lock-defaults))

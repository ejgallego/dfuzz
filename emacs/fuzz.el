(setq fuzz-font-lock-list 
      '(
	("\\b\\(function\\) \\(\\w+\\)\\b" . (1 font-lock-keyword-face))
	("\\b\\(function\\) \\(\\w+\\)\\b" . (2 font-lock-function-name-face))
	("\\b\\(\\w+\\)\\b ?=" . (1 font-lock-variable-name-face))
	("\\b\\(\\w+\\)\\b ?:" . (1 font-lock-variable-name-face))
	("\\[\\(\\w+\\)\\]" . (1 fuzz-font-lock-annot-face))
	))

(defgroup fuzz-faces nil
  "Special faces for Fuzz mode."
  :group 'fuzz)

(defface fuzz-font-lock-annot-face
  '((((background light))
     (:foreground "dark goldenrod"))
    (t (:foreground "dark goldenrod")))
  "Face description for function definitions."
  :group 'fuzz-faces)
(defvar fuzz-font-lock-annot-face
  'fuzz-font-lock-annot-face)

(defun fuzz-mode-init ()
  (setq comment-start "//") ; for M-x comment-region
  (setq fuzz-mode-map (make-sparse-keymap))
  (substitute-key-definition 'indent-for-tab-command
 			     'c-indent-line-or-region ; c indentation is vaguely, approximately right
			     fuzz-mode-map global-map) 
  (use-local-map fuzz-mode-map))

;; (setq fuzz-mode-hook ())
(add-hook 'fuzz-mode-hook '(lambda () (fuzz-mode-init)))
(define-generic-mode fuzz-mode 
  '("//" ("/*" . "*/")) 
  '("if" "let" "fun" "fuzzy" "fuzz" "fuzze" "primiter" "typedef" "then" "else" "inl" "inr" "case" "mu" "sample" "clip" "fold" "unfold") 
  fuzz-font-lock-list 
  '("\\.fz$") nil)

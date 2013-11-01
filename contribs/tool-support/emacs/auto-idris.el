;;;; Elisp for talking to idris --client
;;;; Stopgap until these features work with --ideslave - use with https://github.com/idris-hackers/idris-mode
(require 'idris-mode)

(defvar *auto-idris-output-buf* "*auto-idris-output*")

(defun string-no-properties (str)
  (substring-no-properties str 0 (length str)))

(defun call-idris-client (cmd &optional return-output)
  (if return-output
      (with-temp-buffer
        (call-process "idris" nil t nil "--client" cmd)
        (buffer-string))
    (call-process "idris" nil *auto-idris-output-buf* nil "--client" cmd)
    nil))

(defun idris-get-line-num ()
  "Get the current line number"
  (save-restriction
    (widen)
    (save-excursion
      (beginning-of-line)
      (1+ (count-lines 1 (point))))))


(defun idris-thing-at-point ()
  "Return the line number and name at point"
  (let ((name (symbol-at-point))
        (line (idris-get-line-num)))
    (if name
        (cons (string-no-properties (symbol-name name)) line)
      (error "Nothing identifiable under point"))))

(defun idris-load ()
  "Load the current buffer using Idris client mode"
  (interactive)
  (save-buffer)
  (let* ((file-name (buffer-file-name))
         (cmd (concat ":l " file-name)))
    (call-idris-client cmd)))

(defun idris-type-at-point ()
  "Show the type of the name at point"
  (interactive)
  (message (call-idris-client (concat ":t " (car (idris-thing-at-point))) t)))

(defun idris-add-clause ()
  "Add clauses to the declaration at point"
  (interactive)
  (idris-load)
  (let ((what (idris-thing-at-point)))
    (call-idris-client (concat ":ac! " (number-to-string (cdr what)) (car what))))
  (revert-buffer t t)
  (idris-load))

(defun idris-case-split ()
  "Case split the pattern var at point"
  (interactive)
  (idris-load)
  (let ((what (idris-thing-at-point)))
   (call-idris-client (concat ":cs! " (number-to-string (cdr what)) " " (car what))))
  (revert-buffer t t)
  (idris-load))

(defun idris-proof-search (&optional hints)
  "Invoke the proof search"
  (interactive "sHints: ")
  (let ((hints (if hints (split-string hints "[^a-zA-Z0-9']") " "))
        (what (idris-thing-at-point)))
    (call-idris-client (format ":ps! %s %s %s" (number-to-string (cdr what)) (car what) hints)))
  (revert-buffer t t)
  (idris-load))

(defun idris-add-missing ()
  "Add missing cases"
  (interactive)
  (idris-load)
  (let ((what (idris-thing-at-point)))
   (call-idris-client (concat ":am! " (number-to-string (cdr what)) " " (car what))))
  (revert-buffer t t)
  (idris-load))

;;;; Bindings to imitate Agda somewhat
(define-key idris-mode-map (kbd "C-c C-c") 'idris-case-split)
(define-key idris-mode-map (kbd "C-c C-a") 'idris-proof-search)
(define-key idris-mode-map (kbd "C-c C-m") 'idris-add-missing)
(define-key idris-mode-map (kbd "C-c C-t") 'idris-type-at-point)
(define-key idris-mode-map (kbd "C-c C-d") 'idris-add-clause)

(add-hook 'idris-mode-hook
          (lambda () (add-hook 'after-save-hook 'idris-load t)))

(provide 'auto-idris)

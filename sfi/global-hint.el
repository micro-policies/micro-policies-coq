;;; global-hint.el --- Copy all marked `Hint' lines in a Coq script

;; Author: Antal Spector-Zabusky <antals@seas.upenn.edu>
;; Created: June 6, 2014, 16:03
;; Keywords: languages tools

;;; Commentary:
;; TL;DR: Write "(*Global*) Hint", run "M-x coqgh-collect-global-hints".
;;
;; Coq 8.4 doesn't have support for "Global Hint ..." declarations, so all hints
;; provided inside a section are lost when it's closed.  This is annoying if
;; you're building up a database of hints to be used with "auto" *and* that
;; database builds on itself.  Thus, this Emacs script lets you fake it.
;;
;; When you want a command of the form "Global Hint ...", instead write
;; "(*Global*) Hint" (spaces around all these words are optional, but the line
;; must only contain the hint).  Then, invoke "M-x coqgh-collect-global-hints",
;; and all the marked hints will be copied to a separate section delimited by
;; the lines "(* Start globalized hint section *)" and
;; "(* End globalized hint section *)".  If you want to have multiple such
;; blocks (say, if you have multiple sections), use "M-x
;; coqgh-empty-hint-section".  (While `coqgh-collect-global-hints' tries to put
;; the block in the right place, it might end up back inside a section or
;; outside the module definition -- feel free to move it, or use
;; `coqgh-empty-hint-section'.  This time, however, spaces matter.)
;;
;; It's fine to move these globalized hint sections around or even split them up
;; (so long as you preserve the starting and ending comments).  However, don't
;; bother editing these sections manually if you plan on running
;; `coqgh-collect-global-hints' again; running it will always overwrite the
;; contents of all such delimited sections.

;;; Code:

(require 'rx)

(defun coqgh--comment (rx-form &optional as-string)
  "Wrap an RX-FORM to match its contents inside a Coq comment.
RX-FORM is a regular expression in sexp form (like for `rx').
AS-STRING non-nil means return a string (not a sexp form)."
  (let ((form `(: "(*" (* space) ,rx-form (* space) "*)")))
    (if as-string (rx-to-string form) form)))

(defconst coqgh-hint-line
  (rx-to-string
   `(: bol (* space) ,(coqgh--comment "Global") (* space)
       (group "Hint" (* nonl) eol)))
  "The regular expression that matches a faux-global \"Hint\" line.

Just prefix \"Hint\" with \"(*Global*)\", and you'll be fine.")

(defconst coqgh--hint-section-descriptor
  "globalized hint section"
  "The string used in global hint section delimiters.")

(defun coqgh--hint-section-delimiter (prefix)
  "Return the globalized hint section delimiter starting with PREFIX.
This is a string, not a regular expression."
  (concat "(* " prefix " " coqgh--hint-section-descriptor " *)"))

(defconst coqgh-hint-section-start
  (coqgh--hint-section-delimiter "Start")
  "The string that starts a globalized hint section.")

(defconst coqgh-hint-section-end
  (coqgh--hint-section-delimiter "End")
  "The string that ends a globalized hint section.")

(defconst coqgh-emacs-line
  "(* Can be updated automatically by an Emacs script; see `global-hint.el' *)"
  "A string saying the following stuff is automatically generated.")

(defun coqgh--whole-line-string (string &optional as-string)
  "Return a regular expression form matching a line containing STRING.
The line must contain only STRING (and leading/trailing spaces).
AS-STRING non-nil means return a string (not a sexp form)."
  (let ((form `(: bol (* space) ,string (* space) eol)))
    (if as-string (rx-to-string form) form)))

(defun coqgh--insert-hint-section (hints &optional new)
  "Insert a globalized hint section containing HINTS at point.
NEW non-nil means to insert a new section with start/end lines.
This function changes the point and the match data."
  (message "Inserting%s hint section" (if new " new" ""))
  (if new
      (progn (insert coqgh-emacs-line)
             (newline-and-indent)
             (insert coqgh-hint-section-start)
             (newline-and-indent))
    (delete-region
     (point)
     (save-excursion
       (re-search-forward (coqgh--whole-line-string coqgh-hint-section-end t))
       (match-beginning 0))))
  (dolist (hint hints)
    (insert hint)
    (newline-and-indent))
  (when new
    (insert coqgh-hint-section-end)
    (newline-and-indent)))

(defun coqgh-collect-global-hints ()
  "Copy \"(*Global*) Hint\" lines outside their sections."
  (interactive)
  (save-excursion
    (save-match-data
      (let ((case-fold-search nil)
            hints)
        (goto-char (point-min))
        ;; Find all the hints/sections
        (while (re-search-forward (rx-to-string
                                   `(| (group ,(coqgh--whole-line-string
                                                coqgh-hint-section-start))
                                       (group (regexp ,coqgh-hint-line))))
                                  nil t)
          ;; The first group is the section header, the second group is the
          ;; *whole* hint line, and the *third* group is the hint line without
          ;; the "(*Global*)" prefix
          (let ((section-start (match-string 1)) (hint (match-string 3)))
            (if hint
                (progn
                  (push hint hints)
                  (message "Found %s" hint))
              ;; Skip the section header
              (goto-char (match-end 1))
              (forward-line)
              ;; Insert the hints
              (coqgh--insert-hint-section (nreverse hints))
              ;; Reset the hints
              (setq hints nil))))
        ;; Were there any leftover hints?
        (when hints
          ;; Insert a new hint section at the end of the buffer
          (goto-char (point-max))
          (newline-and-indent)
          (coqgh--insert-hint-section (nreverse hints) t))
        (message "Done collecting global hints")))))

(defun coqgh-empty-hint-section ()
  "Create a new empty globalized hint section at point."
  (interactive)
  (save-excursion
    (save-match-data
      (coqgh--insert-hint-section nil t))))

(provide 'global-hint)

;;; global-hint.el ends here

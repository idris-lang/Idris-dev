;;; GNU Guix --- Functional package management for GNU
;;; Copyright © 2022 Attila Lendvai <attila@lendvai.name>
;;;
;;; This file is part of GNU Guix.
;;;
;;; GNU Guix is free software; you can redistribute it and/or modify it
;;; under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 3 of the License, or (at
;;; your option) any later version.
;;;
;;; GNU Guix is distributed in the hope that it will be useful, but
;;; WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.
;;;
;;; You should have received a copy of the GNU General Public License
;;; along with GNU Guix.  If not, see <http://www.gnu.org/licenses/>.

;; To build and install:
;;   guix package -f guix.scm
;;
;; To build it, but not install it:
;;   guix build -f guix.scm
;;
;; To enter a shell environment for development:
;;   guix shell

(use-modules
 (gnu packages idris)
 (git)
 (guix gexp)
 (guix git)
 (guix git-download)
 (guix packages))

(define *source-dir* (dirname (current-filename)))

(define *include-worktree-changes* #false)

(define (latest-git-commit-hash dir)
  (with-repository dir repo
    (oid->string (reference-target (repository-head repo)))))

(define (current-git-branch-name dir)
  (with-repository dir repo
    (branch-name (repository-head repo))))

(let ((template-package idris-1.3.4)
      (branch-name (current-git-branch-name *source-dir*)))
  (package
    (inherit template-package)
    (name "idris")
    (version (git-version (package-version template-package)
                          (string-append
                           branch-name
                           (if *include-worktree-changes*
                               "-dirty"
                               ""))
                          (latest-git-commit-hash *source-dir*)))
    (source (if *include-worktree-changes*
                (local-file *source-dir*
                            #:recursive? #t
                            #:select? (git-predicate *source-dir*))
                (git-checkout (url *source-dir*)
                              (branch branch-name))))))

((coq-mode . ((eval . (set (make-local-variable 'coq-prog-args)
                            (list "-emacs-U" "-I"
                                  (expand-file-name
                                   ".."
                                   (file-name-directory
                                    (let ((d (dir-locals-find-file ".")))
                                      (if (stringp d) d (car d))))
                                   )
                                  "-as" ""))))))

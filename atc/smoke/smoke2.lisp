; ATC smoke test.

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

(c::defstruct |point2D|
  (|x| c::sint)
  (|y| c::sint))

(defun |read_x_by_value| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|x| |s|))

(c::atc |read_x_by_value| :file-name "smoke" :header t)

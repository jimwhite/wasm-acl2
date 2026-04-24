(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

(include-book "kestrel/c/atc/tests/defstruct" :dir :system)

(defun |read_x_by_value| (|s|)
  (declare (xargs :guard (struct-|point2D|-p |s|)))
  (struct-|point2D|-read-|x| |s|))

(c::atc |point2D| |read_x_by_value| :file-name "smoke3" :header t)

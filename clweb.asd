;;;; System definition for CLWEB, a literate programming system for -*-Lisp-*-

(defpackage "CLWEB-SYSTEM"
  (:documentation "ASDF system package for CLWEB")
  (:use "COMMON-LISP" "ASDF"))
(in-package "CLWEB-SYSTEM")

(defsystem clweb
  :description "CLWEB is a literate programming system for Common Lisp"
  :version "1.0"
  :author "Alex Plotnick <plotnick@cs.brandeis.edu>"
  :depends-on (#+sbcl sb-cltl2)
  :components ((:file "clweb")))

(defmethod perform :after ((op load-op) (component (eql (find-system 'clweb))))
  (provide 'clweb))

(defmethod perform ((op test-op) (component (eql (find-system 'clweb))))
  (operate 'load-op 'clweb-tests)
  (operate 'test-op 'clweb-tests))

;;; The CLWEB test suite gets its own system because it depends on RT,
;;; while CLWEB itself does not.

(defsystem clweb-tests
  :depends-on (clweb)
  :components ((:file "rt" )
               (:file "clweb-tests" :depends-on ("rt"))))

(defmethod perform ((op test-op) (component (eql (find-system 'clweb-tests))))
  (let ((*package* (find-package "CLWEB")))
    (funcall (intern "DO-TESTS"))))

;;;; System definition for CLWEB, a literate programming system for -*-Lisp-*-

(defsystem clweb
  :description "A literate programming system for Common Lisp"
  :version "1.0"
  :author "Alex Plotnick"
  :license "MIT"
  :depends-on ((:version "asdf" 3.1.2)
               (:feature :sbcl "sb-cltl2"))
  :components ((:static-file "LICENSE")
               (:static-file "README")
               (:file "clweb")
               (:file "asdf-operations" :depends-on ("clweb"))))

(defmethod perform :after ((op load-op) (component (eql (find-system 'clweb))))
  (provide 'clweb))

(defmethod perform ((op test-op) (component (eql (find-system 'clweb))))
  (load-system 'clweb/tests)
  (test-system 'clweb/tests))

(defsystem clweb/tests
  :description "CLWEB regression test suite"
  :depends-on ("clweb")
  :components ((:file "rt")
               (:file "clweb-tests" :depends-on ("rt"))))

(defmethod perform ((op test-op) (component (eql (find-system 'clweb/tests))))
  (symbol-call 'clweb 'do-tests))

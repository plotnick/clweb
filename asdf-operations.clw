% -*-CLWEB-*-
\noinx
\font\sc=cmcsc10
\def\asdf{{\sc asdf}}
\def\CLWEB{{\tt CLWEB}}

@1*ASDF operations on webs. ``Another System Definition Facility'' (\asdf)
has become the de~facto standard system construction tool for Common Lisp.
Despite its many flaws, it plays an important r\^ole in the modern Common Lisp
ecosystem, and it's handy to be able to use it with \CLWEB.
@^\asdf@>
@^\CLWEB@>
@^Common Lisp@>

@l
@e (defpackage "CLWEB/ASDF" (:use "COMMON-LISP" "CLWEB" "ASDF"))
@e (in-package "CLWEB/ASDF")

@ \asdf\ was designed to be extensible, so adding basic support
for webs as first-class components is straightforward. We define
a class for webs as source files, and add specialized methods for
the compile and load operations.

The class name |clweb-file| is exported by the \CLWEB\ package.
@^\CLWEB@>
@^tangle@>

@l
(defclass clweb-file (source-file)
  ((type :initform (pathname-type *web-pathname-defaults*))))

(defmethod component-pathname ((component clweb-file))
  (input-file-pathname (call-next-method)))

(defmethod output-files ((op compile-op) (component clweb-file))
  (values (multiple-value-list ;
           (tangle-file-pathnames (component-pathname component)))
          nil))

(defmethod perform ((op compile-op) (component clweb-file))
  (tangle-file (component-pathname component)
               :output-file (first (output-files op component))))

(defmethod perform ((op load-op) (component clweb-file))
  (map nil #'load
       (remove-if (lambda (file) ;
                    (string= (pathname-type file) ;
                             (pathname-type *lisp-pathname-defaults*)))
                  (input-files op component))))

(defmethod perform ((op load-source-op) (component clweb-file))
  (load-web (component-pathname component)))

@ We also define a new \asdf\ operation, |weave-op|, which weaves a web.
It has no effect on any other components.
@^weave@>

@l
(defclass weave-op (downward-operation) ())

(defmethod output-files ((op weave-op) (component clweb-file))
  (values (multiple-value-list ;
           (weave-pathnames (component-pathname component)))
          t))

(defmethod perform ((op weave-op) (component clweb-file))
  (weave (component-pathname component)))

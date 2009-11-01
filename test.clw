% Some limbo text.
@*Initialization.
@l
@e
(defpackage "TEST" (:use "COMMON-LISP"))
@e
(in-package "TEST")

@t*Initialize test harness.
@l
(in-package "TEST")
@e
(eval-when (:compile-toplevel :load-toplevel :execute)
  (require 'rt)
  (loop for symbol being each external-symbol of (find-package "RT")
        do (import symbol)))

@*Foo. The function |foo| adds twice its argument's value to thrice it.
@l
(defun foo (x)
  "The function FOO takes an integer X, and returns the sum of X doubled
and X trebled."
  (+ @<Twice |x|@> @<Thrice |x|@>))

@ @<The only even prime@>=2
@ @<Twice |x|@>=(* x @<The only...@>)
@ @<Thrice...@>=(* x 3)

@t And here's a test for the simple function defined above.
@l
(deftest foo (foo 2) 10)

@*Bar. The function |bar| returns the first four natural numbers (including 0),
and demonstrates how a named section may be defined piecewise.
@l
(defun bar () '(@<Natural numbers@>))

@ @<Natural...@>=0
@ @<Natural...@>=1
@ @<Natural...@>=@<The only even...@>
@ @<Natural...@>=3

@ Here's a section with no code. None at all. Not even a scrap. It exists
just so that we can make sure that in such an eventuality, everything is
copacetic.

@ This section is just here to use the next one.
@l
@<The next section@>

@ And this section is just to be used by the previous one. The |defun| should
be all on one line.
@<The next...@>=
(defun do-some-stuff () ;
  (list 'some 'stuff))

@ And this one gets used by no one at all.
@<Unused section@>=nil
@ Also unused, but with the same name as the last one.
@<Unused section@>=()
@ And one more, with a different name.
@<Another unused section@>=t

@*Markers. Here we test out some of the trickier markers.

@l
(defparameter *cons* '(a . b))
(defparameter *vector* #5(a b c))
(defparameter *bit-vector* #8*1011 "An octet")
(defparameter *bit-string* #B1011)
(defparameter *deadbeef* #Xdeadbeef)
(defparameter *list* '#.(list 1 2 3))
(defparameter *impl* #+sbcl "SBCL" #+(not sbcl) "Not SBCL")

@*Baz. The sole purpose of this section is to exercise some of the
pretty-printing capabilities of |weave|. Note that in inner-Lisp mode,
newlines and such are ignored:
|(defun foo (bar baz)
   (baz (apply #'qux bar)))|

@l
(defun read-stuff-from-file (file &key direction)
  (with-open-file (stream file :direction direction)
    (loop for x = (read stream nil nil nil) ; |x| is a loop-local variable
          while x collect x)))

;;; The next function doesn't really do anything very interesting, it
;;; just contains some examples of how various Common Lisp forms are
;;; usually indented. And this long, pointless comment is just here to
;;; span multiple lines at the top-level.
(defun body-forms ()
  (flet ((lessp (x y)
           (< x
              y))
         (three-values ()
           (values 1 2 3)))
    ;; This multi-line comment is here only to span multiple lines,
    ;; like the one just before the start of this |defun|, only not
    ;; at the top-level.
    (multiple-value-bind (a
                          b
                          c)
        (three-values)
      (foo a)
      (lessp b c))))

(defmacro backq-forms (foo bar list &aux (var (gensym)))
  `(dolist (,var ,list ,list)
     (funcall ,foo ,@bar ,var)))

(defun list-length-example (x)
  (do ((n 0 (+ n 2))
       (fast x (cddr fast))
       (slow x (cdr slow)))
      (nil)
    (when (endp fast) (return n))
    (when (endp (cdr fast)) (return (+ n 1)))
    (when (and (eq fast slow) (> n 0)) (return nil))))
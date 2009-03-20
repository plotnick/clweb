% Some limbo text.
@*Foo. The function |foo| adds twice its argument's value to thrice it.
@l
(defun foo (x)
  (+ @<Twice |x|@> @<Thrice |x|@>))

@ @<The only even prime@>=2
@ @<Twice |x|@>=(* x @<The only...@>)
@ @<Thrice...@>=(* x 3)

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

@ And this section is just to be used by the previous one.
@<The next...@>=
(defun do-some-stuff ()
  (list 'some 'stuff))

@*Markers. Here we test out some of the trickier markers.

@l
(defparameter *cons* '(a . b))
(defparameter *vector* #5(a b c))
(defparameter *bit-vector* #8*1011 "An octet")
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

(defun body-forms ()
  (flet ((lessp (x y)
           (< x
              y))
         (three-values ()
           (values 1 2 3)))
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
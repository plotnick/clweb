% -*-CLWEB-*-
\font\sc=cmcsc10
\font\tenec=ecrm1000
\font\eighttt=cmtt8
\def\ldq{{\tenec \char'23}} % left guillemet
\def\rdq{{\tenec \char'24}} % right guillemet
\def\pb{\.{|...|}} % program brackets
\def\v{\.{\char'174}} % vertical bar in typewriter font
\def\bull{\vrule height .9ex width .8ex depth -.1ex } % square bullet
\def\WEB{{\tt WEB}}
\def\CWEB{{\tt CWEB}}
\def\CLWEB{{\tt CLWEB}}
\def\EOF{{\sc eof}}
\def\progname{{\eighttt CLWEB}}
\def\etc.{{\it \char`&c.\spacefactor1000}}
\def\<#1>{\leavevmode\hbox{$\mkern-2mu\langle${\it #1\/}$\rangle$}}
\def\ansi{{\sc ansi}}
\def\asdf{{\sc asdf}}
\def\cltl{{\sc cl{\rm t}l}-2} % Common Lisp, the Language (2nd ed.)

@*Introduction. This is \CLWEB, a literate programming system for Common
Lisp by Alex Plotnick \<plotnick@@cs.brandeis.edu>. It is modeled
after the \CWEB\ system by Silvio Levy and Donald E.~Knuth, which was in
turn adapted from Knuth's original \WEB\ system. It shares with those
systems not only their underlying philosophy, but also most of their syntax.
Readers unfamiliar with either of them---or with literate programming in
general---should consult the \CWEB\ manual or Knuth's {\it \ldq Literate
Programming\/\rdq} ({\sc csli}:~1992).
@^Knuth, Donald Ervin@>
@^Levy, Silvio@>
@^Plotnick, Alexander F.@>
@^\WEB@>
@^\CWEB@>

This is a preliminary, $\beta$-quality release of the system.
To obtain the latest version, please visit\break
\hbox{\.{http://www.cs.brandeis.edu/\~plotnick/clweb/}}\,.

@ A \CLWEB\ source file consists of a mixture of \TeX, Lisp, and \WEB\
control codes, but which is primary depends on your point of view. The
\CWEB\ manual, for instance, says that ``[w]riting \CWEB\ programs is
something like writing \TeX\ documents, but with an additional `C mode'
that is added to \TeX's horizontal mode, vertical mode, and math mode.''
The same applies, {\it mutatis mutandis}, to the current system, but one
might just as easily think of a web as some code with documentation blocks
and special control codes sprinkled throughout, or as a completely separate
language containing blocks that happen to have the syntax (more or less) of
\TeX\ and Lisp. For the purposes of understanding the implementation, this
last view is perhaps the most useful, since the control codes determine
which syntax to use in reading the material that follows.
@^\WEB@>
@^\CWEB@>

The syntax of the \CLWEB\ control codes themselves is similar to that of
dispatching reader macro characters in Lisp: they all begin with
`\.{@@}$x$', where~$x$ is a single character that selects the control code.
Most of the \CLWEB\ control codes are quite similar to the ones used in
\CWEB; see the \CWEB\ manual for detailed descriptions of the individual
codes.

@ A literate programming system provides two primary operations:
{\it tangling\/} and {\it weaving}. The tangler prepares a literate 
program, or {\it web}, for evaluation by a machine, while the weaver
prepares it for typesetting and subsequent reading by a human. These
operations reflect the two uses of a literate program, and the two
audiences by whom it must be read: the computer on the one hand, and the
human programmers that must understand and maintain it on the other.

Our tangler has two main interface functions: |clweb:tangle-file| and
|clweb:load-web|. The first is analogous to |compile-file|: given a file
containing \CLWEB\ source, it produces an output file that can be
subsequently loaded into a Lisp image with |load|. The function
|clweb:load-web| is analogous to |load|, but also accepts \CLWEB\ source
as input instead of ordinary Lisp source: it loads a web into the Lisp
environment.

The weaver has a single entry point: |clweb:weave| takes a web as input and
generates a file that can be fed to \TeX\ to generate a pretty-printed
version of that web.

@1*System construction. We'll start by setting up a package for the system.
In addition to the top-level tangler and weaver functions mentioned above,
there's also |clweb:load-sections-from-temp-file|, which is conceptually
part of the tangler, but is a special-purpose routine designed to be used
in conjunction with an editor such as Emacs to provide incremental
redefinition of sections; the user will generally never need to call
it directly. |tangle-file-pathnames| and |weave-pathnames| play roles
analagous to |compile-file-pathname|. |clweb-file| is an \asdf\ component
class that represents a web. Next come a few global variables that control
various operations of the weaver. The remainder of the exported symbols are
condition classes for the various errors and warnings that might be
signaled while processing a web.

@l
@e
(eval-when (:compile-toplevel :load-toplevel :execute)
  #+sbcl (require "SB-CLTL2"))
@e
(defpackage "CLWEB"
  (:documentation "A literate programming system for Common Lisp.")
  (:use "COMMON-LISP")
  (:export "TANGLE-FILE"
           "LOAD-WEB"
           "WEAVE"
           "LOAD-SECTIONS-FROM-TEMP-FILE"
           "TANGLE-FILE-PATHNAMES"
           "WEAVE-PATHNAMES"
           "CLWEB-FILE"
           "*COMPILE-TESTS-FILE*"
           "*TANGLE-FILE-PATHNAME*"
           "*TANGLE-FILE-TRUENAME*"
           "*WEAVE-PRINT*"
           "*WEAVE-VERBOSE*"
           "*INDEX-LEXICAL-VARIABLES*"
           "AMBIGUOUS-PREFIX-ERROR"
           "SECTION-NAME-CONTEXT-ERROR"
           "SECTION-NAME-USE-ERROR"
           "SECTION-NAME-DEFINITION-ERROR"
           "UNUSED-NAMED-SECTION-WARNING")
  (:shadow #+(or allegro ccl) "MAKE-PATHNAME")
  #+(or sbcl ccl allegro)
  (:import-from #+sbcl "SB-CLTL2" #+ccl "CCL" #+allegro "SYS"
                #-allegro "FUNCTION-INFORMATION"
                #-allegro "VARIABLE-INFORMATION"
                #-allegro "PARSE-MACRO"
                "AUGMENT-ENVIRONMENT"))
@e
(in-package "CLWEB")

@t*Test suite. The test suite for this system uses Richard Waters's
{\sc rt} library, a copy of which is included in the distribution. For more
information on {\sc rt}, see Richard C.~Waters, ``Supporting the Regression
Testing of Lisp Programs,'' {\it SIGPLAN Lisp Pointers\/}~4, no.~2 (1991):
47--53.

We use the sleazy trick of manually importing the external symbols of
the {\sc rt} package instead of the more sensible |(use-package "RT")|
because many compilers issue warnings when the use-list of a package
changes, which would occur if the |defpackage| form above were evaluated
after the tests have been loaded.

@l
(in-package "CLWEB")
@e
(eval-when (:compile-toplevel :load-toplevel :execute)
  (require "RT")
  (do-external-symbols (symbol (find-package "RT"))
    (import symbol)))

@ We'll define our global variables and condition classes as we need them,
but we'd like them to appear near the top of the tangled output.

@l
@<Global variables@>
@<Condition classes@>

@2*ASDF integration. \asdf\ is ``another system definition facility'' for
Common Lisp. Despite its flaws, it has become the de~facto standard system
construction tool, and plays an important r\^ole in the modern Lisp
ecosystem.

\asdf\ was designed to be extensible, and indeed adding basic support for
webs as first-class components is straightforward. We define a class for
webs as source files, and add specialized methods for the most important
operations.

@l
(defclass clweb-file (asdf:source-file)
  ((type :initform "clw")))

(defmethod asdf:component-pathname ((component clweb-file))
  (input-file-pathname (call-next-method)))

(defmethod asdf:output-files ((op asdf:compile-op) (component clweb-file))
  (values (multiple-value-list ;
           (tangle-file-pathnames (asdf:component-pathname component)))
          nil))

(defmethod asdf:perform ((op asdf:compile-op) (component clweb-file))
  (tangle-file (asdf:component-pathname component)
               :output-file (first (asdf:output-files op component))))

(defmethod asdf:perform ((op asdf:load-op) (component clweb-file))
  (map nil #'load
       (remove-if (lambda (file) (string= (pathname-type file) "lisp"))
                  (asdf:input-files op component))))

(defmethod asdf:perform ((op asdf:load-source-op) (component clweb-file))
  (load-web (asdf:component-pathname component)))

@ We'll define a new \asdf\ operation, |weave-op|, which invokes the weaver
on a web. It has no effect on other components.

@l
(defclass weave-op (asdf:operation) ())

(defmethod asdf:output-files ((op weave-op) (component clweb-file))
  (values (multiple-value-list ;
           (weave-pathnames (asdf:component-pathname component)))
          t))

(defmethod asdf:perform ((op weave-op) component)
  (declare (ignore component)))

(defmethod asdf:perform ((op weave-op) (component clweb-file))
  (weave (asdf:component-pathname component)))

@1*Utilities.

@ Here's a little utility function that we'll use often. It's particularly
useful for functions that accept a list desginator.

@l
(defun ensure-list (object)
  (if (listp object) object (list object)))

@ This auxiliary function---shamelessly stolen from \cltl, Appendix~C.---is
like |mapcar| but has two extra purposes: (1)~it handles dotted lists; (2)~it
tries to make the result share with the argument |x| as much as possible.

@l
(defun maptree (fn x)
  (if (atom x)
      (funcall fn x)
      (let ((a (funcall fn (car x)))
            (d (maptree fn (cdr x))))
        (if (and (eql a (car x)) (eql d (cdr x)))
            x
            (cons a d)))))

@ And here's one taken from {\sc pcl}: |mapappend| is like |mapcar| except
that the results are appended together.

@l
(defun mapappend (fn &rest args)
  (if (some #'null args)
      ()
      (append (apply fn (mapcar #'car args))
              (apply #'mapappend fn (mapcar #'cdr args)))))

@ Sometimes, when we're accumulating text, we won't want to bother with
empty strings. In such cases we'll use the following macro, which is like
|push| but does nothing if the new object is an empty string or |nil|.

@l
(defmacro maybe-push (obj place &aux (g (gensym)))
  `(let ((,g ,obj))
     (when (if (stringp ,g) (plusp (length ,g)) ,g)
       (push ,g ,place))))

@t@l
(deftest maybe-push
  (let ((list '()))
    (maybe-push 'a list)
    (maybe-push nil list)
    (maybe-push "" list)
    (maybe-push 'b list)
    list)
  (b a))

@ This next macro has been written many times by many authors under
many names, which seems somehow appropriate. Paul Graham calls it
|with-gensyms|, but I prefer the more descriptive |with-unique-names|.
It captures a common idiom used in writing macros: given a list of
symbols, it executes the given body in an environment augmented with
bindings for each of those symbols to a fresh, uninterned symbol.

@l
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro with-unique-names (symbols &body body)
    `(let ,(loop for symbol in symbols
                 collect `(,symbol (copy-symbol ',symbol)))
       ,@body)))

@*Sections. The fundamental unit of a web is the {\it section}, which may
be either {\it named\/} or~{\it unnamed}. Named sections are conceptually
very much like parameterless macros, except that they can be defined
piecemeal. The tangler replaces references to a named section with all of
the code defined in all of the sections with that name. (This is where the
name `tangling' comes from: code may be broken up and presented in whatever
order suits the expository purposes of the author, but is then spliced back
together into the order that the programming language expects.) Unnamed
sections, on the other hand, are evaluated or written out to a file for
compilation in the order in which they appear in the source file.

Every section is assigned a number, which the weaver uses for generating
cross-references. The numbers themselves never appear in the source file:
they are generated automatically by the system.

Aside from a name, a section may have a {\it commentary part}, optionally
followed by a {\it code part}. (We don't support the `middle' part of a
section that \WEB\ and \CWEB's sections have, since the kinds of definitions
that can appear there are essentially irrelevant in Lisp.)  The commentary
part consists of \TeX\ material that describes the section; the weaver
copies it (nearly) verbatim into the \TeX\ output file, and the tangler
ignores it. The code part contains Lisp forms and named section references;
the tangler will eventually evaluate or compile those forms, while the
weaver pretty-prints them to the \TeX\ output file.
@^\WEB@>
@^\CWEB@>

Three control codes begin a section: \.{@@\ }, \.{@@*}, and \.{@@t}.
Most sections will begin with \.{@@\ }: these are `regular' sections,
which might be named or unnamed.

@l
(defclass section ()
  ((name :accessor section-name :initarg :name)
   (number :accessor section-number)
   (commentary :accessor section-commentary :initarg :commentary)
   (code :accessor section-code :initarg :code))
  (:default-initargs :name nil :commentary nil :code nil))

@t It's occasionally useful in testing to be able to use numbers as if
they were sections, at least for numbering purposes.

@l
(defmethod section-number ((section integer)) section)

@ Sections introduced with \.{@@*} (`starred' sections) begin a new group
of sections, and get some special formatting during weaving. The control
code \.{@@*} should be immediately followed by a title for this group,
terminated by a period. That title will appear as a run-in heading at the
beginning of the section, as a running head on all subsequent pages until
the next starred section, and in the table of contents.

Starred sections have a numeric parameter associated with them called
`depth'. The depth of a starred section affects how it is formatted in the
woven output: the section name is indented according to its depth in the
table of contents, and sections with small depths (i.e., close to 0) force
a page break.

The tangler makes no distinction at all between sections with stars and
ones with none upon thars.

@l
(defclass starred-section (section)
  ((depth :reader section-depth :initarg :depth))
  (:default-initargs :depth 0))

(defun starred-section-p (object) (typep object 'starred-section))

@ Non-starred sections have no depth, but it shouldn't be an error to ask.

@l
(defmethod section-depth ((section section)) nil)

@ Sections that begin with \.{@@t} are {\it test sections}. They are used to
include test cases alongside the normal code, but are treated specially by
both the tangler and the weaver. The tangler writes them out to a separate
file, and the weaver may elide them entirely.

Test sections are automatically associated with the last non-test section
defined, on the assumption that tests will be defined immediately after the
code they're designed to exercise.

@l
(defclass test-section (section)
  ((test-for :accessor test-for-section :initform nil)))

(defclass starred-test-section (test-section starred-section) ())

(defun test-section-p (object) (typep object 'test-section))

(defmethod initialize-instance :after ((section test-section) &key)
  (when (> (fill-pointer *sections*) 0)
    (setf (test-for-section section) ;
          (elt *sections* (1- (fill-pointer *sections*))))))

@ There can also be \TeX\ text preceding the start of the first section (i.e.,
before the first \.{@@\ } or \.{@@*}), called {\it limbo text}. Limbo text
is generally used to define document-specific formatting macros, set up
fonts, \etc. The weaver passes it through virtually verbatim to the output
file (only replacing occurrences of `\.{@@@@}' with~`\.{@@}'), and the
tangler ignores it completely.

A single instance of the class |limbo-section| contains the limbo text in
its |commentary| slot; it will never have a code part.

@l
(defclass limbo-section (section) ())

@ Whenever we create a non-test section, we store it in the global
|*sections*| vector and set its number to its index therein. This means
that section objects won't be collected by the garbage collector even after
the tangling or weaving has completed, but there's a good reason: keeping
them around allows incremental redefinition of a web, which is important
for interactive development.

We'll also keep the global variable |*current-section*| pointing to the
last section (test or not) created.

@<Global variables@>=
(defvar *sections* (make-array 128 :adjustable t :fill-pointer 0))
(defvar *current-section* nil)

@ @<Initialize global variables@>=
(setf (fill-pointer *sections*) 0)
(setf *current-section* nil)

@ Here's where section numbers are assigned. We use a generic function
for |push-section| so that we can override it for test sections.

@l
(defgeneric push-section (section))
(defmethod push-section ((section section))
  (setf (section-number section) (vector-push-extend section *sections*))
  section)

(defmethod initialize-instance :after ((section section) &key)
  (setq *current-section* (push-section section)))

@t Ensure that the |*current-section*| variable is updated after a new
section instance is made.

@l
(deftest current-section
  (let ((*sections* (make-array 1 :fill-pointer 0)))
    (eql (make-instance 'section) *current-section*))
  t)

@ Test sections aren't stored in the |*sections*| vector; we keep them
separate so that they won't interfere with the numbering of the other
sections.

@<Global variables@>=
(defvar *test-sections* (make-array 128 :adjustable t :fill-pointer 0))

@ @<Initialize global variables@>=
(setf (fill-pointer *test-sections*) 0)

@ @l
(defmethod push-section ((section test-section))
  (let ((*sections* *test-sections*))
    (call-next-method)))

@ The test sections all get woven to a separate output file, and we'll
need a copy of the limbo text there, too.

@l
(defmethod push-section :after ((section limbo-section))
  (vector-push-extend section *test-sections*))

@t To make testing with sections a little easier, we'll define a macro,
|with-temporary-sections|, that will help ensure that we don't accidentally
clobber any real sections. It executes |body| in an environment where
|*sections*| and |*named-sections*| have been rebound and augmented with
the new sections specified by the |sections| argument. That argument should
be a list of {\it section specifiers}, which are lists beginning with one of
the keywords |:section|, |:starred-section|, or~|:limbo|, followed by keyword
arguments that will be used to initialize new |section| instances; e.g.,
|:name| and~|:code|.

@l
(defmacro with-temporary-sections (sections &body body)
  (with-unique-names (spec section name)
    `(let ((*sections* (make-array 16 :adjustable t :fill-pointer 0))
           (*test-sections* (make-array 16 :adjustable t :fill-pointer 0))
           (*named-sections* nil))
       (dolist (,spec ,sections)
         (let* ((,section (apply #'make-instance
                                 (ecase (pop ,spec)
                                   (:section 'section)
                                   (:starred-section 'starred-section)
                                   (:limbo 'limbo-section))
                                 ,spec))
                (,name (section-name ,section)))
           (when ,name
             (push ,section (named-section-sections (find-section ,name))))))
       ,@body)))

@ We keep named sections in a binary search tree whose keys are section
names and whose values are code forms; the tangler will replace references
to those names with the associated code. We use a tree instead of, say,
a hash table so that we can support abbreviations (see below).

@l
(defclass binary-search-tree ()
  ((key :accessor node-key :initarg :key)
   (left-child :accessor left-child :initarg :left)
   (right-child :accessor right-child :initarg :right))
  (:default-initargs :left nil :right nil))

@ The primary interface to the {\sc bst} is the following routine, which
attempts to locate the node with key |item| in the tree rooted at |root|.
If it is not already present and the |insert-if-not-found| argument
is true, a new node is created with that key and added to the tree. The
arguments |predicate| and |test| should be designators for functions
of two arguments, both of which will be node keys; |predicate| should
return true iff its first argument precedes its second in the total
ordering used for the tree, and |test| should return true iff the two
keys are to be considered equivalent.

Two values are returned: the node with key |item| (or |nil| if no such node
was found and |insert-if-not-found| is false), and a boolean representing
whether or not the node was already in the tree.

@l
(defgeneric find-or-insert (item root &key predicate test insert-if-not-found))

(defmethod find-or-insert (item (root binary-search-tree) &key
                           (predicate #'<) (test #'eql)
                           (insert-if-not-found t))
  (flet ((lessp (item node) (funcall predicate item (node-key node)))
         (samep (item node) (funcall test item (node-key node))))
    (do ((parent nil node)
         (node root (if (lessp item node)
                        (left-child node)
                        (right-child node))))
        ((or (null node) (samep item node))
         (if node
             (values node t)
             (if insert-if-not-found
                 @<Insert a new node with key |item| and return it@>
                 (values nil nil)))))))

@ @<Insert a new node...@>=
(let ((node (make-instance (class-of root) :key item)))
  (when parent
    (if (lessp item parent)
        (setf (left-child parent) node)
        (setf (right-child parent) node)))
  (values node nil))

@ Besides searching, probably the most common operation on a {\sc bst} is
to traverse it in-order, applying some function to each node.

@l
(defgeneric map-bst (function tree))

(defmethod map-bst (function (tree null))
  (declare (ignore function)))
(defmethod map-bst (function (tree binary-search-tree))
  (map-bst function (left-child tree))
  (funcall function tree)
  (map-bst function (right-child tree)))

@t Make sure our binary search trees are working as advertised.

@l
(deftest (bst simple)
  (let ((tree (make-instance 'binary-search-tree :key 0)))
    (find-or-insert -1 tree)
    (find-or-insert 1 tree)
    (values (node-key tree)
            (node-key (left-child tree))
            (node-key (right-child tree))))
  0 -1 1)

(deftest (bst random)
  (let ((tree (make-instance 'binary-search-tree :key 0))
        (numbers (cons 0 (loop with limit = 1000
                               for i from 1 to limit
                               collect (random limit)))))
    (dolist (n numbers)
      (find-or-insert n tree))
    (let ((keys '()))
      (flet ((push-key (node)
               (push (node-key node) keys)))
        (map-bst #'push-key tree)
        (equal (nreverse keys)
               (remove-duplicates (sort numbers #'<))))))
  t)

(deftest (bst find-no-insert)
  (let ((tree (make-instance 'binary-search-tree :key 0)))
    (find-or-insert -1 tree :insert-if-not-found nil))
  nil nil)

@ As mentioned above, named sections can be defined piecemeal, with the
code spread out over several sections in the \CLWEB\ source. We might think
of a named section as a sort of `virtual' section, which consists of a
name, the combined code parts of all of the physical sections with that
name, and the number of the first such section.

And that's what we store in the {\sc bst}: nodes that look like sections,
inasmuch as they have specialized |section-name|, |section-code|, and
|section-number| methods, but are not actually instances of the class
|section|. The commentary and code are stored in the |section| instances
that comprise a given named section: references to those sections are
stored in the |sections| slot.

The weaver uses the last two slots, |used-by| and~|cited-by|, to generate
cross-references. They will be populated during reading with lists of all
the sections that reference this named section.

@l
(defclass named-section (binary-search-tree)
  ((key :accessor section-name :initarg :name)
   (sections :accessor named-section-sections :initform '())
   (used-by :accessor used-by :initform '())
   (cited-by :accessor cited-by :initform '())))

(defmethod named-section-sections :around ((section named-section))
  (sort (copy-list (call-next-method)) #'< :key #'section-number))

(defmethod section-code ((section named-section))
  (mapappend #'section-code (named-section-sections section)))

(defmethod section-number ((section named-section))
  (let ((sections (named-section-sections section)))
    (when (null sections)
      (error 'undefined-named-section-error
             :format-control "Undefined named section <~A>."
             :format-arguments (list (section-name section))))
    (section-number (first sections))))

@t@l
(deftest named-section-number/code
  (with-temporary-sections
      '((:section :name "foo" :code (1))
        (:section :name "foo" :code (2))
        (:section :name "foo" :code (3)))
    (let ((section (find-section "foo")))
      (values (section-code section)
              (section-number section))))
  (1 2 3)
  0)

(deftest undefined-named-section
  (handler-case (section-number (make-instance 'named-section :name "foo"))
    (undefined-named-section-error () :error))
  :error)

@ @<Condition classes@>=
(define-condition undefined-named-section-error (simple-error) ())

@ Section names in the input file can be abbreviated by giving a prefix of
the full name followed by `$\ldots$': e.g., \.{@@<Frob...@@>} might refer
to the section named `Frob \(foo\) and tweak \(bar\)'.

Here's a little utility routine that makes working with such section names
easier. Given a name, it returns two values: true or false depending on
whether the name is a prefix or not, and the length of the non-`\.{...}'
segment of the name.

@l
(defun section-name-prefix-p (name)
  (let ((len (length name)))
    (if (string= name "..." :start1 (max (- len 3) 0) :end1 len)
        (values t (- len 3))
        (values nil len))))

@t@l
(deftest (section-name-prefix-p 1) (section-name-prefix-p "a") nil 1)
(deftest (section-name-prefix-p 2) (section-name-prefix-p "ab...") t 2)
(deftest (section-name-prefix-p 3) (section-name-prefix-p "abcd...") t 4)

@ Next we need some special comparison routines for section names that
might be abbreviations. We'll use these as the |test| and |predicate|
functions, respectively, for our {\sc bst}.

@l
(defun section-name-lessp (name1 name2)
  (let ((len1 (nth-value 1 (section-name-prefix-p name1)))
        (len2 (nth-value 1 (section-name-prefix-p name2))))
    (string-lessp name1 name2 :end1 len1 :end2 len2)))

(defun section-name-equal (name1 name2)
  (multiple-value-bind (prefix-1-p len1) (section-name-prefix-p name1)
    (multiple-value-bind (prefix-2-p len2) (section-name-prefix-p name2)
      (let ((end (min len1 len2)))
        (if (or prefix-1-p prefix-2-p)
            (string-equal name1 name2 :end1 end :end2 end)
            (string-equal name1 name2))))))

@t@l
(deftest (section-name-lessp 1) (section-name-lessp "b" "a") nil)
(deftest (section-name-lessp 2) (section-name-lessp "b..." "a...") nil)
(deftest (section-name-lessp 3) (section-name-lessp "ab" "a...") nil)

(deftest (section-name-equal 1) (section-name-equal "a" "b") nil)
(deftest (section-name-equal 2) (section-name-equal "a" "a") t)
(deftest (section-name-equal 3) (section-name-equal "a..." "ab") t)
(deftest (section-name-equal 4) (section-name-equal "a..." "ab...") t)

@ When we look up a named section, either the name used to perform the
lookup, the name for the section in the tree, or both might be a prefix
of the full section name.

@l
(defmethod find-or-insert (item (root named-section) &key
                           (predicate #'section-name-lessp)
                           (test #'section-name-equal)
                           (insert-if-not-found t))
  (multiple-value-bind (node present-p)
      (call-next-method item root
                        :predicate predicate
                        :test test
                        :insert-if-not-found insert-if-not-found)
    (if present-p
        (or @<Check for an ambiguous match, and raise an error in that case@>
            (values node t))
        (values node nil))))

@ @<Condition classes@>=
(define-condition ambiguous-prefix-error (error)
  ((prefix :reader ambiguous-prefix :initarg :prefix)
   (first-match :reader ambiguous-prefix-first-match :initarg :first-match)
   (alt-match :reader ambiguous-prefix-alt-match :initarg :alt-match))
  (:report
   (lambda (condition stream)
     (format stream "~@<Ambiguous prefix: <~A> matches both <~A> and <~A>~:@>" ;
@.Ambiguous prefix...@>
             (ambiguous-prefix condition)
             (ambiguous-prefix-first-match condition)
             (ambiguous-prefix-alt-match condition)))))

@ If there is an ambiguity in a prefix match, the tree ordering guarantees
that it will occur in the sub-tree rooted at |node|.

@<Check for an ambiguous match...@>=
(dolist (child (list (left-child node) (right-child node)))
  (when child
    (multiple-value-bind (alt present-p)
        (call-next-method item child
                          :predicate predicate
                          :test test
                          :insert-if-not-found nil)
      (when present-p
        (restart-case
            (error 'ambiguous-prefix-error
                   :prefix item
                   :first-match (node-key node)
                   :alt-match (node-key alt))
          (use-first-match ()
            :report "Use the first match."
            (return (values node t)))
          (use-alt-match ()
            :report "Use alternate match."
            (return (values alt t))))))))

@ We store our named section tree in the global variable |*named-sections*|,
which is reset before each tangling or weaving. The reason this is global is
the same as the reason |*sections*| was: to allow incremental redefinition.

@<Global variables@>=
(defvar *named-sections* nil)

@ @<Initialize global variables@>=
(setq *named-sections* nil)

@ Section names are normalized by |squeeze|, which trims leading and
trailing whitespace and replaces all runs of one or more whitespace
characters with a single space. Thanks to Richard M.~Kreuter for the
basic structure of this implementation.

@l
(defun squeeze (string)
  (with-input-from-string (*standard-input* string)
    (with-output-to-string (*standard-output*)
      (handler-case
          (flet ((snarf-whitespace ()
                   (loop for char = (read-char)
                         while (whitespacep char)
                         finally (unread-char char))))
            (loop initially (snarf-whitespace)
                  for char = (read-char)
                  do (write-char (if (whitespacep char)
                                     (progn (snarf-whitespace) #\Space)
                                     char))))
        (end-of-file ())))))

@t@l
(deftest (squeeze 1) (squeeze "abc") "abc")
(deftest (squeeze 2) (squeeze "ab c") "ab c")
(deftest (squeeze 3) (squeeze (format nil " a b ~C c " #\Tab)) "a b c")

@ The predicate |whitespacep| determines whether or not a given character
should be treated as whitespace. Note, however, that this routine does
not---and can not, at least not portably---examine the current readtable
to determine which characters currently have ${\it whitespace}_2$ syntax.

@l
(defun whitespacep (char)
  (find char *whitespace* :test #'char=))

@ Only the characters named `Newline' and `Space' are required to be
present in a conforming Common Lisp implementation, but most also
support the semi-standard names `Tab', `Linefeed', `Return', and~`Page'.
Any of these that are supported should be considered whitespace characters.

@<Glob...@>=
(defparameter *whitespace*
  #.(coerce (remove-duplicates
             (remove nil (mapcar #'name-char
                                 '("Newline" "Space" ;
                                   "Tab" "Linefeed" "Return" "Page"))))
            'string))

@ The next routine is our primary interface to named sections: it looks up
a section by name in the tree, and creates a new one if no such section
exists.

@l
(defun find-section (name &aux (name (squeeze name)))
  (if (null *named-sections*)
      (setq *named-sections* (make-instance 'named-section :name name))
      (multiple-value-bind (section present-p)
          (find-or-insert name *named-sections*)
        (when present-p
          @<Update the section name if the new one is better@>)
        section)))

@ We only actually update the name of a section in two cases: if the new
name is not an abbreviation but the old one was, or if they are both
abbreviations but the new one is shorter. (We only need to compare against
the shortest available prefix, since we detect ambiguous matches.)

@<Update the section name...@>=
(multiple-value-bind (new-prefix-p new-len)
    (section-name-prefix-p name)
  (multiple-value-bind (old-prefix-p old-len)
      (section-name-prefix-p (section-name section))
    (when (or (and old-prefix-p (not new-prefix-p))
              (and old-prefix-p new-prefix-p (< new-len old-len)))
      (setf (section-name section) name))))

@t We'll use |*sample-named-sections*| whenever we need to test with some
named sections defined. The tests below don't depend on these sections
having code parts, but later tests will.

@l
(defvar *sample-named-sections*
  (with-temporary-sections
      '((:section :name "foo" :code (:foo))
        (:section :name "bar" :code (:bar))
        (:section :name "baz" :code (:baz))
        (:section :name "quux" :code (:quux :quuux :quuuux)))
    *named-sections*))

(defmacro with-sample-named-sections (&body body)
  `(let ((*named-sections* *sample-named-sections*))
     ,@body))

(defun find-sample-section (name)
  (find-or-insert name *sample-named-sections* :insert-if-not-found nil))

(deftest find-named-section
  (section-name (find-sample-section "foo"))
  "foo")

(deftest find-section-by-prefix
  (section-name (find-sample-section "f..."))
  "foo")

(deftest find-section-by-ambiguous-prefix
  (let ((handled nil))
    (values (section-name (handler-bind ((ambiguous-prefix-error
                                          (lambda (condition)
                                            (declare (ignore condition))
                                            (setq handled t)
                                            (invoke-restart 'use-first-match))))
                            (find-sample-section "b...")))
            handled))
  "bar"
  t)

(deftest find-section
  (with-sample-named-sections
    (find-section (format nil " foo  bar ~C baz..." #\Tab))
    (section-name (find-section "foo...")))
  "foo")

@*Reading a web. We distinguish five distinct modes for reading.
{\it Limbo mode\/} is used for \TeX\ text that precedes the first section
in a web. {\it \TeX\ mode\/} is used for reading the commentary that begins
a section. {\it Lisp mode\/} is used for reading the code part of a section.
{\it Inner-Lisp mode\/} is for reading Lisp forms that are embedded within
\TeX\ material. And {\it restricted mode\/} is used for reading material in
section names and a few other places. The modes are named by the symbols
|:limbo|, |:TeX|, |:lisp|, |:inner-lisp|, and~|:restricted|, respectively.

@<Global variables@>=
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *modes* '(:limbo :TeX :lisp :inner-lisp :restricted)))

(deftype mode () `(member ,@*modes*))

@ We use separate readtables for each mode, stored as an alist keyed on the
mode name. We add an extra mode with name |nil| that keeps a virgin copy of
the standard readtable for when we want to read in `no-mode'. Although we
will modify the readtables stored there, the |*readtables*| list itself
is never changed.

@<Global variables@>=
(defvar *readtables* ;
  (loop for mode in (cons 'nil *modes*) ;
        collect (cons mode (copy-readtable nil))))

@ We'll access the mode-specific readtables via |readtable-for-mode|.

@l
(defun readtable-for-mode (mode)
  (declare (type (or mode null) mode))
  (cdr (assoc mode *readtables*)))

@t@l
(deftest (readtable-for-mode 1) (readtablep (readtable-for-mode :tex)) t)
(deftest (readtable-for-mode 2) (readtablep (readtable-for-mode nil)) t)
(deftest (readtable-for-mode 3)
  (eql (readtable-for-mode :tex) (readtable-for-mode :lisp))
  nil)

@ The following macro executes the given |body| with |*readtable*| bound
appropriately for |mode|.

@l
(defmacro with-mode (mode &body body)
  `(let ((*readtable* (readtable-for-mode ,mode)))
     ,@body))

@t@l
(deftest with-mode
  (loop for (mode . readtable) in *readtables*
        always (with-mode mode (eql *readtable* readtable)))
  t)

@ Sometimes we'll have to detect and report errors during reading. This
condition class and the associated signaling function allow |format|-style
error reporting.

@<Condition classes@>=
(define-condition simple-reader-error (reader-error simple-condition) ()
  (:report (lambda (condition stream)
             (format stream "~S on ~S:~%~?"
                     condition (stream-error-stream condition)
                     (simple-condition-format-control condition)
                     (simple-condition-format-arguments condition)))))

@ This function just signals an error of type |simple-reader-error|.

@l
(defun simple-reader-error (stream control &rest args)
  (error 'simple-reader-error
         :stream stream
         :format-control control
         :format-arguments args))

@ We'll use this object as our end-of-file marker (i.e., as the |eof-value|
argument to |read|). It need not be a symbol; it need not even be an atom.

@<Global variables@>=
(defvar *eof* (make-symbol "EOF"))

@ But instead of using the variable |*eof*| directly in calls to |read|,
we'll use the symbol macro |eof|, which bypasses the variable lookup at
run-time.

@l
(eval-when (:compile-toplevel :load-toplevel :execute)
  (define-symbol-macro eof (load-time-value *eof* t)))

@ We'll test for our {\sc eof} value using |eof-p|.

@l
(defun eof-p (object) (eq object eof))
(deftype eof () '(satisfies eof-p))

@t@l
(deftest eof-p (eof-p (read-from-string "" nil eof)) t)
(deftest eof-type (typep (read-from-string "" nil eof) 'eof) t)

@ We'll occasionally need to know if a given character terminates a token
or not. This function answers that question, but only approximately---if
the user has frobbed the current readtable and set non-standard characters
to whitespace syntax, {\it this routine will not yield the correct
result}. There's unfortunately nothing that we can do about it portably,
since there's no standard way of determining the syntax of a character or
of obtaining a list of all the characters with a given syntax.

@l
(defun token-delimiter-p (char)
  (declare (type character char))
  (or (whitespacep char)
      (multiple-value-bind (function non-terminating-p) ;
          (get-macro-character char)
        (and function (not non-terminating-p)))))

@t@l
(deftest (token-delimiter-p 1) (not (token-delimiter-p #\Space)) nil)
(deftest (token-delimiter-p 2) (not (token-delimiter-p #\))) nil)

@ In some of the reading routines we'll define below, we need to be
careful about reader macro functions that don't return any values. For
example, if the input file contains `\.{(\#\v...\v\#)}', and we na{\"\i}vely
call |read| in the reader macro function for `|#\(|'\thinspace, an error
will be signaled, since |read| will skip over the comment and invoke the
reader macro function for `|#\)|'\thinspace.

The solution is to peek at the next character in the input stream and
manually invoke the associated reader macro function (if any), returning a
list of the values returned by that function. If the next character is not
a macro character, we just call |read| or |read-preserving-whitespace|,
returning a list containing the single object so read.

@l
(defun read-maybe-nothing-internal (read stream ;
                                    eof-error-p eof-value recursive-p)
  (multiple-value-list
   (let* ((next-char (peek-char nil stream nil nil recursive-p))
          (macro-fun (and next-char (get-macro-character next-char))))
     (cond (macro-fun
            (read-char stream)
            (call-reader-macro-function macro-fun stream next-char))
           (t (funcall read stream eof-error-p eof-value recursive-p))))))

(defun read-maybe-nothing (stream &optional ;
                           (eof-error-p t) eof-value recursive-p)
  (read-maybe-nothing-internal #'read stream eof-error-p eof-value recursive-p))

(defun read-maybe-nothing-preserving-whitespace ;
    (stream &optional (eof-error-p t) eof-value recursive-p)
  (read-maybe-nothing-internal #'read-preserving-whitespace ;
                               stream eof-error-p eof-value recursive-p))

@t@l
(deftest (read-maybe-nothing 1)
  (with-input-from-string (s "123") (read-maybe-nothing s))
  (123))

(deftest (read-maybe-nothing 2)
  (with-input-from-string (s "#|x|#") (read-maybe-nothing s))
  nil)

(deftest (read-maybe-nothing-preserving-whitespace)
  (with-input-from-string (s "x y")
    (read-maybe-nothing-preserving-whitespace s t nil nil)
    (peek-char nil s))
  #\Space)

@ In SBCL, most of the standard reader macro functions assume that they're
being called in an environment where the global read buffer is bound and
initialized. It would be nice if that wasn't the case and we could elide
the following nonsense.
@^SBCL@>

@l
(defmacro with-read-buffer ((&rest args) &body body)
  (declare (ignorable args))
  #+sbcl `(sb-impl::with-read-buffer ,args ,@body)
  #-sbcl `(progn ,@body))

(defun call-reader-macro-function (fn stream char)
  (with-read-buffer ()
    (funcall fn stream char)))

@1*Tracking character position. We want the weaver to output properly
indented code, but it's basically impossible to automatically indent
Common Lisp code without a complete static analysis. And so we don't try.
What we do instead is assume that the input is indented correctly, and
try to approximate that on output; we call this process {\it indentation
tracking}.
@^Indentation tracking@>

The way we do this is to record the the column number, or {\it character
position}, of every Lisp form in the input, and use those positions to
reconstruct the original indentation.

We'll define a {\it charpos stream\/} as an object that tracks the
character position of an underlying stream. Note that these aren't
instances of |stream| (and can't be, without relying on an extension to
Common Lisp like Gray streams). But they contain a standard composite
stream we'll call a {\it proxy stream\/} which is hooked up to the underlying
stream whose position they're tracking. It's these proxy streams that
we'll pass around, so all the standard stream functions will still work.
@^proxy stream@>

@l
(defclass charpos-stream ()
  ((charpos :initarg :charpos :initform 0)
   (proxy-stream :accessor charpos-proxy-stream :initarg :proxy)))

@ The {\sc gf} |charpos| returns the current character position of a charpos
stream. It relies on the last calculated character position (stored in the
|charpos| slot) and a buffer that stores the characters input or output
since the last call to |charpos|, retrieved with |get-charpos-stream-buffer|.
Tabs in the underlying stream are interpreted as advancing the column number
to the next multiple of |*tab-width*|.

@l
(defgeneric get-charpos-stream-buffer (stream))

(defgeneric charpos (stream))
(defmethod charpos ((stream charpos-stream))
  (with-slots (charpos) stream
    (loop for char across (get-charpos-stream-buffer stream)
          do (case char
               (#\Tab (incf charpos (- *tab-width* (rem charpos *tab-width*))))
               (#\Newline (setf charpos 0))
               (t (incf charpos)))
          finally (return charpos))))

@ @<Glob...@>=
(defparameter *tab-width* 8)

@ For tracking the character position of an input stream, our proxy stream
will be an echo stream that takes input from the underlying stream and sends
its output to a string stream, which we'll use as our buffer.

@l
(defclass charpos-input-stream (charpos-stream) ())

(defmethod shared-initialize :around ;
    ((instance charpos-input-stream) slot-names &rest initargs &key stream)
  (apply #'call-next-method instance slot-names
         (list* :proxy (make-echo-stream
                        stream
                        (make-string-output-stream
                         :element-type (stream-element-type stream)))
                initargs)))

(defmethod get-charpos-stream-buffer ((stream charpos-input-stream))
  (get-output-stream-string
   (echo-stream-output-stream (charpos-proxy-stream stream))))

@ For the output stream case, our proxy stream is a broadcast stream to the
given stream and a fresh string stream, again used as a buffer.

@l
(defclass charpos-output-stream (charpos-stream) ())

(defmethod shared-initialize :around ;
    ((instance charpos-output-stream) slot-names &rest initargs &key stream)
  (apply #'call-next-method instance slot-names
         (list* :proxy (make-broadcast-stream
                        (make-string-output-stream
                         :element-type (stream-element-type stream))
                        stream)
                initargs)))

(defmethod get-charpos-stream-buffer ((stream charpos-output-stream))
  (get-output-stream-string
   (first (broadcast-stream-streams (charpos-proxy-stream stream)))))

@ Because we'll be passing around the proxy streams, we need to manually
maintain a mapping between them and their associated instances of
|charpos-stream|.

@<Global variables@>=
(defvar *charpos-streams* (make-hash-table :test #'eq))

@ @l
(defmethod initialize-instance :after ((instance charpos-stream) &key)
  (setf (gethash (charpos-proxy-stream instance) *charpos-streams*) instance))

@ The top-level interface to the charpos streams are the following two
functions: |stream-charpos| retrieves the character position of the stream
for which |stream| is a proxy, and |release-charpos-stream| deletes the
reference to the stream maintained by the associated |charpos-stream|
instance.

@l
(defun stream-charpos (stream)
  (charpos (or (gethash stream *charpos-streams*)
               (error "Not tracking charpos for ~S" stream))))

(defun release-charpos-stream (stream)
  (multiple-value-bind (charpos-stream present-p)
      (gethash stream *charpos-streams*)
    (cond (present-p
           (setf (charpos-proxy-stream charpos-stream) nil) ; release stream
           (remhash stream *charpos-streams*))
          (t (warn "Not tracking charpos for ~S" stream)))))

@ Here are a few convenience methods for creating charpos streams. The
|input-stream| and |output-stream| arguments are stream designators.

@l
(defun make-charpos-input-stream (input-stream &key (charpos 0))
  (make-instance 'charpos-input-stream
                 :stream (case input-stream
                           ((t) *terminal-io*)
                           ((nil) *standard-input*)
                           (otherwise input-stream))
                 :charpos charpos))

(defun make-charpos-output-stream (output-stream &key (charpos 0))
  (make-instance 'charpos-output-stream
                 :stream (case output-stream
                           ((t) *terminal-io*)
                           ((nil) *standard-output*)
                           (otherwise output-stream))
                 :charpos charpos))

@ And finally, here are a couple of macros that make using them easy and
trouble-free. They execute |body| in a lexical environment in which |var|
is bound to a proxy stream the tracks the character position for |stream|.

@l
(defmacro with-charpos-input-stream ((var stream &key (charpos 0)) &body body)
  `(let ((,var (charpos-proxy-stream ;
                (make-charpos-input-stream ,stream :charpos ,charpos))))
     (unwind-protect (progn ,@body)
       (release-charpos-stream ,var))))

(defmacro with-charpos-output-stream ((var stream &key (charpos 0)) &body body)
  `(let ((,var (charpos-proxy-stream ;
                (make-charpos-output-stream ,stream :charpos ,charpos))))
     (unwind-protect (progn ,@body)
       (release-charpos-stream ,var))))

@t@l
(deftest charpos-input-stream
  (let ((*tab-width* 8))
    (with-charpos-input-stream (s (make-string-input-stream
                                   (format nil "012~%abc~C~C" #\Tab #\Tab)))
      (values (stream-charpos s)
              (read-line s)
              (stream-charpos s)
              (read-char s)
              (read-char s)
              (read-char s)
              (stream-charpos s)
              (read-char s)
              (stream-charpos s)
              (read-char s)
              (stream-charpos s))))
  0 "012" 0 #\a #\b #\c 3 #\Tab 8 #\Tab 16)

(deftest charpos-output-stream
  (let ((string-stream (make-string-output-stream)))
    (with-charpos-output-stream (s string-stream)
      (values (stream-charpos s)
              (progn (write-string "012" s) (stream-charpos s))
              (progn (write-char #\Newline s) (stream-charpos s))
              (progn (write-string "abc" s) (stream-charpos s))
              (get-output-stream-string string-stream))))
  0 3 0 3 #.(format nil "012~%abc"))

@1*Stream utilities. Sometimes we'll want to look more than one character
ahead in a stream. This macro lets us do so, after a fashion: it executes
|body| in a lexical environment where |var| is bound to a stream whose
input comes from |stream| and |rewind| is bound to a local function that
`rewinds' that stream to its state prior to any reads that were executed in
the body. If |rewind| is invoked more than once, each subsequent invocation
will rewind to the state just after the previous one.

@l
(defmacro with-rewind-stream ((var stream &optional (rewind 'rewind)) &body body)
  (with-unique-names (in out close)
    `(let* ((,out (make-string-output-stream))
            (,var (make-echo-stream ,stream ,out))
            (,close (list ,var ,out)))
       (flet ((,rewind ()
                (let ((,in (make-string-input-stream ;
                            (get-output-stream-string ,out))))
                  (prog1 (setq ,var (make-concatenated-stream ,in ,var))
                    (pushnew ,var ,close)
                    (pushnew ,in ,close)))))
         (declare (ignorable (function ,rewind)))
         (unwind-protect (progn ,@body)
           (map nil #'close ,close))))))

@t@l
(deftest rewind-stream
  (with-input-from-string (s "abcdef")
    (with-rewind-stream (r s)
      (values (read-char r)
              (read-char r)
              (read-char r)
              (progn (rewind) (read-char r))
              (progn (rewind) (read-line r)))))
  #\a #\b #\c #\a "bcdef")

@ And sometimes, we'll want to call |read| on a stream, and keep a copy of
the characters that |read| actually scans. This macro reads from |stream|,
then executes the |body| forms with |object| bound to the object returned
by |read| and |echoed| bound to a variable containing the characters so
consumed.

@l
(defmacro read-with-echo ((stream object echoed) &body body)
  (with-unique-names (out echo raw-output length char)
    `(with-open-stream (,out (make-string-output-stream))
       (with-open-stream (,echo (make-echo-stream ,stream ,out))
         (let* ((,object (read-preserving-whitespace ,echo))
                (,raw-output (get-output-stream-string ,out))
                (,length (length ,raw-output))
                (,echoed (subseq ,raw-output 0 ;
                                 (if @<Should we include...@>
                                     ,length
                                     (1- ,length)))))
           (declare (ignorable ,object ,echoed))
           ,@body)))))

@ We have to be very careful here about delimiters. For self-delimiting
forms like quoted strings, the final delimiter will be---and should
be---the last character consumed. But if there's some other kind of
delimiter---a closing parenthesis, say---then it should {\it not\/} be
delivered as part of |echoed|. The problem is that such a delimiter may
very well have been read and then unread, and the standard says that when
|unread-char| is called with an echo stream as its |input-stream| argument,
``no attempt is made to undo any echoing of the character that might
already have been done on |input-stream|. However,'' it continues,
``characters placed on |input-stream| by |unread-char| are marked in such
a way as to inhibit later re-echo by |read-char|.'' So we can detect a
previously-unread character by reading and then unreading the next character
in the echo stream and seeing if it actually gets echoed.

@<Should we include the last character of |raw-input|?@>=
(let ((,char (read-char ,echo nil eof)))
  (or (eof-p ,char) ; clearly `yes' for {\sc eof}
      (progn (unread-char ,char ,echo)
             (plusp (length (get-output-stream-string ,out))))))

@t@l
(deftest (read-with-echo eof)
  (with-input-from-string (stream ":foo")
    (read-with-echo (stream object chars)
      (values object chars)))
  :foo ":foo")

(deftest (read-with-echo space)
  (with-input-from-string (stream  ":foo :bar")
    (read-with-echo (stream object chars)
      (values object chars)))
  :foo ":foo")

(deftest (read-with-echo string)
  (with-input-from-string (stream "\"foo\" :bar")
    (read-with-echo (stream object chars)
      (values object chars)))
  "foo" "\"foo\"")

(deftest (read-with-echo paren)
  (with-input-from-string (stream ":foo)")
    (read-with-echo (stream object chars)
      (values object chars)))
  :foo ":foo")

(deftest (read-with-echo vector)
  (with-input-from-string (stream "#(1 2 3) :foo")
    (read-with-echo (stream object chars)
      (values object chars)))
  #(1 2 3) "#(1 2 3)")

@1*Markers. Next, we define a class of objects called {\it markers\/} that
denote abstract objects in source code. Some of these objects, such as
newlines and comments, are ones that would ordinarily be ignored by the
reader. Others, such as \.{()} and~\.{'}, are indistinguishable after
reading from other, semantically equivalent objects (here, |nil| and
|quote|), but we want to preserve the distinction in the output. In fact,
nearly every standard macro character in Common Lisp is `lossy', in the
sense that the text of the original source code can not be reliably
recovered from the object returned by |read|.

But during weaving, we want to more closely approximate the original source
code than would be possible using the standard reader. Markers are our
solution to this problem: we define reader macro functions for all of the
standard macro characters that return markers that let us reconstruct, to
varying degrees of accuracy, what was originally given in the source.

If a marker is {\it bound\/}---i.e., if |marker-boundp| returns non-nil when
called with it as an argument---then the tangler will call |marker-value|
to obtain the associated value. (The weaver will never ask for a marker's
value.) Otherwise, the marker will be silently dropped from its containing
form; this is used, e.g., for newlines and comments. The value need not be
stored in the |value| slot, but often is.

@l
(defclass marker ()
  ((value :reader marker-value :initarg :value)))
(defun markerp (object) (typep object 'marker))

(defgeneric marker-boundp (marker))
(defmethod marker-boundp ((marker marker))
  (slot-boundp marker 'value))

@ We'll define specialized pretty-printing routines for some of the
objects we read for use by the tangler. Since they depend heavily on
the specific representations, they're best defined alongside the readers.
A few of these will also be used by the weaver, so we'll define the
accessor for that dispatch table, too.

@l
@<Define the pprint dispatch table setters@>

@ Here's a simple pretty-printing routine that suffices for many marker
types: it simply prints the marker's value if it is bound. Markers that
require specialized printing will override this method.

@l
(set-tangle-dispatch 'marker
  (lambda (stream marker)
    (when (marker-boundp marker)
      (write (marker-value marker) :stream stream))))

@t@l
(deftest print-marker
  (write-to-string (make-instance 'marker :value :foo)
                   :pprint-dispatch *tangle-pprint-dispatch*
                   :pretty t)
  ":FOO")

@t This |print-object| method is purely for debugging purposes.

@l
(defmethod print-object ((obj marker) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (when (marker-boundp obj)
      (princ (marker-value obj) stream))))

(deftest print-marker-unreadably
  (let ((*print-readably* t))
    (handler-case (format nil "~W" (make-instance 'marker :value :foo))
      (print-not-readable (condition)
        (marker-value (print-not-readable-object condition)))))
  :foo)

@ A few of the markers behave differently when tangling for the purposes
of evaluation (e.g., within a call to |load-web|) than when writing out a
tangled Lisp source file. We need this distinction only for read-time
evaluated constructs, such as \.{\#.} and~\.{\#+}/\.{\#-}.

@<Global variables@>=
(defvar *evaluating* nil)

@ Our first marker is for newlines, which we preserve for the purposes of
indentation. They are represented in code forms by an unbound marker, so
the tangler will ignore them. We'll interpret two newlines in a row as
ending a paragraph, as in \TeX; the weaver will insert a bit of extra
vertical space when it encounters such markers.

Note that we don't set a macro character for |#\Newline| in inner-Lisp mode,
since indentation is completely ignored there.

@l
(defclass newline-marker (marker)
  ((indentation :accessor indentation :initform nil)))
(defclass par-marker (newline-marker) ())
(defun newlinep (obj) (typep obj 'newline-marker))

(set-macro-character #\Newline
  (lambda (stream char)
    (declare (ignore char))
    (case (peek-char nil stream nil eof t)
      (#\Newline (read-char stream t nil t)
                 (make-instance 'par-marker))
      (otherwise (make-instance 'newline-marker))))
  nil (readtable-for-mode :lisp))

@t@l
(deftest read-newline
  (newlinep (with-input-from-string (s (format nil "~%"))
              (with-mode :lisp (read s))))
  t)

(deftest read-par
  (typep (with-input-from-string (s (format nil "~%~%"))
           (with-mode :lisp (read s)))
         'par-marker)
  t)

@ The rest of the reader macro functions for standard macro characters are
defined in the order given in section~2.4 of the \ansi\ Common Lisp standard.
We override all of the standard macro characters except |#\)| and~|#\"| (the
former because the standard reader macro function just signals an error,
which is fine, and the latter because we don't need markers for strings).
@^\ansi\ Common Lisp@>

@t When we're testing the reader macro functions, we'll often want to read
from a string-stream that tracks character positions. In fact, most of the
reader tests will involve reading a single form in Lisp mode.

@l
(defmacro read-from-string-with-charpos (string &optional
                                         (eof-error-p t)
                                         (eof-value nil) &key
                                         (preserve-whitespace nil))
  (let ((reader (if preserve-whitespace 'read-preserving-whitespace 'read)))
    (with-unique-names (string-stream charpos-stream)
      `(with-open-stream (,string-stream (make-string-input-stream ,string))
         (with-charpos-input-stream (,charpos-stream ,string-stream)
           (,reader ,charpos-stream ,eof-error-p ,eof-value))))))

(defun read-form-from-string (string &key (mode :lisp))
  (let ((*package* (find-package "CLWEB")))
    (with-mode mode
      (read-from-string-with-charpos string))))

@ {\it Left-Parenthesis.} We have two different kinds of markers for lists.
The first is one for empty lists, so that we can maintain a distinction
that the standard Lisp reader does not: between the empty list and |nil|.
The second, for non-empty lists, stores not just the elements of the list,
but their character positions as well; this is what allows us to do our
indentation tracking.

Note that we bind our empty-list marker to the value |'()| so that it's
preserved during tangling.

@l
(defclass empty-list-marker (marker) () (:default-initargs :value '()))
(defvar *empty-list* (make-instance 'empty-list-marker))

(defclass list-marker (marker)
  ((length :accessor list-marker-length :initarg :length)
   (list :accessor list-marker-list :initarg :list)
   (charpos :accessor list-marker-charpos :initarg :charpos)))
(defun list-marker-p (obj) (typep obj 'list-marker))

(defclass consing-dot-marker (marker) ())
(defvar *consing-dot* (make-instance 'consing-dot-marker))

(defmethod marker-boundp ((marker list-marker)) t)
(defmethod marker-value ((marker list-marker))
  (do* ((list (list nil))
        (tail list)
        (marker-list (list-marker-list marker) (cdr marker-list))
        (x (car marker-list) (car marker-list)))
       ((endp marker-list) (cdr list))
    (cond ((eq x *consing-dot*)
           (rplacd tail @<Find the tail...@>)
           (return (cdr list)))
          ((markerp x)
           (when (marker-boundp x)
             (let ((obj (list x)))
               (rplacd tail obj)
               (setq tail obj))))
          (t (let ((obj (list x)))
               (rplacd tail obj)
               (setq tail obj))))))

@ There might be more than one object in a list marker following a consing
dot, because of unbound markers (e.g., newlines and comments). So we just
use the first bound marker or non-marker object that we find.

@<Find the tail of the list marker@>=
(dolist (x marker-list (error "Nothing after . in list"))
  (when (or (not (markerp x))
            (and (markerp x)
                 (marker-boundp x)))
    (return x)))

@ We don't use |list-marker|s at all in inner-Lisp mode (since we don't do
indentation tracking there), but we still want markers for the empty list.
The function |make-list-reader| returns a closure that peeks ahead in the
given stream looking for a closing parenthesis, and either returns an
empty-list marker or invokes a full list-reading function, which is stored
in the variable |next|. For inner-Lisp mode, that function is the standard
reader macro function for `|#\(|'\thinspace.

@l
(defun make-list-reader (next)
  (lambda (stream char)
    (if (char= (peek-char t stream t nil t) #\) )
        (progn (read-char stream t nil t) *empty-list*)
        (funcall next stream char))))

(set-macro-character #\( (make-list-reader (get-macro-character #\( nil))
                     nil (readtable-for-mode :inner-lisp))

@t@l
(deftest (read-empty-list :inner-lisp)
  (typep (read-form-from-string "()" :mode :inner-lisp) 'empty-list-marker)
  t)

(deftest (read-list :inner-lisp)
  (listp (read-form-from-string "(:a :b :c)" :mode :inner-lisp))
  t)

(deftest read-empty-list
  (typep (read-form-from-string "()") 'empty-list-marker)
  t)

@ In Lisp mode, we need a full list reader that records character positions
of the list elements. This would be almost straightforward if not for the
consing dot.

@l
(defun list-reader (stream char)
  (declare (ignore char))
  (loop with list = '()
        with charpos-list = '()
        for n upfrom 0
        and next-char = (peek-char t stream t nil t)
        as charpos = (stream-charpos stream)
        until (char= #\) next-char)
        if (char= #\. next-char)
          do @<Read the next token from |stream|, which might be a consing dot@>
        else
          do @<Read the next object from |stream| and push it onto |list|@>
        finally (read-char stream t nil t)
                (return (make-instance 'list-marker
                                       :length n
                                       :list (nreverse list)
                                       :charpos (nreverse charpos-list)))))

(set-macro-character #\( (make-list-reader #'list-reader)
                     nil (readtable-for-mode :lisp))

@t Check that when we read a list, we get both the contents and the character
positions correct.

@l
(defmacro define-list-reader-test (name string expected-list expected-charpos)
  `(deftest ,name
     (let* ((marker (read-form-from-string ,string))
            (list (marker-value marker))
            (charpos (list-marker-charpos marker)))
       (and (equal list ',expected-list)
            (equal charpos ',expected-charpos)))
     t))

(define-list-reader-test (list-reader 1) "(a b c)" (a b c) (1 3 5))
(define-list-reader-test (list-reader 2) "(a b . c)" (a b . c) (1 3 5 7))
(define-list-reader-test (list-reader 3) "(a b .c)" (a b .c) (1 3 5))
(define-list-reader-test (list-reader 4) "(a b #|c|#)" (a b) (1 3))
(define-list-reader-test (list-reader 5) "(#|foo|#)" () ())

@ If the next character is a dot, it could either be a consing dot, or the
beginning of a token that happens to start with a dot. We decide by looking
at the character {\it after\/} the dot: if it's a delimiter, then it
{\it was\/} a consing dot; otherwise, we rewind and carefully read in the
next object.

@<Read the next token from |stream|...@>=
(with-rewind-stream (stream stream)
  (read-char stream t nil t) ; consume dot
  (let ((following-char (read-char stream t nil t)))
    (cond ((token-delimiter-p following-char)
           (unless (or list *read-suppress*)
             (simple-reader-error stream "Nothing appears before . in list."))
           (unread-char following-char stream)
           (push *consing-dot* list)
           (push charpos charpos-list))
          (t (rewind)
             @<Read the next object...@>))))

@t@l
(deftest read-list-error
  (handler-case (read-form-from-string "(. a)")
    (reader-error () :error))
  :error)

(deftest read-dotted-list
  (with-input-from-string (stream "(foo .(foo))")
    (with-charpos-input-stream (cstream stream)
      (with-mode :lisp
        (read cstream)
        (peek-char nil cstream nil))))
  nil)

@ We have to be careful when reading in a list, because the next character
might be a macro character whose associated reader macro function returns
zero values, and we don't want to accidentally read the closing
`|#\)|'\thinspace.

@<Read the next object...@>=
(let ((values (read-maybe-nothing stream t nil t)))
  (when values
    (push (car values) list)
    (push charpos charpos-list)))

@ {\it Single-Quote.} We want to distinguish between a form quoted with
a single-quote and one quoted (for whatever reason) with |quote|, another
distinction ignored by the standard Lisp reader. We'll use this marker
class for \.{\#'}, too, which is why it's a little more general than one
might think is needed.

@l
(defclass quote-marker (marker)
  ((quote :reader quote-marker-quote :initarg :quote)
   (form :reader quoted-form :initarg :form)))

(defmethod marker-boundp ((marker quote-marker)) t)
(defmethod marker-value ((marker quote-marker))
  (list (quote-marker-quote marker) (quoted-form marker)))

(defun single-quote-reader (stream char)
  (declare (ignore char))
  (make-instance 'quote-marker :quote 'quote :form (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-macro-character #\' #'single-quote-reader nil (readtable-for-mode mode)))

@t@l
(deftest read-quoted-form
  (let ((marker (read-form-from-string "':foo")))
    (values (quoted-form marker)
            (marker-value marker)))
  :foo
  (quote :foo))

@ {\it Semicolon.} Comments in Lisp code also need to be preserved for
output during weaving. Comment markers are always unbound, and are
therefore stripped during tangling.

@l
(defclass comment-marker (marker)
  ((text :reader comment-text :initarg :text)))

@ To read a comment, we accumulate all of the characters starting with the
semicolon and ending just before the next newline, which we leave for the
newline reader to pick up. If the comment is empty, though, the newline is
consumed, and we return zero values. This provides for `soft newlines'; i.e.,
line breaks in the source file that will not appear in the woven output.

@l
(defun comment-reader (stream char)
  (if (char= (peek-char nil stream nil #\Newline t) #\Newline)
      (progn (read-char stream t nil t) (values))
      (make-instance 'comment-marker
                     :text @<Read characters up to, but not including,
                             the next newline@>)))

(set-macro-character #\; #'comment-reader nil (readtable-for-mode :lisp))

@ @<Read characters up to...@>=
(with-output-to-string (s)
  (write-char char s) ; include the opening |#\;|
  (do ()
      ((char= (peek-char nil stream nil #\Newline t) #\Newline))
    (write-char (read-char stream t nil t) s)))

@t@l
(deftest read-comment
  (let ((marker (read-form-from-string "; foo")))
    (values (comment-text marker)
            (marker-boundp marker)))
  "; foo"
  nil)

(deftest read-empty-comment
  (with-input-from-string (s (format nil ";~%"))
   (with-mode :lisp
     (read-maybe-nothing s)))
  nil)

@ {\it Backquote\/} has formally defined semantics, but the representation
is explicitly implementation-specific. We therefore need to supply our own
backquote reader to ensure a consistent representation across implementations.

This backquote implementation is based on Appendix~C of~\cltl. It has been
modified to conform to the overall style of this program, to support commas
inside vectors, and to remove the code simplifier. This last is in the
interest of simplicity: because we preserve backquotes during tangling, we
can leave optimization to the Lisp implementation.
@^\cltl@>

@ We use conses to represent backquoted forms (since, as we'll see,
backquote is an ordinary macro), but we'll use atomic instances of a
dedicated class to represent commas. The reason is that we depend on the
pretty printer to correctly print backquoted forms, and even though most
Lisp implementations support printing their own representations of
backquote and comma, there's no reason to expect them to correctly support
ours. (They don't even get their own representations right all of the time.)
Moreover, providing a pretty printing method for conses that have some
specialized comma representation as their car is not sufficient, because
many implementation-provided pretty printing routines (e.g., for |defun|,
|let|,~\etc.) blindly call down to something like |pprint-fill| without
first distinguishing between atoms and lists. (Thanks to Duane Rettig of
Franz,~Inc.\ for helping to track this down.) Using an atomic representation
guarantees that our commas won't accidentally be printed as lists.

It is still possible for this scheme to go wrong, though: if an
implementation-supplied pretty printing routine expects a list in some
context and gets an atom instead, it could signal an error. If this
happens to you, please report it to the author.

@l
(defvar *backquote* (make-symbol "BACKQUOTE"))
(defun backquotep (object) (eq object *backquote*))
(deftype backquote-form () '(cons (satisfies backquotep)))

(defclass comma ()
  ((form :initarg :form :initform nil)))
(defclass splicing-comma (comma)
  ((modifier :reader comma-modifier :initarg :modifier :type character)))

(defmethod comma-modifier ((comma comma)) nil)

(defun make-comma (modifier form)
  (if modifier
      (make-instance 'splicing-comma :modifier modifier :form form)
      (make-instance 'comma :form form)))

(defun commap (obj) (typep obj 'comma))

@ To process a comma, we need to tangle the form being unquoted. If that
form is a named section reference, we take the car of the tangled form,
on the assumption that you can't meaningfully unquote more than one form.
We accept an optional argument to disable the tangling for the sake of
the weaver, which wants the untangled form.

@l
(defgeneric comma-form (comma &key tangle))
(defmethod comma-form ((comma comma) &key (tangle t))
  (let ((form (slot-value comma 'form)))
    (unless tangle (return-from comma-form form))
    (let ((tangled-form (tangle form)))
      (typecase form
        (named-section
         (when (rest tangled-form)
           (cerror "Ignore the extra forms."
                   "Tried to unquote more than one form from section @<~A@>."
                   (section-name form)))
         (first tangled-form))
        (t tangled-form)))))

@t This is just for debugging. It's important for safety that commas be
printed using the unreadable object syntax.

@l
(defmethod print-object ((object comma) stream)
  (print-unreadable-object (object stream)
    (format stream ",~@[~C~]~S" (comma-modifier object) (comma-form object))))

@ The reader macro functions for backquote and comma are straightforward.

@l
(dolist (mode '(:lisp :inner-lisp))
  (set-macro-character #\`
    (lambda (stream char)
      (declare (ignore char))
      (list *backquote* (read stream t nil t)))
    nil (readtable-for-mode mode))
  (set-macro-character #\,
    (lambda (stream char)
      (declare (ignore char))
      (case (peek-char nil stream t nil t)
        ((#\@ #\.) (make-comma (read-char stream t nil t)
                               (read stream t nil t)))
        (otherwise (make-comma nil (read stream t nil t)))))
    nil (readtable-for-mode mode)))

@ |#:backquote| is an ordinary macro (not a read-macro) that processes the
expression~|x|, looking for embedded commas. We use an uninterned symbol
for |#:backquote| to avoid problems with macro expansion during indexing;
the indexing code walker breaks symbol identity during macro expansion, but
not for uninterned symbols.

@l
(defmacro backquote (x)
  (bq-process x))
(setf (macro-function *backquote*) (macro-function 'backquote))

(defun bq-process (x &aux (x (tangle x)))
  (typecase x
    (simple-vector `(apply #'vector ,(bq-process (coerce x 'list))))
    (splicing-comma (error ",~C~S after `" (comma-modifier x) (comma-form x)))
    (comma (comma-form x))
    (atom `(quote ,x))
    (backquote-form (bq-process (bq-process (cadr x))))
    (t @<Process the list |x| for backquotes and commas@>)))

@ We do one simplification here which, although not strictly in accordance
with the formal rules on pages~528--529 of~\cltl\ (section~2.4.6 of \ansi\
Common Lisp), is necessary in the presence of nested backquotes; viz.,~we
will never append |(quote nil)| to the end of a list. This seems to be an
error in the formal rules: in particular, reducing the case of a
|nil|-terminated list to the general case of a dotted list appears to be
overly simplistic.
@^\cltl@>
@^\ansi\ Common Lisp@>

@<Process the list |x|...@>=
(do ((p x (cdr p))
     (q '() (cons (bracket (car p)) q)))
    ((and (atom p) (not (commap p)))
     (cons 'append (nreconc q (and p (list (list 'quote p))))))
  (typecase p
    (splicing-comma (error "Dotted ,~C~S" (comma-modifier p) (comma-form p)))
    (comma (return (cons 'append (nreconc q (list (comma-form p))))))))

@ This implements the bracket operator of the formal rules.

@l
(defun bracket (x)
  (typecase x
    (splicing-comma (comma-form x))
    (comma `(list ,(comma-form x)))
    (t `(list ,(bq-process x)))))

@t The first two tests come from page~528 of~\cltl; the third comes from
Appendix~C.
@^\cltl@>

@l
(deftest (bq 1)
  (let ((b 3))
    (declare (special b))
    (equal (eval (tangle (read-form-from-string "`(a b ,b ,(+ b 1) b)")))
           '(a b 3 4 b)))
  t)

(deftest (bq 2)
  (let ((x '(a b c)))
    (declare (special x))
    (equal (eval (tangle
                  (read-form-from-string ;
                   "`(x ,x ,@x foo ,(cadr x) bar ,(cdr x) baz ,@(cdr x))")))
           '(x (a b c) a b c foo b bar (b c) baz b c)))
  t)

(defun r (x) (reduce #'* x))
(deftest (bq nested)
  (let ((q '(r s))
        (r '(3 5))
        (s '(4 6)))
    (declare (special q r s))
    (values (eval (eval (tangle (read-form-from-string "``(,,q)"))))
            (eval (eval (tangle (read-form-from-string "``(,@,q)"))))
            (eval (eval (tangle (read-form-from-string "``(,,@q)"))))
            (eval (eval (tangle (read-form-from-string "``(,@,@q)"))))))
  (24)
  24
  ((3 5) (4 6))
  (3 5 4 6))

@t@l
(deftest (bq vector)
  (let ((a '(1 2 3)))
    (declare (special a))
    (values (eval (tangle (read-form-from-string "`#(:a)")))
            (eval (tangle (read-form-from-string "`#(\"a\")")))
            (eval (tangle (read-form-from-string "`#(,a)")))
            (eval (tangle (read-form-from-string "`#(,@a)")))))
  #(:a)
  #("a")
  #((1 2 3))
  #(1 2 3))

@t Test the interaction between backquote, comma, and named sections.
If a named section with more than one form (like `\<quux>') follows a
comma, a continuable error is signaled, and all but the first are
discarded.

@l
(deftest (bq named-section)
  (with-sample-named-sections
    (values (eval (tangle (read-form-from-string "`(, @<foo@>)")))
            (eval (tangle (read-form-from-string "`(,@ @<foo@>)")))))
  (:foo)
  :foo)

(deftest (bq too-many-forms)
  (with-sample-named-sections
    (let ((handled nil))
      (handler-bind ((error (lambda (condition)
                              (setq handled t)
                              (continue condition))))
        (values (eval (tangle (read-form-from-string "`(,@ @<quux@>)")))
                handled))))
  :quux
  t)

@ During tangling, we print backquotes and commas using the backquote
syntax, as recommended (but not required) by section~2.4.6.1 of the
\ansi\ standard.
@^\ansi\ Common Lisp@>

@l
(set-tangle-dispatch 'backquote-form
  (lambda (stream obj) ;
    (format stream "`~W" (cadr obj))))

(set-tangle-dispatch 'comma
  (lambda (stream obj) ;
    (format stream ",~@[~C~]~W" (comma-modifier obj) (comma-form obj))))

@ {\it Sharpsign\/} is the all-purpose dumping ground for Common Lisp
reader macros. Because it's a dispatching macro character, we have to
handle each sub-char individually, and unfortunately we need to override
most of them. We'll handle them in the order given in section~2.4.8
of the CL standard.

@ Sharpsign single-quote is just like single-quote, except that the form is
`quoted' with |function| instead of |quote|.

@l
(defclass function-marker (quote-marker) ())

(defun sharpsign-quote-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (make-instance 'function-marker :quote 'function :form (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\' #'sharpsign-quote-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest read-function
  (let ((marker (read-form-from-string "#'identity")))
    (values (quoted-form marker)
            (marker-value marker)))
  identity
  #'identity)

@ Sharpsign left-parenthesis creates |simple-vector|s. The feature that we
care about preserving is the length specification and consequent possible
abbreviation.

@l
(defclass simple-vector-marker (marker)
  ((length :initarg :length)
   (elements :reader simple-vector-marker-elements :initarg :elements)
   (element-type :reader simple-vector-marker-element-type ;
                 :initarg :element-type))
  (:default-initargs :element-type t))

(defmethod marker-boundp ((marker simple-vector-marker)) t)
(defmethod marker-value ((marker simple-vector-marker))
  (let ((elements (tangle (simple-vector-marker-elements marker)))
        (element-type (simple-vector-marker-element-type marker)))
    (if (slot-boundp marker 'length)
        (with-slots (length) marker
          (let ((supplied-length (length elements)))
            (fill (replace (make-array length :element-type element-type) ;
                           elements)
                  (elt elements (1- supplied-length))
                  :start supplied-length)))
        (coerce elements `(vector ,element-type)))))

;; Adapted from SBCL's |sharp-left-paren|.
(defun simple-vector-reader (stream sub-char arg)
  (declare (ignore sub-char))
  (let* ((list (read-delimited-list #\) stream t))
         (length (handler-case (length list)
                   (type-error (error)
                     (declare (ignore error))
                     (simple-reader-error ;
                      stream "improper list in #(): ~S" list)))))
    (unless *read-suppress*
      (if arg
          (if (> length arg)
              (simple-reader-error ;
               stream "vector longer than specified length: #~S~S" arg list)
              (make-instance 'simple-vector-marker :length arg :elements list))
          (make-instance 'simple-vector-marker :elements list)))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\( #'simple-vector-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest read-simple-vector
  (marker-value (read-form-from-string "#5(:a :b :c #C(0 1))"))
  #(:a :b :c #C(0 1) #C(0 1)))

@ Sharpsign asterisk also creates a vector, but the token following the
asterisk must be composed entirely of the characters `0' and~`1', which
it uses to construct a |simple-bit-vector|. It supports the same kind of
length abbreviation that \.{\#()} does.

@l
(defclass bit-vector-marker (simple-vector-marker) ()
  (:default-initargs :element-type 'bit))

(defun simple-bit-vector-reader (stream sub-char arg)
  (declare (ignore sub-char))
  (apply #'make-instance 'bit-vector-marker
         :elements (coerce @<Read `0's and `1's from |stream|@> 'bit-vector)
         (when arg `(:length ,arg))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\* #'simple-bit-vector-reader ;
                                (readtable-for-mode mode)))

@ @<Read `0's and `1's...@>=
(loop for char = (read-char stream nil nil t)
      while (and char (or (char= char #\0) (char= char #\1)))
      collect (ecase char (#\0 0) (#\1 1))
      finally (when char (unread-char char stream)))

@t@l
(deftest read-bit-vector
  (marker-value (read-form-from-string "#6*101"))
  #6*101)

@ Sharpsign dot permits read-time evaluation. Ordinarily, of course, the
form evaluated is lost, as only the result of the evaluation is returned.
We want to preserve the form for both weaving and tangling to a file. But
we also want to return the evaluated form as the |marker-value| when we're
tangling for evaluation. So if we're not evaluating, we return a special
`pseudo-marker' with a specialized pretty-printing method. This gives us an
appropriate value in all three situations: during weaving, we have just
another marker; when tangling for evaluation, we get the read-time-evaluated
value; and in a tangled source file, we get a \.{\#.} form.

@l
(defclass read-time-eval ()
  ((form :reader read-time-eval-form :initarg :form)))

(set-tangle-dispatch 'read-time-eval
  (lambda (stream obj)
    (format stream "#.~W" (read-time-eval-form obj))))

(defclass read-time-eval-marker (read-time-eval marker) ())

(defmethod marker-boundp ((marker read-time-eval-marker)) t)
(defmethod marker-value ((marker read-time-eval-marker))
  (if *evaluating*
      (call-next-method)
      (make-instance 'read-time-eval :form (read-time-eval-form marker))))

(defun sharpsign-dot-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (let ((form (read stream t nil t)))
    (unless *read-suppress*
      (unless *read-eval*
        (simple-reader-error stream "can't read #. while *READ-EVAL* is NIL"))
      (make-instance 'read-time-eval-marker
                     :form form
                     :value (eval (tangle form))))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\. #'sharpsign-dot-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest (read-time-eval 1)
  (let* ((*read-eval* t)
         (*evaluating* nil))
    (write-to-string (marker-value (read-form-from-string "#.(+ 1 1)"))
                     :pprint-dispatch *tangle-pprint-dispatch*
                     :pretty t))
  "#.(+ 1 1)")

(deftest (read-time-eval 2)
  (let* ((*read-eval* t)
         (*evaluating* t))
    (marker-value (read-form-from-string "#.(+ 1 1)")))
  2)

@ Sharpsign B, O, X, and~R all represent rational numbers in a specific
radix, but the radix is discarded by the standard reader, which just
returns the number. We use the standard reader macro function for getting
the actual value, and store the radix in our marker.

@l
(defclass radix-marker (marker)
  ((base :reader radix-marker-base :initarg :base)))

(defparameter *radix-prefix-alist* ;
  '((#\B . 2) (#\O . 8) (#\X . 16) (#\R . nil)))

(defun radix-reader (stream sub-char arg)
  (make-instance 'radix-marker
                 :base (or (cdr (assoc (char-upcase sub-char) ;
                                       *radix-prefix-alist*)) ;
                           arg)
                 :value @<Call the standard reader macro fun...@>))

(dolist (mode '(:lisp :inner-lisp))
  (dolist (sub-char '(#\B #\b #\O #\o #\X #\x #\R #\r))
    (set-dispatch-macro-character #\# sub-char #'radix-reader ;
                                  (readtable-for-mode mode))))

@ @<Call the standard reader macro function for \.{\#\<|sub-char|>}@>=
(funcall (get-dispatch-macro-character #\# sub-char (readtable-for-mode nil))
         stream sub-char arg)

@t@l
(deftest (read-radix 1)
  (let ((marker (read-form-from-string "#B1011")))
    (values (radix-marker-base marker)
            (marker-value marker)))
  2
  11)

(deftest (read-radix 2)
  (let ((marker (read-form-from-string "#14R11")))
    (values (radix-marker-base marker)
            (marker-value marker)))
  14
  15)

@ Sharpsign~C reads a list of two real numbers representing, respectively,
the real and imaginary parts of a complex number.

@l
(defclass complex-marker (marker)
  ((components :reader complex-components :initarg :components)))

(defmethod marker-boundp ((marker complex-marker)) t)
(defmethod marker-value ((marker complex-marker))
  (apply #'complex (tangle (complex-components marker))))

(defun complex-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (make-instance 'complex-marker
                 :components (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\C #'complex-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest read-complex
  (let ((marker (read-form-from-string "#C(0 1)")))
    (marker-value marker))
  #C(0 1))

@ Sharpsign~$n$A constructs an $n$-dimensional array. We don't need any
particularly special handling, but we have to override it anyway because
the standard reader will be confused by finding markers where it expects
sequences.

@l
(defclass array-marker (marker)
  ((rank :reader array-marker-rank :initarg :rank)
   (initial-contents :reader array-marker-initial-contents ;
                     :initarg :initial-contents)))

(defmethod marker-boundp ((marker array-marker)) t)
(defmethod marker-value ((marker array-marker))
  (loop with contents = (tangle (array-marker-initial-contents marker))
        repeat (array-marker-rank marker)
        for seq = contents then (elt seq 0)
        collect (length seq) into dimensions
        finally (return (make-array dimensions :initial-contents contents))))

(defun array-reader (stream sub-char arg)
  (declare (ignore sub-char))
  (unless arg (simple-reader-error stream "no rank supplied with #A"))
  (make-instance 'array-marker ;
                 :rank arg ;
                 :initial-contents (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\A #'array-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest read-array
  (let ((marker (read-form-from-string "#2A((1 2 3) (4 5 6))")))
    (equalp (marker-value marker)
            #2A((1 2 3) (4 5 6))))
  t)

@ Sharpsign~S requires determining the standard constructor function of the
structure type named, which we simply can't do portably. So we cache the
form as given, then dump it out to a string and let the standard reader
parse it when we need the value.

@l
(defclass structure-marker (marker)
  ((form :reader structure-marker-form :initarg :form)))

(defmethod marker-boundp ((marker structure-marker)) t)
(defmethod marker-value ((marker structure-marker))
  (let ((*readtable* (readtable-for-mode nil)))
    (values (read-from-string
             (write-to-string marker
                              :pprint-dispatch *tangle-pprint-dispatch*
                              :pretty t
                              :readably t)))))

(set-tangle-dispatch 'structure-marker
  (lambda (stream obj)
    (format stream "#S~W" (structure-marker-form obj)))
  1)

(defun structure-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (make-instance 'structure-marker :form (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\S #'structure-reader ;
                                (readtable-for-mode mode)))

@t@l
(defstruct person (name 007 :type string))
(deftest structure-marker
  (person-name (marker-value ;
                (read-form-from-string "#S(person :name \"James\")")))
  "James")

@ Sharpsign~P reads namestrings and turns them into pathnames.

@l
(defclass pathname-marker (marker)
  ((namestring :reader pathname-marker-namestring :initarg :namestring)))

(defmethod marker-boundp ((marker pathname-marker)) t)
(defmethod marker-value ((marker pathname-marker))
  (parse-namestring (pathname-marker-namestring marker)))

(set-tangle-dispatch 'pathname-marker
  (lambda (stream obj)
    (format stream "#P~W" (pathname-marker-namestring obj)))
  1)

(defun pathname-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (make-instance 'pathname-marker :namestring (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\P #'pathname-reader ;
                                (readtable-for-mode mode)))

@ Sharpsign $+$ and~$-$ provide read-time conditionalization based on
feature expressions, described in section~24.1.2 of the CL standard.
This routine, adapted from SBCL, interprets such an expression.

@l
(defun featurep (x)
  (etypecase x
    (cons
     (case (car x)
       ((:not not)
        (cond
          ((cddr x) ;
           (error "too many subexpressions in feature expression: ~S" x))
          ((null (cdr x)) ;
           (error "too few subexpressions in feature expression: ~S" x))
          (t (not (featurep (cadr x))))))
       ((:and and) (every #'featurep (cdr x)))
       ((:or or) (some #'featurep (cdr x)))
       (t
        (error "unknown operator in feature expression: ~S." x))))
    (symbol (not (null (member x *features* :test #'eq))))))

@t@l
(deftest featurep
  (let ((*features* '(:a :b)))
    (featurep '(:and :a (:or :c :b) (:not :d))))
  t)

@ For sharpsign $+/-$, we use the same sort of trick we used for \.{\#.}
above: we have a marker that returns the appropriate value when tangling for
evaluation, but returns a `pseudo-marker' when tangling to a file, so that
we can preserve the original form.

This case is slightly trickier, though, because we can't just call |read|
on the form, since if the the test fails, |*read-suppress*| will be true,
and we won't get anything back. So we use an echo stream to catch the raw
characters that the reader scans, and use that to reconstruct the form.

@l
(defclass read-time-conditional ()
  ((plusp :reader read-time-conditional-plusp :initarg :plusp)
   (test :reader read-time-conditional-test :initarg :test)
   (form :reader read-time-conditional-form :initarg :form)))

(set-tangle-dispatch 'read-time-conditional
  (lambda (stream obj)
    (format stream "#~:[-~;+~]~S~A"
            (read-time-conditional-plusp obj)
            (read-time-conditional-test obj)
            (read-time-conditional-form obj))))

(defclass read-time-conditional-marker (read-time-conditional marker) ())

(defmethod marker-boundp ((marker read-time-conditional-marker))
  (if *evaluating*
      (call-next-method)
      t))

(defmethod marker-value ((marker read-time-conditional-marker))
  (if *evaluating*
      (call-next-method)
      (make-instance 'read-time-conditional
                     :plusp (read-time-conditional-plusp marker)
                     :test (read-time-conditional-test marker)
                     :form (read-time-conditional-form marker))))

(defun read-time-conditional-reader (stream sub-char arg)
  (declare (ignore arg))
  (let* ((plusp (ecase sub-char (#\+ t) (#\- nil)))
         (*readtable* (readtable-for-mode nil))
         (test (let ((*package* (find-package "KEYWORD"))
                     (*read-suppress* nil))
                 (read stream t nil t)))
         (*read-suppress* (if plusp (not (featurep test)) (featurep test))))
    (read-with-echo (stream value form)
      (apply #'make-instance 'read-time-conditional-marker
             :plusp plusp :test test :form form
             (and (not *read-suppress*) (list :value value))))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\+ #'read-time-conditional-reader ;
                                (readtable-for-mode mode))
  (set-dispatch-macro-character #\# #\- #'read-time-conditional-reader ;
                                (readtable-for-mode mode)))

@t@l
(deftest (read-time-conditional 1)
  (let* ((*evaluating* nil)
         (*features* nil)
         (conditional (marker-value (read-form-from-string "#-foo 1"))))
    (values (read-time-conditional-plusp conditional)
            (read-time-conditional-test conditional)
            (read-time-conditional-form conditional)))
  nil :foo " 1")

(deftest (read-time-conditional 2)
  (let ((*features* '(:a))
        (*evaluating* t))
    (values (marker-value (read-form-from-string "#+a 1"))
            (marker-value (read-form-from-string "#-b 2"))
            (marker-boundp (read-form-from-string "#-a 1"))
            (marker-boundp (read-form-from-string "#+b 2"))))
  1
  2
  nil
  nil)

(deftest (read-time-conditional charpos)
  (list-marker-charpos (with-mode :lisp
                         (read-from-string-with-charpos
                          (format nil "(#-:foo foo~% bar)"))))
  (1 0 1))

@1*Web control codes. So much for the standard macro characters. Now we're
ready to move on to \WEB-specific reading. We accumulate \TeX\ mode
material such as commentary, section names, \etc. using the following
function, which reads from |stream| until encountering either \EOF\ or an
element of the |control-chars| argument, which should be a designator for a
list of characters.

@l
(defun snarf-until-control-char (stream control-chars &aux ;
                                 (control-chars (ensure-list control-chars)))
  (with-output-to-string (string)
    (loop for char = (peek-char nil stream nil eof nil)
          until (or (eof-p char) (member char control-chars))
          do (write-char (read-char stream) string))))

@t@l
(deftest snarf-until-control-char
  (with-input-from-string (s "abc*123")
    (values (snarf-until-control-char s #\*)
            (snarf-until-control-char s '(#\a #\3))))
  "abc"
  "*12")

@ In \TeX\ mode (including restricted contexts), we allow embedded Lisp
code to be surrounded by \pb, where it is read in inner-Lisp mode.

@l
(defun read-inner-lisp (stream char)
  (with-mode :inner-lisp
    (read-delimited-list char stream)))

(dolist (mode '(:TeX :restricted))
  (set-macro-character #\| #'read-inner-lisp nil (readtable-for-mode mode)))

@t@l
(deftest read-inner-lisp
  (with-mode :TeX
    (values (read-from-string "|:foo :bar|")))
  (:foo :bar))

@ The call to |read-delimited-list| in |read-inner-lisp| will only stop at
the closing \v\ if we make it a terminating macro character, overriding its
usual Lisp meaning as an escape character.

@l
(set-macro-character #\| (get-macro-character #\) nil) ;
                     nil (readtable-for-mode :inner-lisp))

@ We make |#\@| a non-terminating dispatching macro character in every
mode, and define some convenience routines for retrieving and setting the
reader macro functions that implement the control codes.

@l
(dolist (mode *modes*)
  ;; The CL standard does not say that calling |make-dispatch-macro-character|
  ;; on a character that's already a dispatching macro character is supposed
  ;; to signal an error, but SBCL does so anyway; hence the |ignore-errors|.
@^SBCL@> ;
  (ignore-errors
    (make-dispatch-macro-character #\@ t (readtable-for-mode mode))))

(defun get-control-code (sub-char mode)
  (get-dispatch-macro-character #\@ sub-char (readtable-for-mode mode)))

(defun set-control-code (sub-char function &optional (modes *modes*))
  (dolist (mode (ensure-list modes))
    (set-dispatch-macro-character #\@ sub-char function ;
                                  (readtable-for-mode mode))))

@ The control code \.{@@@@} yields the string \.{"@@"} in all modes, but
it should really only be used in \TeX\ text.

@l
(set-control-code #\@ (lambda (stream sub-char arg)
                        (declare (ignore sub-char stream arg))
                        (string "@")))

@t@l
(deftest literal-@
  (with-mode :TeX
    (values (read-from-string "@@")))
  "@")

@ Ordinary sections are introduced by \.{@@\ } or \.{@@|#\Newline|}.

@l
(defun start-section-reader (stream sub-char arg)
  (declare (ignore stream sub-char arg))
  (make-instance 'section))

(dolist (sub-char '(#\Space #\Newline))
  (set-control-code sub-char #'start-section-reader '(:limbo :TeX :lisp)))

@ Starred sections, introduced by \.{@@*}, accept an optional numeric
argument for the depth. Rather than the \CWEB\ syntax in which the argument
follows the `\.{*}', we follow the usual Common Lisp syntax and assume the
argument occurs between the `\.{@@}' and the `\.{*}'.
@^\CWEB@>

@l
(defun start-starred-section-reader (stream sub-char arg)
  (declare (ignore stream sub-char))
  (apply #'make-instance 'starred-section (when arg `(:depth ,arg))))

(set-control-code #\* #'start-starred-section-reader '(:limbo :TeX :lisp))

@ Test sections are handled similarly, but are introduced with \.{@@t}.
Test sections may also be `starred'. Immediately following whitespace
is ignored.

@l
(defun start-test-section-reader (stream sub-char arg)
  (declare (ignore sub-char))
  (prog1 (if (and (char= (peek-char t stream t nil t) #\*)
                  (read-char stream t nil t))
             (apply #'make-instance 'starred-test-section ;
                    (when arg `(:depth ,arg)))
             (make-instance 'test-section))
         (loop until (char/= (peek-char t stream t nil t) #\Newline)
               do (read-char stream t nil t))))

(set-control-code #\t #'start-test-section-reader '(:limbo :TeX :lisp))

@t We bind |*test-sections*| to avoid polluting the global test section
vector.

@l
(deftest start-test-section-reader
  (let ((*test-sections* (make-array 2 :fill-pointer 0)))
    (with-input-from-string (s (format nil "@t~%:foo @t* :bar"))
      (with-mode :lisp
        (values (typep (read s) 'test-section) (read s)
                (typep (read s) 'starred-test-section) (read s)))))
  t :foo
  t :bar)

@ The control codes \.{@@l} and~\.{@@p} (where `l' is for `Lisp' and `p'
is for `program'---both control codes do the same thing) begin the code
part of an unnamed section. They are valid only in \TeX\ mode; every
section must begin with a commentary, even if it is empty. We set the
control codes in Lisp mode only for error detection.

@l
(defclass start-code-marker (marker)
  ((name :reader section-name :initarg :name))
  (:default-initargs :name nil))

(defun start-code-reader (stream sub-char arg)
  (declare (ignore stream sub-char arg))
  (make-instance 'start-code-marker))

(dolist (sub-char '(#\l #\p))
  (set-control-code sub-char #'start-code-reader '(:TeX :lisp)))

@t@l
(deftest start-code-marker
  (with-mode :TeX
    (values-list (mapcar (lambda (marker) (typep marker 'start-code-marker))
                         (list (read-from-string "@l")
                               (read-from-string "@p")))))
  t
  t)

@ The control code \.{@@e} (`e' for `eval') indicates that the following
form should be evaluated by the section reader, {\it in addition to\/}
being tangled into the output file. Evaluated forms should be used only
for establishing state that is needed by the reader: package definitions,
structure definitions that are used with \.{\#S}, \etc.

@l
(defclass evaluated-form-marker (marker) ())

(defun read-evaluated-form (stream sub-char arg)
  (declare (ignore sub-char arg))
  (loop for form = (read stream t nil t)
        until (not (newlinep form)) ; skip over newlines
        finally (return (make-instance 'evaluated-form-marker :value form))))

(set-control-code #\e #'read-evaluated-form :lisp)

@t@l
(deftest (read-evaluated-form 1)
  (let ((marker (read-form-from-string (format nil "@e t"))))
    (and (typep marker 'evaluated-form-marker)
         (marker-value marker)))
  t)

(deftest (read-evaluated-form 2)
  (let ((marker (read-form-from-string (format nil "@e~%t"))))
    (and (typep marker 'evaluated-form-marker)
         (marker-value marker)))
  t)

@ Several control codes, including \.{@@<}, contain `restricted' \TeX\
text, called {\it control text}, that extends to the next \.{@@>}. When
we first read control text, we ignore inner-Lisp material (that is, Lisp
forms surrounded by \pb). During weaving, we'll re-scan it to pick up such
material. The reason for this two-pass approach is that control text will
frequently be used as keys in the various binary search trees, so it's
convenient to keep it in string form until the last possible moment (i.e.,
right up until we need to print it out).

The only control codes that are valid in restricted mode are \.{@@>}
and~\.{@@@@}.

@l
(defvar *end-control-text* (make-symbol "@>"))
(set-control-code #\> (constantly *end-control-text*) :restricted)

(defun read-control-text (stream &optional ;
                          (eof-error-p t) eof-value recursive-p)
  (with-output-to-string (string)
    (with-mode :restricted
      (loop for text = (snarf-until-control-char stream #\@)
            for next = (read-preserving-whitespace stream ;
                                                   eof-error-p eof-value ;
                                                   recursive-p)
            do (write-string text string)
            if (eq next *end-control-text*) do (loop-finish)
            else do (write-string next string)))))

@t@l
(deftest read-control-text
  (with-input-from-string (s "frob |foo| and tweak |bar|@>")
    (read-control-text s))
  "frob |foo| and tweak |bar|")

@ The control code \.{@@<} introduces a section name, which extends to the
closing \.{@@>}. Its meaning is context-dependent.

In \TeX\ mode, a name must be followed by \.{=}, which attaches the name to
the current section and begins the code part.

In Lisp and inner-Lisp modes, a name is taken to refer to the section so
named. During tangling, such references in Lisp mode will be replaced with
the code defined for that section. References in inner-Lisp mode are only
citations, and so are not expanded.

@l
(defun make-section-name-reader (definition-allowed-p use)
  (lambda (stream sub-char arg)
    (declare (ignore sub-char arg))
    (let* ((name (read-control-text stream t nil t))
           (definitionp (eql (peek-char nil stream nil nil t) #\=)))
      (if definitionp
          (if definition-allowed-p
              (progn
                (read-char stream)
                (make-instance 'start-code-marker :name name))
              @<Signal an error about section definition in Lisp mode@>)
          (if definition-allowed-p
               @<Signal an error about section name use in \TeX\ mode@>
               (let ((named-section (find-section name)))
                 (if use
                     (pushnew *current-section* (used-by named-section))
                     (pushnew *current-section* (cited-by named-section)))
                 named-section))))))

(set-control-code #\< (make-section-name-reader t nil) :TeX)
(set-control-code #\< (make-section-name-reader nil t) :lisp)
(set-control-code #\< (make-section-name-reader nil nil) :inner-lisp)

@ @<Condition classes@>=
(define-condition section-name-context-error (error)
  ((name :reader section-name :initarg :name)))

(define-condition section-name-definition-error (section-name-context-error)
  ()
  (:report (lambda (condition stream)
             (format stream "Can't define a named section in Lisp mode: ~A" ;
@.Can't define a named section...@>
                     (section-name condition)))))

(define-condition section-name-use-error (section-name-context-error)
  ()
  (:report (lambda (condition stream)
             (format stream "Can't use a section name in TeX mode: ~A" ;
@.Can't use a section...@>
                     (section-name condition)))))

@ @<Signal an error about section definition in Lisp mode@>=
(restart-case (error 'section-name-definition-error :name name)
  (use-section ()
    :report "Don't define the section, just use it."
    (find-section name)))

@ @<Signal an error about section name use in \TeX\ mode@>=
(restart-case (error 'section-name-use-error :name name)
  (name-section ()
    :report "Name the current section and start the code part."
    (make-instance 'start-code-marker :name name))
  (cite-section ()
    :report "Assume the section is just being cited."
    (find-section name)))

@t@l
(deftest (read-section-name :TeX)
  (with-mode :TeX
    (section-name (read-from-string "@<foo@>=")))
  "foo")

(deftest (read-section-name :lisp)
  (with-sample-named-sections
    (with-mode :lisp
      (section-name (read-from-string "@<foo@>"))))
  "foo")

(deftest section-name-definition-error
  (with-sample-named-sections
    (section-name
     (handler-bind ((section-name-definition-error
                     (lambda (condition)
                       (declare (ignore condition))
                       (invoke-restart 'use-section))))
       (with-mode :lisp
         (read-from-string "@<foo@>=")))))
  "foo")

(deftest section-name-use-error
  (with-sample-named-sections
    (section-name
     (handler-bind ((section-name-use-error
                     (lambda (condition)
                       (declare (ignore condition))
                       (invoke-restart 'cite-section))))
       (with-mode :TeX
         (read-from-string "@<foo@>")))))
  "foo")

@ The control code \.{@@x} reads the following form, which should be a
designator for a list of packages, and informs the indexing sub-system
that symbols in those packages are to be indexed. It returns the form.

This control code probably won't be needed terribly often, since the
indexer automatically adds the current package (i.e., the value of
|*package*| at the time of indexing) to the list of packages whose
symbols should be indexed.

Note that this is {\it completely different\/} than the \.{@@x} control
code of \WEB\ and \CWEB, which is part of their change-file system.
@^\WEB@>
@^\CWEB@>


@l
(defun index-package-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (let ((form (read stream)))
    (index-package form)
    form))

(set-control-code #\x #'index-package-reader :lisp)

@t@l
(deftest index-package-reader
  (let ((*index-packages* nil))
    (read-form-from-string "@x\"CLWEB\"")
    (not (null (interesting-symbol-p 'index-package-reader))))
  t)

@ These next control codes are used to manually create index entries.
They differ only in how they are typeset in the woven output.
@^manual index entries@>

@l
(defun index-entry-reader (stream sub-char arg)
  (declare (ignore arg))
  (add-index-entry *index*
                   (make-instance (ecase sub-char
                                    (#\^ 'heading)
                                    (#\. 'tt-heading)
                                    (#\: 'custom-heading))
                                  :name (read-control-text stream))
                   *current-section*)
  (values))

(dolist (sub-char '(#\^ #\. #\:))
  (set-control-code sub-char #'index-entry-reader '(:TeX :lisp)))

@1*Reading sections. We come now to the heart of the \WEB\ parser. This
function is a tiny state machine that models the global syntax of a \WEB\
file. (We can't just use reader macros since sections and their parts lack
explicit closing delimiters.) It returns a list of |section| objects.

@l
(defun read-sections (input-stream &key (append t))
  (with-charpos-input-stream (stream input-stream)
    (flet ((finish-section (section commentary code)
             @<Trim whitespace and reverse...@>
             (setf (section-commentary section) commentary)
             (setf (section-code section) code)
             (when (section-name section)
               (let ((named-section (find-section (section-name section))))
                 (if append
                     (push section (named-section-sections named-section))
                     (setf (named-section-sections named-section) ;
                           (list section)))))
             section))
      (prog (form commentary code section sections)
         (setq section (make-instance 'limbo-section))
         @<Accumulate limbo text in |commentary|@>
       commentary
         @<Finish the last section...@>
         @<Accumulate \TeX-mode material in |commentary|@>
       lisp
         @<Accumulate Lisp-mode material in |code|@>
       eof
         (push (finish-section section commentary code) sections)
         (return (nreverse sections))))))

@ Limbo text is \TeX\ text that proceeds the first section marker, and we
treat it as commentary for a special section with no code. Note that
inner-Lisp material is not recognized in limbo text.

@<Accumulate limbo text in |commentary|@>=
(with-mode :limbo
  (loop
    (maybe-push (snarf-until-control-char stream #\@) commentary)
    (let ((next-input (read-maybe-nothing-preserving-whitespace ;
                       stream nil eof nil)))
      (when next-input
        (typecase (setq form (car next-input))
          (eof (go eof))
          (section (go commentary))
          (t (push form commentary)))))))

@ @<Finish the last section and initialize section variables@>=
(push (finish-section section commentary code) sections)
(check-type form section)
(setq section form
      commentary '()
      code '())

@ The commentary part that begins a section consists of \TeX\ text and
inner-Lisp material surrounded by \pb. It is terminated by either the start
of a new section, the beginning of the code part, or \EOF\null. If a code part
is detected, we also set the name of the current section, which may be |nil|.

@<Accumulate \TeX-mode material in |commentary|@>=
(with-mode :TeX
  (loop
    (maybe-push (snarf-until-control-char stream '(#\@ #\|)) commentary)
    (let ((next-input (read-maybe-nothing-preserving-whitespace ;
                       stream nil eof nil)))
      (when next-input
        (typecase (setq form (car next-input))
          (eof (go eof))
          (section (go commentary))
          (start-code-marker (setf (section-name section) (section-name form))
                             (go lisp))
          (t (push form commentary)))))))

@ The code part of a section consists of zero or more Lisp forms and is
terminated by either \EOF\ or the start of a new section. This is also
where we evaluate \.{@@e} forms.

@<Accumulate Lisp-mode material in |code|@>=
(check-type form start-code-marker)
(with-mode :lisp
  (loop
    (let ((next-input (read-maybe-nothing-preserving-whitespace ;
                       stream nil eof nil)))
      (when next-input
        (typecase (setq form (car next-input))
          (eof (go eof))
          (section (go commentary))
          (start-code-marker ;
           @<Complain about starting a section without a commentary part@>)
          (newline-marker (when code (push form code)))
          (evaluated-form-marker (let ((form (marker-value form)))
                                   (let ((*evaluating* t)
                                         (*readtable* (readtable-for-mode nil)))
                                     (eval (tangle form)))
                                   (push form code)))
          (t (push form code)))))))

@ @<Complain about starting a section without a commentary part@>=
(cerror "Start a new unnamed section with no commentary." ;
@.Start a new unnamed...@>
        'section-lacks-commentary :stream stream)
(setq form (make-instance 'section))
@<Finish the last section...@>

@ @<Condition classes@>=
(define-condition section-lacks-commentary (parse-error)
  ((stream :initarg :stream :reader section-lacks-commentary-stream))
  (:report (lambda (error stream)
             (let* ((input-stream
                     (do ((stream (section-lacks-commentary-stream error)))
                         (())
                       (typecase stream
                         (echo-stream
                          (setq stream (echo-stream-input-stream stream)))
                         (t (return stream)))))
                    (position (file-position input-stream))
                    (pathname (when (typep input-stream 'file-stream)
                                (pathname input-stream))))
               (format stream
                       "~@<Can't start a section with a code part ~
~:[~;~:*at position ~D in file ~A.~]~:@>" ;
@.Can't start a section...@>
                       position (or pathname input-stream))))))

@ We trim trailing whitespace from the last string in |commentary|, leading
whitespace from the first, and any trailing newline marker from |code|.
Leading newlines are handled in |@<Accumulate Lisp-mode...@>|.

@<Trim whitespace and reverse |commentary| and |code|@>=
(when (stringp (car commentary))
  (rplaca commentary (string-right-trim *whitespace* (car commentary))))
(setq commentary (nreverse commentary))
(when (stringp (car commentary))
  (rplaca commentary (string-left-trim *whitespace* (car commentary))))
(setq code (nreverse (member-if-not #'newlinep code)))

@*Tangling. Tangling involves recursively replacing each reference to a
named section with the code accumulated for that section. The function
|tangle-1| expands one level of such references, returning the
possibly-expanded form and a boolean representing whether or not any
expansions were actually performed.

Note that this is a splicing operation, like `\.{,@@}', not a simple
substitution, like normal Lisp macro expansion:
if \X$n$:foo\X$\mathrel\E$|(x y)|, then
\((tangle-1 \'(a \X$n$:foo\X\ b))\)$\;\to\;$|(a x y b)|,~|t|.

Tangling also replaces bound markers with their associated values, and
removes unbound markers. If the keyword argument |expand-named-sections|
is false, then this is in fact all that |tangle-1| does; we'll use this
capability later in the indexing code.

@l
(defun tangle-1 (form &key (expand-named-sections t))
  (flet ((tangle-1 (form)
           (tangle-1 form :expand-named-sections expand-named-sections)))
    (typecase form
      (marker (values (marker-value form) t))
      (named-section
       (if expand-named-sections
           (values (section-code form) t)
           (values form nil)))
      (atom (values form nil))
      ((cons named-section *)
       (multiple-value-bind (d cdr-expanded-p) (tangle-1 (cdr form))
         (if expand-named-sections
             (values (append (section-code (car form)) d) t)
             (values (cons (car form) d) cdr-expanded-p))))
      ((cons marker *)
       (values (if (marker-boundp (car form))
                   (cons (marker-value (car form)) (tangle-1 (cdr form)))
                   (tangle-1 (cdr form)))
               t))
      (t (multiple-value-bind (a car-expanded-p) (tangle-1 (car form))
           (multiple-value-bind (d cdr-expanded-p) (tangle-1 (cdr form))
             (values (if (and (eql a (car form))
                              (eql d (cdr form)))
                         form
                         (cons a d))
                     (or car-expanded-p cdr-expanded-p))))))))

@t@l
(deftest (tangle-1 1)
  (tangle-1 (read-form-from-string ":a"))
  :a
  nil)

(deftest (tangle-1 2)
  (tangle-1 (read-form-from-string "(:a :b :c)"))
  (:a :b :c)
  t)

(deftest (tangle-1 3)
  (with-sample-named-sections
    (tangle-1 (read-form-from-string "@<foo@>")))
  (:foo)
  t)

@ |tangle| repeatedly calls |tangle-1| on |form| until it can no longer be
expanded. Like |tangle-1|, it returns the possibly-expanded form and an
`expanded' flag. This code is adapted from SBCL's |macroexpand|.

@l
(defun tangle (form &key (expand-named-sections t))
  (labels ((expand (form expanded)
             (multiple-value-bind (new-form newly-expanded-p)
                 (tangle-1 form :expand-named-sections expand-named-sections)
               (if newly-expanded-p
                   (expand new-form t)
                   (values new-form expanded)))))
    (expand form nil)))

@t@l
(deftest tangle
  (with-sample-named-sections
    (tangle (read-form-from-string (format nil "(:a @<foo@>~% :b)"))))
  (:a :foo :b)
  t)

@ This little utility function returns a list of all of the forms in all
of the unnamed sections' code parts. This is our first-order approximation
of the complete program; if you tangle it, you get the whole thing.

@l
(defun unnamed-section-code-parts (sections)
  (mapappend #'section-code (coerce (remove-if #'section-name sections) 'list)))

@ We're now ready for the high-level tangler interface. We begin with
|load-web|, which uses a helper function, |load-web-from-stream|, so that
it can handle input from an arbitrary stream. The logic is straightforward:
we loop over the tangled forms read from the stream, evaluating each one in
turn.

Note that like |load|, we bind |*readtable*| and |*package*| to their
current values, so that assignments to those variables in the \WEB\ code
will not affect the calling environment.

@l
(defun load-web-from-stream (stream print &key (append t) &aux
                             (*readtable* *readtable*)
                             (*package* *package*)
                             (*evaluating* t))
  (dolist (form (tangle (unnamed-section-code-parts
                         (read-sections stream :append append))) t)
    (if print
        (let ((results (multiple-value-list (eval form))))
          (format t "~&; ~{~S~^, ~}~%" results))
        (eval form))))

(defun load-web (filespec &key
                 (verbose *load-verbose*)
                 (print *load-print*)
                 (if-does-not-exist t)
                 (external-format :default))
  "Load the web given by FILESPEC into the Lisp environment."
  @<Initialize global variables@>
  (when verbose (format t "~&; loading WEB from ~S~%" filespec))
  (if (streamp filespec)
      (load-web-from-stream filespec print)
      (with-open-file (stream (merge-pathnames filespec ;
                                               (make-pathname :type "CLW" ;
                                                              :case :common))
                       :direction :input
                       :external-format external-format
                       :if-does-not-exist (if if-does-not-exist :error nil))
        (load-web-from-stream stream print))))

@ This next function exists solely for the sake of front-ends that wish to
load a piece of a \WEB, such as the author's `\.{clweb.el}'. Note that it
does not initialize the global variables like |*named-sections*|; this
allows for incremental redefinition.
@.clweb.el@>

@l
(defun load-sections-from-temp-file (file append &aux (file (probe-file file)))
  "Load web sections from FILE, then delete it. If APPEND is true, named
section definitions in FILE will be appended to existing definitions;
otherwise, they will replace them."
  (when file
    (unwind-protect
         (with-open-file (stream file :direction :input)
           (load-web-from-stream stream t :append append))
      (delete-file file))))

@ Both Allegro and CCL get the wrong case for pathname components created
using |make-pathname| with a supplied |defaults| argument when |case|
is |:common|. This simple wrapper seems to behave correctly.

@l
#+(or allegro ccl)
(defun make-pathname (&key host device directory name type version
                      (defaults
                       (cl:make-pathname :host (pathname-host
                                                *default-pathname-defaults*
                                                :case :common)
                                         :device nil
                                         :directory nil
                                         :name nil
                                         :type nil
                                         :version nil
                                         :case :common))
                      (case :local))
  (merge-pathnames
   (cl:make-pathname :host (or host (pathname-host defaults :case case))
                     :device device
                     :directory directory
                     :name name
                     :type type
                     :version version
                     :case case)
   defaults))

@ Both |tangle-file| and |weave|, below, take a |tests-file| argument that
has slightly hairy defaulting behavior. If it's supplied and is non-|nil|,
then we use a pathname derived from the one given by merging in a default
type (`\.{LISP}' in the case of tangling, `\.{TEX}' for weaving). If it's
not supplied, then we construct a pathname from the input file by appending
the string \.{"-TESTS"} to its name component, using the supplied type, and
merging defaults from the output filename. Finally, if the argument is
supplied and is |nil|, then no tests file will be written at all.

@l
(defun tests-file-pathname (input-file type &key
                            (output-file *default-pathname-defaults*)
                            (tests-file nil tests-file-supplied) ;
                            &allow-other-keys)
  (if tests-file
      (make-pathname :type type :defaults tests-file :case :common)
      (unless tests-file-supplied
        (make-pathname :name (concatenate 'string ;
                                          (pathname-name input-file ;
                                                         :case :common) ;
                                          "-TESTS")
                       :type type
                       :defaults output-file
                       :case :common))))

@t We'll shortly be defining a whole bunch of tests for pathname-generating
functions. These tests become vastly more compact if we use logical
pathnames. So we'll define a trivial translation for the logical pathname
host `\.{CLWEB-TEST}'. In the extremely unlikely event that this conflicts
with a logical pathname host in your environment, please notify the author.

@l
@e
(eval-when (:compile-toplevel :load-toplevel :execute)
  (setf (logical-pathname-translations "clweb-test") '(("**;*.*.*" ""))))

@t@l
(deftest (tests-file-pathname 1)
  (tests-file-pathname #P"clweb-test:foo" "LISP"
                       :tests-file #P"clweb-test:bar")
  #P"clweb-test:bar.lisp")

(deftest (tests-file-pathname 2)
  (tests-file-pathname #P"clweb-test:foo" "TEX"
                       :output-file #P"clweb-test:")
  #P"clweb-test:foo-tests.tex")

(deftest (tests-file-pathname 3)
  (tests-file-pathname #P"clweb-test:foo" "TEX"
                       :output-file #P"clweb-test:a;b;")
  #P"clweb-test:a;b;foo-tests.tex")

(deftest (tests-file-pathname 4)
  (tests-file-pathname #P"clweb-test:foo" "LISP"
                       :tests-file nil)
  nil)

@ Some tests might not be worth spending time compiling, or might be
easier to debug if not compiled, or might involve unwanted complexity
to support compilation (e.g., |make-load-form|). So we'll allow the
user to specify whether to compile a tests file, with a variable for
the default preference.

@<Global variables@>=
(defvar *compile-tests-file* t
  "The default value to use for the :COMPILE-TESTS-FILE argument to
TANGLE-FILE.")

@ During tangling, we bind |*tangle-file-pathname*| and
|*tangle-file-truename*| in the same way that |compile-file| binds
|*compile-file-pathname*| and |*compile-file-truename*|.

@<Global variables@>=
(defvar *tangle-file-pathname* nil)
(defvar *tangle-file-truename* nil)

@ We'll use a custom pprint-dispatch table for tangling to avoid cluttering
the default table.

@<Global variables@>=
(defparameter *tangle-pprint-dispatch* (copy-pprint-dispatch nil))

@ @<Define the pprint dispatch table setters@>=
(defun set-tangle-dispatch (type-specifier function &optional (priority 0))
  (set-pprint-dispatch type-specifier function priority ;
                       *tangle-pprint-dispatch*))

@ \ansi\ Common Lisp's |open| specification was intended to allow an
implementation to supply semantics for the various |:if-exists| modes
consistent with the conventions of the file system with which the program
interacted, including, notably, allowing the default |:if-exists|
disposition of |:new-version| to have the same semantics as some other
opening mode. The implementors of SBCL, however, chose to needlessly
inconvenience their users by making the default |:if-exists| disposition
signal an error.
@^\ansi\ Common Lisp@>
@^SBCL@>

@<|:if-exists| default disposition@>=
#+sbcl :supersede #-sbcl :new-version

@ In keeping with the usual behavior of both Lisp and \TeX, the type
component of an input filename argument to any top-level function may
be omitted; it defaults to~`\.{CLW}'.

@l
(defun input-file-pathname (input-file)
  "Apply defaults to the given input filename."
  (merge-pathnames input-file (make-pathname :type "CLW" :case :common)))

@t@l
(deftest input-file-pathname
  (input-file-pathname #P"clweb-test:foo")
  #P"clweb-test:foo.clw.newest")

@ The file tangler operates by writing out the tangled code to a Lisp source
file and then invoking the file compiler on that file. The arguments are
essentially the same as those to |compile-file|, except for the |tests-file|
keyword argument, which specifies the file to which the test sections' code
should be written (see~|tests-file-pathname|, above, for the defaulting
behavior).

We return the values returned by invoking |compile-file| on the tangled
file. We compile the tests file, if any, {\it after\/} the tangled file,
on the assumption that the tests might require a module provided by the
output file. Note that this might cause the output file to be unintentionally
loaded; the work-around is to disable production of the tests file by
supplying a null |tests-file| argument.

@l
(defun tangle-file (input-file &rest args &key output-file tests-file
                    (verbose *compile-verbose*)
                    (print *compile-print*)
                    (if-exists @<|:if-exists|...@>)
                    (compile-tests-file *compile-tests-file*)
                    (external-format :default) &allow-other-keys &aux
                    (input-file (input-file-pathname input-file))
                    (readtable *readtable*)
                    (package *package*))
  "Tangle and compile the web in INPUT-FILE, producing OUTPUT-FILE."
  (declare (ignorable output-file tests-file))
  (multiple-value-bind (output-file lisp-file tests-output-file tests-file)
      (apply #'tangle-file-pathnames input-file args)
    (with-standard-io-syntax
      (let* ((*readtable* readtable)
             (*package* package)
             (*tangle-file-pathname* input-file)
             (*tangle-file-truename* (truename *tangle-file-pathname*)))
        (when verbose (format t "~&; tangling web from ~A:~%" input-file))
        @<Initialize global variables@>
        (with-open-file (input input-file ;
                               :direction :input ;
                               :external-format external-format)
          (read-sections input))
        @<Complain about any unused named sections@>
        @<Ensure that every referenced named section is defined@>
        (cond ((and tests-file (> (length *test-sections*) 1))
               (when verbose (format t "~&; writing tests to ~A~%" tests-file))
               (tangle-sections *test-sections*
                                :input-file input-file
                                :output-file tests-file
                                :if-exists if-exists
                                :external-format external-format))
              (t (setq tests-file nil)))
        (when verbose (format t "~&; writing tangled code to ~A~%" lisp-file))
        (tangle-sections *sections*
                         :input-file input-file
                         :output-file lisp-file
                         :if-exists if-exists
                         :external-format external-format)
        (with-compilation-unit ()
          (multiple-value-prog1
              (compile-file lisp-file
                            :output-file output-file
                            :verbose verbose
                            :print print
                            :external-format external-format)
            (when (and tests-file compile-tests-file)
              (compile-file tests-file
                            :output-file tests-output-file
                            :verbose verbose
                            :print print
                            :external-format external-format))))))))

@ This routine performs the defaulting for the filename arguments to
|tangle-file|. It returns four pathnames: the output (\.{FASL}) file,
the intermediate Lisp file, the test suite output file, and~the test
suite Lisp file. The defaulting behavior is as follows:

\smallskip
\item\bull The output filename is generated by calling |compile-file-pathname|
with the supplied input filename and other arguments, including any supplied
|output-file|. It is thus system-specific.

\item\bull The Lisp filename is generated from the defaulted output filename
by replacing its type component with~`\.{LISP}'.

\item\bull The tests filename is computed by the function |tests-file-pathname|
using the defaulted input and output filenames.

\item\bull The tests output filename is generated from the defaulted tests
filename by replacing its type with the type of the defaulted output file.

@l
(defun default-input-file (input-file)
  (merge-pathnames input-file (make-pathname :type "CLW" :case :common)))

(defun tangle-file-pathnames (input-file &rest args &key ;
                              output-file tests-file &allow-other-keys)
  "Compute and return the names of the defaulted input file and files
output by the tangler."
  (declare (ignorable output-file tests-file))
  (let* ((input-file (input-file-pathname input-file))
         (output-file (apply #'compile-file-pathname input-file ;
                             :allow-other-keys t args))
         (lisp-file (make-pathname :type "LISP" ;
                                   :defaults output-file ;
                                   :case :common))
         (tests-file (apply #'tests-file-pathname input-file "LISP" ;
                            :output-file output-file ;
                            args))
         (tests-output-file ;
          (when tests-file
            (make-pathname :type (pathname-type output-file :case :common)
                           :defaults tests-file
                           :case :common))))
    (values output-file lisp-file tests-output-file tests-file)))

@t@l
(deftest (tangle-file-pathnames 1)
  (tangle-file-pathnames #P"clweb-test:foo")
  #.(compile-file-pathname #P"clweb-test:foo.lisp")
  #P"clweb-test:foo.lisp.newest"
  #.(compile-file-pathname #P"clweb-test:foo-tests.lisp")
  #P"clweb-test:foo-tests.lisp.newest")

(deftest (tangle-file-pathnames 2)
  (let* ((input-file #P"clweb-test:foo")
         (fasl-type (pathname-type (compile-file-pathname input-file) ;
                                   :case :common))
         (output-file (make-pathname :type fasl-type
                                     :defaults #P"clweb-test:a;b;bar"
                                     :case :common)))
    (tangle-file-pathnames input-file :output-file output-file))
  #.(compile-file-pathname #P"clweb-test:a;b;bar.lisp")
  #P"clweb-test:a;b;bar.lisp.newest"
  #.(compile-file-pathname #P"clweb-test:a;b;foo-tests.lisp")
  #P"clweb-test:a;b;foo-tests.lisp.newest")

(deftest (tangle-file-pathnames 3)
  (tangle-file-pathnames #P"clweb-test:foo" :tests-file nil)
  #.(compile-file-pathname #P"clweb-test:foo.lisp")
  #P"clweb-test:foo.lisp.newest"
  nil
  nil)

@ A named section doesn't do any good if it's never referenced, so we issue
warnings about unused named sections.

@<Complain about any unused...@>=
(let ((unused-sections '()))
  (flet ((note-unused-section (section)
           (when (null (used-by section))
             (push section unused-sections))))
    (map-bst #'note-unused-section *named-sections*)
    (map nil
         (lambda (section)
           (warn 'unused-named-section-warning
                 :format-control "Unused named section <~A>."
                 :format-arguments (list (section-name section))))
         (sort unused-sections #'< :key #'section-number))))

@ @<Condition classes@>=
(define-condition unused-named-section-warning (simple-warning) ())

@ Named sections that are referenced but never defined are assumed to be
errors. Here we'll rely on the fact that |section-number| detects this
condition and signals an error if it occurs.

@<Ensure that every referenced...@>=
(map-bst #'section-number *named-sections*)

@ |tangle-file| uses this helper function to actually write the tangled forms
to the intermediate Lisp source file. It's used for both ordinary and test
sections.

@l
(defun tangle-sections (sections &key input-file output-file ;
                        if-exists external-format)
  (with-open-file (output output-file
                   :direction :output
                   :if-exists if-exists
                   :external-format external-format)
    (format output ";;;; TANGLED WEB FROM \"~A\". DO NOT EDIT.~%" input-file)
    (let ((*evaluating* nil)
          (*print-pprint-dispatch* *tangle-pprint-dispatch*)
          (*print-readably* t))
      @<Output a form that sets the source pathname@>
      (dolist (form (tangle (unnamed-section-code-parts sections)))
        (pprint form output)))))

@ Allegro Common Lisp uses the variable |*source-pathname*| to locate
definitions in source files. If we override that, we can get it to look
in the \CLWEB\ file instead of the tangled Lisp file.
@^Allegro Common Lisp@>

We have to do this output as a string rather than a form because the
package |"EXCL"| might not exist in the implementation with which we're
tangling.

@<Output a form that sets...@>=
(format output
        "#+ALLEGRO~
         ~&(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL)~
         ~&  (SETQ EXCL:*SOURCE-PATHNAME* ~S))~%"
        *tangle-file-pathname*)

@*Weaving. The function |weave| reads a web from |input-file| and produces
an output \TeX\ file named by |output-file|. By default, it also weaves
test sections to the file named by |tests-file| and produces an index and
list of section names which can be included from the output file. The
defaulting behavior for the filename arguments is complex; see below.

If |verbose| is true, |weave| prints a message in the form of a comment to
standard output indicating what file is being woven. If |verbose| is not
supplied, the value of |*weave-verbose*| is used.

If |print| is true, the section number of each section encountered is printed
to standard output, with starred sections prefixed with a `\.{*}'. If |print|
is not supplied, the value of |*weave-print*| is used.

Finally, the |external-format| argument specifies the external file
format to be used when opening both the input file and the output file.
{\it N.B.\/}: standard \TeX\ only handles 8-bit characters, and the
encodings for non-printable-{\sc ascii} characters vary widely.

If successful, |weave| returns the truename of the output file. 

@l
(defun weave (input-file &rest args &key output-file tests-file index-file
              (verbose *weave-verbose*)
              (print *weave-print*)
              (external-format :default) &aux
              (input-file (input-file-pathname input-file))
              (readtable *readtable*)
              (package *package*))
  "Weave the web contained in INPUT-FILE, producing the TeX file OUTPUT-FILE."
  (declare (ignorable output-file tests-file index-file))
  (multiple-value-bind (output-file index-file sections-file)
       (apply #'weave-pathnames input-file args)
    (with-standard-io-syntax
      (let ((*readtable* readtable)
            (*package* package))
        (when verbose (format t "~&; weaving web from ~A:~%" input-file))
        @<Initialize global variables@>
        (with-open-file (input input-file ;
                               :direction :input ;
                               :external-format external-format)
          (read-sections input))
        (let ((tests-file (apply #'tests-file-pathname input-file "TEX" ;
                                 :output-file output-file ;
                                 args)))
          (when (and tests-file (> (length *test-sections*) 1))
            (when verbose (format t "~&; weaving tests to ~A~%" tests-file))
            (multiple-value-bind (output-file index-file sections-file)
                (apply #'weave-pathnames input-file ;
                       :output-file tests-file ;
                       args)
              @<Fix up the index and sections filenames for test suite output@>
              (weave-sections *test-sections*
                              :input-file input-file
                              :output-file output-file
                              :index-file index-file
                              :sections-file sections-file
                              :verbose verbose
                              :print print
                              :external-format external-format
                              :weaving-tests t))))
        (when verbose (format t "~&; weaving sections to ~A~%" output-file))
        (weave-sections *sections*
                        :input-file input-file
                        :output-file output-file
                        :index-file index-file
                        :sections-file sections-file
                        :verbose verbose
                        :print print
                        :external-format external-format)))))

@ We don't accept a separate argument for the test suite index filename,
so we have to do a little post-processing to get it all right. At this
point, |output-file| is the name of the {\it tests\/} output file; we'll
use its name component as the name components of the index and sections
files for the test suite.

@<Fix up the index and sections filenames...@>=
(when index-file
  (let ((output-file-name (make-pathname :name (pathname-name output-file))))
    (setq index-file (merge-pathnames output-file-name index-file)
          sections-file (merge-pathnames output-file-name sections-file))))

@ This routine does the defaulting for the filename arguments to |weave|.
It returns three filenames: the output (\TeX) filename, the index filename,
and the section names list filename. They are defaulted as follows:

\smallskip
\item\bull If |output-file| is not supplied or is |nil|, a pathname will be
generated from |input-file| by replacing its type component with~`\.{TEX}'.

\item\bull If |index-file| is not supplied or is supplied and non-null,
an index of variables, functions, classes, \etc. will be written to the
indicated file. The default filename is generated from |output-file| by
replacing its type component with~`\.{IDX}'.

\item\bull The sections filename is generated from the index filename
by replacing its type component with~`\.{SCN}'.

@l
(defun weave-pathnames (input-file &key output-file ;
                        (index-file nil index-file-supplied) ;
                        &allow-other-keys)
  "Compute and return the names of the defaulted input file and files
output by the weaver."
  (let* ((input-file (input-file-pathname input-file))
         (output-file (let ((output-file-defaults
                             (make-pathname :type "TEX" ;
                                            :defaults input-file ;
                                            :case :common)))
                        (if output-file
                            (merge-pathnames output-file output-file-defaults)
                            output-file-defaults)))
         (index-file (let ((index-file-defaults
                            (make-pathname :type "IDX" ;
                                           :defaults output-file ;
                                           :case :common)))
                       (if index-file
                           (merge-pathnames index-file index-file-defaults)
                           (when (not index-file-supplied) ;
                             index-file-defaults))))
         (sections-file (when index-file
                          (make-pathname :type "SCN" ;
                                         :defaults index-file ;
                                         :case :common))))
    (values output-file index-file sections-file)))

@t@l
(deftest (weave-pathnames 1)
  (weave-pathnames #P"clweb-test:foo")
  #P"clweb-test:foo.tex.newest"
  #P"clweb-test:foo.idx.newest"
  #P"clweb-test:foo.scn.newest")

(deftest (weave-pathnames 2)
  (weave-pathnames #P"clweb-test:foo" :output-file #P"clweb-test:a;b;bar")
  #P"clweb-test:a;b;bar.tex.newest"
  #P"clweb-test:a;b;bar.idx.newest"
  #P"clweb-test:a;b;bar.scn.newest")

(deftest (weave-pathnames 3)
  (weave-pathnames #P"clweb-test:foo" :index-file nil)
  #P"clweb-test:foo.tex.newest"
  nil
  nil)

(deftest (weave-pathnames 4)
  (weave-pathnames #P"clweb-test:foo"
                   :output-file #P"clweb-test:a;b;bar.tex"
                   :index-file #P"clweb-test:c;index")
  #P"clweb-test:a;b;bar.tex.newest"
  #P"clweb-test:c;index.idx.newest"
  #P"clweb-test:c;index.scn.newest")

@ @<Global variables@>=
(defvar *weave-verbose* t
  "The default for the :VERBOSE argument to WEAVE.")
(defvar *weave-print* t
  "The default for the :PRINT argument to WEAVE.")

@ The following routine does most of the actual output for the weaver.
It takes a list of sections and the defaulted arguments from |weave|,
and writes the output file and possibly the index and section list files
as well. It's used to produce both the primary and test output, which
differ only slightly; the |weaving-tests| argument will be true if it's
currently weaving the tests.

@l
(defun weave-sections (sections &key input-file output-file ;
                       index-file sections-file
                       weaving-tests verbose print
                       (if-exists  @<|:if-exists|...@>)
                       external-format)
  (macrolet ((with-output-file ((stream filespec) &body body)
               `(with-open-file (,stream ,filespec
                                 :direction :output
                                 :external-format external-format
                                 :if-exists if-exists)
                  ,@body)))
    (with-output-file (out output-file)
      (format out "\\input clwebmac~%")
      (when weaving-tests @<Write the program name to the tests output file@>)
      (if print
          @<Weave the sections to the output file, reporting as we go@>
          (map nil (lambda (section) (weave-object section out)) sections))
      (when index-file
        (when verbose (format t "~&; writing the index to ~A~%" index-file))
        (with-output-file (idx index-file)
          (weave-object (index-sections sections ;
                                        :index (if weaving-tests ;
                                                   (make-index) ;
                                                   *index*))
                        idx))
        (with-output-file (scn sections-file)
          (map-bst (lambda (section)
                     (unless (every (if weaving-tests ;
                                        (complement #'test-section-p) ;
                                        #'test-section-p)
                                    (named-section-sections section))
                       (weave-object (make-section-name-index-entry section) ;
                                     scn)))
                   *named-sections*))
        (format out "~&\\inx~%\\fin~%\\con~%"))
      (format out "~&\\end~%")
      (truename out))))

@ We'll use the pretty printer to print the section numbers to standard
output as we weave them. Starred sections get a `\.{*}' prefix, and the
whole of the output is in the form of a comment.

@<Weave the sections...@>=
(flet ((weave-section (section)
         (format t "~:[~;*~]~D" ;
                 (starred-section-p section) ;
                 (section-number section))
         (weave-object section out)))
  (pprint-logical-block (nil (coerce sections 'list) :per-line-prefix ";  ")
    (weave-section (pprint-pop))
    (loop
      (pprint-exit-if-list-exhausted)
      (write-char #\Space)
      (pprint-newline :fill)
      (weave-section (pprint-pop)))))

@ In the tests output file, we generate references to the sections of the
main program that are presumably being tested. To produce those references,
the \TeX\ macros \.{\\T} and \.{\\Ts} use the \.{\\progname} macro. We
provide a default definition here using the name of the input file, but
the user can easily override this by giving an alternate definition in the
limbo text.

@<Write the program name...@>=
(format out "\\def\\progname{~/clweb::print-escaped/}~%"
        (if input-file
            (string-capitalize (pathname-name input-file))
            "program"))

@1*Printing the woven output. The individual sections and their contents
are printed using the pretty printer with a customized dispatch table.

@<Global variables@>=
(defparameter *weave-pprint-dispatch* (copy-pprint-dispatch nil))

@ @<Define the pprint dispatch table setters@>=
(defun set-weave-dispatch (type-specifier function &optional (priority 0))
  (set-pprint-dispatch type-specifier function priority ;
                       *weave-pprint-dispatch*))

@ Here's a little convenience routine for weaving an object to a stream.

@l
(defun weave-object (object stream)
  (write object
         :stream stream :readably t
         :case :downcase
         :pretty t :pprint-dispatch *weave-pprint-dispatch* ;
         :right-margin 1000))

@ \TeX-mode material is represented as a list of strings containing pure
\TeX\ text and lists of (inner-)Lisp forms, and this routine is responsible
for printing it. It takes a |&rest| parameter so that it can be used with
the `\.{\~/.../}' |format| directive.

@l
(defun print-TeX (stream tex-mode-material &rest args)
  (declare (ignore args))
  (dolist (x tex-mode-material)
    (etypecase x
      (string (write-string x stream))
      (list (dolist (form x)
              (format stream "\\(~W\\)" form))))))

@ Control text (like section names) and comments are initially read as
strings containing pure \TeX\ text, but they actually contain restricted
\TeX-mode material, which may include inner-Lisp material. This routine
re-reads such strings and picks up any inner-Lisp material.

@l
(defun read-TeX-from-string (input-string)
  (with-mode :restricted
    (with-input-from-string (stream input-string)
      (loop for text = (snarf-until-control-char stream #\|)
            for forms = (read-preserving-whitespace stream nil eof nil)
            if (plusp (length text)) collect text
            if (eof-p forms) do (loop-finish) else collect forms))))

@ Printing a limbo section is simple: we just dump out the \TeX\ text.
Notice that we use a priority of~$1$ so as to override the normal section
object printer, which we'll come to next.

@l
(defun print-limbo (stream section)
  (let ((commentary (section-commentary section)))
    (when commentary
      (print-TeX stream commentary)
      (terpri stream))))

(set-weave-dispatch 'limbo-section #'print-limbo 1)

@ Section objects are printed just like any other objects, but they use some
special \TeX\ macros to set up the formatting. They begin with either \.{\\M}
or \.{\\N} depending on whether the section is unstarred or starred. Then
comes the commentary, which is separated from the code part by a bit of
vertical space using the \.{\\Y} macro if both are present. The code part
always starts with \.{\\B}, followed by the name if it's a named section.
Then comes the code, which we output one form at a time, using alignment
tabs (\.{\\+}). Last come the cross-references and a final \.{\\fi} that
matches the \.{\\ifon} in \.{\\M} and \.{\\N}.

@l
(defun print-section (stream section)
  (format stream "~&\\~:[M~*~;N{~D}~]{~D}"
          (starred-section-p section)
          (section-depth section)
          (section-number section))
  (let* ((commentary (section-commentary section))
         (name (section-name section))
         (named-section (and name (find-section name)))
         (code (section-code section)))
    (print-TeX stream commentary)
    (cond ((and commentary code) (format stream "~&\\Y\\B~%"))
          (code (format stream "~&\\B~%")))
    (when named-section
      (print-section-name stream named-section)
      (format stream "${}~:[\\mathrel+~;~]\\E{}$\\6~%"
              (= (section-number section) (section-number named-section))))
    (when code
      (dolist (form code)
        (typecase form
          (newline-marker (format stream "~W" form))
          (t (format stream "~@<\\+~@;~W~;\\cr~:>" form))))
      (format stream "~&\\egroup~%")) ; matches \.{\\bgroup} in \.{\\B}
    (when (and (not named-section)
               (typep section 'test-section)
               (section-code section))
      (format stream "\\T~P~D.~%"
              (length (section-code section))
              (section-number (test-for-section section))))
    (when (and named-section
               (= (section-number section)
                  (section-number named-section)))
      (print-xrefs stream #\A ;
                   (remove section (named-section-sections named-section)))
      (print-xrefs stream #\U ;
                   (remove section (used-by named-section)))
      (print-xrefs stream #\Q ;
                   (remove section (cited-by named-section)))))
  (format stream "~&\\fi~%"))

(set-weave-dispatch 'section #'print-section)

@ The cross-references lists use the macros \.{\\A} (for `also'),
\.{\\U} (for `use'), \.{\\Q} (for `quote'), and their pluralized variants,
along with the conjunction macros \.{\\ET} (for two section numbers)
and~\.{\\ETs} (for between the last of three or more).

@l
(defun print-xrefs (stream kind xrefs)
  (when xrefs
    ;; This was 16 lines of code over two sections in \CWEB\null. I love |format|.
    (format stream "\\~C~{~#[~;~D~;s ~D\\ET~D~:;s~@{~#[~;\\ETs~D~;~D~:;~D, ~]~}~]~}.~%"
            kind (sort (mapcar #'section-number xrefs) #'<))))

@ Aside from printing the section name in the body of the woven output,
this next routine also knows how to print entries for the section name
index, which uses a similar, but slightly different format.

@l
(defun print-section-name (stream section &key (indexing nil))
  (format stream "~:[~;\\I~]\\X~{~D~^, ~}:~/clweb::print-TeX/\\X"
          indexing
          (if indexing
              (sort (mapcar #'section-number ;
                            (named-section-sections section)) ;
                            #'<)
              (list (section-number section)))
          (read-TeX-from-string (section-name section))))

(set-weave-dispatch 'named-section #'print-section-name)

@ When printing the section name index, the weaver wraps each named section
in a |section-name-index| instance so that we can dispatch on that type.

@l
(defclass section-name-index-entry ()
  ((named-section :accessor named-section :initarg :named-section)))

(defun make-section-name-index-entry (section)
  (make-instance 'section-name-index-entry :named-section section))

(set-weave-dispatch 'section-name-index-entry
  (lambda (stream section-name &aux (section (named-section section-name)))
    (print-section-name stream section :indexing t)
    (terpri stream)
    (print-xrefs stream #\U (remove section (used-by section)))
    (print-xrefs stream #\Q (remove section (cited-by section)))))

@ Because we're outputting \TeX, we need to carefully escape characters
that \TeX\ treats as special. Unfortunately, because \TeX's syntax is so
malleable (not unlike Lisp's), it's nontrivial to decide what to escape,
how, and when.

The following routine is the basis for most of the escaping. It writes
|string| to the output stream designated by |stream|, escaping the
characters given in the a-list |*print-escape-list*|. The entries in this
a-list should be of the form `(\<characters>~.~\<replacement>)',
where \<replacement> describes how to escape each of the characters
in \<characters>. Suppose $c$ is a character in |string| that
appears in one of the \<characters> strings. If the corresponding
\<replacement> is a single character, then |print-escaped| will
output it prior to every occurrence of $c$. If \<replacement> is a
string, it will be output {\it instead of\/} every occurrence of $c$ in
the input. Otherwise, $c$ will be output without escaping.

The default value for |*print-escape-list*| defined below is suitable for
escaping most \TeX\ metacharacters; callers should bind it to a new
value if they require specialized escaping.

@l
(defparameter *print-escape-list* ;
  '((" \\%&#$^_" . #\\)
    ("~" . "$\\sim$")
    ("{" . "$\\{$") ("}" . "$\\}$")
    ("<" . "$<$") (">" . "$>$")))

(defun print-escaped (stream string &rest args &aux
                      (stream (case stream
                                ((t) *terminal-io*)
                                ((nil) *standard-output*)
                                (otherwise stream))))
  (declare (ignore args))
  (loop for char across string
        as escape = (cdr (assoc char *print-escape-list* :test #'find))
        if escape
          do (etypecase escape
               (character (write-char escape stream)
                          (write-char char stream))
               (string (write-string escape stream)))
        else
          do (write-char char stream)))

@t@l
(deftest print-escaped
  (with-output-to-string (s)
    (print-escaped s "foo#{bar}*baz"))
  "foo\\#$\\{$bar$\\}$*baz")

@ We print strings one line at a time, being careful to properly end each
alignment row. As a special nicety for |format| strings, if the last
character before a newline is a~`\.{\~}', we skip any whitespace following
the newline.

@l
(defun print-string (stream string)
  (loop with *print-escape-list* = `(("{*~}" . #\\)
                                     ("\\" . "\\\\\\\\")
                                     ("\"" . "\\\\\"")
                                     ,@*print-escape-list*)
        for last = 0 then (if (char= (elt string (1- newline)) #\~)
                              (position-if-not #'whitespacep string ;
                                                :start newline)
                              (1+ newline))
        for newline = (position #\Newline string :start last)
        as line = (subseq string last newline)
        do (format stream "\\.{~:[~;\"~]~/clweb::print-escaped/~:[~;\"~]}"
                   (zerop last) line (null newline))
        while newline do (format stream "\\cr~:@_")))

(set-weave-dispatch 'string #'print-string)

@ We print non-graphic characters using their names, when available.

@l
(defun print-char (stream char)
  (let ((graphicp (and (graphic-char-p char) (standard-char-p char)))
        (name (char-name char))
        (*print-escape-list* `(("{~}" . #\\) ,@*print-escape-list*)))
    (format stream "\\#\\CH{~/clweb::print-escaped/}"
            (if (and name (not graphicp))
                name
                (string char)))
    char))

(set-weave-dispatch 'character #'print-char)

@ Symbols are printed by first writing them out to a string, then printing
that string. This relieves us of the burden of worrying about case conversion,
package prefixes, and the like---we just let the Lisp printer handle it.

Lambda-list keywords and symbols in the `keyword' package have specialized
\TeX\ macros that add a bit of emphasis.

@l
(defun print-symbol (stream symbol)
  (let* ((group-p (cond ((member symbol lambda-list-keywords)
                         (write-string "\\K{" stream))
                        ((keywordp symbol)
                         (write-string "\\:{" stream))))
         (string (write-to-string symbol :escape nil :pretty nil)))
    (multiple-value-bind (prefix suffix)
        @<Split |string| into a prefix and nicely formatted suffix@>
      (print-escaped stream prefix)
      (when suffix (write-string suffix stream)))
    (when group-p (write-string "}" stream))))

(set-weave-dispatch 'symbol #'print-symbol)

@ Symbols with certain suffixes also get a bit of fancy formatting. 
We test for suffixes one at a time, and if we find a match, we return
two values: the portion of |string| before the suffix and the suffix
replacement. Otherwise, we just return the string.

@<Split |string|...@>=
(loop with string-length = (length string)
      for (suffix . replacement) in *print-symbol-suffixes*
      as prefix-end = (max 0 (- string-length (length suffix)))
      when (string= string suffix :start1 prefix-end)
        do (return (values (subseq string 0 prefix-end) replacement))
      finally (return string))

@ We'll keep the suffixes in a global variable in case the user wants to
override them for whatever reason. The format is simply a list of pairs
of the form `(\<suffix>~.~\<replacement>)'.

@<Global variables@>=
(defvar *print-symbol-suffixes*
  '(("/=" . "$\\neq$")
    ("<=" . "$\\leq$")
    (">=" . "$\\geq$")
    ("-" . "$-$")
    ("+" . "$+$")
    ("=" . "$=$")))

@ A few symbols get special replacements.

@l
(defmacro weave-symbol-replace (symbol replacement)
  `(set-weave-dispatch '(eql ,symbol)
     (lambda (stream obj)
       (declare (ignore obj))
       (write-string ,replacement stream))
     1))

(weave-symbol-replace lambda "\\L")
(weave-symbol-replace pi "$\\pi$")

@ We transform \.{\#'} into instances of |function-marker| during reading,
so we don't want lists of the form |(function foo)| turned into |#'foo|
during weaving.

@l
(set-weave-dispatch '(cons (eql function))
  (lambda (stream obj)
    (format stream "(~{~W~^ ~})" obj))
  1)

@1*Indentation tracking. Next, we turn to list printing, and the tricky
topic of indentation. On the assumption that the human writing a web is
smarter than a program doing any sort of automatic indentation, we attempt
to approximate (but not duplicate) on output the indentation given in the
input by utilizing the character position values that the list reader
stores in the list markers. We do this by breaking up lists into
{\it logical blocks\/}---the same sort of (abstract) entities that the
pretty printer uses, but made concrete here. A logical block defines a
left edge for a list of forms, some of which may be nested logical blocks.

@l
(defclass logical-block ()
  ((list :reader logical-block-list :initarg :list)))

(defun make-logical-block (list)
  (make-instance 'logical-block :list list))

@ The analysis of the indentation is performed by a recursive |labels|
routine, to which we will come in a moment. That routine operates on an
list of |(form . charpos)| conses, taken from a list marker. Building this
list does cost us some consing, but vastly simplifies the logic, since we
don't have to worry about keeping multiple indices synchronized.

@l
(defun analyze-indentation (list-marker)
  (declare (type list-marker list-marker))
  (labels ((find-next-newline (list) (member-if #'newlinep list :key #'car))
           (next-logical-block (list) @<Build a logical block from |list|@>))
    ;; Sanity check.
    (assert (= (length (list-marker-list list-marker))
               (length (list-marker-charpos list-marker)))
            ((list-marker-list list-marker) (list-marker-charpos list-marker))
            "List marker's list and charpos-list aren't the same length.")
    (next-logical-block (mapcar #'cons
                                (list-marker-list list-marker)
                                (list-marker-charpos list-marker)))))

@ To build a logical block, we identify groups of sub-forms that share a
common left margin, which we'll call the {\it block indentation}. If that
left margin is to the right of that of the current block, we recursively
build a new subordinate logical block. The block ends when the first form
on the next line falls to the left of the current block, or we run out of
forms.

For example, consider the following simple form:
\smallskip\hskip2\parindent
\vbox{\B\+(first \!&second\cr\+&third)\cr\egroup}
\smallskip\noindent We start off with an initial logical block whose
indentation is the character position of |first|: this is the {\it block
indentation}. Then we look at |second|, and see that the first form on the
following line, |third|, has the same position, and that it exceeds the
current indentation level. And so we recurse, appending to the new logical
block until we encounter a form whose indentation is less than the new
block indentation, or, as in this trivial example, the end of the list.

More concretely, |next-logical-block| returns two values: the logical block
constructed, and the unused portion of the list, which will always either
be |nil| (we consumed the rest of the forms), or begin with a newline.

We keep a pointer to the next newline in |newline|, and |next-indent| is
the indentation of the immediately following form, which will become the
current indentation when we pass |newline|. As we do so, we store the
difference between the current indentation and the block indentation in
the newline marker, so that the printing routine, below, doesn't have to
worry about character positions at all: it can just look at the newline
markers and the logical block structure.

As an optimization, if we build a block that doesn't directly contain any
newlines---a trivial logical block---we simply return a list of sub-forms
instead of a logical block structure. This can make the resulting \TeX\
somewhat simpler.

@<Build a logical block...@>=
(do* ((block '())
      (block-indent (cdar list))
      (indent block-indent)
      (newline (find-next-newline list))
      (next-indent (cdadr newline)))
     ((or (endp list)
          (and (eq list newline) next-indent (< 0 next-indent block-indent)))
      (values (if (notany #'newlinep block)
                  (nreverse block)
                  (make-logical-block (nreverse block)))
              list))
  (if (and indent next-indent
           (> next-indent indent)
           (= next-indent (cdar list)))
      (multiple-value-bind (sub-block tail) (next-logical-block list)
        (check-type (caar tail) (or newline-marker null))
        (push sub-block block)
        (setq list tail))
      (let ((next (car (pop list))))
        (push next block)
        (when (and list (newlinep next))
          (setf indent (cdar list)
                (indentation next) (- indent block-indent)
                newline (find-next-newline list)
                next-indent (cdadr newline))))))

@ Printing list markers is now simple, since the complexity is all in the
logical blocks$\ldots$

@l
(defun print-list (stream list-marker)
  (let ((block (analyze-indentation list-marker)))
    (etypecase block
      (list (format stream "~<(~;~@{~W~^ ~}~;)~:>" block))
      (logical-block (format stream "(~W)" block)))))

(set-weave-dispatch 'list-marker #'print-list)

@ $\ldots$but even here, it's not that bad. We start with a \.{\\!}, which
is just an alias for \.{\\cleartabs}. Then we call (unsurprisingly)
|pprint-logical-block|, using a per-line-prefix for our alignment tabs.

In the loop, we keep a one-token look-ahead to check for newlines, so that
we can output separating spaces when and only when there isn't a newline
coming up.

The logical-block building machinery above set the indentation on newlines
to the difference in character positions of the first form following
the newline and the block indentation. For differences of 1 or~2 columns,
we use a single quad (\.{\\1}); for any more, we use two (\.{\\2}).

@l
(defun print-logical-block (stream block)
  (write-string "\\!" stream)
  (pprint-logical-block (stream (logical-block-list block) :per-line-prefix "&")
    (do (indent
         next
         (obj (pprint-pop) next))
        (nil)
      (cond ((newlinep obj)
             (format stream "\\cr~:[~;\\Y~]~:@_" (typep obj 'par-marker))
             (setq indent (indentation obj))
             (pprint-exit-if-list-exhausted)
             (setq next (pprint-pop)))
            (t (format stream "~@[~[~;\\1~;\\1~:;\\2~]~]~W" indent obj)
               (setq indent nil)
               (pprint-exit-if-list-exhausted)
               (setq next (pprint-pop))
               (unless (newlinep next)
                 (write-char #\Space stream)))))))

(set-weave-dispatch 'logical-block #'print-logical-block)

@1*Printing markers. Finally, we come to the printing of markers.
These are all quite straightforward; the only thing to watch out for
is the priorities. Because |pprint-dispatch| doesn't respect sub-type
relationships, we need to set a higher priority for a sub-class than
for its parent if we want a specialized pretty-printing routine.

Many of these routines output \TeX\ macros defined in \.{clwebmac.tex},
which see.
@.clwebmac.tex@>

@ @l
(set-weave-dispatch 'newline-marker
  (lambda (stream obj)
    (declare (ignore obj))
    (terpri stream)))

(set-weave-dispatch 'par-marker
  (lambda (stream obj)
    (declare (ignore obj))
    (format stream "~&\\Y~%"))
  1)

@ @l
(set-weave-dispatch 'empty-list-marker
  (lambda (stream obj)
    (declare (ignore obj))
    (write-string "()" stream)))

(set-weave-dispatch 'consing-dot-marker
  (lambda (stream obj)
    (declare (ignore obj))
    (write-char #\. stream)))

@ @l
(set-weave-dispatch 'quote-marker
  (lambda (stream obj)
    (format stream "\\'~W" (quoted-form obj))))

@ @l
(set-weave-dispatch 'comment-marker
  (lambda (stream obj)
    (format stream "\\C{~/clweb::print-TeX/}"
            (read-TeX-from-string (comment-text obj)))))

@ @l
(set-weave-dispatch 'backquote-form
  (lambda (stream obj)
    (format stream "\\`~W" (cadr obj))))

(set-weave-dispatch 'comma
  (lambda (stream obj)
    (format stream "\\CO{~@[~C~]}~W"
            (comma-modifier obj)
            (comma-form obj :tangle nil))))

@ @l
(set-weave-dispatch 'function-marker
  (lambda (stream obj)
    (format stream "\\#\\'~S" (quoted-form obj)))
  1)

@ @l
(set-weave-dispatch 'simple-vector-marker
  (lambda (stream obj)
    (format stream "\\#~@[~D~]~S"
            (and (slot-boundp obj 'length)
                 (slot-value obj 'length))
            (slot-value obj 'elements))))

(set-weave-dispatch 'bit-vector-marker
  (lambda (stream obj)
    (format stream "\\#~@[~D~]*~{~[0~;1~]~}"
            (and (slot-boundp obj 'length)
                 (slot-value obj 'length))
            (map 'list #'identity
                 (slot-value obj 'elements))))
  1)

@ @l
(set-weave-dispatch 'read-time-eval-marker
  (lambda (stream obj)
    (format stream "\\#.~W" (read-time-eval-form obj))))

@ @l
(set-weave-dispatch 'radix-marker
  (lambda (stream obj)
    (format stream "$~VR_{~2:*~D}$"
            (radix-marker-base obj) (marker-value obj))))

@ @l
(set-weave-dispatch 'complex-marker
  (lambda (stream obj)
    (format stream "\\#C~W" (complex-components obj))))

@ @l
(set-weave-dispatch 'array-marker
  (lambda (stream obj)
    (format stream "\\#~DA~W"
            (array-marker-rank obj)
            (array-marker-initial-contents obj))))

@ @l
(set-weave-dispatch 'structure-marker
  (lambda (stream obj)
    (format stream "\\#S~W" (structure-marker-form obj))))

@ @l
(set-weave-dispatch 'pathname-marker
  (lambda (stream obj)
    (format stream "\\#P~W" (pathname-marker-namestring obj))))

@ Read-time conditionals, like literal strings, must be printed one line at
a time so as to respect the alignment tabs. Since the \.{\\RC} macro switches
to a monospaced font and activates \.{\\obeyspaces}, dealing with indentation
is straightforward.

@l
(set-weave-dispatch 'read-time-conditional-marker
  (lambda (stream obj)
    (let* ((form (read-time-conditional-form obj))
           (lines @<Split |form| into lines, eliding any initial indentation@>)
           (*print-escape-list* `((" " . " ") ,@*print-escape-list*)))
      (flet ((print-rc-prefix ()
               (format stream "\\#$~:[-~;+~]$~S"
                       (read-time-conditional-plusp obj)
                       (read-time-conditional-test obj)))
             (print-rc-line (line)
               (format stream "\\RC{~/clweb::print-escaped/}" line)))
        (cond ((= (length lines) 1)
               (print-rc-prefix)
               (print-rc-line (first lines)))
              (t (write-string "\\!" stream)
                 (pprint-logical-block (stream lines :per-line-prefix "&")
                   (print-rc-prefix)
                   (pprint-exit-if-list-exhausted)
                   (loop for line = (pprint-pop)
                         when (plusp (length line)) do (print-rc-line line)
                         do (pprint-exit-if-list-exhausted)
                            (format stream "\\cr~:@_")))))))))

@ @<Split |form| into lines...@>=
(loop with indent = (if (char= (elt form 0) #\Newline)
                        (1- (position-if-not #'whitespacep form :start 1))
                        0)
      for last = 0 then (+ indent newline 1)
      for newline = (position #\Newline form :start last)
      as line = (subseq form last newline)
      collect line while newline)

@*Code walking. Our last major task is to produce an index of every
interesting symbol that occurs in a web (we'll define what makes a
symbol `interesting' later). We would like separate entries for each
kind of object that a given symbol names: e.g., local or global function,
lexical or special variable, \etc. And finally, we should note whether
a given occurrence of a symbol is a definition/binding or just a use.

In order to accomplish this, we need to walk the tangled code of the
entire program, since the meaning of a symbol in Common Lisp depends,
in general, on its lexical environment, which can only be determined
by code walking. For reasons that will be explained later, we'll
actually be walking a special sort of munged code that isn't exactly
Common Lisp. And because of this, none of the available code walkers
will quite do what we want. So we'll roll our own.

@ We'll use the environments {\sc api} defined in~\cltl, since even
though it's not part of the Common Lisp standard, it's widely supported,
and does everything we need it to do.
@^environments {\sc api}@>
@^\cltl@>

Allegro Common Lisp has an additional function,
|ensure-portable-walking-environment|, that needs to be called on
any environment object that a portable walker uses; we'll provide
a trivial definition for other Lisps.
@^Allegro Common Lisp@>

@l
(defun ensure-portable-walking-environment (env)
  #+allegro (sys:ensure-portable-walking-environment env)
  #-allegro env)

@ Allegro doesn't define |parse-macro| or |enclose|, so we'll need
to provide our own definitions.
@^Allegro Common Lisp@>

We'll use our own version of |enclose| on all implementations.
Thanks to Duane Rettig of Franz,~Inc.\ for the idea behind this
implementation (post to {\it comp.lang.lisp}, message-id
\<4is97u4vv.fsf@@franz.com>, 2004-10-18).

@l
(defun enclose (lambda-expression &optional env ;
                (walker (make-instance 'walker)))
  (coerce (walk-lambda-expression walker lambda-expression nil env) 'function))

@ The following code for |parse-macro| is obviously extremely
implementation-specific; a portable version would be much more complex.
@^Allegro Common Lisp@>

@l
#+allegro
(defun parse-macro (name lambda-list body &optional env)
  (declare (ignorable name lambda-list body env))
  (excl::defmacro-expander `(,name ,lambda-list ,@body) env))

@ The good people at Franz also decided that they needed an extra value
returned from both |variable-information| and |function-information|.
But instead of doing the sensible thing and adding that extra value at
the {\it end\/} of the list of returned values, they {\it changed\/}
the order from the one specified by~\cltl, so that their new value is
the second value returned, and what should be second is now fourth.
Thanks, Franz!
@^Allegro Common Lisp@>

@l
(defmacro reorder-env-information (fn orig)
  `(defun ,fn (&rest args)
     (multiple-value-bind (type locative declarations local) (apply ,orig args)
       (declare (ignore locative))
       (values type local declarations))))

#+allegro
(reorder-env-information variable-information #'sys:variable-information)
#+allegro
(reorder-env-information function-information #'sys:function-information)

@ Along with the environment, most of the walker functions take a `context'
argument that gives some extra information about the form being walked.
Those arguments will always be instances of |walk-context|, or |nil| if
there is no relevant information to supply.

@l
(defclass walk-context () ())

(defun make-context (context &rest args)
  (apply #'make-instance context args))

@ The most important kind of context we'll supply is the {\it namespace\/}
of a name that's about to be walked. Namespaces are associated with
environments, but the \cltl\ environments {\sc api} does not provide
functions for dealing directly with many of the kinds of namespaces
that we'll define. However, the most important namespaces---variable
names, function names, macros, \etc.---do have corresponding entries
in the lexical environment objects that we'll pass around, and we'll
make it easy to maintain this link.

The main problem that these namespace objects solve is that we'll
need to walk names of all kinds {\it before\/} we add them to or even
look them up in the environment because of the referring symbols the
indexing walker uses to track sections in tangled code. We'll therefore
use them to represent both a namespace that an evaluated name should
already exist in, and the namespace in which a new binding is being
established.

Associated with every namespace is a name---not the name that's being
walked, but an identifier for the namespace itself, like `variable' or
`function'. Those names will be keyword symbols, and for namespaces that
correspond directly to lexical environments, the name should match the
symbol returned as the second value from the environment accessor for that
namespace. For instance, |variable-information| returns |:lexical| as its
second value if the given variable is a lexical variable in the current
environment, and so our lexical variable namespace has |:lexical| as its
name.

Every entry in a namespace---i.e., every binding---can be either `local'
or `global'. For some namespaces, only global names are supported (e.g.,
compiler macros can only be global), but the question ``is this binding
local or global?'' still makes sense for those namespaces.

@l
(defclass namespace (walk-context)
  ((name :reader namespace-name :initform nil :allocation :class)
   (local :reader local-binding-p :initarg :local :type boolean))
  (:default-initargs :local nil))

@t@l
(defmethod print-object ((x namespace) stream)
  (print-unreadable-object (x stream :type t :identity t)
    (when (local-binding-p x)
      (prin1 :local stream))))

@ During a walk, we'll sometimes need to go from a namespace name to the
class we use to represent that namespace. The following hash table and
accessor functions implement that mapping.

@l
(defparameter *namespace-classes* (make-hash-table :test 'eq))

(defun (setf find-namespace-class) (class namespace-name)
  (setf (gethash namespace-name *namespace-classes*) class))

(defun find-namespace-class (namespace-name)
  (flet ((read-namespace-class-name ()
           (loop
             (format *query-io* "Enter a namespace class name: ")
             (let ((class (find-class (read *query-io*) nil)))
               (when (and class (subtypep class 'namespace))
                 (return (list class)))))))
    (restart-case
        (or (gethash namespace-name *namespace-classes*)
            (error "Can't find namespace class for namespace ~S." ;
                   namespace-name))
      (use-value (value)
        :report "Specify a class to use this time."
        :interactive read-namespace-class-name
        value)
      (store-value (value)
        :report "Specify a class to store and use in the future."
        :interactive read-namespace-class-name
        (setf (find-namespace-class namespace-name) value)))))

@ We'll wrap up the namespace class definitions in a little defining
macro that eliminates some syntactic redundancies and sets up the
\hbox{namespace name $\rightarrow$ namespace class} mapping.

@l
(defmacro defnamespace (class-name (&rest supers) &optional ;
                        namespace-name other-slot-specs)
  `(progn
     (defclass ,class-name ,(or supers '(namespace))
       (,@(when namespace-name
             `((name :initform ',namespace-name :allocation :class)))
        ,@other-slot-specs))
     ,@(when namespace-name
         `((setf (find-namespace-class ',namespace-name) ;
                 (find-class ',class-name))))))

@<Define namespace classes@>

@ And here are the basic namespace definitions themselves. We've put them
in a named section so that we can add to the list later and not have to
worry about forward references.

@<Define namespace classes@>=
(defnamespace variable-name () :variable)
(defnamespace lexical-variable-name (variable-name) :lexical)
(defnamespace special-variable-name (variable-name) :special)
(defnamespace constant-name () :constant)
(defnamespace symbol-macro-name () :symbol-macro)

(defnamespace operator () :operator)
(defnamespace function-name (operator) :function)
(defnamespace setf-function-name (function-name) :setf-function)
(defnamespace macro-name (operator) :macro)
(defnamespace compiler-macro-name (operator) :compiler-macro)
(defnamespace special-operator (operator) :special-form)

(defnamespace block-name () :block)
(defnamespace tag-name () :tag)
(defnamespace catch-tag () :catch-tag)
(defnamespace type-name () :type)

@ |class-name| is a symbol in the \.{COMMON-LISP} package, so we can't
use it for the name of a class.

@<Define namespace...@>=
(defnamespace class-name% () :class)
(defnamespace condition-class-name (class-name%) :condition-class)

@ We'll use two additional namespaces for macros and symbol macros, because
when we add those to the lexical environments, we'll need to supply the
definitions as well. Using seperate namespace classes makes the bookkeeping
slightly simpler.

@<Define namespace...@>=
(defnamespace symbol-macro-definition (symbol-macro-name))
(defnamespace macro-definition (macro-name))

@ The people at Franz just can't seem to resist tweaking the environments
{\sc api}: their version of |function-information| returns |:sepcial-operator|
rather than |:special-form| when the function spec names a special operator.
This may be more precise terminology, but it's an arbitrary and capricious
change. Still, it's easy enough to provide an alias for our namespace class.

@l
(setf (find-namespace-class :special-operator) (find-class 'special-operator))

@ The reason the association between namespace names and environment types
is important is that when we walk a name, we can sometimes only give a best
guess as to the correct namespace. For instance, when we walk an evaluated
symbol, it could be a lexical variable, a special variable, a constant,
or~a symbol macro---we can't know until we look it up in the environment.
But in general, we {\it can't\/} look it up until we've walked it; the best
we can do is say that it's a variable of some kind. Once the walk happens,
we can get more information from the environment, and that's exactly what
we'll do.

The function |update-context| takes a (walked) name, a context instance,
and~an environment object, and returns a new context that reflects the
given context as updated by the appropriate environment entry for that
name. It uses the mapping between namespace names and environment types,
which we'll retrieve using |find-namespace-class|.

@l
(defgeneric update-context (name context env))

(defmethod update-context (name (context walk-context) env)
  (declare (ignore name env))
  context)

(defmethod update-context (name (context variable-name) env)
  (multiple-value-bind (type local) (variable-information name env)
    (if type
        (make-context (find-namespace-class type) :local local)
        context)))

@ For function names, we need to check if the function is a generic function,
then what type it has in the environment. If the name is being bound, it won't
necessarily be in the environment yet, so we'll just return the given context.

However, just because we don't find the name in the environment doesn't
mean it isn't there: neither Allegro nor~CCL correctly support looking~up
a function name of the form `(|setf|~\<symbol>)' in an arbitrary lexical
environment, and SBCL versions prior to~1.0.47.30 signaled an error due
to a type declaration bug (whence the careful error handling). We therefore
special-case the non-atomic-function-name case, which really shouldn't be
necessary.

@l
(deftype setf-function () '(cons (eql setf) (cons symbol null)))

(defmethod update-context (name (context operator) env)
  (multiple-value-bind (type local) ;
      (handler-case (function-information name env)
        (type-error () (values nil nil)))
    (cond ((and (not local) (generic-function-p name))
           (make-context (etypecase name
                           (symbol 'generic-function-name)
                           (setf-function 'generic-setf-function-name))))
          ((or type (not (symbolp name)))
           (make-context (find-namespace-class
                          (etypecase name
                            (symbol type)
                            (setf-function :setf-function)))
                         :local (or local (local-binding-p context))))
          (t context))))

@t@l
(deftest (update-context generic-setf)
  (typep (update-context '(setf class-name) (make-context 'operator) nil)
         'generic-setf-function-name)
  t)

(deftest (update-context macro)
  (let ((context (update-context 'setf (make-context 'operator) nil)))
    (and (typep context 'macro-name)
         (not (local-binding-p context))))
  t)

(deftest (update-context local-macro)
  (let ((context (update-context 'foo
                                 (make-context 'operator)
                                 (augment-environment
                                  (ensure-portable-walking-environment nil)
                                  :macro `((foo ,(lambda (form env)
                                                   (declare (ignore env))
                                                   form)))))))
    (and (typep context 'macro-name)
         (local-binding-p context)))
  t)

(deftest (update-context function)
  (let ((context (update-context 'identity (make-context 'operator) nil)))
    (and (typep context 'function-name)
         (not (local-binding-p context))))
  t)

(deftest (update-context local-function)
  (let ((context (update-context 'foo
                                 (make-context 'operator)
                                 (augment-environment
                                  (ensure-portable-walking-environment nil)
                                  :function '(foo)))))
   (and (typep context 'function-name)
        (local-binding-p context)))
  t)

(deftest (update-context special-operator)
  (let ((context (update-context 'if (make-context 'operator) nil)))
    (and (typep context 'special-operator)
         (not (local-binding-p context))))
  t)

@ Macro definitions have to be handled separately, but they're much simpler
than functions.

@l
(defmethod update-context (name (context macro-definition) env)
  (multiple-value-bind (type local) (function-information (car name) env)
    (if type
        (make-context (find-namespace-class type) :local local)
        context)))

@ Now we come to the walker proper. Code walkers are represented as instances
of the class |walker|. The walker protocol consists of a handful of generic
functions, which we'll describe as we come to them; subclasses of |walker|
may add methods to them to customize the behavior of the walk.

@l
(defclass walker () ())

@<Walker generic functions@>

@ We'll wrap |macroexpand-1| so that walker sub-classes get a chance to
override it.

@l
(defmethod macroexpand-for-walk ((walker walker) form env)
  (macroexpand-1 form env))

@ @<Walker generic functions@>=
(defgeneric macroexpand-for-walk (walker form env))

@ The main entry point for the walker is |walk-form|. The walk ordinarily
stops after encountering an atom or a special form; otherwise, we macro
expand and try again. If a walker method wants to decline to walk, however,
it may throw a form to the tag |continue-walk|, and the walk will continue
with macro expansion of that form.

@l
(defmethod walk-form ((walker walker) form &optional env toplevel &aux
                      (env (ensure-portable-walking-environment env)))
  (let ((expanded t))
    (loop
      (setq form (catch 'continue-walk @<Walk |form|@>))
      (multiple-value-setq (form expanded)
        (macroexpand-for-walk walker form env)))))

@ @<Walker generic functions@>=
(defgeneric walk-form (walker form &optional env toplevel))

@ When we hit an atom that is not a symbol macro, a compound form whose
car is not a macro, or~a special form, we return the walked form and break
out of the macro-expansion loop.

@<Walk |form|@>=
(cond ((atom form)
       @<Walk the atom |form|@>)
      ((not (symbolp (car form)))
       (return (walk-list walker form env toplevel)))
      ((or (not expanded) (walk-as-special-form-p walker (car form) form env))
       (return (walk-compound-form walker (car form) form env ;
                                   :toplevel toplevel)))
      (t form))

@ When we walk an atomic form, we need to check whether or not it's a
symbol macro. If it is, we'll let the walk continue with the expansion;
otherwise, we'll just return the walked atom. But it's important to walk
the atom {\it before\/} checking whether it's a symbol macro because of
the games we play later with referring symbols in the indexer.
@^referring symbols@>

@<Walk the atom...@>=
(typecase form
  (symbol
   (let ((var (walk-name walker form (make-context 'variable-name) env)))
     (if (eql (variable-information var env) :symbol-macro)
         var ; wait for macro expansion
         (return var))))
  (t (return (walk-atomic-form walker form nil env :toplevel toplevel))))

@ The walker will treat a compound form as a special form if and only if
|walk-as-special-form-p| returns true of that form. Besides the walker
instance, the form being walked, and~the current environment, we'll supply
the operator of the compound form as a separate argument so that we can
use |eql|~specializers. The |operator| should generally be |eql|
to~|(car form)|.

@l
(defmethod walk-as-special-form-p (walker operator form env)
  (declare (ignore walker operator form env))
  nil)

@ @<Walker generic functions@>=
(defgeneric walk-as-special-form-p (walker operator form env))

@ Here's a utility function we'll use often in walker methods: it walks
each element of the supplied list and returns a new list of the results
of those walks.

@l
(defun walk-list (walker list env &optional toplevel)
  (do ((form list (cdr form))
       (newform () (cons (walk-form walker (car form) env toplevel)
                         newform)))
      ((atom form) (nreconc newform form))))

@ The functions |walk-atomic-form| and |walk-compound-form| are the real
work-horses of the walker. Besides the walker instance, the form, and~the
current environment, |walk-atomic-form| takes a context instance, and
|walk-compound-form| takes an |operator| argument like
|walk-as-special-form-p|. They both take a |toplevel| keyword argument,
which will be true if the form occurs at top level.

@<Walker generic functions@>=
(defgeneric walk-atomic-form (walker form context env &key toplevel))
(defgeneric walk-compound-form (walker operator form env &key toplevel))

@ The default method for |walk-atomic-form| simply returns the form.

@l
(defmethod walk-atomic-form ((walker walker) form context env &key toplevel)
  (declare (ignore context env toplevel))
  form)

(defmethod walk-atomic-form ((walker walker) (form cons) context env &key ;
                             toplevel)
  (declare (ignore env toplevel))
  (error "Unexpected non-atomic form ~S (~S)" form context))

@t@l
(deftest walk-atomic-form
  (walk-atomic-form (make-instance 'walker) ':foo nil nil)
  :foo)

(deftest walk-non-atomic-form
  (handler-case (walk-atomic-form (make-instance 'walker) '(a b c) nil nil)
    (error () nil))
  nil)

@ This method for |walk-compound-form| is used for most funcall-like forms;
it treats its car as a function name and walks its cdr.

@l
(defmethod walk-compound-form ((walker walker) (operator symbol) form env &key ;
                               toplevel)
  (declare (ignore toplevel))
  `(,(walk-name walker (car form) (make-context 'operator) env)
    ,@(walk-list walker (cdr form) env)))

@t@l
(deftest walk-compound-form
  (walk-compound-form (make-instance 'walker) :foo '(:foo 2 3) nil)
  (:foo 2 3))

@ A compound form might also have a \L~expression as its car.

@l
(deftype lambda-expression () '(cons (eql lambda) (cons list *)))

(defmethod walk-compound-form ((walker walker) (operator cons) form env &key ;
                               toplevel)
  (declare (ignore toplevel))
  (etypecase operator
    (lambda-expression
     `(,(walk-lambda-expression walker operator nil env)
        ,@(walk-list walker (cdr form) env)))))

@t@l
(deftest (walk-compound-form lambda)
  (let ((operator '(lambda (x) x)))
    (walk-compound-form (make-instance 'walker) operator `(,operator 0)
                        (ensure-portable-walking-environment nil)))
  ((lambda (x) x) 0))

(deftest (walk-compound-form invalid)
  (handler-case
      (let ((operator '(x)))
        (walk-compound-form (make-instance 'walker) operator `(,operator 0)
                            (ensure-portable-walking-environment nil)))
    (error () nil))
  nil)

@t These sorts of complex type specifiers are surprisingly easy to get wrong.

@l
(deftest lambda-expression-type
  (flet ((lambda-expression-p (x) (typep x 'lambda-expression)))
    (and (lambda-expression-p '(lambda (x) x))
         (lambda-expression-p '(lambda () t))
         (lambda-expression-p '(lambda ()))
         (not (lambda-expression-p '(lambda x x)))
         (not (lambda-expression-p 'lambda))))
  t)

@ Whenever we can recognize a form as a name---a variable name, a function
name, \etc.---we'll walk it using this function. The |context| argument
describes the namespace in which the name resides.

@ @<Walker generic functions@>=
(defgeneric walk-name (walker name context env &key))

@ The default method just returns the name being walked.

@l
(defmethod walk-name ((walker walker) name context env &key)
  (declare (ignore context env))
  name)

@ Walking a name for the purposes of {\it binding\/} it in some namespace
or the lexical environment is often different, so we'll use another function.
The function |walk-bindings| binds each name in |names| in the given
|namespace| under the optional control of the declarations in |declare|.
It returns two values: the walked names, and a possibly-augmented lexical
environment object.

@<Walker generic functions@>=
(defgeneric walk-bindings (walker names namespace env &key declare))

@ The default method just walks each of the names and returns the original
environment.

@l
(defmethod walk-bindings ((walker walker) names (namespace namespace) ;
                          env &key declare)
  (declare (ignore declare))
  (values (mapcar (lambda (name) (walk-name walker name namespace env)) names)
          env))

@ As a convenience, we'll use this little function when we only want to
walk a single binding.

@l
(defun walk-binding (walker name namespace env &key declare)
  (multiple-value-bind (names env)
      (walk-bindings walker (list name) namespace env :declare declare)
    (values (first names) env)))

@ Many of the special forms defined in Common Lisp can be walked using the
default method for |walk-compound-form| just defined, since their syntax is
the same as an ordinary function call. But it's important to override
|walk-as-special-form-p| for these operators, because ``[a]n
implementation is free to implement a Common Lisp special operator as a
macro'' (\ansi\ Common Lisp, section~3.1.2.1.2.2).
@^\ansi\ Common Lisp@>

@l
(macrolet ((walk-as-special-form (operator)
             `(defmethod walk-as-special-form-p ;
                  ((walker walker) (operator (eql ',operator)) form env)
                (declare (ignore form env))
                t)))
  (walk-as-special-form if)
  (walk-as-special-form load-time-value)
  (walk-as-special-form multiple-value-call)
  (walk-as-special-form multiple-value-prog1)
  (walk-as-special-form progv)
  (walk-as-special-form setq)
  (walk-as-special-form unwind-protect))

@ The rest of the special form walkers we define will need methods
specialized on particular operators for both |walk-as-special-form-p|
and |walk-compound-form|. The following macro makes sure that these are
consistently defined.

@l
(defmacro define-special-form-walker (operator (walker form env &rest rest) ;
                                      &body body)
  (let ((oparg `(,(make-symbol "OPERATOR") (eql ',operator))))
    (flet ((arg-name (arg) (if (consp arg) (car arg) arg)))
      `(progn
         (defmethod walk-as-special-form-p (,walker ,oparg ,form ,env)
           (declare (ignorable ,@(mapcar #'arg-name `(,walker ,form ,env))))
           t)
         (defmethod walk-compound-form (,walker ,oparg ,form ,env ,@rest)
           (declare (ignorable ,@(mapcar #'arg-name `(,walker ,form ,env))))
           ,@body)))))

@t To make writing walker tests easier and more complete, we'll use a walker
subclass that recognizes a few non-standard special forms that are useful for
testing.

@l
(defclass test-walker (walker) ())

@t The simplest special form we'll recognize is |ensure-toplevel|, which
simply asserts that it occurs at top level, or not if an argument of |nil|
is given.

@l
(define-special-form-walker ensure-toplevel ((walker test-walker) form env ;
                                             &key toplevel)
  (destructuring-bind (operator &optional (ensure-toplevel t)) form
    (declare (ignore operator))
    (assert (if ensure-toplevel toplevel (not toplevel))
            (form ensure-toplevel toplevel)
            "~:[At~;Not at~] top level." ensure-toplevel))
  form)

@t@l
(deftest toplevel
  (let ((walker (make-instance 'test-walker))
        (env (ensure-portable-walking-environment nil)))
    (flet ((walk (form toplevel)
             (tree-equal (walk-form walker form env toplevel) form)))
      (values (walk '(ensure-toplevel) t)
              (walk '(ensure-toplevel nil) nil)
              (walk '(let () (ensure-toplevel nil)) t)
              (handler-case (walk '(ensure-toplevel) nil)
                (error () nil))
              (handler-case (walk '(ensure-toplevel nil) t)
                (error () nil))
              (handler-case (walk '(let () (ensure-toplevel)) t)
                (error () nil)))))
  t t t nil nil nil)

@t Most of our walker tests will be defined using the following macro,
which takes a name for the test and a few options, a form to be walked,
and~an optional result. If the result is omitted, it is assumed that the
result of the walk should be the same as the walked form. If it is supplied
and |nil|, the result will not be checked. Neither the form nor the result
is evaluated.

@l
(defmacro define-walker-test (name-and-options form &optional ;
                              (result nil result-supplied))
  (destructuring-bind (name &key (toplevel nil)) (ensure-list name-and-options)
    `(deftest (walk ,name)
       (let* ((form ',form)
              (walker (make-instance 'test-walker))
              (walked-form (walk-form walker form nil ,toplevel)))
         ,(cond (result `(tree-equal walked-form ',result))
                ((not result-supplied) '(tree-equal walked-form form))
                (t t)))
       t)))

@ |progn| is special because it preserves top-levelness.

@l
(define-special-form-walker progn ((walker walker) form env &key toplevel)
  `(,(car form)
    ,@(walk-list walker (cdr form) env toplevel)))

@t@l
(define-walker-test progn
  (progn :foo :bar :baz))

(define-walker-test (progn-toplevel :toplevel t)
  (progn (ensure-toplevel)))

@ Block names have their own namespace class.

@l
(define-special-form-walker block ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-binding walker (cadr form) (make-context 'block-name) env)
    ,@(walk-list walker (cddr form) env)))

(define-special-form-walker return-from ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-name walker (cadr form) (make-context 'block-name) env)
    ,(walk-form walker (caddr form) env)))

@t@l
(define-walker-test block/return-from
  (block :foo (return-from :foo 4)))

@ |go| tags do, too.

@l
(define-special-form-walker tagbody ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,@(loop with tag-context = (make-context 'tag-name)
            for tag/statement in (cdr form)
            collect (typecase tag/statement
                      ((or symbol integer)
                       (walk-name walker tag/statement tag-context env))
                      (t (walk-form walker tag/statement env))))))

(define-special-form-walker go ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-name walker (cadr form) (make-context 'tag-name) env)))

@t@l
(define-walker-test tagbody/go
  (tagbody foo (go foo)))

@ Ditto for catch tags. Catch tags are evaluated, though, and it's the
result that is used as the name, so we'll use a |walk-name| method that
actually walks the form. Since catch tags are dynamic, and thus not stored
in the lexical environment, we won't use |walk-bindings|, but we will
pass a keyword argument to |walk-name| so that specialized methods can
discriminate between the establishment of a catch tag and a throw to one.

@l
(defmethod walk-name ((walker walker) name (context catch-tag) env &key catch)
  (declare (ignore catch))
  (walk-form walker name env))

(define-special-form-walker catch ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-name walker (cadr form) (make-context 'catch-tag) env :catch t)
    ,@(walk-list walker (cddr form) env)))

(define-special-form-walker throw ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-name walker (cadr form) (make-context 'catch-tag) env)
    ,(walk-form walker (caddr form) env)))

@t@l
(define-walker-test catch/throw
  (catch 'foo (throw 'foo :foo)))

@ The special form |the| takes a type specifier and a form. We won't even
bother walking the type specifier. SBCL has a similar but non-standard
|truly-the| special form that it unfortunately doesn't provide a macro
definition for; we'll support that, too.
@^SBCL@>

@l
(defun walk-the (walker form env)
  `(,(car form)
    ,(cadr form)
    ,(walk-form walker (caddr form) env)))

(macrolet ((define-the-walker (operator)
             `(define-special-form-walker ,operator ;
                  ((walker walker) form env &key toplevel)
                (declare (ignore toplevel))
                (walk-the walker form env))))
  (define-the-walker the)
  #+sbcl (define-the-walker sb-ext:truly-the))

@t@l
(define-walker-test the
  (the (or number nil) (sqrt 4)))

@ The |quote| special operator just returns its argument.

@l
(define-special-form-walker quote ((walker walker) form env &key toplevel)
  (declare (ignore env toplevel))
  form)

@t@l
(define-walker-test quote-1 'foo)
(define-walker-test quote-2 '(1 2 3))

@ We'll pretend to be a compiler for the purposes of walking, and
evaluate top level forms that appear in an |eval-when| with situation
|:compile-toplevel|.

@l
(define-special-form-walker eval-when ;
    ((walker walker) form env &key toplevel &aux
     (eval (and toplevel
                (or (member :compile-toplevel (cadr form))
                    (member 'compile (cadr form))))))
  `(,(car form)
    ,(cadr form)
    ,@(loop for form in (cddr form)
            as walked-form = (walk-form walker form env toplevel)
            when eval do (eval walked-form)
            collect walked-form)))

@t@l
(define-walker-test (eval-when-non-toplevel :toplevel nil)
  (eval-when (:compile-toplevel :load-toplevel :execute)
    (error "Oops; this shouldn't have been evaluated.")))

(deftest (walk eval-when-toplevel)
  (let* ((string-output-stream (make-string-output-stream))
         (*standard-output* string-output-stream)
         (walker (make-instance 'test-walker))
         (form '(eval-when (:compile-toplevel)
                  (princ :foo))))
    (and (tree-equal (walk-form walker form nil t) form)
         (get-output-stream-string string-output-stream)))
  "FOO")

@ Allegro's definition of |defconstant| is somewhat funky. Aside from the
expected `special' declamation, the expansion includes calls to two functions:
|defconstant1| and |defconstant2| (both in the \.{EXCL} package). Only the
first is wrapped in an |(eval-when (compile))|, but it's the second that
actually sets the value. The net effect is that if we walk a |defconstant|
form in the usual way, the constant gets declaimed special, but remains
unbound, which can cause problems.
@^Allegro Common Lisp@>

The work-around is simple: we treat |defconstant| as a special form, and
wrap the expanded form in an |(eval-when (:compile-toplevel))|. This can't
hurt, because the standard says that ``[a]n implementation may choose to
evaluate the value-form [of a top level |defconstant| form] at compile time,
load time, or~both.''

@l
(define-special-form-walker defconstant ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (throw 'continue-walk
    `(eval-when (:compile-toplevel)
       ,(macroexpand-for-walk walker form env))))

@t@l
(deftest (walk defconstant)
  (let ((name (make-symbol "TWO-PI"))
        (walker (make-instance 'walker)))
    (and (walk-form walker `(defconstant ,name (* 2 pi)) nil t)
         (symbol-value name)))
  #.(* 2 pi))

@ The |function| special form takes either a valid function name or a
\L~expression. Under SBCL, this is extended to also include their non-standard
|named-lambda| special forms, which we'll come to shortly.
@^SBCL@>

@l
(deftype named-lambda-expression () ;
  '(cons (eql #+sbcl sb-int:named-lambda #-sbcl named-lambda)))

(define-special-form-walker function ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(typecase (cadr form)
       (lambda-expression (walk-lambda-expression walker (cadr form) nil env))
       (named-lambda-expression (walk-form walker (cadr form) env))
       (t (walk-name walker (cadr form) (make-context 'function-name) env)))))

@t@l
(define-walker-test function
  (function foo))

(define-walker-test function-setf-function
  (function (setf foo)))

(define-walker-test function-lambda
  (function (lambda (x) x)))

@ Next, we'll work our way up to parsing \L~expressions and other
function-defining forms.

Given a sequence of declarations and possibly a documentation string
followed by other forms (as occurs in the bodies of |defun|, |defmacro|,
\etc.), |parse-body| returns |(values forms decls doc)|, where |decls|
is the declaration specifiers found in each |declare| expression, |doc|
holds a doc string (or |nil| if there is none), and |forms| holds the
other forms. See \ansi\ Common Lisp section~3.4.11 for the rules on
the syntactic interaction of doc strings and declarations.
@^\ansi\ Common Lisp@>

If |doc-string-allowed| is false (the default), then no forms will be
treated as documentation strings.

@l
(defun parse-body (body &key doc-string-allowed walker env &aux doc)
  (flet ((doc-string-p (x rest)
           (and (stringp x) doc-string-allowed rest (null doc)))
         (declarationp (x)
           (and (listp x) (eql (car x) 'declare))))
    (loop for forms = body then (cdr forms)
          as x = (car forms)
          while forms
          if (doc-string-p x (cdr forms)) do (setq doc x)
          else if (declarationp x) append (cdr x) into decls
               else do (loop-finish)
          finally (return (values forms
                                  (if walker
                                      (walk-declaration-specifiers ;
                                       walker decls env)
                                      decls)
                                  doc)))))

@t@l
(deftest (parse-body 1)
  (parse-body '("doc" (declare (optimize speed)) :foo :bar)
              :doc-string-allowed t)
  (:foo :bar)
  ((optimize speed))
  "doc")

(deftest (parse-body 2)
  (parse-body '((declare (optimize speed))
                "doc"
                (declare (optimize space))
                :foo :bar)
              :doc-string-allowed t)
  (:foo :bar)
  ((optimize speed) (optimize space))
  "doc")

(deftest (parse-body 3)
  (parse-body '("doc" "string") :doc-string-allowed t)
  ("string")
  nil
  "doc")

(deftest (parse-body 4)
  (parse-body '((declare (optimize debug)) "string") :doc-string-allowed t)
  ("string")
  ((optimize debug))
  nil)

(deftest (parse-body 5)
  (parse-body '((declare (optimize debug)) "string") :doc-string-allowed nil)
  ("string")
  ((optimize debug))
  nil)

@ Because of the shorthand notation for type declarations, walking general
declaration expressions is difficult. However, we don't care about type
declarations, since they're not allowed to affect program semantics. We
therefore just throw out everything except `special', `optimize', `ignore',
and~`ignorable' declarations. Optimize declarations are preserved only
because CCL's macro-expansion machinery uses blatantly unsafe code, and
depends on local declarations to lower the safety level. Ignore(able)
declarations are preserved primarily to keep SBCL from complaining about
unused variables in macro functions.
@^Clozure Common Lisp@>
@^SBCL@>

@l
(defun walk-declaration-specifiers (walker decls env)
  (loop for decl in decls
        when (walk-declaration-specifier walker decl env) collect it))

(defmethod walk-declaration-specifier ((walker walker) decl-spec env)
  (destructuring-bind (identifier . data) decl-spec
    (case identifier
      (special @<Walk the `special' declarations...@>)
      ((ignore ignorable) @<Walk the `ignore' or `ignorable' declarations...@>)
      (optimize `(optimize ,@data)))))

@ @<Walk the `special' declarations in |data|@>=
(flet ((walk-var (var)
         (walk-name walker var (make-context 'special-variable-name) env)))
  `(special ,@(mapcar #'walk-var data)))

@ @<Walk the `ignore' or `ignorable' declarations in |data|@>=
(flet ((walk-var/fn (name)
         (etypecase name
           (symbol (walk-name walker name (make-context 'variable-name) env))
           ((cons (eql function)) `(function
                                    ,(walk-name walker (cadr name) ;
                                                (make-context 'function-name) ;
                                                env))))))
  `(,identifier ,@(mapcar #'walk-var/fn data)))

@t @l
(deftest walk-declaration-specifiers
  (equal (walk-declaration-specifiers (make-instance 'walker)
                                      '((type foo x)
                                        (special x y)
                                        (ignore z)
                                        (ignorable (function f))
                                        (optimize (speed 3) (safety 0)))
                                      nil)
         '((special x y)
           (ignore z)
           (ignorable (function f))
           (optimize (speed 3) (safety 0))))
  t)

@ @<Walker generic functions@>=
(defgeneric walk-declaration-specifier (walker decl-spec env))

@ Before we dive into \L-lists, let's define our variable-binding walker.
We'll return the list of names and an environment augmented with the new
bindings.

@l
(defmethod walk-bindings ((walker walker) names (namespace variable-name) ;
                          env &key declare)
  (let ((decls (nconc @<Find declarations...@>
                      (list @<Construct a declaration spec...@>))))
    (values names (augment-environment env :variable names :declare decls))))

@ SBCL's environment handling is extremely picky, and signals warnings
about declarations for variables it doesn't know about. To shut it up,
we'll supply only declarations that apply to the variable names currently
being added to the environment.
@^SBCL@>

@<Find declarations in |declare| that apply to variables in |names|@>=
(mapcan (lambda (decl)
          (and (member (car decl) '(ignore ignorable special))
               (let ((vars (intersection (cdr decl) names)))
                 (and vars (list `(,(car decl) ,@vars))))))
        declare)

@ Lexical bindings in Common Lisp shadow special bindings, {\it unless\/}
the special declaration is global. However, on all of the implmentations
tested so far, |augment-environment| {\it always\/} interprets bindings as
lexical unless a |special| declaration is provided, regardless of whether
the binding has been proclaimed special in the global environment. This
seems to just be a pervasive bug: the specification for |augment-environment|
says that ``[w]hether each [variable] binding is to be interpreted as
special or lexical depends on |special| declarations recorded in the
environment or provided in the |:declare| argument'' (\cltl, p.~212).
@^\cltl@>

We can work around this by checking if a variable was proclaimed special in
the global environment, and adding a |special| declaration for the new
binding if so. We need to special-case symbols in the \.{COMMON-LISP}
package, because it is an error for a conforming program to declare
bindings of such variables |special|. Moreover, SBCL has the notion of a
`package lock' that applies not only to the \.{COMMON-LISP} package, but to
several other implementation-specific packages as well. Symbols in locked
packages include the same prohibition on |special| declarations, so we'll
omit them from our new declaration as well.
@^SBCL@>

@<Construct a declaration specifier for special variables in |names|@>=
`(special ;
  ,@(remove-if-not (lambda (name)
                     (and (eq (variable-information name nil) :special)
                          #+sbcl
                          (not (sb-ext:package-locked-p (symbol-package name)))
                          (not (eq (symbol-package name) ;
                                   (find-package "COMMON-LISP")))))
                   names))

@t@l
(defvar *foo* nil "A global special variable.")

(deftest walk-bindings
  (let ((names '(*foo* bar baz))
        (walker (make-instance 'walker))
        (context (make-context 'variable-name))
        (env (ensure-portable-walking-environment nil)))
    (multiple-value-bind (walked-names new-env)
        (walk-bindings walker names context env :declare '((special bar)))
      (and (equal walked-names names)
           (equal (mapcar (lambda (var) ;
                            (variable-information var new-env)) ;
                          names)
                  '(:special :special :lexical)))))
  t)

@ The syntax of \L-lists is given in section~3.4 of the \ansi\ standard.
We accept the syntax of macro \L-lists, since they are the most general,
and appear to be a superset of every other type of \L-list.
@^\ansi\ Common Lisp@>

This function returns two values: the walked \L-list and a new environment
object containing bindings for all of the parameters found therein.

@l
(defun walk-lambda-list (walker lambda-list decls env)
  (let ((new-lambda-list '())
        (state :reqvars))
    (labels ((walk-var (var)
               (multiple-value-setq (var env)
                 (walk-binding walker var ;
                               (make-context 'variable-name :local t) ;
                               env ;
                               :declare decls)))
             (update-state (keyword)
               (setq state (case keyword
                             (&optional :optvars)
                             ((&rest &body) :restvars)
                             (&key :keyvars)
                             (&aux :auxvars)
                             (&environment :envvar)
                             (t state))))
             (maybe-destructure (var/pattern)
               (if (consp var/pattern)
                   (multiple-value-setq (var/pattern env)
                     (walk-lambda-list walker var/pattern decls env))
                   (walk-var var/pattern))))
      @<Check for |&whole| and |&environment| vars...@>
      (do* ((lambda-list lambda-list (cdr lambda-list))
            (arg (car lambda-list) (if (consp lambda-list) ;
                                       (car lambda-list) ;
                                       lambda-list)))
           ((atom lambda-list)
            (values (nreconc new-lambda-list (and arg (walk-var arg))) env))
        (ecase state
          (:envvar @<Process |arg| as an environment parameter@>)
          ((:reqvars :restvars) @<Process |arg| as a required parameter@>)
          (:optvars @<Process |arg| as an optional parameter@>)
          (:keyvars @<Process |arg| as a keyword parameter@>)
          (:auxvars @<Process |arg| as an auxiliary variable@>))))))

@ A |&whole| variable must come first in a \L-list, and an |&environment|
variable, although it may appear anywhere in the list, must be bound along
with |&whole|. We'll pop a |&whole| variable off the front of |lambda-list|,
but we'll leave any |&environment| variable to be picked up later.

@<Check for |&whole| and |&environment| vars and augment the
  environment if found@>=
(and (consp lambda-list)
     (eql (car lambda-list) '&whole)
     (push (pop lambda-list) new-lambda-list)
     (car (push (walk-var (pop lambda-list)) new-lambda-list)))
(do ((lambda-list lambda-list (cdr lambda-list)))
    ((atom lambda-list) nil)
  (when (eql (car lambda-list) '&environment)
    (return (cadr lambda-list))))

@ We've already added the environment variable to our lexical environment,
so we just push it onto the new \L-list and prepare for the next parameter.

@<Process |arg| as an environment parameter@>=
(push (walk-var arg) new-lambda-list)
(when (consp lambda-list)
  (update-state (car lambda-list)))

@ Required parameters may be either symbols or patterns. Rest parameters
have the same syntax.

@<Process |arg| as a required parameter@>=
(etypecase arg
  (symbol @<Process the symbol in |arg| as a parameter@>)
  (cons
   (multiple-value-bind (pattern new-env) ;
       (walk-lambda-list walker arg decls env)
     (setq env new-env)
     (push pattern new-lambda-list))))

@ Watch the order here: in the non-simple-|var| case, both the init
form and the pattern (if any) need to be walked in an environment
{\it unaugmented\/} with any supplied-p-parameter.

@<Process |arg| as an optional parameter@>=
(etypecase arg
  (symbol @<Process the symbol...@>)
  (cons
   (destructuring-bind (var/pattern &optional
                        (init-form nil init-form-supplied)
                        (supplied-p-parameter nil spp-supplied))
       arg
     (when init-form-supplied
       (setq init-form (walk-form walker init-form env)))
     (push (nconc (list (maybe-destructure var/pattern))
                  (and init-form-supplied (list init-form))
                  (and spp-supplied (list (walk-var supplied-p-parameter))))
           new-lambda-list))))

@ @<Process |arg| as a keyword parameter@>=
(etypecase arg
  (symbol @<Process the symbol in |arg| as a parameter@>)
  (cons
   (destructuring-bind (var/kv &optional
                        (init-form nil init-form-supplied)
                        (supplied-p-parameter nil spp-supplied))
       arg
     (when init-form-supplied
       (setq init-form (walk-form walker init-form env)))
     (cond ((consp var/kv)
            (destructuring-bind (keyword-name var/pattern) var/kv
              (setq var/pattern (maybe-destructure var/pattern))
              (setq var/kv (list (walk-atomic-form walker keyword-name ;
                                                   nil env)
                                 var/pattern))))
           (t (setq var/kv (walk-var var/kv))))
     (push (nconc (list var/kv)
                  (and init-form-supplied (list init-form))
                  (and spp-supplied (list (walk-var supplied-p-parameter))))
           new-lambda-list))))

@ @<Process |arg| as an auxiliary variable@>=
(etypecase arg
  (symbol @<Process the symbol...@>)
  (cons
   (destructuring-bind (var &optional init-form) arg
     (setq var (walk-var var)
           init-form (and init-form (walk-form walker init-form env)))
     (push (nconc (list var)
                  (and init-form (list init-form)))
           new-lambda-list))))

@ @<Process the symbol in |arg| as a parameter@>=
(cond ((member arg lambda-list-keywords)
       (push arg new-lambda-list)
       (update-state arg))
      (t (setq arg (walk-var arg))
         (push arg new-lambda-list)))

@ While we're in the mood to deal with \L-lists, here's a routine that can
walk the `specialized' \L-lists used in |defmethod| forms. We can't use the
same function as the one used to parse macro \L-lists, since the syntax
would be ambiguous: there would be no way to distinguish between a
specialized required parameter and a destructuring pattern. What we can do,
however, is peel off just the required parameters from a specialized
\L-list, and feed the rest to |walk-lambda-list|.

This function returns the same kind of values as |walk-lambda-list|;
viz., the walked specialized \L-list and an environment augmented with
the parameters found therein.

@l
(deftype class-specializer () '(cons symbol (cons symbol null)))
(deftype compound-specializer (&optional (operator 'eql))
  `(cons symbol (cons (cons (eql ,operator) *) null)))

(defun walk-specialized-lambda-list (walker lambda-list decls env)
  (let ((req-params @<Extract the required parameters from |lambda-list|@>))
    (multiple-value-bind (other-params env) ;
        (walk-lambda-list walker lambda-list decls env)
      (values (nconc req-params other-params) env))))

@ @<Extract the required...@>=
(flet ((walk-var (spec &aux (context (make-context 'variable-name :local t)))
         (flet ((walk-binding (x &aux name)
                  (declare (ignorable name)) ; Allegro thinks this is ignored
                  (multiple-value-setq (name env)
                    (walk-binding walker x context env :declare decls))))
           (etypecase spec
             (symbol (walk-binding spec))
             (class-specializer
              (list (walk-binding (car spec))
                    (walk-name walker (cadr spec) ;
                               (make-context 'class-name%) env)))
             ((compound-specializer eql)
              (list (walk-binding (car spec))
                    `(eql ,(walk-form walker (cadadr spec)))))))))
  (loop until (or (null lambda-list)
                  (member (car lambda-list) lambda-list-keywords))
        collect (walk-var (pop lambda-list))))

@ Having built up the necessary machinery, walking a \L~expression is now
straightforward. The slight generality of possibly walking the car of the
form using |walk-name| is because this function will also be used to walk
the bindings in |flet|, |macrolet|, and~|labels| special forms.

@l
(defun walk-lambda-expression (walker form context env)
  (let ((lambda-list (cadr form))
        (body (cddr form)))
    (multiple-value-bind (forms decls doc) ;
        (parse-body body :walker walker :env env :doc-string-allowed t)
      (multiple-value-bind (lambda-list env) ;
          (walk-lambda-list walker lambda-list decls env)
        `(,(let ((name (car form)))
             (case name
               (lambda name)
               (t (walk-name walker (car form) context env))))
          ,lambda-list
          ,@(when doc `(,doc))
          ,@(when decls `((declare ,@decls)))
          ,@(walk-list walker forms env))))))

@ `|lambda|' is not a special operator in Common Lisp, but we'll treat
\L~expressions as special forms.

@l
(define-special-form-walker lambda ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-lambda-expression walker form nil env))

@ We'll also support a `named lambda'. Several Lisp implementations use
such forms internally, but SBCL unfortunately does not provide a portable
macro defintion. (This is just rude; Allegro has a similar |named-function|
special operator, but they provide a macro definition that expands into
a regular |lambda|.) The syntax is assumed to be
`(|named-lambda| \<name> \<lambda-list> \<body>)'.
@^SBCL@>

@l
(define-special-form-walker #+sbcl sb-int:named-lambda #-sbcl named-lambda
    ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-lambda-expression walker ;
                          `(lambda ,(caddr form) ,@(cdddr form)) nil env))

@t To test the walker on binding forms, including \L~expressions, we'll
define a new special form for our test walker, |check-binding|, which
checks that a list of symbols have the right kind of binding in the
current lexical environment. Its syntax is `(|check-binding| \<symbols>
\<namespace> \<type>)', where \<symbols> is an unevaluated designator
for a list of symbols, \<namespace> is one of |:function| or~|:variable|,
and~\<type> is the type of binding expected for each of the given
symbols (e.g., |:lexical|, |:special|, |:function|). If any of the
symbols have the incorrect type of binding, it signals an error.

@l
(define-special-form-walker check-binding ((walker test-walker) form env &key ;
                                           toplevel)
  (declare (ignore toplevel))
  (flet ((check-binding (name namespace expected-type local &aux ;
                         (env (and local env)))
           (let ((actual-type
                  (ecase namespace
                    (:function (function-information name env))
                    (:variable (variable-information name env)))))
             (assert (eql actual-type expected-type)
                     (name namespace local)
                     "~:[Global~;Local~] ~(~A~) binding of ~S type ~S, not ~S."
                     local namespace name actual-type expected-type))))
    (destructuring-bind (symbols namespace type &optional (local t)) (cdr form)
      (loop with symbols = (ensure-list symbols)
            for symbol in symbols
            do (check-binding symbol namespace type local))
      form)))

@t@l
(define-walker-test ordinary-lambda-list
  (lambda (x y &optional
           (o (+ (check-binding o :variable nil)
                 (check-binding x :variable :special)
                 (check-binding y :variable :lexical)))
           (p nil p-supplied-p) &rest args &key
           ((secret k) 1 k-s-p)
           (k2 (check-binding k-s-p :variable :lexical))
           k3 &allow-other-keys &aux
           w (z (if k-s-p o x)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding (y z o k k-s-p k2 k3 args w z) :variable :lexical)
    (check-binding secret :variable nil)))

(define-walker-test macro-lambda-list
  (lambda (&whole w (x y)
           &optional ((o) (+ x y))
           &key ((:k (k1 k2)) (2 3) k-s-p)
           &environment env . body)
    (check-binding (w x y o k1 k2 k-s-p env body) :variable :lexical)))

@ We come now to the binding special forms. The six lexical binding
forms in Common Lisp (|let|, |let*|, |flet|, |labels|, |macrolet|,
and~|symbol-macrolet|) all have essentially the same syntax; only the
scope and namespace of the bindings differ.

@ |let|, |flet|, |macrolet|, and~|symbol-macrolet| are all `parallel' binding
forms: they walk their bindings in an unaugmented environment, then execute
their body forms in an environment that contains all of the new bindings.

@l
(define-special-form-walker let ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let* ((bindings (mapcar #'ensure-list (cadr form)))
           (init-forms (mapcar (lambda (form) (walk-form walker form env))
                               (mapcar #'cadr bindings))))
      (multiple-value-bind (vars env)
          (walk-bindings walker
                         (mapcar #'car bindings)
                         (make-context 'variable-name :local t)
                         env
                         :declare decls)
        `(,(car form)
          ,(mapcar #'list vars init-forms)
          ,@(when decls `((declare ,@decls)))
          ,@(walk-list walker forms env))))))

@t@l
(define-walker-test let
  (let ((x 1)
        (y (check-binding x :variable nil)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding y :variable :lexical)))

@ We need a |walk-bindings| method for local function bindings; this will
be used for |labels| as well. Notice that we don't currently preserve any
declarations that can affect function bindings, so we simply ignore any
supplied declarations.

@l
(defmethod walk-bindings ((walker walker) names (namespace function-name) ;
                          env &key declare)
  (declare (ignore declare))
  (values names
          (augment-environment env :function names)))

@ @l
(define-special-form-walker flet ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let* ((bindings (cadr form))
           (context (make-context 'function-name :local t))
           (fns (mapcar (lambda (fn) ;
                          (walk-lambda-expression walker fn context env))
                        bindings)))
      (multiple-value-bind (function-names env)
          (walk-bindings walker
                         (mapcar #'car bindings)
                         context
                         env
                         :declare decls)
        `(,(car form)
          ,(mapcar #'cons function-names (mapcar #'cdr fns))
          ,@(when decls `((declare ,@decls)))
          ,@(walk-list walker forms (if decls
                                        (augment-environment env :declare decls)
                                        env)))))))

@t As of SBCL version 1.0.47, we get a style warning about the `ignore'
declaration for the function |bar|. This appears to be a bug in SBCL, not
in our declaration or environment handling; simply evaluating the form
|(augment-environment (augment-environment nil :function '(foo))
                      :declare '((ignore (function foo))))|
produces the same kind of warning.

@l
(define-walker-test flet
  (flet ((foo (x) (check-binding x :variable :lexical))
         (bar (y) y))
    (declare (special x)
             (ignore (function bar)))
    (check-binding x :variable :special)
    (check-binding foo :function :function)))

@ The bindings established by |macrolet| and |symbol-macrolet| are
different from those established by the other binding forms in that they
include definitions as well as names. We need to build the expander functions
using |parse-macro| and |enclose| before we add them to the environment.

@l
(defmethod walk-bindings ((walker walker) defs (namespace macro-definition) ;
                          env &key declare)
  (let* ((fns (mapcar (lambda (exp) ;
                        (walk-lambda-expression walker exp nil env))
                      defs))
         (defs (mapcar (lambda (def)
                         (destructuring-bind (name lambda-list &rest body) def
                           (list name
                                 (enclose (parse-macro name lambda-list ;
                                                       body env) ;
                                          env walker))))
                       fns)))
    (values fns (augment-environment env :macro defs :declare declare))))

@ Note that |macrolet| preserves top-levelness of its body forms.

@l
(define-special-form-walker macrolet ((walker walker) form env &key toplevel)
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let ((bindings (cadr form)))
      (multiple-value-bind (defs env)
          (walk-bindings walker bindings
                         (make-context 'macro-definition :local t)
                         env
                         :declare decls)
        `(,(car form)
          ,defs
          ,@(when decls `((declare ,@decls)))
          ,@(walk-list walker forms env toplevel))))))

@t@l
(define-walker-test (macrolet :toplevel t)
  (macrolet ((foo (x) (check-binding x :variable :lexical)))
    (check-binding foo :function :macro)
    (ensure-toplevel)))

@ Walking |symbol-macrolet| is simpler, since the definitions are given in
the bindings themselves. The body forms of a top level |macrolet| form are
also considered top level.

@l
(defmethod walk-bindings ((walker walker) defs ;
                          (namespace symbol-macro-definition) ;
                          env &key declare)
  (values (setq defs (mapcar (lambda (p)
                               `(,(car p)
                                 ,(walk-form walker (cadr p) env)))
                             defs))
          (augment-environment env :symbol-macro defs :declare declare)))

(define-special-form-walker symbol-macrolet ((walker walker) form env &key ;
                                             toplevel)
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let ((bindings (cadr form)))
      (multiple-value-bind (defs env)
          (walk-bindings walker bindings
                         (make-context 'symbol-macro-definition :local t)
                         env
                         :declare decls)
        `(,(car form)
          ,defs
          ,@(when decls `((declare ,@decls)))
          ,@(walk-list walker forms env toplevel))))))

@t@l
(define-walker-test (symbol-macrolet :toplevel t)
  (symbol-macrolet ((foo :foo)
                    (bar :bar))
    (check-binding (foo bar) :variable :symbol-macro)
    (ensure-toplevel)
    foo bar)
  (symbol-macrolet ((foo :foo)
                    (bar :bar))
    (check-binding (foo bar) :variable :symbol-macro)
    (ensure-toplevel)
    :foo :bar))

@ The two outliers are |let*|, which augments its environment sequentially,
and |labels|, which does so before walking any of its bindings.

@l
(define-special-form-walker let* ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let ((context (make-context 'variable-name :local t)))
      `(,(car form)
        ,(mapcar (lambda (p &aux (p (ensure-list p)))
                   (let ((var (car p))
                         (init-form (walk-form walker (cadr p) env)))
                     (multiple-value-setq (var env)
                       (walk-binding walker var context env :declare decls))
                     (list var init-form)))
                 (cadr form))
        ,@(when decls `((declare ,@decls)))
        ,@(walk-list walker forms env)))))

@t@l
(define-walker-test let*
  (let* ((x 1)
         (y (check-binding x :variable :special)))
    (declare (special x))
    (check-binding y :variable :lexical)))

@ @l
(define-special-form-walker labels ((walker walker) form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (forms decls) ;
      (parse-body (cddr form) :walker walker :env env)
    (let* ((context (make-context 'function-name :local t))
           (bindings (cadr form))
           (function-names '()))
      (dolist (binding bindings (setf function-names (nreverse function-names)))
        (multiple-value-bind (function-name new-env)
            (walk-binding walker (car binding) context env :declare decls)
          (push function-name function-names)
          (setq env new-env)))
      `(,(car form)
        ,(mapcar (lambda (p) ;
                   (walk-lambda-expression walker p context env))
                 (mapcar #'cons function-names (mapcar #'cdr bindings)))
        ,@(when decls `((declare ,@decls)))
        ,@(walk-list walker forms (if decls
                                      (augment-environment env :declare decls)
                                      env))))))

@t@l
(define-walker-test labels
  (labels ((foo (x) (check-binding x :variable :lexical))
           (bar (y) (check-binding foo :function :function)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding foo :function :function)))

@ The last special form we need a specialized walker for is |locally|,
which simply executes its body in a lexical environment augmented by a
set of declarations. Note that |locally| preserves top-levelness of its
body forms.

@l
(define-special-form-walker locally ((walker walker) form env &key toplevel)
  (multiple-value-bind (forms decls) ;
      (parse-body (cdr form) :walker walker :env env)
    `(,(car form)
      ,@(when decls `((declare ,@decls)))
      ,@(walk-list walker forms ;
                   (augment-environment env :declare decls) ;
                   toplevel))))

@t@l
(define-walker-test (locally :toplevel t)
  (locally ()
    (ensure-toplevel)
    (let ((y t))
      (check-binding y :variable :lexical)
      (locally (declare (special y))
        (ensure-toplevel nil)
        (check-binding y :variable :special)))))

@ In order to recognize global proclamations, we'll treat |declaim| as a
special form.

@l
(define-special-form-walker declaim ((walker walker) form env &key toplevel)
  `(,(car form)
    ,@(let ((decls (walk-declaration-specifiers walker (cdr form) env)))
        (when toplevel
          (mapcar #'proclaim decls))
        decls)))

@t@l
(define-walker-test (declaim :toplevel t)
  (progn
    (declaim (special *foo*))
    (check-binding *foo* :variable :special nil)))

@t We don't do anything special with |define-symbol-macro|, but it should
expand into an `(|eval-when| (|:compile-toplevel|) ...)' form that will
let us pick up the definition. We need to write this test out long-hand
because we'll use a gensym for the symbol macro name to avoid cluttering
the global environment.

@l
(deftest (walk define-symbol-macro)
  (let ((walker (make-instance 'test-walker))
        (name (gensym)))
    (not (null (walk-form walker
                          `(progn
                             (define-symbol-macro ,name (ensure-toplevel))
                             (check-binding ,name :variable :symbol-macro nil))
                          nil t))))
  t)

@t Here's a simple walker mix-in class that allows easy tracing of a walk.
It's only here for debugging purposes; it's not a superclass of any of
the walker classes defined in this program.

@l
(defclass tracing-walker (walker) ())

(defmethod walk-atomic-form :before ;
    ((walker tracing-walker) form context env &key toplevel)
  (declare (ignore env))
  (format *trace-output*
          "~&~@<; ~@;walking~:[~; toplevel~] atomic form ~S ~S~:>~%"
          toplevel form context))

(defmethod walk-compound-form :before ;
    ((walker tracing-walker) operator form env &key toplevel)
  (declare (ignore operator env))
  (format *trace-output*
          "~&~@<; ~@;walking~:[~; toplevel~] compound form ~W~:>~%"
          toplevel form))

(defmethod walk-name :before ;
    ((walker tracing-walker) name context env &rest args)
  (declare (ignore env))
  (format *trace-output*
          "~&~@<; ~@;walking name ~S ~S~@[~S~]~:>~%" name context args))

(defmethod walk-bindings :before ;
    ((walker tracing-walker) names context env &key declare)
  (declare (ignore env declare))
  (format *trace-output*
          "~&~@<; ~@;walking bindings ~S ~S~:>~%" names context))

@*Indexing. Formally, an {\it index\/} is an ordered collection of
{\it entries}, each of which is a (\<heading>, \<locator>) pair:
the {\it locator\/} indicates where the object denoted by the
{\it heading\/} may be found. A list of entries with the same heading
is called an {\it entry list}, or sometimes just an {\it entry\/};
the latter is an abuse of terminology, but useful and usually clear
in context.

In this program, our main job in indexing is to automatically produce
entries whose headings are names (symbols, generally) together with the
namespace in which the name is bound, and whose locators are the sections
in which that binding is defined or used. E.g., given a definition of a
function named |foo| in some section $m$ and a use of that function in
section $n$, we'd like to produce an entry list like `|foo|~function:
$\underline{m}, n$'. If there were also a class named |foo|, that would
have a separate entry.

The basic idea is to use a specialized walker class to perform a code walk
of all the code parts in a web, and to build the index as we go. Because
the code walker knows about all of the standard namespaces and how the
various special forms introduce new bindings, we can use the context it
provides during a walk to construct our headings. We'll have to use a
trick to get the locations right, but we'll come to that in a bit.

@ Of course, we don't want to index {\it all\/} of the symbols in a web:
nobody really cares about all of the uses of |let|, for instance---or
indeed any (or at least most) of the symbols in the \.{COMMON-LISP}
package. Instead, we'll have the notion of an {\it interesting\/} symbol;
if a symbol is interesting, we'll index it, and if not, then we won't.

By default, we'll say a symbol is interesting if its home package in one
of the packages listed in |*index-packages*|. By adding methods to the
{\sc gf} |interesting-symbol-p|, the user can extend this notion in
essentially arbitrary ways.

@l
(defgeneric interesting-symbol-p (object))
(defmethod interesting-symbol-p (object)
  (declare (ignore object)))
(defmethod interesting-symbol-p ((object symbol))
  (member (symbol-package object) *index-packages*))

@ @<Global variables@>=
(defvar *index-packages* nil
  "The list of packages whose symbols should be indexed.")

@ @<Initialize global...@>=
(setq *index-packages* nil)

@ The user can add packages to the |*index-packages*| list using the
\.{@@x} control code, which calls the following function.

@l
(defun index-package (packages &aux (packages (ensure-list packages)))
  "Inform the weaver that it should index the symbols in PACKAGES."
  (dolist (package packages)
    (pushnew (find-package package) *index-packages*)))

@t@l
(deftest index-package
  (let ((*index-packages* nil))
    (index-package "KEYWORD")
    (values (interesting-symbol-p 'nil)
            (not (null (interesting-symbol-p ':foo)))))
  nil t)

@t We need to make sure that the \CLWEB\ package is in |*index-packages*|
when testing the indexer.

@l
(index-package "CLWEB")

@1*Headings. In this program, headings will generally be represented by
instances of the class |heading|. Headings may in general be multi-leveled,
and are sorted lexicographically. Any object with applicable methods for
|heading-name| and |sub-heading| is treated as a valid heading; the former
should always return a string designator, and the latter should return the
next sub-heading or |nil| if there is none.

@l
@<Define |heading-name| generic function@>

(defclass heading ()
  ((name :initarg :name :initform "")
   (sub-heading :reader sub-heading :initarg :sub-heading :initform nil)))

(defun make-heading (name &optional sub-heading)
  (make-instance 'heading :name name :sub-heading sub-heading))

(defmethod heading-name ((heading heading))
  (heading-name (slot-value heading 'name)))

(defmethod heading-name :suffix ((heading heading))
  (when (sub-heading heading)
    (heading-name (sub-heading heading))))

@t@l
(deftest heading-name
  (heading-name (make-heading "foo" (make-heading "bar")))
  "foo bar")

@ These heading classes are for headings that should be prefaced with a
\TeX\ macro when printed. Instances of |tt-heading| get printed with `\.{\\.}'
so as to appear in \.{typewriter type}, and |custom-heading| instances are
printed under the control of the \TeX\ macro `\.{\\9}', which the user can
define as desired. Additional subclasses can simply provide new defaults
for the |macro| initarg.

@l
(defclass pretty-heading (heading)
  ((macro :reader macro-heading :initarg :macro)))
(defclass tt-heading (pretty-heading) () (:default-initargs :macro "\\."))
(defclass custom-heading (pretty-heading) () (:default-initargs :macro "\\9"))

@ We'll allow string designators as headings, too. Notice that we strip
leading whitespace and backslashes from strings acting as heading names;
this helps the common case of a manual entry that begins with a \TeX\
macro sort correctly.

@l
(defmethod sub-heading (heading)
  (declare (ignore heading)))

(defmethod heading-name ((heading character))
  heading)

(defmethod heading-name ((heading string))
  (string-left-trim '(#\Space #\Tab #\Newline #\\) heading))

(defmethod heading-name ((heading symbol))
  heading)

@t Check the behavior of heading designators.

@l
(deftest (heading-name character)
  (heading-name #\A)
  "A")

(deftest (heading-name string)
  (heading-name "\\foo")
  "foo")

(deftest (heading-name symbol)
  (values (heading-name :foo)
          (heading-name '|\\foo|))
  "FOO" "\\foo")

@ We'll be storing index entries in a {\sc bst} ordered by heading, so we'll
need some comparison predicates for them. These are generic functions so that
the user may provide specialized methods on their own heading classes if they
want them sorted in a particular way. Letter case is ignored by default.

@l
(defgeneric entry-heading-lessp (h1 h2))
(defmethod entry-heading-lessp (h1 h2)
  (string-lessp (heading-name h1) (heading-name h2)))

(defgeneric entry-heading-equalp (h1 h2))
(defmethod entry-heading-equalp (h1 h2)
  (string-equal (heading-name h1) (heading-name h2)))

@t When testing our comparison functions, we have to be careful to check
that everything works properly when the arguments are swapped around, too.

@l
(defun entry-heading-strictly-lessp (x y)
  (and (entry-heading-lessp x y)
       (not (entry-heading-lessp y x))))

(deftest entry-heading-lessp
  (let* ((a (make-heading "a"))
         (b (make-heading "b"))
         (x (make-heading "x"))
         (y (make-heading "y"))
         (ax (make-heading "a" x))
         (ay (make-heading "a" y))
         (bx (make-heading "b" x))
         (by (make-heading "a" y)))
    (every #'identity
           (list (not (entry-heading-strictly-lessp a a))
                 (entry-heading-strictly-lessp a b)
                 (entry-heading-strictly-lessp a ax)
                 (entry-heading-strictly-lessp ax ay)
                 (entry-heading-strictly-lessp ax bx)
                 (entry-heading-strictly-lessp ay bx)
                 (entry-heading-strictly-lessp ax by))))
  t)

(defun entry-heading-symmetric-equalp (x y)
  (and (entry-heading-equalp x y)
       (entry-heading-equalp y x)))

(defun entry-heading-symmetric-unequalp (x y)
  (and (not (entry-heading-equalp x y))
       (not (entry-heading-equalp y x))))

(deftest entry-heading-equalp
  (let* ((a (make-heading "a"))
         (b (make-heading "b"))
         (x (make-heading "x"))
         (y (make-heading "y"))
         (ax (make-heading "a" x))
         (ay (make-heading "a" y)))
    (every #'identity
           (list (entry-heading-symmetric-equalp a a)
                 (entry-heading-symmetric-unequalp a b)
                 (entry-heading-symmetric-equalp ax ax)
                 (entry-heading-symmetric-unequalp ax ay))))
  t)

@t This is just for debugging purposes; we don't use it anywhere in this
program.

@l
(defmethod print-object ((heading heading) stream)
  (print-unreadable-object (heading stream :type t :identity nil)
    (format stream "\"~A\"" (heading-name heading))))

@ When we build entries for Lisp objects, we'll use the walker's namespace
objects as sub-headings. In order to make creating nice names from those
objects easier, we'll use a custom method combination that joins together
the results of each applicable method into one delimited string. This turns
out to be generally convenient for heading names of all kinds, so we'll use
it for |heading-name|.

@<Define |heading-name|...@>=
(defun join-strings (strings &optional (delimiter #\Space) &aux
                     (strings (ensure-list strings))
                     (delimiter (string delimiter)))
  (with-output-to-string (out)
    (loop for (string . more) on strings
          when string
            do (write-string (string string) out)
            and when more do (write-string delimiter out))))

(define-method-combination join-strings (&optional (delimiter #\Space))
    ((override (:override))
     (prefix (:prefix))
     (primary () :required t)
     (suffix (:suffix)))
  (flet ((call-methods (methods)
           (mapcar (lambda (method) `(ensure-list (call-method ,method))) ;
                   methods)))
    (let ((form `(join-strings (append ,@(call-methods prefix)
                                       ,@(call-methods primary)
                                       ,@(call-methods (reverse suffix)))
                               ,delimiter)))
      (if override
          `(call-method ,(first override) ;
                        (,@(rest override) (make-method ,form)))
          form))))

(defgeneric heading-name (heading)
  (:method-combination join-strings))

@t@l
(deftest join-strings
  (values (join-strings "foo")
          (join-strings '("foo" "bar"))
          (join-strings '(:foo :bar nil :baz) #\,))
  "foo"
  "foo bar"
  "FOO,BAR,BAZ")

(defclass dead-beef () ())
(defclass kobe-beef (dead-beef) ())
(defclass rotten-beef (dead-beef) ())
(defgeneric describe-beef (beef)
  (:method-combination join-strings ", ")
  (:method ((beef dead-beef)) "steak")
  (:method :prefix ((beef dead-beef)) (list "big" "fat" "juicy"))
  (:method :suffix ((beef dead-beef)) "yum!")
  (:method :prefix ((beef kobe-beef)) "delicious")
  (:method ((beef kobe-beef)) "Kobe")
  (:method :suffix ((beef kobe-beef)) "from Japan")
  (:method :override ((beef rotten-beef)) "Yuck!"))

(deftest join-strings-method-combination
  (values (describe-beef (make-instance 'dead-beef))
          (describe-beef (make-instance 'kobe-beef))
          (describe-beef (make-instance 'rotten-beef)))
  "big, fat, juicy, steak, yum!"
  "delicious, big, fat, juicy, Kobe, steak, yum!, from Japan"
  "Yuck!")

@ Every namespace has a name associated with it, and we'll derive our
primary heading name from that.

@l
(defmethod heading-name ((namespace namespace))
  (substitute #\Space #\- (string-downcase (namespace-name namespace)))) 

@ Lexical and special variables need their names to be |:lexical| and
|:special|, respectively, to match the types returned by the environment
functions. We'll append the suffix ``variable'' to both.

@l
(defmethod heading-name :suffix ((namespace lexical-variable-name)) "variable")
(defmethod heading-name :suffix ((namespace special-variable-name)) "variable")

@ Local functions, macros, and~symbol macros should be marked as such.

@l
(defmethod heading-name :prefix ((namespace operator))
  (and (local-binding-p namespace) "local"))

(defmethod heading-name :prefix ((namespace symbol-macro-name))
  (and (local-binding-p namespace) "local"))

@t@l
(deftest function-heading-name
  (values (heading-name (make-context 'function-name))
          (heading-name (make-context 'function-name :local t))
          (heading-name (make-context 'generic-function-name))
          (heading-name (make-context 'setf-function-name))
          (heading-name (make-context 'setf-function-name :local t)))
  "function"
  "local function"
  "generic function"
  "setf function"
  "local setf function")

@ Method definitions will have their qualifiers prepended, or `primary'
if there are none.

@l
(defmethod heading-name :prefix ((namespace method-name))
  (mapcar #'string-downcase ;
          (or (method-qualifier-names namespace) '(:primary))))

@t@l
(deftest method-heading-name
  (values (heading-name (make-context 'method-name))
          (heading-name (make-context 'method-name ;
                                      :qualifiers '(:before :during :after))))
  "primary method"
  "before during after method")

@1*Locators. Now let's turn our attention to the other half of index entries.
In this program, a locator is either a pointer to a section (the usual case)
or a cross-reference to another index entry. We'll represent locators as
instances of a |locator| class, and use a single generic function, |location|,
to dereference them.

Section locators have an additional slot for a definition flag, which
when true indicates that the object referred to by the associated heading
is defined in the section represented by that locator, not just used.
Such locators will be given a bit of typographic emphasis by the weaver
when it prints the containing entry.

@l
(defclass locator () ())

(defclass section-locator (locator)
  ((section :accessor location :initarg :section)
   (def :accessor locator-definition-p :initarg :def :initform nil)))

(defclass xref-locator (locator)
  ((heading :accessor location :initarg :heading)))
(defclass see-locator (xref-locator) ())
(defclass see-also-locator (xref-locator) ())

@ Here's a constructor for the various kinds of locators.

@l
(defun make-locator (&key section def see see-also)
  (assert (if (or see see-also) (and (not section) (not def)) t)
          (section def see see-also)
          "Can't use :SECTION or :DEF with :SEE or :SEE-ALSO.")
  (assert (if def section t) (section def) "Can't use :DEF without :SECTION.")
  (assert (not (and see see-also)) (see see-also) ;
          "Can't use both :SEE and :SEE-ALSO.")
  (cond (section (make-instance 'section-locator :section section :def def))
        (see (make-instance 'see-locator :heading see))
        (see-also (make-instance 'see-locator :heading see-also))))

@1*Index entries. Since we'll eventually want the index sorted by heading,
we'll store the entries in a binary search tree. To simplify processing,
what we'll actually store is {\it entry lists}, which are collections of
entries with identical headings, but we'll overload the term in what seems
to be a fairly traditional manner and call them entries, too.

@l
(defclass index-entry (binary-search-tree)
  ((key :accessor entry-heading)
   (locators :accessor entry-locators :initarg :locators :initform '())))

(defmethod find-or-insert (item (root index-entry) &key
                           (predicate #'entry-heading-lessp)
                           (test #'entry-heading-equalp)
                           (insert-if-not-found t))
  (call-next-method item root
                    :predicate predicate
                    :test test
                    :insert-if-not-found insert-if-not-found))

@t This |print-object| method is just for debugging purposes.

@l
(defmethod print-object ((entry index-entry) stream)
  (print-unreadable-object (entry stream :type t :identity nil)
    (format stream "~W:" (entry-heading entry))
    (dolist (locator (sort (copy-list (entry-locators entry)) #'<
                           :key (lambda (x) (section-number (location x)))))
      (format stream " ~:[~D~;[~D]~]"
              (locator-definition-p locator)
              (section-number (location locator))))))

@ We'll store the entry trees in |index| objects.

@l
(defclass index ()
  ((entries :accessor index-entries :initform nil)))

(defun make-index () (make-instance 'index))

@ We'll keep a global index around so that we can add `manual' entries (i.e.,
entries not automatically generated via the code walk) during reading.

@<Global variables@>=
(defvar *index* nil)

@ @<Initialize global variables@>=
(setq *index* (make-index))

@ This function adds an index entry for |heading| with location |section|.
A new locator is constructed only when necessary, and duplicate locators are
automatically suppressed. Definitional locators are also made to supersede
ordinary ones.

@l
(define-modify-macro orf (&rest args) or)

(defun add-index-entry (index heading section &optional def)
  (flet ((make-locator () (make-locator :section section :def def)))
    (if (null (index-entries index))
        (setf (index-entries index)
              (make-instance 'index-entry ;
                             :key heading ;
                             :locators (list (make-locator))))
        (let* ((entry (find-or-insert heading (index-entries index)))
               (old-locator (find section (entry-locators entry) ;
                                  :key #'location)))
          (if old-locator
              (orf (locator-definition-p old-locator) def)
              (push (make-locator) (entry-locators entry)))))))

@ And this function looks up a specific heading in an index, and returns
any locators that it finds.

@l
(defun find-index-entries (index heading)
  (let ((entries (index-entries index)))
    (when entries
      (multiple-value-bind (entry present-p) ;
          (find-or-insert heading entries :insert-if-not-found nil)
        (when present-p
          (entry-locators entry))))))

@t@l
(deftest (add-index-entry 1)
  (let ((index (make-index))
        (heading 'foo))
    (add-index-entry index heading 1)
    (add-index-entry index heading 2)
    (add-index-entry index heading 3)
    (sort (mapcar #'location (find-index-entries index heading)) #'<))
  (1 2 3))

(deftest (add-index-entry 2)
  (let* ((index (make-index))
         (heading 'foo))
    (add-index-entry index heading 1)
    (add-index-entry index heading 1 t) ; def should replace use
    (locator-definition-p (first (find-index-entries index heading))))
  t)

@ Now we come to the interface between the indexer and the indexing walker
we'll define below. The idea is that the walker picks up information about
symbols and function names and in what section they're defined or used, and
passes it all down to |index| encoded in the |context| object.

@l
(defgeneric index (index name section context &optional def))

(defmethod index ((index index) name section context &optional def)
  (when (and name section context)
    (add-index-entry index (make-heading name context) section def)))

@ The global variable |*index-lexical-variables*| controls whether or
not the indexer will create entries for lexical variables. Its value
is {\it not\/} re-initialized on each run.

@<Global variables@>=
(defvar *index-lexical-variables* nil
  "If this flag is non-nil, the indexer will index lexical variables.")

@ @l
(defmethod index ((index index) name section (context lexical-variable-name) ;
                  &optional def)
  (declare (ignore name section def))
  (when *index-lexical-variables*
    (call-next-method)))

@ We index special and (sometimes) lexical variables, but we don't want
to index undifferentiated variable names (e.g., as occur in declarations,
\etc.).

@l
(defmethod index :around ;
    ((index index) name section (context variable-name) &optional def)
  (declare (ignore name section def))
  (unless (eq (class-of context) (find-class 'variable-name))
    (call-next-method)))

@ There are a few other kinds of names that we walk but don't currently
bother indexing.

@l
(defmacro dont-index (namespace)
  `(defmethod index :around ;
       ((index index) name section (context ,namespace) &optional def)
     (declare (ignore name section def))))

(dont-index block-name)
(dont-index tag-name)
(dont-index slot-name)

@1*Referring symbols. We'll perform the indexing by walking over the code
of each section and noting each of the interesting symbols that we find
there according to its semantic role. In theory, this should be a
straightforward task for any Common Lisp code walker. What makes it tricky
is that references to named sections can occur anywhere in a form, which
might break the syntax of macros and special forms unless we tangle the
form first. But once we tangle a form, we lose the provenance of the
sub-forms that came from named sections, and so our index would be wrong.

The trick that we use to overcome this problem is to tangle the forms in
a special way where instead of just splicing the named section code into
place, we make a special kind of copy of each form, and splice that into
place. These copies will have each interesting symbol replaced with an
uninterned symbol whose value cell contains the symbol it replaced and
whose |section| property contains the section in which the original symbol
occurred. We'll call these uninterned symbols {\it referring symbols}.
@^referring symbols@>

First, we'll need a routine that does the substitution just described.
The substitution is done blindly and without regard to the syntax or
semantics of Common Lisp, since we can't walk pre-tangled code. We take
care to substitute inside of commas, too.

@l
(defun substitute-referring-symbols (form section)
  (let (symbols refsyms)
    (labels ((collect-symbols (form)
               (cond ((interesting-symbol-p form)
                      (pushnew form symbols))
                     ((atom form) nil)
                     (t (collect-symbols (car form))
                        (collect-symbols (cdr form)))))
             (make-referring-symbol (symbol)
               (let ((refsym (copy-symbol symbol)))
                 (setf (symbol-value refsym) symbol)
                 (setf (get refsym 'section) section)
                 @<Copy any macro function associated with |symbol|...@>
                 @<Make |refsym| an alias for any class...@>
                 (cons symbol refsym)))
             (substitute-symbols (form)
               (cond ((commap form)
                      (make-comma (comma-modifier form)
                                  (substitute-referring-symbols ;
                                   (comma-form form) ;
                                   section)))
                     ((symbolp form)
                      (or (cdr (assoc form refsyms)) form))
                     ((atom form) form)
                     (t (maptree #'substitute-symbols form)))))
      (collect-symbols form)
      (setq refsyms (mapcar #'make-referring-symbol symbols))
      (maptree #'substitute-symbols form))))

@ If the original symbol has a global definition as a macro, we'll copy
that, too, so as not to break code walkers and such.

@<Copy any macro function associated with |symbol| to |refsym|@>=
(let ((function (macro-function symbol)))
  (when function
    (setf (macro-function refsym) function)))

@ And if the original symbol names a class, we'll make the referring symbol
an alias for that class. This is necessary, for instance, when a referring
symbol replaces a symbol naming a class in a type specification that is
used before we have a chance to swap it back out.

The association between symbols and classes named by those symbols is
not stored in the symbols themselves, which means that we need to manually
remove the associations when we no longer need them. So whenever we alias
a class with a referring symbol, we'll push that symbol onto the global
|*referring-classes*| list, and we'll remove the association when we're
finished indexing.

@<Make |refsym| an alias for any class named by |symbol|@>=
(let ((class (find-class symbol nil)))
  (when class
    (setf (find-class refsym) class)
    (push refsym *referring-classes*)))

@ @<Global variables@>=
(defvar *referring-classes* '())

@ @<Initialize global variables@>=
(setq *referring-classes* '())

@ Unfortunately, on most implementations simply removing the association
between a symbol and a class is not enough to actually free the storage
allocated to that association. Since we're potentially generating many
such associations (hundreds are created during the indexing of this
program, for instance), this could leak non-trivial amounts of memory,
especially with repeated runs.
@^memory leak@>

@<Clean up after indexing@>=
(dolist (symbol *referring-classes* (setq *referring-classes* '()))
  (setf (find-class symbol) nil))

@ Given a symbol, this next function first determines whether it is a
referring symbol, and if so, it returns the referenced symbol and the
section from whence it came. Otherwise, it just returns the given symbol.
This interface makes it convenient to use in a |multiple-value-bind| form
without having to apply a predicate first.
@^referring symbols@>

@l
(defun symbol-provenance (symbol)
  (let (section)
    (if (and (not (symbol-package symbol))
             (boundp symbol)
             (setq section (get symbol 'section)))
        (values (symbol-value symbol) section)
        symbol)))

@t@l
(deftest (symbol-provenance 1)
  (let ((*index-packages* (list (find-package "KEYWORD"))))
    (symbol-provenance (substitute-referring-symbols :foo 1)))
  :foo 1)

(deftest (symbol-provenance 2)
  (symbol-provenance :foo)
  :foo)

(deftest (symbol-provenance 3)
  (let ((symbol (make-symbol "FOO")))
    (eql (symbol-provenance symbol) symbol))
  t)

(deftest (symbol-provenance 4)
  (let ((*index-packages* (list (find-package "KEYWORD"))))
    (symbol-provenance
     (macroexpand
      (substitute-referring-symbols (tangle (read-form-from-string "`,:foo")) ;
                                    1))))
  :foo 1)

@ To replace all of the referring symbols in a form, we'll use the following
simple function.
@^referring symbols@>

@l
(defun unsubstitute-referring-symbols (x)
  (typecase x
    (symbol (symbol-provenance x))
    (atom x)
    (t (maptree #'unsubstitute-referring-symbols x))))

@ To get referring symbols in the tangled code, we'll use an around
method on |section-code| that conditions on a special variable,
|*indexing*|, that we'll bind to true while we're tangling for the
purposes of indexing.
@^referring symbols@>

We can't feed the raw section code to |substitute-referring-symbols|, since
it's not really Lisp code: it's full of markers and such. So we'll abuse the
tangler infrastructure and use it to do marker replacement, but {\it not\/}
named-section expansion.

@l
(defmethod section-code :around ((section section))
  (let ((code (call-next-method)))
    (if *indexing*
        (substitute-referring-symbols (tangle code :expand-named-sections nil) ;
                                      section)
        code)))

@ The top-level indexing routine will use this function to obtain the
completely tangled code with referring symbols, and {\it that\/}'s what
we'll walk.
@^referring symbols@>

@l
(defun tangle-code-for-indexing (sections)
  (let ((*indexing* t))
    (tangle (unnamed-section-code-parts sections))))

@ @<Global variables@>=
(defvar *indexing* nil)

@ So here, finally, is the top-level indexing routine: it walks the
tangled, symbol-replaced code of the given sections and returns an index
of all of the interesting symbols so encountered.

@l
(defun index-sections (sections &key
                       (index *index*)
                       (walker (make-instance 'indexing-walker :index index)))
  (let ((*evaluating* t))
    (index-package *package*)
    (unwind-protect
         (dolist ;
             (form (tangle-code-for-indexing sections) (walker-index walker))
           (handler-case (walk-form walker form nil t)
             (package-error () form)))
      @<Clean up after indexing@>)))

@1*The indexing walker. Now we're ready to define the specialized walker
class that does the actual indexing.

@l
(defclass indexing-walker (walker)
  ((index :accessor walker-index :initarg :index :initform (make-index))))

@t Here's a little routine that returns a list of all the entries in an
index. The elements of that list are lists of the form |(heading-names
locations)|, where each location is either a section number or a list
|(:def section-number)|.

@l
(defun all-index-entries (index)
  (let ((entries))
    (map-bst
     (lambda (entry)
       (push (list (heading-name (entry-heading entry))
                   (loop for locator in (entry-locators entry)
                         if (locator-definition-p locator)
                           collect `(:def ,(section-number (location locator)))
                         else
                           collect (section-number (location locator))))
             entries))
     (index-entries index))
    (nreverse entries)))

@t To test our indexing walker, we'll almost always define tests using the
macro |define-indexing-test|. That macro relies on a few layers of helper
functions and macros, so we'll work our way up from the lowest level.

The function |walk-sections| takes a walker, a list of section specifiers,
and an environment, and walks the code in the given sections as the indexer
does. It accepts two keyword arguments as options: if |verify-walk| is true,
it will assert that the walked forms are |tree-equal| to the originals, and
the |toplevel| argument is passed down to |walk-form|. It returns a list of
walked forms.

@l
(defun walk-sections (walker sections env &key (verify-walk t) toplevel)
  (with-temporary-sections sections
    (let ((tangled-code (tangle (unnamed-section-code-parts *sections*)))
          (mangled-code (tangle-code-for-indexing *sections*)))
      (loop for form in tangled-code
            and mangled-form in mangled-code
            as walked-form = (walk-form walker mangled-form env toplevel)
            when verify-walk
              do (assert (tree-equal walked-form form)
                         (walked-form mangled-form form)
                         "Walked form does not match original.")
            collect walked-form))))

@t The next level up is |test-indexing-walk|. This function is essentially
just a wrapper for |walk-sections|: it creates an indexing walker instance,
walks the given sections using |walk-sections|, and then compares the index
entries created by the walk with a list of expected entries. It returns a
boolean representing the result of that comparison.

Along with the keyword argument accepted by |walk-sections|, it takes
three others: |index-lexicals| provides the value to which
|*index-lexical-variables*| will be bound during the walk; |trace|
controls whether the walk should be traced or not; and~|print| sets the
verbosity level: if it's true, the walked forms and the actual index
entries will be printed to standard output.

@l
(defclass tracing-indexing-walker (tracing-walker indexing-walker) ())

(defun test-indexing-walk (sections expected-entries env &key
                           (verify-walk t) toplevel index-lexicals trace print)
  (let* ((walker (make-instance (if trace
                                    'tracing-indexing-walker
                                    'indexing-walker)))
         (*index-lexical-variables* index-lexicals)
         (walked-sections (walk-sections walker sections env ;
                                         :verify-walk verify-walk ;
                                         :toplevel toplevel)))
    (when print (pprint walked-sections))
    (let ((entries (all-index-entries (walker-index walker))))
      (when print (pprint entries))
      (tree-equal entries expected-entries :test #'equal))))

@t Finally we come to |define-indexing-test|. It takes two required
arguments: a name-and-options list and a list of section specifiers.
Any remaining arguments are treated as expected index entries, and
are gathered together and passed down to |test-indexing-walk|.

The name of the test will be `(|index| \<name>)', where \<name> comes from
the |name-and-options| argument. It behaves like the first argument to
|defstruct|: if it's an atom, it's just a name, but if it's a list, the car
of the list is used as the name and the cdr is interpreted as a plist of
keyword options. Only one of those options, |aux|, is interpreted directly
by |define-indexing-test|; the rest are passed down to the helper functions
|test-indexing-walk| and |walk-sections|.

The |aux| option, if provided, should be an unquoted list of symbols.
Each of those symbols will be used as the name of a variable bound in
the body of the test to a symbol with the same name interned in a temporary
package. That package will be added to the |*index-packages*| list, and
so each of those symbols will be `interesting' to the indexer. The idea
is that many tests will need to attach global information or bindings to
symbols, but we don't want that information to outlive the tests. These
auxiliary names provide a simple method of achieving that goal: if a
backquoted form is used for the section specifiers, unquoted references
to those names will be replaced with symbols that are interesting but only
exist for the dynamic extent of the walk.

@l
(defmacro with-unique-indexing-names (names &body body)
  `(let* ((temp-package (make-package "INDEX-TEMP"))
          (*index-packages* (cons temp-package *index-packages*))
          ,@(loop for name in names ;
                  collect `(,name (intern ,(string name) temp-package))))
     (unwind-protect (progn ,@body)
       (delete-package temp-package))))

(defmacro define-indexing-test (name-and-options sections ;
                                &rest expected-entries)
  (destructuring-bind (name &rest options &key aux &allow-other-keys) ;
      (if (listp name-and-options)
          (copy-list name-and-options) ; so we can safely use |remf| below
          (list name-and-options))
    (remf options :aux)
    `(deftest (index ,@(ensure-list name))
       (with-unique-indexing-names ,aux
         (test-indexing-walk ,sections ',expected-entries nil ,@options))
       t)))

@ We'll start with a method that undoes the substitution of referring
symbols inside quoted forms.
@^referring symbols@>

@l
(defmethod walk-compound-form ;
    ((walker indexing-walker) (operator (eql 'quote)) form env &key toplevel)
  (declare (ignore env toplevel))
  `(quote ,(unsubstitute-referring-symbols (cadr form))))

@t@l
(define-indexing-test quoted-form
  '((:section :code ((quote foo)))
    (:section :code ((quote (foo bar))))))

@ We have to override the walker's macro expansion function, since the
forms that we're considering might be or contain referring symbols, which
might not have the appropriate definition as macros. There are two
important cases here: (1)~a form that is a referring symbol whose referent
is a symbol macro in the local or global environment; and (2)~a compound
form, the operator of which is a referring symbol whose referent has a
macro definition in the local environment. The first case is handled via
the call to |walk-variable-name| in |walk-form| for symbol macros.
We handle the second case here: we'll index the use of the macro, then hand
off control to the next method (which will perform the actual expansion),
passing the referent of the referring symbol.
@^referring symbols@>

@l
(defmethod macroexpand-for-walk ((walker indexing-walker) (form cons) env)
  (multiple-value-bind (symbol section) (symbol-provenance (car form))
    (if section
        (multiple-value-bind (type local) (function-information symbol env)
          (case type
            (:macro
             (index (walker-index walker) symbol section ;
                    (make-context 'macro-name :local local))
             (call-next-method walker (cons symbol (cdr form)) env))
            (t (call-next-method))))
        (call-next-method))))

@ The only ordinary atomic forms we care about are referring symbols, which
we'll index and then return the referents of. Everything else gets handled
by the default method.

@l
(defmethod walk-atomic-form ((walker indexing-walker) (form symbol) ;
                             context env &key toplevel)
  (declare (ignore env toplevel))
  (multiple-value-bind (symbol section) (symbol-provenance form)
    (when section
      (index (walker-index walker) symbol section context))
    symbol))

@ To provide a hook for indexing arbitrary function calls, we'll swap out
referring symbols that occur as the operator in a compound form. This lets
us write |eql|-specialized methods on the |operator| argument while still
preserving the provenance via the |form|.

If the operator is a referring symbol, we have to do a full call to pick up
any newly-applicable methods. Otherwise, we can just use |call-next-method|.

@l
(defmethod walk-compound-form :around ;
    ((walker indexing-walker) (operator symbol) form env &rest args)
  (multiple-value-bind (symbol section) (symbol-provenance operator)
    (if section
        (apply #'walk-compound-form walker symbol form env args)
        (call-next-method))))

@ When we walk a name that is or contains a referring symbol, we'll swap
out the symbol and index the name. This method handles the mechanics by
using two auxiliary routines, |destructure-name| and |construct-name|.
The idea is that a name might be as simple as a symbol, or a list like
`(|setf| \<name>)', or, as in the case of a macro definition, even include
a definition. |destructure-name| takes apart such names based on the
namespace and returns the symbol we'll use in the index if it's a referring
symbol; |construct-name| goes the other way.

@l
(defgeneric destructure-name (name namespace))
(defgeneric construct-name (symbol name namespace))

(defmethod walk-name ((walker indexing-walker) name namespace env &key def)
  (multiple-value-bind (symbol section) ;
      (symbol-provenance (destructure-name name namespace))
    (let ((name (construct-name symbol name namespace)))
      (when section
        (index (walker-index walker) symbol section
               (if def namespace (update-context name namespace env))
               def))
      name)))

@ We'll use the same auxiliary routines for walking bindings. It's slightly
complicated because we have to be able to handle multiple bindings
simultaneously, and we need to wait for the indexing until we have the
augmented environment. So we hold on to the referred-to symbols and their
provenances while we call up to the next method to perform the actual
bindings, and then index them one at a time.

@l
(defmethod walk-bindings ((walker indexing-walker) names namespace env &key ;
                          declare)
  (let ((symbols '())
        (sections '()))
    (dolist (name names (progn (setf symbols (nreverse symbols))
                               (setf sections (nreverse sections))))
      (multiple-value-bind (symbol section) ;
          (symbol-provenance (destructure-name name namespace))
        (push symbol symbols)
        (push section sections)))
    (multiple-value-bind (names env)
        (call-next-method walker
                          (mapcar (lambda (symbol name) ;
                                    (construct-name symbol name namespace))
                                  symbols names)
                          namespace env
                          :declare declare)
      (loop for symbol in symbols and section in sections and name in names
            when section
              do (index (walker-index walker) symbol section ;
                        (update-context name namespace env) ;
                        t))
      (values names env))))

@ Here are the methods for destructuring names. The default method is the
common case, where no destructuring is actually necessary. Functions are
either symbols or |setf| functions, and~macro and symbol macro definitions
are represented using lists of the form `(\<name> \<definition>)'.

@l
(defmethod destructure-name (name namespace)
  (declare (ignore namespace))
  name)

(defmethod destructure-name (name (namespace function-name))
  (etypecase name
    (symbol name)
    (setf-function (cadr name))))

(defmethod destructure-name (def (namespace macro-definition))
  (car def))

(defmethod destructure-name (def (namespace symbol-macro-definition))
  (car def))

@ And here's how we put names back together based on their original form.

@l
(defmethod construct-name (symbol name namespace)
  (declare (ignore name namespace))
  symbol)

(defmethod construct-name (symbol name (namespace function-name))
  (etypecase name
    (symbol symbol)
    (setf-function `(setf ,symbol))))

(defmethod construct-name (symbol def (namespace macro-definition))
  (cons symbol (cdr def)))

(defmethod construct-name (symbol def (namespace symbol-macro-definition))
  (cons symbol (cdr def)))

@t@l
(define-indexing-test (lexical-variable :index-lexicals t)
  '((:section :code ((let ((x nil) (y nil) (z nil))))))
  ("X lexical variable" ((:def 0)))
  ("Y lexical variable" ((:def 0)))
  ("Z lexical variable" ((:def 0))))

(define-indexing-test special-variable
  '((:section :code ((locally (declare (special *x*)) *x*))))
  ("*X* special variable" (0)))

(define-indexing-test (macrolet :verify-walk nil)
  '((:section :code ((macrolet ((frob (x) `(* ,x 42))) (frob 6)))))
  ("FROB local macro" ((:def 0))))

(define-indexing-test (symbol-macrolet :verify-walk nil)
  '((:section :code ((symbol-macrolet ((foo :bar)) foo))))
  ("FOO local symbol macro" ((:def 0))))

@ The one kind of name we'll walk differently is catch tags. Because they
might be arbitrary forms, we can't reliably specify how to take them apart
and put them back together. But that doesn't matter, because we only care
about one specific kind of tag: quoted symbols.

@l
(deftype quoted-symbol () '(cons (eql quote) (cons symbol null)))

(defmethod walk-name ((walker indexing-walker) tag (namespace catch-tag) env ;
                      &key catch)
  (typecase tag
    (quoted-symbol
     (multiple-value-bind (symbol section) (symbol-provenance (cadr tag))
       (when section
         (index (walker-index walker) symbol section namespace catch))
       `(quote ,symbol)))
    (t (walk-form walker tag env))))

@t@l
(define-indexing-test catch/throw
  '((:section :code ((catch 'foo (throw 'bar (throw (lambda () 'baz) t))))))
  ("BAR catch tag" (0))
  ("FOO catch tag" ((:def 0))))

@t Note that this test assumes that the walker's global environment is the
same as the environment in which these tests are defined.

@l
(defvar *super* t)
(define-symbol-macro bait switch)
(defconstant the-ultimate-answer 42)

(define-indexing-test (variables :verify-walk nil)
  '((:section :code (*super*))
    (:section :code (bait))
    (:section :code (the-ultimate-answer)))
  ("*SUPER* special variable" (0))
  ("BAIT symbol macro" (1))
  ("THE-ULTIMATE-ANSWER constant" (2)))

@t These tests, like the |(index variables)| test we just defined, assume
that the walker sees definitions in the current global environment.

@l
(defun square (x) (* x x))
(define-indexing-test function
  '((:section :code ((square 1))))
  ("SQUARE function" (0)))

(defmacro frob-foo (foo) `(1+ (* ,foo 42)))
(define-indexing-test (macro :verify-walk nil)
  '((:section :code ((frob-foo 6))))
  ("FROB-FOO macro" (0)))

@t @l
(define-indexing-test function-name
  '((:section :code ((flet ((foo (x) x)))))
    (:section :code ((labels (((setf foo) (y x) y))))))
  ("FOO local function" ((:def 0)))
  ("FOO local setf function" ((:def 1))))

@2*Indexing defining forms. Now we can turn our attention to walking
defining forms such as |defun| and |defparameter|. The idea here is
to index the name being defined before macro expansion robs us of the
opportunity. We'll do that by pretending that the defining forms are
actually special forms, which stops the walker from expanding them.
After we're finished indexing, we can let the expansion continue via a
|throw| to the |continue-walk| tag. But sometimes we won't even bother
with the expansions; we don't care about getting an accurate and complete
walk here, but rather only about indexing all of the interesting names.

@ |defun| and~|define-compiler-macro| are perfect examples of defining
forms that we'll walk as special forms for the purposes of indexing.
If we didn't catch them before macro expansion, we'd have a very hard
time noticing that they were definitions at all. We won't bother letting
them expand, since we get everything we need from walking the name with
|walk-name| and the body with |walk-lambda-expression|.

@l
(defun walk-defun (walker form context env)
  (let ((name (walk-name walker (cadr form) context env :def t)))
    `(,(car form)
      ,@(walk-lambda-expression walker (cons name (cddr form)) context env))))

(define-special-form-walker defun ((walker indexing-walker) form env &key ;
                                   toplevel)
  (declare (ignore toplevel))
  (walk-defun walker form (make-context 'function-name) env))

(define-special-form-walker define-compiler-macro ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-defun walker form (make-context 'compiler-macro-name) env))

@t@l
(define-indexing-test (defun :verify-walk nil)
  '((:section :code ((defun foo (x) x))))
  ("FOO function" ((:def 0))))

(define-indexing-test (define-compiler-macro :verify-walk nil :toplevel t
                                             :aux (compile-foo))
  `((:section :code ((define-compiler-macro ,compile-foo (&whole x) x))))
  ("COMPILE-FOO compiler macro" ((:def 0))))

@ We'll handle |defmacro| and |define-symbol-macro| similarly, except that
we do need them to be expanded so that we can pick up their definitions in
the global environment.

@l
(define-special-form-walker defmacro ((walker indexing-walker) form env &key ;
                                      toplevel)
  (declare (ignore toplevel))
  (throw 'continue-walk
    (walk-defun walker form (make-context 'macro-name) env)))

(define-special-form-walker define-symbol-macro ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  (let* ((context (make-context 'symbol-macro-name))
         (name (walk-name walker (cadr form) context env :def t)))
    (throw 'continue-walk
      `(,(car form) ,name ,(walk-form walker (caddr form) env)))))

@t@l
(define-indexing-test (defmacro :verify-walk nil :toplevel t
                                :aux (twiddle twiddle-foo))
  `((:section :code ((eval-when (:compile-toplevel)
                       (defun ,twiddle (x) (* x 42)))))
    (:section :code ((defmacro ,twiddle-foo (x) (,twiddle x))))
    (:section :code ((,twiddle-foo 123))))
  ("TWIDDLE function" (1 (:def 0)))
  ("TWIDDLE-FOO macro" (2 (:def 1))))

(define-indexing-test (symbol-macro :verify-walk nil :toplevel t
                                    :aux (foo-bar-baz))
  `((:section :code ((define-symbol-macro ,foo-bar-baz (:bar :baz))))
    (:section :code (,foo-bar-baz)))
  ("FOO-BAR-BAZ symbol macro" (1 (:def 0))))

@ We'll need to let |defvar| and |defparameter| expand after walking, too,
in order to pick up the |special| proclamations.

@l
(defun walk-defvar (walker form env)
  (throw 'continue-walk
    `(,(car form)
      ,(walk-name walker (cadr form) ;
                  (make-context 'special-variable-name) ;
                  env :def t)
      ,@(cddr form))))

(define-special-form-walker defvar ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-defvar walker form env))

(define-special-form-walker defparameter ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-defvar walker form env))

@t@l
(define-indexing-test (defvar :verify-walk nil :toplevel t
                              :aux (super duper))
  `((:section :code ((defvar ,super 450)))
    (:section :code ((defparameter ,duper (1+ ,super)))))
  ("DUPER special variable" ((:def 1)))
  ("SUPER special variable" (1 (:def 0))))

@ We have to treat |defconstant| specially because of the work-around in
the walker for Allegro, but it's basically the same as above.
@^Allegro Common Lisp@>

@l
(define-special-form-walker defconstant ;
    ((walker indexing-walker) form env &rest args)
  (apply #'call-next-method walker 'defconstant
         `(defconstant ,(walk-name walker (cadr form) ;
                                   (make-context 'constant-name) env :def t)
            ,@(walk-list walker (cddr form) env))
         env args))

@t@l
(define-indexing-test (defconstant :verify-walk nil :toplevel t
                                   :aux (el-gordo))
  `((:section :code ((defconstant ,el-gordo most-positive-fixnum))))
  ("EL-GORDO constant" ((:def 0))))

@ Structure definitions get walked to pick up the structure name as well as
any automatically defined functions. We'll let the walk continue with the
expansion so that the compiler can pick up the structure definition, too.

@l
@<Declare |structure-description| structure@>
@<Define |defstruct| parsing routines@>

(define-special-form-walker defstruct ((walker indexing-walker) form env &key ;
                                       toplevel)
  (declare (ignore toplevel))
  (let ((structure-description)
        (name-and-options))
    (throw 'continue-walk
      `(,(pop form)
        ,(multiple-value-setq (name-and-options structure-description)
                              (walk-defstruct-name-and-options walker ;
                                                               (pop form) ;
                                                               env))
        ,@(and (stringp (car form)) (list (pop form)))
        ,@(mapcar (lambda (slot-description)
                    (walk-defstruct-slot-description walker ;
                                                     slot-description ;
                                                     structure-description ;
                                                     env))
                  form)))))

@ We'll use an auxiliary data structure, called a {\it structure description},
to handle most of the bookkeeping as we walk a |defstruct| form. (Some of this
code was inspired by SBCL's |defstruct| processing, although it is simplified
in many ways.)

@<Declare |structure-description|...@>=
(defun symbolicate (&rest strings)
  (values (intern (join-strings strings ""))))

(defstruct (structure-description
            (:conc-name "STRUCT-")
            (:constructor make-structure-description
                          (name &aux
                           (conc-name (symbolicate name "-"))
                           (copier-name (symbolicate "COPY-" name))
                           (predicate-name (symbolicate name "-P")))))
  (name nil :type symbol :read-only t)
  (conc-name nil :type (or symbol null))
  (constructors () :type list)
  (copier-name nil :type (or symbol null))
  (predicate-name nil :type (or symbol null))
  (include nil :type list))

@ We'll need several subroutines to do the work of parsing and walking a
|defstruct| form. We'll start with the processing of the name and options.

Notice that |walk-defstruct-name-and-options| returns two values: the
walked name and options (a form), and the structure description that will
be passed down to the slot description parsing routines.

The recursion in |walk-defstruct-option| is just a lazy way of canonicalizing
options supplied as atoms that are equivalent to one-element lists; it will
never go more than one level deep.

@<Define |defstruct| parsing routines@>=
(defun walk-defstruct-name-and-options (walker name-and-options env)
  (destructuring-bind (name &rest options) (ensure-list name-and-options)
    (let* ((struct-name (walk-name walker name (make-context 'struct-name) ;
                                   env :def t))
           (struct-description (make-structure-description struct-name)))
      (values `(,struct-name
                ,@(loop for option in options
                        collect (walk-defstruct-option walker option ;
                                                       struct-description env)
                        finally @<Index auto-generated structure function...@>))
              struct-description))))

(defun walk-defstruct-option (walker option description env)
  (cond ((member option '(:conc-name :constructor :copier :predicate))
         (walk-defstruct-option walker (list option) description env))
        ((atom option)
         option)
        (t `(,(first option)
             ,@(ensure-list @<Walk one |defstruct| option@>)))))

@ We only care about specifically about a handful of |defstruct| options.
At this point, |option| will have been converted to list form; we'll walk
it and record relevant information in |description| as we go.

@<Walk one |defstruct| option@>=
(let ((args (rest option))
      (struct-name (struct-name description)))
  (case (first option)
    (:conc-name
     (destructuring-bind (&optional conc-name) args
       (setf (struct-conc-name description)
             (if (symbolp conc-name)
                 (walk-atomic-form walker conc-name nil env)
                 (make-symbol (string conc-name))))))
    (:constructor
     (destructuring-bind ;
           (&optional (name (symbolicate "MAKE-" struct-name)) &rest arglist) ;
         args
       (let* ((context (make-context (if arglist ;
                                         'struct-boa-constructor ;
                                         'struct-constructor-name)))
              (name (walk-name walker name context env :def t)))
         (car (push (cons name arglist) (struct-constructors description))))))
    (:copier
     (destructuring-bind (&optional (name (symbolicate "COPY-" struct-name))) ;
         args
       (setf (struct-copier-name description)
             (walk-name walker name (make-context 'struct-copier-name) ;
                        env :def t))))
    (:predicate
     (destructuring-bind (&optional (name (symbolicate struct-name "-P"))) ;
         args
       (setf (struct-predicate-name description)
             (walk-name walker name (make-context 'struct-predicate-name) ;
                        env :def t))))
    (:include
     (destructuring-bind (name &rest slot-descriptions) args
       (setf (struct-include description)
             `(,(walk-name walker name (make-context 'struct-name) env)
               ,@(mapcar (lambda (slot-description)
                           (walk-defstruct-slot-description walker ;
                                                            slot-description ;
                                                            description ;
                                                            env))
                         slot-descriptions)))))
    (t (walk-list walker args env))))

@ Explicitly named constructor functions, copiers, and predicates are
indexed during the walk of the corresponding options. But if the options
are not given, we still need to index the default generated names.

@<Index auto-generated structure function names@>=
(let ((section (nth-value 1 (symbol-provenance name))))
  (flet ((index (name context-type)
           (when name
             (index (walker-index walker) name section ;
                    (make-context context-type) t))))
    (loop for (name . arglist) in (or (struct-constructors struct-description)
                                      `((,(symbolicate "MAKE-" struct-name))))
          do (index name (if arglist ;
                             'struct-boa-constructor ;
                             'struct-constructor-name)))
    (index (struct-copier-name struct-description) 'struct-copier-name)
    (index (struct-predicate-name struct-description) 'struct-predicate-name)))

@ Structure slot descriptions are straightforward: they're either a symbol
naming the slot, or a list containing the slot name, an optional initform,
and~possibly the keyword options |:type| and |:read-only|. We don't care
about the type, but the |:read-only| option determines whether a reader
or an accessor is defined, which we do care about.

@<Define |defstruct| parsing routines@>=
(defun walk-defstruct-slot-description ;
    (walker slot-description struct-description env)
  (typecase slot-description
    (symbol
     (walk-defstruct-slot-name walker slot-description nil ;
                               struct-description env))
    (cons
     (destructuring-bind (slot-name &optional (initform nil initform-supplied)
                          &rest args &key read-only &allow-other-keys)
         slot-description
       `(,(walk-defstruct-slot-name walker slot-name read-only ;
                                    struct-description env)
          ,@(when initform-supplied `(,(walk-form walker initform env)))
          ,@args)))
    (t slot-description)))

@ As we walk structure slot names, we'll index the automatically created
reader or accessor functions.

In the case of a conflict with an inherited reader or accessor function name,
the definition is inherited from the included structure. Because we don't
keep structure descriptions around, we can't detect this case directly.
But we {\it can\/} check to see if there's already a definition in the
index for the proposed name, either as a reader or an accessor; if there
is, we'll assume it will be inherited and that we should not index it as
a definition here.

@<Define |defstruct| parsing routines@>=
(defun walk-defstruct-slot-name ;
    (walker slot-name read-only-p struct-description env)
  (declare (ignore env))
  (multiple-value-bind (symbol section) (symbol-provenance slot-name)
    (let ((name (symbolicate (struct-conc-name struct-description) symbol))
          (reader (make-context 'struct-slot-reader))
          (accessor (make-context 'struct-slot-accessor))
          (index (walker-index walker)))
      (unless (and (struct-include struct-description)
                   (some #'locator-definition-p
                         (or (find-index-entries index ;
                                                 (make-heading name accessor))
                             (find-index-entries index ;
                                                 (make-heading name reader)))))
        (index index name section (if read-only-p reader accessor) t)))
    symbol))

@ @<Define namespace...@>=
(defnamespace struct-name () :structure)
(defnamespace struct-constructor-name (function-name) :constructor-function)
(defnamespace struct-boa-constructor (function-name) :boa-constructor)
(defnamespace struct-copier-name (function-name) :copier-function)
(defnamespace struct-predicate-name (function-name) :type-predicate)
(defnamespace struct-slot-reader (function-name) :slot-reader)
(defnamespace struct-slot-accessor (function-name) :slot-accessor)

@ Even puns deserve to be properly typeset.

@l
(defmethod heading-name :override ((heading struct-boa-constructor))
  "{\\sc boa} constructor")

@t Even the simplest structure definition generates four index entries:
the structure itself, a constructor function, a copy function, and a type
predicate.

@l
(define-indexing-test (defstruct :verify-walk nil :toplevel t
                                 :aux (foo))
  `((:section :code ((defstruct ,foo))))
  ("COPY-FOO copier function" ((:def 0)))
  ("FOO structure" ((:def 0)))
  ("FOO-P type predicate" ((:def 0)))
  ("MAKE-FOO constructor function" ((:def 0))))

@t The |:constructor|, |:copier|, and |:predicate| options each have
three variants: keyword only, keyword with null argument, and~keyword
with non-null argument.

@l
(define-indexing-test ((defstruct functions) :verify-walk nil :toplevel t
                                             :aux (a b c cons-c dup-c cp))
  `((:section :code ((defstruct (,a :constructor
                                    (:predicate nil)))))
    (:section :code ((defstruct (,b (:constructor nil)
                                    (:predicate)))))
    (:section :code ((defstruct (,c (:constructor ,cons-c)
                                    (:copier ,dup-c)
                                    (:predicate ,cp))))))
  ("A structure" ((:def 0)))
  ("B structure" ((:def 1)))
  ("B-P type predicate" ((:def 1)))
  ("C structure" ((:def 2)))
  ("CONS-C constructor function" ((:def 2)))
  ("COPY-A copier function" ((:def 0)))
  ("COPY-B copier function" ((:def 1)))
  ("CP type predicate" ((:def 2)))
  ("DUP-C copier function" ((:def 2)))
  ("MAKE-A constructor function" ((:def 0))))

@t Included structure names are indexed as uses.

@l
(define-indexing-test ((defstruct :include) :verify-walk nil :toplevel t
                                            :aux (base derived))
  `((:section :code ((defstruct (,base (:constructor nil)
                                       (:copier nil)
                                       (:predicate nil)))))
    (:section :code ((defstruct (,derived (:include ,base)
                                          (:constructor nil)
                                          (:copier nil)
                                          (:predicate nil))))))
  ("BASE structure" (1 (:def 0)))
  ("DERIVED structure" ((:def 1))))

@t Structure slot readers and accessors are indexed. Their names are
prefixed by the |:conc-name| option, which defaults to the structure
name followed by a hyphen. Neither constructor nor predicate functions
are affected by |:conc-name|.

@l
(define-indexing-test ((defstruct accessors) :verify-walk nil :toplevel t
                                             :aux (town))
  `((:section :code ((defstruct ,town
                       area
                       watertowers
                       (firetrucks 1 :type fixnum) ; an initialized slot
                       population
                       (elevation 5128 :read-only t)))))
  ("COPY-TOWN copier function" ((:def 0)))
  ("MAKE-TOWN constructor function" ((:def 0)))
  ("TOWN structure" ((:def 0)))
  ("TOWN-AREA slot accessor" ((:def 0)))
  ("TOWN-ELEVATION slot reader" ((:def 0)))
  ("TOWN-FIRETRUCKS slot accessor" ((:def 0)))
  ("TOWN-P type predicate" ((:def 0)))
  ("TOWN-POPULATION slot accessor" ((:def 0)))
  ("TOWN-WATERTOWERS slot accessor" ((:def 0))))

(define-indexing-test ((defstruct conc-name) :verify-walk nil :toplevel t
                                             :aux (clown))
  `((:section :code ((defstruct (,clown (:conc-name bozo-))
                       (nose-color 'red)
                       frizzy-hair-p
                       polkadots))))
  ("BOZO-FRIZZY-HAIR-P slot accessor" ((:def 0)))
  ("BOZO-NOSE-COLOR slot accessor" ((:def 0)))
  ("BOZO-POLKADOTS slot accessor" ((:def 0)))
  ("CLOWN structure" ((:def 0)))
  ("CLOWN-P type predicate" ((:def 0)))
  ("COPY-CLOWN copier function" ((:def 0)))
  ("MAKE-CLOWN constructor function" ((:def 0))))

@t Inherited slot accessors don't get indexed.

@l
(define-indexing-test ((defstruct inherited-accessor)
                       :verify-walk nil :toplevel t
                       :aux (a b))
  `((:section :code ((defstruct (,a (:conc-name nil)
                                    (:constructor nil)
                                    (:copier nil)
                                    (:predicate nil))
                       a-b)))
    (:section :code ((defstruct (,b (:include ,a)
                                    (:conc-name a-)
                                    (:constructor nil)
                                    (:copier nil)
                                    (:predicate nil))
                       (b nil :read-only t)))))
  ("A structure" (1 (:def 0)))
  ("A-B slot accessor" ((:def 0)))
  ("B structure" ((:def 1))))

@ Now we'll turn to the various {\sc clos} forms. We'll start with a little
macro to pull off method qualifiers from a |defgeneric| form or a method
description. Syntactically, the qualifiers are any non-list objects
preceding the specialized \L-list.

@l
(defmacro pop-qualifiers (place)
  `(loop until (listp (car ,place)) collect (pop ,place)))

@ For |defgeneric| forms, we're interested in the name of the generic
function being defined, the method combination type, and any methods that
may be specified as method descriptions. The environment objects don't keep
track of whether a function is generic or not, so we'll have to maintain
that information ourselves.

@l
(define-special-form-walker defgeneric ((walker indexing-walker) form env &key ;
                                        toplevel)
  (declare (ignore toplevel))
  (destructuring-bind (operator function-name lambda-list &rest options) form
    `(,operator
      ,(note-generic-function
        (walk-name walker function-name
                   (make-context ;
                    (etypecase function-name
                      (symbol 'generic-function-name)
                      (setf-function 'generic-setf-function-name)))
                    env :def t))
      ,(walk-lambda-list walker lambda-list nil env)
      ,@(loop for form in options
              collect (case (car form)
                        (:method-combination ;
                         @<Walk the method combination option in |form|@>)
                        (:method @<Walk the method description in |form|@>)
                        (t (walk-list walker form env)))))))

@ @<Define namespace...@>=
(defnamespace generic-function-name (function-name) :generic-function)
(defnamespace generic-setf-function-name (generic-function-name ;
                                          setf-function-name) ;
  :generic-setf-function)

@t@l
(define-indexing-test (defgeneric :aux (foo))
  `((:section :code ((defgeneric ,foo (x y)
                       (:documentation "foo")
                       (:method-combination progn)
                       (:method progn ((x t) y) x)
                       (:method :around (x (y (eql 't))) y))))
    (:section :code ((,foo 2 3)))
    (:section :code ((defgeneric (setf ,foo) (new x y)))))
  ("FOO around method" ((:def 0)))
  ("FOO generic function" (1 (:def 0)))
  ("FOO generic setf function" ((:def 2)))
  ("FOO progn method" ((:def 0))))

@ To note that a function is a generic function, we'll stick a property on
the function name's plist. (If it's a |setf| function, we'll use the cadr
of the function name.) We can then just check for that property, although
if the function name is |fboundp|, we'll check the actual type of the
function object instead.

@l
(defun note-generic-function (function-name)
  (typecase function-name
    (symbol (setf (get function-name 'generic-function) t))
    (setf-function (setf (get (cadr function-name) 'generic-setf-function) t)))
  function-name)

(defun generic-function-p (function-name)
  (if (fboundp function-name)
      (typep (fdefinition function-name) 'generic-function)
      (typecase function-name
        (symbol (get function-name 'generic-function))
        (setf-function (get (cadr function-name) 'generic-setf-function)))))

@t@l
(deftest generic-function-p
  (values (not (null (generic-function-p 'make-instance)))
          (null (generic-function-p '#:foo))
          (not (null (generic-function-p (note-generic-function '#:foo)))))
  t t t)

@ Method descriptions are very much like |defmethod| forms with an implicit
function name; this routine walks both. The function name (if non-null) and
qualifiers (if any) should have been walked already; we'll walk the
specialized \L-list and body forms here.

@l
(defun walk-method-definition (walker operator function-name qualifiers ;
                               lambda-list body env)
  (multiple-value-bind (body-forms decls doc) ;
      (parse-body body :walker walker :env env)
    (multiple-value-bind (lambda-list env) ;
        (walk-specialized-lambda-list walker lambda-list decls env)
      `(,operator
        ,@(when function-name `(,function-name))
        ,@qualifiers
        ,lambda-list
        ,@(when doc `(,doc))
        ,@(when decls `((declare ,@decls)))
        ,@(walk-list walker body-forms env)))))

@ @<Walk the method description in |form|@>=
(let* ((operator (pop form))
       (qualifiers (mapcar (lambda (q) (walk-atomic-form walker q nil env))
                           (pop-qualifiers form)))
       (lambda-list (pop form))
       (body form))
  (walk-name walker function-name
             (make-context 'method-name :qualifiers qualifiers)
             env :def t)
  (walk-method-definition walker operator nil qualifiers lambda-list body env))

@ @<Define namespace...@>=
(defnamespace method-name (function-name) :method
  ((qualifiers :reader method-qualifier-names ;
               :initarg :qualifiers ;
               :initform nil)))
(defnamespace setf-method-name (method-name setf-function-name) :setf-method)

@t@l
(defmethod print-object ((x method-name) stream)
  (print-unreadable-object (x stream :type t :identity t)
    (prin1 (method-qualifier-names x) stream)))

@ Walking a |defmethod| form is almost, but not quite, the same as walking
a method description.

@l
(define-special-form-walker defmethod
    ((walker indexing-walker) form env &key toplevel &aux
     (operator (pop form))
     (function-name (pop form)) ; don't walk yet: wait for the qualifiers
     (qualifiers (mapcar (lambda (q) (walk-atomic-form walker q nil env))
                         (pop-qualifiers form)))
     (lambda-list (pop form))
     (body form))
  (declare (ignore toplevel))
  (walk-method-definition walker operator
                          (note-generic-function
                           (walk-name walker function-name
                                      (make-context ;
                                       (etypecase function-name
                                         (symbol 'method-name)
                                         (setf-function 'setf-method-name))
                                       :qualifiers qualifiers)
                                      env :def t))
                          qualifiers lambda-list body env))

@t@l
(define-indexing-test (defmethod :aux (foo))
  `((:section :code ((defmethod ,foo (x y) (+ x y))))
    (:section :code ((defmethod ,foo :before (x y))))
    (:section :code ((defmethod (setf ,foo) (new-foo foo) new-foo)))
    (:section :code ((funcall #'(setf ,foo) y x))))
  ("FOO before method" ((:def 1)))
  ("FOO generic setf function" (3))
  ("FOO primary method" ((:def 0)))
  ("FOO primary setf method" ((:def 2))))

@ We'll walk |defclass| and |define-condition| forms in order to index the
class names, super-classes, and~accessor methods.

@l
(defun walk-defclass (walker form context env)
  (destructuring-bind (operator name supers slot-specs &rest options) form
    (throw 'continue-walk
      `(,operator
        ,(walk-name walker name context env :def t)
        ,(mapcar (lambda (super) (walk-name walker super context env))
                 supers)
        ,(mapcar (lambda (spec) (walk-slot-specifier walker spec env))
                 slot-specs)
        ,@(walk-list walker options env)))))

(define-special-form-walker defclass ((walker indexing-walker) form env &key ;
                                      toplevel)
  (declare (ignore toplevel))
  (walk-defclass walker form (make-context 'class-name%) env))

(define-special-form-walker define-condition ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  (walk-defclass walker form (make-context 'condition-class-name) env))

@t@l
(define-indexing-test (defclass :verify-walk nil
                                :aux (foo bar a b foo-a1 foo-a2 foo-b))
  `((:section :code ((defclass ,foo ()
                       ((,a :reader ,foo-a1 :reader ,foo-a2)))))
    (:section :code ((define-condition ,bar ()
                       ((,b :accessor ,foo-b))))))
  ("BAR condition class" ((:def 1)))
  ("FOO class" ((:def 0)))
  ("FOO-A1 reader method" ((:def 0)))
  ("FOO-A2 reader method" ((:def 0)))
  ("FOO-B accessor method" ((:def 1))))

@ The only slot options we care about are |:reader|, |:writer|,
and~|:accessor|. We index the methods implicitly created by those
options.

@l
(defun walk-slot-specifier (walker spec env)
  (etypecase spec
    (symbol (walk-name walker spec (make-context 'slot-name) env))
    (cons (destructuring-bind (name &rest options) spec
            `(,(walk-name walker name (make-context 'slot-name) env :def t)
              ,@(loop for (opt-name opt-value) on options by #'cddr
                      if (member opt-name '(:reader :writer :accessor))
                        append `(,opt-name
                                 ,(walk-name walker opt-value
                                             (make-context 'method-name ;
                                                           :qualifiers ;
                                                           (list opt-name))
                                             env :def t))
                      else
                        append `(,opt-name ,opt-value)))))))

@ @<Define namespace...@>=
(defnamespace slot-name () :slot)

@ We'll also walk |define-method-combination| forms to get the names of the
method combination types. We'll skip the expansion.

@l
(define-special-form-walker define-method-combination ;
    ((walker indexing-walker) form env &key toplevel)
  (declare (ignore toplevel))
  `(,(car form)
    ,(walk-name walker (cadr form) (make-context 'method-combination-name) ;
                env :def t)
    ,@(walk-list walker (cddr form) env)))

@ @<Define namespace...@>=
(defnamespace method-combination-name () :method-combination)

@ We'll also index custom method combination type uses, which occur in the
|:method-combination| option given to a |defgeneric| form.

@<Walk the method combination...@>=
`(,(car form)
  ,(walk-atomic-form walker (cadr form) ;
                     (make-context 'method-combination-name) env)
  ,@(walk-list walker (cddr form) env))

@t@l
(define-indexing-test (define-method-combination :verify-walk nil
                                                 :aux (foo generic-foo))
  `((:section :code ((define-method-combination ,foo)))
    (:section :code ((defgeneric ,generic-foo () (:method-combination ,foo)))))
  ("FOO method combination" (1 (:def 0)))
  ("GENERIC-FOO generic function" ((:def 1))))

@1*Writing the index. All that remains now is to write the index entries
out to the index file. We'll be extra fancy and try to coalesce adjacent
locators, so that, e.g., if |foo| is used in sections 1, 2, and~3, the
entry will be printed as `|foo|:~1--3'. The function |coalesce-locators|
takes a sorted list of locators and returns a list of locators and
|section-range| instances. Note that definitional locators will never be
part of a range.

@l
(defclass section-range ()
  ((start :reader start-section :initarg :start)
   (end :reader end-section :initarg :end)))

(defun coalesce-locators (locators)
  (flet ((maybe-make-section-range (start end)
           (cond ((eql start end) start)
                 ((and start end)
                  (make-instance 'section-range ;
                                 :start (location start) ;
                                 :end (location end))))))
    (do* ((locators locators (cdr locators))
          (loc (car locators) (car locators))
          (coalesced-locators '())
          start end)
         ((endp locators) ;
          (nreconc coalesced-locators ;
                   (ensure-list (maybe-make-section-range start end))))
      (flet ((maybe-push-range (start end)
               (let ((range (maybe-make-section-range start end)))
                 (when range (push range coalesced-locators)))))
        (cond ((locator-definition-p loc)
               (maybe-push-range start end)
               (push loc coalesced-locators)
               (setq start nil end nil))
              ((and end ;
                    (= (section-number (location loc)) ;
                       (1+ (section-number (location end)))))
               (setq end loc))
              (t (maybe-push-range start end)
                 (setq start loc end start)))))))

@t@l
(defmethod location ((range section-range))
  (list (start-section range)
        (end-section range)))

(deftest (coalesce-locators 1)
  (mapcar (lambda (sections)
            (mapcar #'location
                    (coalesce-locators
                     (mapcar (lambda (n)
                               (make-instance 'section-locator :section n))
                             sections))))
          '((1 3 5 7)
            (1 2 3 5 7)
            (1 3 4 5 7)
            (1 2 3 5 6 7)
            (1 2 3 5 6 7 9)))
  ((1 3 5 7)
   ((1 3) 5 7)
   (1 (3 5) 7)
   ((1 3) (5 7))
   ((1 3) (5 7) 9)))

(deftest (coalesce-locators 2)
  (mapcar #'location
          (coalesce-locators
           `(,(make-instance 'section-locator :section 1 :def t)
             ,@(mapcar (lambda (n)
                         (make-instance 'section-locator :section n))
                       '(2 3 5))
             ,(make-instance 'section-locator :section 6 :def t))))
  (1 (2 3) 5 6))

@ Here are the pretty-printing routines for the index itself.

@l
(set-weave-dispatch 'index
  (lambda (stream index)
    (map-bst (lambda (entry) (write entry :stream stream))
             (index-entries index))))

(set-weave-dispatch 'index-entry
  (lambda (stream entry)
    (format stream "\\I~/clweb::print-entry-heading/~{, ~W~}.~%"
            (entry-heading entry)
            (coalesce-locators
             (sort (copy-list (entry-locators entry)) #'<
                   :key (lambda (loc) (section-number (location loc))))))))

(set-weave-dispatch 'section-range
  (lambda (stream range)
    (format stream "~D--~D"
            (section-number (start-section range))
            (section-number (end-section range)))))

(set-weave-dispatch 'section-locator
  (lambda (stream loc)
    (format stream "~:[~D~;\\[~D]~]"
            (locator-definition-p loc)
            (section-number (location loc)))))

@ Entry headings come in many flavors, and need special treatment in order
to be printed nicely and correctly. We're intentionally conflating headers
with their names here, since the types we accept as names are also valid
headings on their own.

The generic function |print-entry-heading| accepts a |&rest| argument only
because it's called from a \.{\~/.../} |format| directive; we always ignore
the extra arguments.

@l
(defgeneric print-entry-heading (stream heading &rest args &key &allow-other-keys))

(defmethod print-entry-heading (stream (heading heading) &key)
  (print-entry-heading stream (slot-value heading 'name))
  (when (sub-heading heading)
    (write-char #\Space stream)
    (print-entry-heading stream (sub-heading heading))))

(defmethod print-entry-heading (stream (heading namespace) &key)
  (write-string (heading-name heading) stream))

(defmethod print-entry-heading (stream (heading character) &key)
  (print-char stream heading))

(defmethod print-entry-heading (stream (heading string) &key)
  (write-char #\{ stream)
  (print-TeX stream (read-TeX-from-string heading))
  (write-char #\} stream))

(defmethod print-entry-heading (stream (heading symbol) &key)
  (format stream "\\(~W\\)" heading))

(defmethod print-entry-heading :before (stream (heading pretty-heading) &key)
  (write-string (macro-heading heading) stream))

@1*Coda: extending the indexer. Here's a self-contained example of how one
might extend the indexer to recognize and record specific kinds of forms.
In this program, we define reader macro functions for most of the standard
macro characters. It might be nice to have dedicated index entries for
those definitions that show which macro character is defined where.

@ To begin, we'll define a heading class for macro characters, a subclass
for dispatch macro characters, and a constructor function for both. This
example is slightly atypical in this regard: most index extensions would
simply use a new namespace class and use that as their heading, but we have
some specialized sorting requirements that are easiest to fulfill in this
way. It's also a bit of a semantic stretch to call macro characters a
`namespace'.

@l
(defclass macro-char-heading (heading)
  ((name :reader macro-char :initarg :char)))

(defclass dispatch-macro-char-heading (macro-char-heading)
  ((sub-char :reader macro-sub-char :initarg :sub-char)))

(defmethod sub-heading ((heading dispatch-macro-char-heading))
  (macro-sub-char heading))

(defun make-macro-char-heading (char &optional ;
                                (sub-char nil sub-char-supplied-p))
  (if sub-char-supplied-p
      (make-instance 'dispatch-macro-char-heading ;
                     :char char ;
                     :sub-char (and (characterp sub-char) sub-char))
      (make-instance 'macro-char-heading :char char)))

@ When the macro character headings are printed to the index, we'll attach
a little label describing what kind of character they are.

@l
(defmethod print-entry-heading :after (stream (heading macro-char-heading) &key)
  (format stream " ~:[~;dispatch ~]macro character"
          (typep heading 'dispatch-macro-char-heading)))

@ We'd like the macro character index entries to precede all of the other
entries, and we'd like non-dispatching macro chars before dispatching chars.
Most types of index entries wouldn't bother with this; they'd just be mixed
in with the others in the normal lexicographic ordering.

@l
(defmethod entry-heading-lessp ((h1 macro-char-heading) h2)
  (declare (ignore h2))
  t)
(defmethod entry-heading-lessp (h1 (h2 macro-char-heading))
  (declare (ignore h1))
  nil)
(defmethod entry-heading-lessp ((h1 macro-char-heading) ;
                                (h2 dispatch-macro-char-heading))
  t)
(defmethod entry-heading-lessp ((h1 dispatch-macro-char-heading) ;
                                (h2 macro-char-heading))
  nil)
(defmethod entry-heading-lessp ((h1 macro-char-heading) (h2 macro-char-heading))
  (char-lessp (macro-char h1) (macro-char h2)))
(defmethod entry-heading-lessp ((h1 dispatch-macro-char-heading) ;
                                (h2 dispatch-macro-char-heading))
  (and (not (char-lessp (macro-char h2) (macro-char h1)))
       (or (and (not (macro-sub-char h1)) (macro-sub-char h2))
           (and (macro-sub-char h1)
                (macro-sub-char h2)
                (char-lessp (macro-sub-char h1) (macro-sub-char h2))))))

@ We also need an equality predicate. We'll say that no macro character
heading is equal to anything other than another macro character heading,
and that two such headings are equal if their primary and secondary
characters are the same (ignoring differences of case).

@l
(defmethod entry-heading-equalp ((h1 macro-char-heading) h2)
  (declare (ignore h2))
  nil)
(defmethod entry-heading-equalp (h1 (h2 macro-char-heading))
  (declare (ignore h1))
  nil)
(defmethod entry-heading-equalp ((h1 macro-char-heading) ;
                                 (h2 macro-char-heading))
  (and (char-equal (macro-char h1) (macro-char h2))
       (equalp (sub-heading h1) (sub-heading h2))))

@t We'll use the strict comparison functions we defined above for testing
|entry-heading-lessp| and |entry-heading-equalp|.

@l
(deftest macro-char-heading-lessp
  (let* ((a (make-macro-char-heading #\a))
         (b (make-macro-char-heading #\b))
         (ab (make-macro-char-heading #\a #\b))
         (ac (make-macro-char-heading #\a #\c)))
    (every #'identity
           (list (entry-heading-strictly-lessp a b)
                 (not (entry-heading-strictly-lessp b a))
                 (entry-heading-strictly-lessp a ab)
                 (entry-heading-strictly-lessp b ab)
                 (not (entry-heading-strictly-lessp ab ab))
                 (entry-heading-strictly-lessp ab ac))))
  t)

(deftest macro-char-heading-equalp
  (let* ((a (make-macro-char-heading #\a))
         (b (make-macro-char-heading #\b))
         (ab (make-macro-char-heading #\a #\b)))
    (every #'identity
           (list (entry-heading-symmetric-equalp a a)
                 (entry-heading-symmetric-unequalp a b)
                 (entry-heading-symmetric-unequalp b a)
                 (entry-heading-symmetric-unequalp a ab)
                 (entry-heading-symmetric-equalp ab ab))))
  t)

@ Next, we'll tell the indexer that the symbols |set-macro-character| and
|set-dispatch-macro-character| are `interesting' and that they should be
replaced with referring symbols. (In general, this is dangerous for symbols
in the Common Lisp package, so be careful.)

@l
(defmethod interesting-symbol-p ((object (eql 'set-macro-character))) ;
  t)
(defmethod interesting-symbol-p ((object (eql 'set-dispatch-macro-character))) ;
  t)

@ And finally, we'll add some methods to |walk-compound-form| specialized
on those function names. We're relying here on the around~method specialized
on |indexing-walker| that swaps out referring symbols for the |operator|
argument but leaves them as the car of the |form|. Also notice that by
overriding the default method and not calling |index-name|, we can prevent
the functions themselves from being indexed, which is what we want in this
case.

@l
(defmethod walk-compound-form ;
    ((walker indexing-walker) (operator (eql 'set-macro-character))
     form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (symbol section) (symbol-provenance (car form))
    (when (and section (characterp (second form)))
      (add-index-entry (walker-index walker)
                       (make-macro-char-heading (second form))
                       section t))
    `(,symbol ,@(walk-list walker (cdr form) env))))

(defmethod walk-compound-form ;
    ((walker indexing-walker) (operator (eql 'set-dispatch-macro-character))
     form env &key toplevel)
  (declare (ignore toplevel))
  (multiple-value-bind (symbol section) (symbol-provenance (car form))
    (when (and section (characterp (second form)))
      (add-index-entry (walker-index walker)
                       (make-macro-char-heading (second form) (third form))
                       section t))
    `(,symbol ,@(walk-list walker (cdr form) env))))

@t@l
(define-indexing-test macro-character
  '((:section :code ((set-macro-character #\! '#:read-bang)))
    (:section :code ((set-dispatch-macro-character #\@ #\! '#:read-at-bang))))
  ("!" ((:def 0)))
  ("@ !" ((:def 1))))

@*Index.
@t*Index.

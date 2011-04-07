% -*-CLWEB-*-
\font\sc=cmcsc10
\font\tenec=ecrm1000
\font\eighttt=cmtt8
\def\ldq{{\tenec \char'23}} % left guillemet
\def\rdq{{\tenec \char'24}} % right guillemet
\def\pb{\.{|...|}} % program brackets
\def\v{\.{\char'174}} % vertical bar in typewriter font
\def\WEB{{\tt WEB}}
\def\CWEB{{\tt CWEB}}
\def\CLWEB{{\tt CLWEB}}
\def\EOF{{\sc eof}}
\def\progname{{\eighttt CLWEB}}
\def\etc.{{\it \char`&c.\spacefactor1000}}
\def\<#1>{\leavevmode\hbox{$\mkern-2mu\langle${\it #1\/}$\rangle$}}
\def\ansi{{\sc ansi}}
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

Our tangler has two main interface functions: |tangle-file| and |load-web|.
The first is analogous to |compile-file|: given a file containing \CLWEB\
source, it produces an output file that can be subsequently loaded into a
Lisp image with |load|. The function |load-web| is analogous to |load|,
but also accepts \CLWEB\ source as input instead of ordinary Lisp source:
it loads a web into the Lisp environment.

The weaver has a single entry point: |weave| takes a web as input and
generates a file that can be fed to \TeX\ to generate a pretty-printed
version of that web.

@1*System construction. We'll start by setting up a package for the system.
In addition to the top-level tangler and weaver functions mentioned above,
there's also |load-sections-from-temp-file|, which is conceptually part of
the tangler, but is a special-purpose routine designed to be used in
conjunction with an editor such as Emacs to provide incremental
redefinition of sections; the user will generally never need to call it
directly. Then there are a few global variables that control various
operations of the weaver. The remainder of the exported symbols are
condition classes for the various errors and warnings that might be
signaled while processing a web.

@l
(provide "CLWEB")

@e
(eval-when (:compile-toplevel :load-toplevel :execute)
  #+sbcl (require "SB-CLTL2"))
@e
(defpackage "CLWEB"
  (:use "COMMON-LISP"
        #+sbcl "SB-CLTL2"
        #+allegro "SYS"
        #+ccl "CCL")
  (:export "TANGLE-FILE"
           "LOAD-WEB"
           "WEAVE"
           "LOAD-SECTIONS-FROM-TEMP-FILE"
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
  (:shadow "ENCLOSE"
           #+allegro "FUNCTION-INFORMATION"
           #+allegro "VARIABLE-INFORMATION"))
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

@1*Utilities.

@ Here's a little utility function that we'll use often. It's particularly
useful for functions that accept a list desginator.

@l
(defun ensure-list (object)
  (if (listp object) object (list object)))

@ And here's one taken from {\sc pcl}: |mapappend| is like |mapcar| except
that the results are appended together.

@l
(defun mapappend (function &rest args)
  (if (some #'null args)
      ()
      (append (apply function (mapcar #'car args))
              (apply #'mapappend function (mapcar #'cdr args)))))

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
       (dolist (,spec ',sections)
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
If it is not already present and the |:insert-if-not-found| argument
is true, a new node is created with that key and added to the tree. The
arguments |:predicate| and |:test| should be designators for functions
of two arguments, both of which will be node keys; |:predicate| should
return true iff its first argument precedes its second in the total
ordering used for the tree, and |:test| should return true iff the two
keys are to be considered equivalent.

Two values are returned: the node with key |item| (or |nil| if no such node
was found and |:insert-if-not-found| is false), and a boolean representing
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
  (section-number (first (named-section-sections section))))

@t@l
(deftest named-section-number/code
  (with-temporary-sections
      ((:section :name "foo" :code (1))
       (:section :name "foo" :code (2))
       (:section :name "foo" :code (3)))
    (let ((section (find-section "foo")))
      (values (section-code section)
              (section-number section))))
  (1 2 3)
  0)

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
might be abbreviations. We'll use these as the |:test| and |:predicate|
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
characters with a single space.

@l
(defun squeeze (string)
  (loop with squeezing = nil
        for char across (string-trim *whitespace* string)
        if (not squeezing)
          if (whitespacep char)
            do (setq squeezing t) and collect #\Space into chars
          else
            collect char into chars
        else
          unless (whitespacep char)
            do (setq squeezing nil) and collect char into chars
        finally (return (coerce chars 'string))))

@t@l
(deftest (squeeze 1) (squeeze "abc") "abc")
(deftest (squeeze 2) (squeeze "ab c") "ab c")
(deftest (squeeze 3) (squeeze (format nil " a b ~C c " #\Tab)) "a b c")

@ Clozure Common Lisp provides a suitable definition for this predicate, but
it's simple enough to define it ourselves. Note, however, that this routine
does not---and can not, at least not portably---look at the current readtable
to determine what characters currently have whitespace syntax.
@^Clozure Common Lisp@>

@l
#-ccl
(defun whitespacep (char) (find char *whitespace* :test #'char=))

@ This list should contain the characters named `Space', `Tab', `Newline',
`Linefeed', `Page', and~`Return', in that order. However, `Linefeed' might
be the same character as `Newline' or `Return', and so might not appear as
a distinct character. This is a known bug, caused by the fact that we're
not currently overriding the character name reader.
@^bug, known@>

@<Glob...@>=
(defparameter *whitespace*
  #.(coerce '(#\Space #\Tab #\Newline #\Linefeed #\Page #\Return) 'string))

@ The next routine is our primary interface to named sections: it looks up
a section by name in the tree, and creates a new one if no such section
exists.

@l
(defun find-section (name &aux (name (squeeze name)))
  (if (null *named-sections*)
      (values (setq *named-sections* (make-instance 'named-section :name name));
              nil)
      (multiple-value-bind (section present-p)
          (find-or-insert name *named-sections*)
        (when present-p
          @<Update the section name if the new one is better@>)
        (values section present-p))))

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
      ((:section :name "foo" :code (:foo))
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
will modify the readtables themselves, the |*readtables*| list is never
changed once it's initialized.

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

@ The following macro is just a bit of syntactic sugar for executing the
given forms with |*readtable*| bound appropriately for the given mode.

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

@ We frequently need an object to use as the |eof-value| argument to
|read|. It need not be a symbol; it need not even be an atom.

@<Global variables@>=
(defvar *eof* (make-symbol "EOF"))

@ @l
(defun eof-p (object) (eq object *eof*))
(deftype eof () '(satisfies eof-p))

@t@l
(deftest eof-p (eof-p (read-from-string "" nil *eof*)) t)
(deftest eof-type (typep (read-from-string "" nil *eof*) 'eof) t)

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
stream whose position they're tracking, and it's these proxy streams that
we'll pass around, so that the standard stream functions will all work.
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
(defvar *tab-width* 8)

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
  (with-unique-names (in out closing)
    `(let* ((,out (make-string-output-stream))
            (,var (make-echo-stream ,stream ,out))
            (,closing (list ,out ,var)))
       (flet ((,rewind ()
                (let ((,in (make-string-input-stream ;
                            (get-output-stream-string ,out))))
                  (prog1 (setq ,var (make-concatenated-stream ,in ,var))
                    (push ,var ,closing)
                    (push ,in ,closing)))))
         (unwind-protect (progn ,@body)
           (map nil #'close ,closing))))))

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
  (with-unique-names (out echo raw-output length)
    `(with-open-stream (,out (make-string-output-stream))
       (with-open-stream (,echo (make-echo-stream ,stream ,out))
         (let* ((,object (read-preserving-whitespace ,echo))
                (,raw-output (get-output-stream-string ,out))
                (,length (length ,raw-output))
                (,echoed (subseq ,raw-output
                                 0
                                 (if (or (eof-p (peek-char nil ,echo nil *eof*))
                                         (token-delimiter-p ;
                                          (elt ,raw-output (1- ,length))))
                                     ,length
                                     (1- ,length)))))
           (declare (ignorable ,object ,echoed))
           ,@body)))))

@t@l
(deftest read-with-echo
  (with-input-from-string (stream  ":foo :bar")
    (read-with-echo (stream object chars)
      (values object chars)))
  :foo ":foo ")

(deftest read-with-echo-to-eof
  (with-input-from-string (stream ":foo")
    (read-with-echo (stream object chars)
      (values object chars)))
  :foo ":foo")

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

@l
@<Define the function |set-tangle-dispatch|@>

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
    (case (peek-char nil stream nil *eof* t)
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
           (push *consing-dot* list)
           (push charpos charpos-list))
          (t (rewind)
             @<Read the next object...@>))))

@t@l
(deftest read-list-error
  (handler-case (read-form-from-string "(. a)")
    (reader-error () :error))
  :error)

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

@ We use conses to represent backquoted forms, but we use instances of
a dedicated class to represent commas, which simplifies both the processing
code and the pretty-printing routines.

@l
(defvar *backquote* (make-symbol "BACKQUOTE"))
(defun backquotep (object) (eq object *backquote*))
(deftype backquote () '(cons (satisfies backquotep)))

(defclass comma ()
  ((form :initarg :form)))
(defclass splicing-comma (comma)
  ((modifier :reader comma-modifier :initarg :modifier)))

(defun commap (obj) (typep obj 'comma))

@ To process a comma, we need to tangle the form that followed it. If that
form is a named section reference, we take the |car| of the tangled form,
on the assumption that you can't meaningfully unquote more than one form.
This violation of the general principle that named section expansion has
splicing semantics is a consequence of our using the Lisp reader to process
both web syntax and Lisp.

@l
(defgeneric comma-form (comma))
(defmethod comma-form ((comma comma))
  (let* ((form (slot-value comma 'form))
         (tangled-form (tangle form)))
    (typecase form
      (named-section
       (when (rest tangled-form)
         (cerror "Ignore the extra forms."
                 "Tried to unquote more than one form from section @<~A@>."
                 (section-name form)))
       (first tangled-form))
      (t tangled-form))))

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
        ((#\@ #\.) (make-instance 'splicing-comma
                                  :modifier (read-char stream t nil t)
                                  :form (read stream t nil t)))
        (otherwise (make-instance 'comma :form (read stream t nil t)))))
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
    (vector `(apply #'vector ,(bq-process (coerce x 'list))))
    (splicing-comma (error ",~C~S after `" (comma-modifier x) (comma-form x)))
    (comma (comma-form x))
    (atom `(quote ,x))
    (backquote (bq-process (bq-process (cadr x))))
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

(deftest (bq vector)
  (let ((a '(1 2 3)))
    (declare (special a))
    (values (eval (tangle (read-form-from-string "`#(:a)")))
            (eval (tangle (read-form-from-string "`#(,a)")))
            (eval (tangle (read-form-from-string "`#(,@a)")))))
  #(:a)
  #((1 2 3))
  #(1 2 3))

@t Test the interaction between backquote, comma, and named sections.

@l
(deftest (bq named-section)
  (with-sample-named-sections
    (values (eval (tangle (read-form-from-string "`(, @<foo@>)")))
            (eval (tangle (read-form-from-string "`(,@ @<foo@>)")))))
  (:foo)
  :foo)

(deftest (bq too-many-forms)
  (let ((*named-sections* *sample-named-sections*)
        (handled nil))
    (handler-bind ((error (lambda (condition)
                            (setq handled t)
                            (continue condition))))
      (values (eval (tangle (read-form-from-string "`(,@ @<quux@>)")))
              handled)))
  :quux
  t)

@ During tangling, we print backquotes and commas using the backquote
syntax, as recommended (but not required) by section~2.4.6.1 of the
\ansi\ standard.
@^\ansi\ Common Lisp@>

@l
(set-tangle-dispatch 'backquote
  (lambda (stream obj)
    (format stream "`~W" (cadr obj))))

(set-tangle-dispatch 'splicing-comma
  (lambda (stream obj)
    (format stream ",~C~W" (comma-modifier obj) (comma-form obj)))
  1)

(set-tangle-dispatch 'comma
  (lambda (stream obj)
    (format stream ",~W" (comma-form obj))))

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
   (elements :initarg :elements)
   (element-type :initarg :element-type))
  (:default-initargs :element-type t))

(defmethod marker-boundp ((marker simple-vector-marker)) t)
(defmethod marker-value ((marker simple-vector-marker))
  (with-slots (elements element-type) marker
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
  (marker-value (read-form-from-string "#5(:a :b :c)"))
  #(:a :b :c :c :c))

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
(loop for char = (read-char stream nil #\Space t)
      while (or (char= char #\0) (char= char #\1))
      collect (ecase char (#\0 0) (#\1 1))
      finally (unread-char char stream))

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
  (let* ((*readtable* (if *evaluating* (readtable-for-mode nil) *readtable*))
         (form (read stream t nil t)))
    (unless *read-suppress*
      (unless *read-eval*
        (simple-reader-error stream "can't read #. while *READ-EVAL* is NIL"))
      (make-instance 'read-time-eval-marker :form form :value (eval form)))))

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
    (format stream "#~:[-~;+~]~S ~A"
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
    (peek-char t stream t nil t)
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
         (conditional (marker-value (read-form-from-string "#-a 1"))))
    (values (read-time-conditional-plusp conditional)
            (read-time-conditional-test conditional)
            (read-time-conditional-form conditional)))
  nil :a "1")

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
    (loop for char = (peek-char nil stream nil *eof* nil)
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
                       stream nil *eof* nil)))
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
                       stream nil *eof* nil)))
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
                       stream nil *eof* nil)))
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
                 (tangle-1 form
                           :expand-named-sections expand-named-sections)
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
does {\it not\/} initialize the global variables like |*named-sections*|;
this allows for incremental redefinition.
@.clweb.el@>

@l
(defun load-sections-from-temp-file (file append &aux
                                     (truename (probe-file file)))
  "Load web sections from FILE, then delete it."
  (when truename
    (unwind-protect
         (with-open-file (stream truename :direction :input)
           (load-web-from-stream stream t :append append))
      (delete-file truename))))


@ Both |tangle-file| and |weave|, below, take a |tests-file| argument that
has slightly hairy defaulting behavior. If it's supplied and is non-|nil|,
then we use a pathname derived from the one given by merging in a default
type (`\.{LISP}' in the case of tangling, `\.{TEX}' for weaving). If it's
not supplied, then we construct a pathname from the output file by
appending the string \.{"-TESTS"} to its name component. Finally, if the
argument is supplied and is |nil|, then no tests file will be written at
all.

@l
(defun tests-file-pathname (output-file type &key ;
                            (tests-file nil tests-file-supplied-p) ;
                            &allow-other-keys)
  (if tests-file
      (merge-pathnames tests-file (make-pathname :type type :case :common))
      (unless tests-file-supplied-p
        (merge-pathnames
         (make-pathname :name (concatenate 'string ;
                                           (pathname-name output-file ;
                                                          :case :common) ;
                                           "-TESTS")
                        :type type
                        :case :common)
         output-file))))

@t@l
(deftest (tests-file-pathname 1)
  (equal (tests-file-pathname (make-pathname :name "FOO" :case :common) "LISP"
                              :tests-file (make-pathname :name "BAR" ;
                                                         :case :common))
         (make-pathname :name "BAR" :type "LISP" :case :common))
  t)

(deftest (tests-file-pathname 2)
  (equal (tests-file-pathname (make-pathname :name "FOO" :case :common) "TEX")
         (make-pathname :name "FOO-TESTS" :type "TEX" :case :common))
  t)

(deftest (tests-file-pathname 3)
  (tests-file-pathname (make-pathname :name "FOO" :case :common) "LISP"
                       :tests-file nil)
  nil)

@ We'll use a custom pprint-dispatch table for tangling to avoid cluttering
the default table.

@<Global variables@>=
(defparameter *tangle-pprint-dispatch* (copy-pprint-dispatch nil))

@ @<Define the function |set-tangle-dispatch|@>=
(defun set-tangle-dispatch (type-specifier function &optional (priority 0))
  (set-pprint-dispatch type-specifier function priority ;
                       *tangle-pprint-dispatch*))

@ The file tangler operates by writing out the tangled code to a Lisp source
file and then invoking the file compiler on that file. The arguments are
essentially the same as those to |compile-file|, except for the |tests-file|
keyword argument, which specifies the file to which the test sections' code
should be written (see~|tests-file-pathname|, above, for the defaulting).

We return the values returned by invoking |compile-file| on the tangled
file, but we actually compile the tests file, if any, {\it after\/} the
tangled file, on the assumption that the tests might require a module
provided by the output file. Note that this might cause the output file
to be unintentionally loaded; the work-around is to disable production
of the tests file by supplying |:tests-file nil|.

@l
(defun tangle-file (input-file &rest args &key
                    output-file
                    tests-file
                    (verbose *compile-verbose*)
                    (print *compile-print*)
                    (external-format :default) &allow-other-keys &aux
                    @<Merge defaults for tangler file names@>
                    (*tangle-file-pathname* input-file)
                    (*tangle-file-truename* (truename *tangle-file-pathname*))
                    (*readtable* *readtable*)
                    (*package* *package*))
  "Tangle and compile the web in INPUT-FILE, producing OUTPUT-FILE."
  (declare (ignorable output-file tests-file))
  (when verbose (format t "~&; tangling web from ~A:~%" input-file))
  @<Initialize global variables@>
  (with-open-file (input input-file
                   :direction :input
                   :external-format external-format)
    (read-sections input))
  @<Complain about any unused named sections@>
  (flet ((write-forms (sections output-file)
           (with-open-file (output output-file
                            :direction :output
                            :if-exists :supersede
                            :external-format external-format)
             (format output ";;;; TANGLED WEB FROM \"~A\". DO NOT EDIT.~%" ;
                     input-file)
             (let ((*evaluating* nil)
                   (*print-pprint-dispatch* *tangle-pprint-dispatch*)
                   (*print-level* nil))
               @<Output a form that sets the source pathname@>
               (dolist (form (tangle (unnamed-section-code-parts sections)))
                 (pprint form output))))))
    (when (and tests-file ;
               (> (length *test-sections*) 1)) ; there's always a limbo section
      (when verbose (format t "~&; writing tests to ~A~%" tests-file))
      (write-forms *test-sections* tests-file))
    (when verbose (format t "~&; writing tangled code to ~A~%" lisp-file))
    (write-forms *sections* lisp-file)
    (multiple-value-prog1
        (apply #'compile-file lisp-file :allow-other-keys t args)
      (when tests-file
        (compile-file tests-file ; use default output file
                      :verbose verbose
                      :print print
                      :external-format external-format)))))

@ @<Merge defaults for tangler...@>=
(input-file (merge-pathnames input-file ;
                             (make-pathname :type "CLW" :case :common)))
(output-file (apply #'compile-file-pathname ;
                    input-file :allow-other-keys t args))
(lisp-file (merge-pathnames (make-pathname :type "LISP" :case :common) ;
                            output-file))
(tests-file (apply #'tests-file-pathname output-file "LISP" args))

@ During tangling, we bind |*tangle-file-pathname*| and
|*tangle-file-truename*| in the same way that |compile-file| binds
|*compile-file-pathname*| and |*compile-file-truename*|.

@<Global variables@>=
(defvar *tangle-file-pathname* nil)
(defvar *tangle-file-truename* nil)

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
(defun weave (input-file &rest args &key
              output-file
              tests-file
              (index-file nil index-file-supplied-p)
              (verbose *weave-verbose*)
              (print *weave-print*)
              (if-does-not-exist t)
              (external-format :default) &aux
              @<Merge defaults for weaver file names@>
              (*readtable* *readtable*)
              (*package* *package*))
  "Weave the web contained in INPUT-FILE, producing the TeX file OUTPUT-FILE."
  (declare (ignorable tests-file))
  (when verbose (format t "~&; weaving web from ~A:~%" input-file))
  @<Initialize global variables@>
  (with-open-file (input input-file
                   :direction :input
                   :external-format external-format
                   :if-does-not-exist (if if-does-not-exist :error nil))
    (read-sections input))
  (when (and tests-file ;
             (> (length *test-sections*) 1)) ; there's always a limbo section
    (when verbose (format t "~&; weaving tests to ~A~%" tests-file))
    (weave-sections *test-sections*
                    :input-file input-file
                    :output-file tests-file
                    :verbose verbose
                    :print print
                    :external-format external-format
                    :weaving-tests t))
  (when verbose (format t "~&; weaving sections to ~A~%" output-file))
  (weave-sections *sections*
                  :input-file input-file
                  :output-file output-file
                  :index-file index-file
                  :sections-file sections-file
                  :verbose verbose
                  :print print
                  :external-format external-format))

@ In keeping with the usual behavior of both Lisp and \TeX, the type of
the input file may be omitted; it defaults to `\.{CLW}'.

If |output-file| is not supplied or is |nil|, a pathname will be generated
from |input-file| by replacing its |type| component with `\.{TEX}'.

The |tests-file| argument is derived from the given file name and the output
file name by |tests-file-pathname|, which see.

If |index-file| is not supplied or is supplied and non-null, an index of
variables, functions, classes, \etc. will be written to the indicated file.
The default file name is generated from |output-file| by replacing its
|type| component with `\.{IDX}'. In addition, a list of section names will
be written to a file whose name is generated from the index file name by
replacing its type component with `\.{SCN}'.

@<Merge defaults for weaver...@>=
(input-file (merge-pathnames input-file ;
                             (make-pathname :type "CLW" :case :common)))
(output-file (if output-file
                 (merge-pathnames output-file ;
                                  (make-pathname :type "TEX" :case :common))
                 (merge-pathnames (make-pathname :type "TEX" :case :common) ;
                                  input-file)))
(tests-file (apply #'tests-file-pathname output-file "TEX" args))
(index-file (if index-file
                (merge-pathnames index-file ;
                                 (make-pathname :type "IDX" :case :common))
                (when (not index-file-supplied-p)
                  (merge-pathnames (make-pathname :type "IDX" :case :common) ;
                                   output-file))))
(sections-file (when index-file
                 (merge-pathnames (make-pathname :type "SCN" :case :common) ;
                                  index-file)))

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
(defun weave-sections (sections &key
                       input-file output-file index-file sections-file
                       weaving-tests verbose print external-format)
  (flet ((weave (object stream)
           (write object
                  :stream stream ;
                  :case :downcase :escape nil :level nil
                  :pretty t :pprint-dispatch *weave-pprint-dispatch* ;
                  :right-margin 1000)))
    (macrolet ((with-output-file ((stream filespec) &body body)
                 `(with-open-file (,stream ,filespec
                                   :direction :output
                                   :external-format external-format
                                   :if-exists :supersede)
                    ,@body)))
      (with-output-file (out output-file)
        (format out "\\input clwebmac~%")
        (when weaving-tests
          @<Write the program name to the tests output file@>)
        (if print
            @<Weave the sections to the output file, reporting as we go@>
            (map nil (lambda (section) (weave section out)) sections))
        (when index-file
          (when verbose (format t "~&; writing the index to ~A~%" index-file))
          (with-output-file (idx index-file)
            (weave (index-sections sections) idx))
          (with-output-file (scn sections-file)
            (map-bst (lambda (section)
                       (unless (every #'test-section-p ;
                                      (named-section-sections section))
                         (weave (make-section-name-index-entry section) scn)))
                     *named-sections*))
          (format out "~&\\inx~%\\fin~%\\con~%"))
        (format out "~&\\end~%")
        (truename out)))))

@ We'll use the pretty printer to print the section numbers to standard
output as we weave them. Starred sections get a `\.{*}' prefix, and the
whole of the output is in the form of a comment.

@<Weave the sections...@>=
(flet ((weave-section (section)
         (format t "~:[~;*~]~D" ;
                 (starred-section-p section) ;
                 (section-number section))
         (weave section out)))
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
The rest of the weaver proper consists entirely of pretty-printing routines
that we'll install in that table.

@<Global variables@>=
(defparameter *weave-pprint-dispatch* (copy-pprint-dispatch nil))

@ @l
(defun set-weave-dispatch (type-specifier function &optional (priority 0))
  (set-pprint-dispatch type-specifier function priority ;
                       *weave-pprint-dispatch*))

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
            for forms = (read-preserving-whitespace stream nil *eof* nil)
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
Then comes the code, which we output one form at a time, using tabs for
every line unless it's atomic. Last come the cross-references and a final
\.{\\fi} that matches the \.{\\ifon} in \.{\\M} and \.{\\N}.

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
      (format stream "${}~:[\\mathrel+~;~]\\E{}$~%"
              (= (section-number section) (section-number named-section))))
    (when code
      (dolist (form code)
        (if (or (list-marker-p form) (listp form))
            (format stream "~@<\\+~@;~W~;\\cr~:>" form)
            (format stream "~W~:[\\par~;~]" form (newlinep form))))
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
  (format stream "\\fi~%"))

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
  '((" \\%&#$^_~" . #\\) ("{" . "$\\{$") ("}" . "$\\}$")))

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
  (loop with *print-escape-list* = `(("{*}" . #\\)
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
        (*print-escape-list* `(("{}" . #\\) ,@*print-escape-list*)))
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
    ("<" . "$<$")
    (">" . "$>$")
    ("-" . "$-$")
    ("+" . "$+$")
    ("=" . "$=$")))

@ A few symbols get special replacements.

@l
(macrolet ((weave-symbol (symbol replacement)
             `(set-weave-dispatch '(eql ,symbol)
                (lambda (stream obj)
                  (declare (ignore obj))
                  (write-string ,replacement stream))
                1)))
  (weave-symbol lambda "\\L")
  (weave-symbol pi "$\\pi$"))

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
(defstruct (logical-block (:constructor make-logical-block (list)))
  list)

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
instead of a logical block structure. This allows the printer to elide the
alignment tabs, and makes the resulting \TeX\ much simpler.

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
(set-weave-dispatch 'backquote
  (lambda (stream obj)
    (format stream "\\`~W" (cadr obj))))

@ Note that |comma-form| method tangles the form, whence the raw slot access.

@l
(set-weave-dispatch 'splicing-comma
  (lambda (stream obj)
    (format stream "\\CO{~C}~W" (comma-modifier obj) (slot-value obj 'form)))
  1)

(set-weave-dispatch 'comma
  (lambda (stream obj)
    (format stream "\\CO{}~W" (slot-value obj 'form))))

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
(set-weave-dispatch 'read-time-conditional-marker
  (lambda (stream obj)
    (format stream "\\#~:[--~;+~]\\RC{~S ~/clweb::print-escaped/}"
            (read-time-conditional-plusp obj)
            (read-time-conditional-test obj)
            (read-time-conditional-form obj))))

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

@ We'll pass around instances of a |walker| class during our code walk
to provide a hook (via subclassing) for overriding walker methods.

@l
(defclass walker () ())

@ The walker protocol consists of a handful of generic functions, which
we'll describe as we come to them.

@l
@<Walker generic functions@>

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
(unless (fboundp 'ensure-portable-walking-environment)
  (defun ensure-portable-walking-environment (env) env))

@ Allegro doesn't define |parse-macro| or |enclose|, so we'll need
to provide our own definitions. In fact, we'll use our own version
of |enclose| on all implementations (note that it's shadowed in
the package definition at the beginning of the program). Thanks
to Duane Rettig of Franz,~Inc.\ for the idea behind this trivial
implementation (post to comp.lang.lisp of 18~Oct, 2004, message-id
\<4is97u4vv.fsf@@franz.com>).
@^Allegro Common Lisp@>

@l
(defun enclose (lambda-expression &optional env ;
                (walker (make-instance 'walker)))
  (coerce (walk-form walker lambda-expression env) 'function))

@ The following code for |parse-macro| is obviously extremely
implementation-specific; a portable version would be much more complex.
@^Allegro Common Lisp@>

@l
(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (fboundp 'parse-macro)
    (defun parse-macro (name lambda-list body &optional env)
      (declare (ignorable name lambda-list body env))
      #+allegro (excl::defmacro-expander `(,name ,lambda-list ,@body) env)
      #-allegro (error "PARSE-MACRO not implemented"))))

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

@ The main entry point for the walker is |walk-form|. The walk ordinarily
stops after encountering an atomic or special form; otherwise, we macro
expand and try again. If a walker method wants to decline to walk, however,
it may |throw| the given form, and the walk will continue with macro
expansion.

@l
(defmethod walk-form ((walker walker) form &optional env &aux
                      (env (ensure-portable-walking-environment env))
                      (expanded t))
  (flet ((symbol-macro-p (form env)
           (and (symbolp form)
                (eql (variable-information form env) :symbol-macro))))
    (loop
      (catch form
        (cond ((symbol-macro-p form env)) ; wait for macro expansion
              ((atom form)
               (return (walk-atomic-form walker :evaluated form env)))
              ((not (symbolp (car form)))
               (return (walk-list walker form env)))
              ((or (not expanded)
                   (walk-as-special-form-p walker (car form) form env))
               (return (walk-compound-form walker (car form) form env)))))
      (multiple-value-setq (form expanded)
        (macroexpand-for-walk walker form env)))))

@ @<Walker generic functions@>=
(defgeneric walk-form (walker form &optional env))

@ The walker will treat a form as a special form if and only if
|walk-as-special-form-p| returns true of that form.

@l
(defmethod walk-as-special-form-p (walker operator form env)
  (declare (ignore walker operator form env))
  nil)

@ @<Walker generic functions@>=
(defgeneric walk-as-special-form-p (walker operator form env))

@ Macroexpansion and environment augmentation both get wrapped in generic
functions to allow subclasses to override the usual behavior. The default
methods just call down to the normal Lisp functions.

@l
(defmethod macroexpand-for-walk ((walker walker) form env)
  (macroexpand-1 form env))

(defmethod augment-walker-environment ((walker walker) env &rest args)
  (apply #'augment-environment env args))

@ @<Walker generic functions@>=
(defgeneric macroexpand-for-walk (walker form env))
(defgeneric augment-walker-environment (walker env &rest args))

@ Here's a utility function we'll use often in walker methods: it walks
each element of the supplied list and returns a new list of the results
of those walks.

@l
(defun walk-list (walker list env)
  (do ((form list (cdr form))
       (newform () (cons (walk-form walker (car form) env) newform)))
      ((atom form) (nreconc newform form))))

@ The functions |walk-atomic-form| and |walk-compound-form| are the real
work-horses of the walker. Besides the walker instance, the form, and the
lexical environment, |walk-atomic-form| takes a keyword symbol denoting the
context in which the atom occurs, and |walk-compound-form| takes an
additional |operator| argument, |eql| to~|(car form)|, so that we can
use |eql|~specializers. The |operator| of a form passed to
|walk-compound-form| should always be a symbol or a \L~expression.

@<Walker generic functions@>=
(defgeneric walk-atomic-form (walker context form env &key))
(defgeneric walk-compound-form (walker operator form env))

@ The default method for |walk-atomic-form| simply returns the form.
Note that this function won't be called for symbol macros; those are
expanded in |walk-form|.

@l
(defmethod walk-atomic-form ((walker walker) context form env &key)
  (declare (ignore context env))
  form)

(defmethod walk-atomic-form ((walker walker) context (form cons) env &key)
  (declare (ignore env))
  (error "Unexpected non-atomic form ~S (~S)" form context))

@t@l
(deftest walk-atomic-form
  (walk-atomic-form (make-instance 'walker) nil ':foo nil)
  :foo)

(deftest walk-non-atomic-form
  (handler-case (walk-atomic-form (make-instance 'walker) nil '(a b c) nil)
    (error () nil))
  nil)

@ The default method for |walk-compound-form| is used for most funcall-like
forms; it leaves its |car| unevaluated and walks its |cdr|.

@l
(defmethod walk-compound-form ((walker walker) operator form env)
  (declare (ignore operator))
  `(,(walk-atomic-form walker :operator (car form) env)
    ,@(walk-list walker (cdr form) env)))

@ A compound form might also have a \L~expression as its |car|.

@l
(deftype lambda-expression () '(cons (eql lambda) (cons list *)))

(defmethod walk-compound-form ((walker walker) (operator cons) form env)
  (check-type operator lambda-expression)
  `(,(walk-lambda-expression walker operator env)
    ,@(walk-list walker (cdr form) env)))

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

@ Common Lisp defines a {\it function name\/} as ``[a] symbol or a list
|(setf symbol)|.'' Since they're not necessarily atomic, we define a special
walker function just for function names.

@l
(deftype setf-function-name () '(cons (eql setf) (cons symbol null)))
(defun setf-function-name-p (function-name)
  (typep function-name 'setf-function-name))

(defmethod walk-function-name ((walker walker) function-name env &key)
  (typecase function-name
    (symbol ;
     (walk-atomic-form walker :unevaluated function-name env))
    (setf-function-name ;
     `(setf ,(walk-atomic-form walker :unevaluated (cadr function-name) env)))
    (t (cerror "Use the function name anyway." ;
               'invalid-function-name :name function-name)
       function-name)))

@ @<Walker generic functions@>=
(defgeneric walk-function-name (walker function-name env &key &allow-other-keys))

@ @<Condition classes@>=
(define-condition invalid-function-name (parse-error)
  ((name :initarg :name :reader invalid-function-name))
  (:report (lambda (error stream)
             (format stream "~@<Invalid function name ~A.~:@>" ;
@.Invalid function name...@>
                     (invalid-function-name error)))))

@t@l
(deftest (walk-function-name symbol)
  (equal (walk-function-name (make-instance 'walker) 'foo nil)
         'foo)
  t)

(deftest (walk-function-name setf-function)
  (equal (walk-function-name (make-instance 'walker) '(setf foo) nil)
         '(setf foo))
  t)

(deftest (walk-function-name invalid)
  (let ((error-handled nil))
    (handler-bind ((invalid-function-name
                    (lambda (condition)
                      (setq error-handled t)
                      (continue condition))))
      (values (equal (walk-function-name (make-instance 'walker) '(foo bar) nil)
                     '(foo bar))
              error-handled)))
  t t)

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
  (walk-as-special-form catch)
  (walk-as-special-form if)
  (walk-as-special-form load-time-value)
  (walk-as-special-form multiple-value-call)
  (walk-as-special-form multiple-value-prog1)
  (walk-as-special-form progn)
  (walk-as-special-form progv)
  (walk-as-special-form setq)
  (walk-as-special-form tagbody)
  (walk-as-special-form throw)
  (walk-as-special-form unwind-protect))

@ The rest of the special form walkers we define will need methods
specialized on particular operators for both |walk-as-special-form-p|
and |walk-compound-form|. The following macro makes sure that these are
consistently defined.

@l
(defmacro define-special-form-walker (operator (walker form env &rest rest) ;
                                      &body body)
  (let ((oparg `(,(gensym "OPERATOR") (eql ',operator))))
    (flet ((arg-name (arg) (if (consp arg) (car arg) arg)))
      `(progn
         (defmethod walk-as-special-form-p (,walker ,oparg ,form ,env)
           (declare (ignorable ,@(mapcar #'arg-name `(,walker ,form ,env))))
           t)
         (defmethod walk-compound-form (,walker ,oparg ,form ,env ,@rest)
           (declare (ignorable ,@(mapcar #'arg-name `(,walker ,form ,env))))
           ,@body)))))

@t Many of the walker tests will be defined using the following macro,
which takes a name for the test, a form to be walked, and an optional
result. Neither the form nor the result will be evaluated. If the result
is omitted, it is assumed that the result of the walk should be the same
as the walked form.

@l
(defmacro define-simple-walker-test (name form &optional (result nil resultp))
  `(deftest (walk ,name)
     (let ((walker (make-instance 'walker)))
       (tree-equal (walk-form walker ',form) ,(if resultp `',result `',form)))
     t))

@ Block-like special forms have a |cdr| that begins with a single
unevaluated form, followed by zero or more evaluated forms.

@l
(macrolet ((define-block-like-walker (operator)
             `(define-special-form-walker ,operator ((walker walker) form env)
                `(,(car form)
                  ,(walk-atomic-form walker :unevaluated (cadr form) env)
                  ,@(walk-list walker (cddr form) env)))))
  (define-block-like-walker block)
  (define-block-like-walker return-from))

@t@l
(define-simple-walker-test block/return-from
  (block foo (return-from foo 4)))

@ The special form |the| takes an unevaluated type specifier and a form.
We can't sensibly do anything at all with a general type specifier, so
we simply won't walk it.

@l
(define-special-form-walker the ((walker walker) form env)
  `(,(car form)
    ,(cadr form)
    ,@(walk-list walker (cddr form) env)))

@t@l
(define-simple-walker-test the
  (the (or number nil) (sqrt 4)))

@ Quote-like special forms are entirely unevaluated.

@l
(macrolet ((define-quote-like-walker (operator)
             `(define-special-form-walker ,operator ((walker walker) form env)
                (declare (ignore walker env))
                form)))
  (define-quote-like-walker quote)
  (define-quote-like-walker go))

@t@l
(define-simple-walker-test quote 'foo)
(define-simple-walker-test go (go home))

@ |eval-when| takes a list of situations and some forms. We don't need to
do anything special with either.

@l
(define-special-form-walker eval-when ((walker walker) form env)
  `(,(car form)
    ,(walk-list walker (cadr form) env)
    ,@(walk-list walker (cddr form) env)))

@t@l
(define-simple-walker-test eval-when
  (eval-when (:compile-toplevel :load-toplevel :execute)
    (do-some-stuff)))

@ The |function| special form takes either a valid function name or a
\L~expression.

@l
(define-special-form-walker function ((walker walker) form env)
  `(,(car form)
    ,(typecase (cadr form)
       (lambda-expression (walk-lambda-expression walker (cadr form) env))
       (otherwise (walk-function-name walker (cadr form) env)))))

@t@l
(define-simple-walker-test function
  (function foo))

(define-simple-walker-test function-setf-function
  (function (setf foo)))

(define-simple-walker-test function-lambda
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

If |doc-string-allowed| is |nil| (the default), then no forms will be
treated as documentation strings.

@l
(defun parse-body (body &key doc-string-allowed walker env &aux doc)
  (flet ((doc-string-p (x remaining-forms)
           (and (stringp x) doc-string-allowed remaining-forms (null doc)))
         (declaration-p (x)
           (and (listp x) (eql (car x) 'declare))))
    (loop for forms = body then (cdr forms)
          as x = (car forms)
          while forms
          if (doc-string-p x (cdr forms)) do (setq doc x)
          else if (declaration-p x) append (cdr x) into decls
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

@ Declaration forms aren't evaluated in Common Lisp, but we'll want to be
able to walk the specifiers.

@<Walker generic functions@>=
(defgeneric walk-declaration-specifiers (walker decls env))

@ @l
(defmethod walk-declaration-specifiers ((walker walker) decls env)
  (declare (ignore env))
  decls)

@ The syntax of \L-lists is given in section~3.4 of the \ansi\ standard.
We accept the syntax of macro \L-lists, since they are the most general,
and appear to be a superset of every other type of \L-list.
@^\ansi\ Common Lisp@>

This function returns two values: the walked \L-list and a new environment
object containing bindings for all of the parameters found therein.

@l
(defun walk-lambda-list (walker lambda-list decls env &aux
                         new-lambda-list (state :reqvars))
  (labels ((augment-env (&rest vars &aux (vars (remove-if #'null vars)))
             (setq env (augment-walker-environment walker env ;
                                                   :variable vars ;
                                                   :declare decls)))
           (walk-var (var)
             (walk-atomic-form walker :binding var env))
           (update-state (keyword)
             (setq state (ecase keyword
                           ((nil) state)
                           (&optional :optvars)
                           ((&rest &body) :restvar)
                           (&key :keyvars)
                           (&aux :auxvars)
                           (&environment :envvar))))
           (maybe-destructure (var/pattern)
             (if (consp var/pattern)
                 (walk-lambda-list walker var/pattern decls env)
                 (values (walk-var var/pattern)
                         (augment-env var/pattern)))))
    @<Check for |&whole| and |&environment| vars, and augment the lexical
      environment with them if found@>
    (do* ((lambda-list lambda-list (cdr lambda-list))
          (arg (car lambda-list) (car lambda-list)))
         ((null lambda-list) (values (nreverse new-lambda-list) env))
      (ecase state
        (:envvar @<Process |arg| as an environment parameter@>)
        ((:reqvars :restvar) ; required and rest parameters have the same syntax
         @<Process |arg| as a required parameter@>)
        (:optvars @<Process |arg| as an optional parameter@>)
        (:keyvars @<Process |arg| as a keyword parameter@>)
        (:auxvars @<Process |arg| as an auxiliary variable@>))
      (when (or (atom lambda-list)
                (and (cdr lambda-list)
                     (atom (cdr lambda-list))))
        @<Process dotted rest var@>))))

@ A |&whole| variable must come first in a \L-list, and an |&environment|
variable, although it may appear anywhere in the list, must be bound along
with |&whole|. We'll pop a |&whole| variable off the front of |lambda-list|,
but we'll leave any |&environment| variable to be picked up later.

@<Check for |&whole| and |&environment|...@>=
(let ((wholevar (and (consp lambda-list)
                     (eql (car lambda-list) '&whole)
                     (push (pop lambda-list) new-lambda-list)
                     (car (push (walk-var (pop lambda-list)) new-lambda-list))))
      (envvar (do ((lambda-list lambda-list (cdr lambda-list)))
                  ((atom lambda-list) nil)
                (when (eql (car lambda-list) '&environment)
                  (return (cadr lambda-list))))))
  (augment-env wholevar envvar))

@ We've already added the environment variable to our lexical environment,
so we just push it onto the new \L-list and prepare for the next parameter.

@<Process |arg| as an environment parameter@>=
(push (walk-var (pop lambda-list)) new-lambda-list)
(when (consp lambda-list)
  (update-state (car lambda-list)))

@ @<Process |arg| as a required parameter@>=
(etypecase arg
  (symbol @<Process the symbol in |arg| as a parameter@>)
  (cons
   (multiple-value-bind (pattern new-env)
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
   (destructuring-bind (var/pattern &optional init-form supplied-p-parameter) ;
       arg
     (when init-form
       (setq init-form (walk-form walker init-form env)))
     (multiple-value-setq (var/pattern env)
       (maybe-destructure var/pattern))
     (when supplied-p-parameter
       (augment-env supplied-p-parameter))
     (push (nconc (list var/pattern)
                  (and init-form (list init-form))
                  (and supplied-p-parameter (list supplied-p-parameter)))
           new-lambda-list))))

@ @<Process |arg| as a keyword parameter@>=
(cond ((eql arg '&allow-other-keys)
       (push (pop lambda-list) new-lambda-list)
       (update-state (car lambda-list)))
      (t
       (etypecase arg
         (symbol @<Process the symbol in |arg| as a parameter@>)
         (cons
          (destructuring-bind (var/kv &optional init-form supplied-p-parameter) arg
            (when init-form
              (setq init-form (walk-form walker init-form env)))
            (cond ((consp var/kv)
                   (destructuring-bind (keyword-name var/pattern) var/kv
                     (multiple-value-setq (var/pattern env)
                       (maybe-destructure var/pattern))
                     (setq var/kv (list (walk-var keyword-name) var/pattern))))
                  (t (setq var/kv (walk-var var/kv))
                     (augment-env var/kv)))
            (when supplied-p-parameter
              (setq supplied-p-parameter (walk-var supplied-p-parameter))
              (augment-env supplied-p-parameter))
            (push (nconc (list var/kv)
                         (and init-form (list init-form))
                         (and supplied-p-parameter (list supplied-p-parameter)))
                  new-lambda-list))))))

@ @<Process |arg| as an auxiliary variable@>=
(etypecase arg
  (symbol @<Process the symbol...@>)
  (cons
   (destructuring-bind (var &optional init-form) arg
     (setq var (walk-var var)
           init-form (and init-form (walk-form walker init-form env)))
     (augment-env var)
     (push (nconc (list var)
                  (and init-form (list init-form)))
           new-lambda-list))))

@ @<Process the symbol in |arg| as a parameter@>=
(cond ((member arg lambda-list-keywords)
       (push arg new-lambda-list)
       (update-state arg))
      (t (setq arg (walk-var arg))
         (augment-env arg)
         (push arg new-lambda-list)))

@ We normalize a dotted rest parameter into a proper |&rest| parameter
to avoid having to worry about reversing an improper |new-lambda-list|.

@<Process dotted rest var@>=
(let ((var (walk-var (if (consp lambda-list) (cdr lambda-list) lambda-list))))
  (augment-env var)
  (push '&rest new-lambda-list)
  (push var new-lambda-list))
(setq lambda-list nil)

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
(flet ((augment-env (var)
         (setq env (augment-walker-environment walker env ;
                                               :variable (list var) ;
                                               :declare decls)))
       (walk-var (spec)
         (etypecase spec
           (symbol (walk-atomic-form walker :binding spec env))
           (class-specializer
            (list (walk-atomic-form walker :binding (car spec) env)
                  (walk-atomic-form walker :class-specializer (cadr spec) env)))
           ((compound-specializer eql)
            (list (walk-atomic-form walker :binding (car spec) env)
                  `(eql ,(walk-form walker (cadadr spec))))))))
  (loop until (or (null lambda-list)
                  (member (car lambda-list) lambda-list-keywords))
        as var = (walk-var (pop lambda-list))
        do (augment-env (if (consp var) (car var) var))
        collect var))

@ Having built up the necessary machinery, walking a \L~expression is now
straightforward. The slight generality of walking the car of the form using
|walk-function-name| is because this function will also be used to walk the
bindings in |flet|, |macrolet|, and~|labels| special forms. Also note that
this function passes all of its extra arguments down to |walk-function-name|;
this will be used later to aid in the indexing process.

@l
(defun walk-lambda-expression (walker form env &rest args &aux
                               (lambda-list (cadr form)) (body (cddr form)))
  (multiple-value-bind (forms decls doc) ;
      (parse-body body :walker walker :env env :doc-string-allowed t)
    (multiple-value-bind (lambda-list env) ;
        (walk-lambda-list walker lambda-list decls env)
      `(,(apply #'walk-function-name walker (car form) env args)
        ,lambda-list
        ,@(if doc `(,doc))
        ,@(if decls `((declare ,@decls)))
        ,@(walk-list walker forms env)))))

@ `lambda' is not a special operator in Common Lisp, but we'll treat
\L~expressions as special forms.

@l
(define-special-form-walker lambda ((walker walker) form env)
  (walk-lambda-expression walker form env))

@t To test the walker on binding forms, including \L~expressions, we'll use
a specialized walker class that recognizes a custom |check-binding| special
form. Its syntax is |(check-binding symbols namespace type)|, where
|symbols| is an unevaluated designator for a list of symbols, |namespace|
is one of |:function| or~|:variable|, and |type| is the type of binding
expected for each of the given symbols (e.g., |:lexical|, |:special|,
|:function|). It checks the bindings of |symbols| in the current lexical
environment, and simply returns |symbols| if the checks are all successful.

@l
(defclass test-walker (walker) ())

(define-special-form-walker check-binding ((walker test-walker) form env)
  (flet ((check-binding (name namespace env type)
           (assert (eql (ecase namespace
                          (:function (function-information name env))
                          (:variable (variable-information name env)))
                        type)
                   (name namespace env type)
                   "~@(~A~) binding of ~A not of type ~A."
                   namespace name type)))
   (destructuring-bind (symbols namespace type) (cdr form)
     (loop with symbols = (ensure-list symbols)
           for symbol in symbols
           do (check-binding symbol namespace env type))
     (if (listp symbols)
         (walk-list walker symbols env)
         (walk-form walker symbols env)))))

(defmacro define-walk-binding-test (name form walked-form)
  `(deftest ,name
     (tree-equal (walk-form (make-instance 'test-walker) ',form)
                 ',walked-form)
     t))

@t@l
(define-walk-binding-test walk-ordinary-lambda-list
  (lambda (x y
           &optional (o (+ (check-binding o :variable nil)
                           (check-binding x :variable :special)
                           (check-binding y :variable :lexical)))
           &key ((secret k) 1 k-s-p)
                (k2 (check-binding k-s-p :variable :lexical))
                k3
           &rest args &aux w (z (if k-s-p o x)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding (y z o k k-s-p k2 k3 args w z) :variable :lexical)
    (check-binding secret :variable nil))
  (lambda (x y
           &optional (o (+ o x y))
           &key ((secret k) 1 k-s-p) (k2 k-s-p) k3
           &rest args &aux w (z (if k-s-p o x)))
    (declare (special x))
    x (y z o k k-s-p k2 k3 args w z) secret))

(define-walk-binding-test walk-macro-lambda-list
  (lambda (&whole w (x y) &optional ((o) (+ x y))
           &key ((:k (k1 k2)) (2 3) k-s-p)
           &environment env . body)
    (check-binding (w x y o k1 k2 k-s-p env body) :variable :lexical))
  (lambda (&whole w (x y) &optional ((o) (+ x y))
           &key ((:k (k1 k2)) (2 3) k-s-p)
           &environment env &rest body)
    (w x y o k1 k2 k-s-p env body)))

@ We come now to the binding special forms. The six binding special
forms in Common Lisp (|let|, |let*|, |flet|, |labels|, |macrolet|, and
|symbol-macrolet|) all have essentially the same syntax; only the scope
and namespace of the bindings differ.

We'll start with a little utility routine that walks a variable-like
binding form (e.g., the |cadr| of a |let|/|let*| or |symbol-macrolet|
form). It normalizes atomic binding forms to conses in order to avoid
special cases in the actual walker methods.

The function-like binding forms will use |walk-lambda-expression| for
the same purpose.

@l
(defun walk-variable-binding (walker p env &aux ;
                              (binding (if (consp p) p (list p))))
  (list (walk-atomic-form walker :binding (car binding) env)
        (and (cdr binding)
             (walk-form walker (cadr binding) env))))

@ |let|, |flet|, |macrolet|, and |symbol-macrolet| are all `parallel' binding
forms: they walk their bindings in an unaugmented environment, then execute
their body forms in an environment that contains all of the new bindings.

@l
(define-special-form-walker let
    ((walker walker) form env &aux
     (bindings (mapcar (lambda (p) (walk-variable-binding walker p env)) ;
                       (cadr form)))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    `(,(car form)
      ,bindings
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms
                   (augment-walker-environment walker env
                                               :variable (mapcar #'car bindings)
                                               :declare decls)))))

@ @l
(define-special-form-walker flet
    ((walker walker) form env &aux
     (bindings (mapcar (lambda (p) ;
                         (walk-lambda-expression walker p env ;
                                                 :operator 'flet ;
                                                 :local t :def t))
                       (cadr form)))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    `(,(car form)
      ,bindings
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms
                   (augment-walker-environment walker env
                                               :function (mapcar #'car bindings)
                                               :declare decls)))))


@ The bindings established by |macrolet| and |symbol-macrolet| are
different from those established by the other binding forms in that they
include definitions as well as names. We'll use a little helper function,
|make-macro-definitions|, for building the expander functions in the
former case.

@l
(defun make-macro-definitions (walker defs env)
  (mapcar (lambda (def &aux
                   (name (walk-atomic-form walker :symbol-macro-binding ;
                                           (car def) env)))
            (list name ;
                  (enclose (parse-macro name (cadr def) (cddr def) env) ;
                           env walker)))
          defs))

(define-special-form-walker macrolet
    ((walker walker) form env &aux
     (bindings (mapcar (lambda (p) ;
                         (walk-lambda-expression walker p env ;
                                                 :operator 'macrolet ;
                                                 :local t :def t))
                       (cadr form)))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    `(,(car form)
      ,bindings
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms
                   (augment-walker-environment walker env
                                               :macro (make-macro-definitions ;
                                                       walker bindings env)
                                               :declare decls)))))

@ Walking |symbol-macrolet| is simpler, since the definitions are given in
the bindings themselves.

@l
(define-special-form-walker symbol-macrolet
    ((walker walker) form env &aux
     (bindings (mapcar (lambda (p) (walk-variable-binding walker p env)) ;
                       (cadr form)))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    `(,(car form)
      ,bindings
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms
                   (augment-walker-environment walker env
                                               :symbol-macro bindings
                                               :declare decls)))))

@t@l
(define-walk-binding-test walk-let
  (let ((x 1)
        (y (check-binding x :variable nil)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding y :variable :lexical))
  (let ((x 1) (y x)) (declare (special x)) x y))

(define-walk-binding-test walk-flet
  (flet ((foo (x) (check-binding x :variable :lexical))
         (bar (y) y))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding foo :function :function))
  (flet ((foo (x) x) (bar (y) y)) (declare (special x)) x foo))

(define-walk-binding-test walk-macrolet
  (macrolet ((foo (x) `,(check-binding x :variable :lexical))
             (bar (y) `,y))
    (check-binding foo :function :macro)
    (foo :foo))
  (macrolet ((foo (x) x) (bar (y) y)) foo :foo))

(define-walk-binding-test walk-symbol-macrolet
  (symbol-macrolet ((foo :foo)
                    (bar :bar))
    (check-binding (foo bar) :variable :symbol-macro))
  (symbol-macrolet ((foo :foo) (bar :bar)) (:foo :bar)))

@ The two outliers are |let*|, which augments its environment sequentially,
and |labels|, which does so before walking any of its bindings.

@l
(define-special-form-walker let*
    ((walker walker) form env &aux
     (bindings (cadr form))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    `(,(car form)
      ,(mapcar (lambda (p &aux
                        (walked-binding (walk-variable-binding walker p env))
                        (variable (list (car walked-binding))))
                 (setq env (augment-walker-environment walker env
                                                       :variable variable
                                                       :declare decls))
                 walked-binding)
               bindings)
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms env))))

@ @l
(define-special-form-walker labels
    ((walker walker) form env &aux
     (bindings (cadr form))
     (body (cddr form)))
  (multiple-value-bind (forms decls) (parse-body body :walker walker :env env)
    (let* ((function-names (mapcar (lambda (p)
                                     (walk-function-name walker (car p) env
                                                         :operator 'labels
                                                         :local t
                                                         :def t))
                                   bindings))
           (env (augment-walker-environment walker env
                                            :function function-names
                                            :declare decls)))
      `(,(car form)
        ,(mapcar (lambda (p) (walk-lambda-expression walker p env)) bindings)
        ,@(if decls `((declare ,@decls)))
        ,@(walk-list walker forms env)))))

@t@l
(define-walk-binding-test walk-let*
  (let* ((x 1)
         (y (check-binding x :variable :special)))
    (declare (special x))
    (check-binding y :variable :lexical))
  (let* ((x 1) (y x)) (declare (special x)) y))

(define-walk-binding-test walk-labels
  (labels ((foo (x) (check-binding x :variable :lexical))
           (bar (y) (check-binding foo :function :function)))
    (declare (special x))
    (check-binding x :variable :special)
    (check-binding foo :function :function))
  (labels ((foo (x) x) (bar (y) foo)) (declare (special x)) x foo))

@ The last special form we need a specialized walker for is |locally|,
which simply executes its body in a lexical environment augmented by a
set of declarations.

@l
(define-special-form-walker locally ((walker walker) form env)
  (multiple-value-bind (forms decls) ;
      (parse-body (cdr form) :walker walker :env env)
    `(,(car form)
      ,@(if decls `((declare ,@decls)))
      ,@(walk-list walker forms
                   (augment-walker-environment walker env :declare decls)))))

@t@l
(define-walk-binding-test walk-locally
  (let ((y t))
    (check-binding y :variable :lexical)
    (locally (declare (special y))
      (check-binding y :variable :special)))
  (let ((y t)) y (locally (declare (special y)) y)))

@t Here's a simple walker mix-in class that allows easy tracing of a walk.
It's only here for debugging purposes; it's not a superclass of any of
the walker classes defined in this program.

@l
(defclass tracing-walker (walker) ())

(defmethod walk-atomic-form :before ;
    ((walker tracing-walker) context form env &key)
  (format t "; walking atomic form ~S (~S)~@[ (~(~A~) variable)~]~%"
          form context
          (and (symbolp form)
               (eq context ':evaluated)
               (variable-information form env))))

(defmethod walk-compound-form :before ;
    ((walker tracing-walker) operator form env)
  (declare (ignore operator env))
  (format t "~<; ~@;walking compound form ~W~:>~%" (list form)))

@*Indexing. Having constructed our code walker, we can now use it to
produce an index of the symbols in a web. By default, we'll say a symbol
is {\it interesting\/} if it is interned in one of the packages listed
in |*index-packages*|. The user can add packages to this list using
the \.{@@x} control code, which calls the following function. It takes
a designator for a list of package designators, and adds each package
to |*index-packages*|.

@l
(defun index-package (packages &aux (packages (ensure-list packages)))
  "Inform the weaver that it should index the symbols in PACKAGES."
  (dolist (package packages)
    (pushnew (find-package package) *index-packages*)))

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

@t@l
(deftest index-package
  (let ((*index-packages* nil))
    (index-package "KEYWORD")
    (values (interesting-symbol-p nil)
            (not (null (interesting-symbol-p :foo)))))
  nil t)

@t We need to make sure that the \CLWEB\ package is in |*index-packages*|
when testing the indexer.

@l
(index-package "CLWEB")

@ Before we proceed, let's establish some terminology. Formally, an
{\it index\/} is an ordered collection of {\it entries}, each of which
is a (\<heading>, \<locator>) pair: the {\it locator\/} indicates where the
object referred to by the {\it heading\/} may be found. A list of entries
with the same heading is called an {\it entry list}, or sometimes just an
{\it entry\/}; the latter is an abuse of terminology, but useful and
usually clear in context.

@1*Headings. In this program, headings are usually represented by instances
of the class |heading|. Headings may in general be multi-leveled, and are
sorted lexicographically. Any object with applicable methods for
|heading-name| and |sub-heading| are treated as valid headings; the former
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

@ We'll define a set of heading classes to be used as sub-headings that
represent the type of the object referred to by the primary heading. The
complication here is that we want to make it simple to add {\it modifiers\/}
like `local' or `generic' to a base type like `function', and to have those
modifiers become part of the name in a predictable way. In particular, the
order is important: we don't want to end up with a heading like `setf local
function' when we mean `local setf function'.

We'll build up a few pieces of machinery that let us define those classes
and their fancy names in a nice, declarative way. The first is a custom
method combination that joins together the results of each applicable
method into one delimited string. We'll use this for |heading-name|.

@<Define |heading-name|...@>=
(defun join-strings (strings &optional (delimiter #\Space) &aux
                     (strings (ensure-list strings))
                     (delimiter (string delimiter)))
  (with-output-to-string (out)
    (loop for (string . more) on strings
          do (write-string (string string) out)
          when more do (write-string delimiter out))))

(define-method-combination join-strings (&optional (delimiter #\Space))
    ((prefix (:prefix))
     (primary () :required t)
     (suffix (:suffix)))
  (flet ((call-methods (methods)
           (mapcar (lambda (method) `(ensure-list (call-method ,method))) ;
                   methods)))
    `(join-strings (append ,@(call-methods prefix)
                           ,@(call-methods primary)
                           ,@(call-methods (reverse suffix)))
                   ,delimiter)))

(defgeneric heading-name (heading)
  (:method-combination join-strings))

@t@l
(deftest join-strings
  (values (join-strings "foo")
          (join-strings '("foo" "bar"))
          (join-strings '(:foo :bar :baz) #\,))
  "foo"
  "foo bar"
  "FOO,BAR,BAZ")

(defclass dead-beef () ())
(defclass kobe-beef (dead-beef) ())
(defgeneric describe-beef (beef)
  (:method-combination join-strings ", ")
  (:method ((beef dead-beef)) "steak")
  (:method :prefix ((beef dead-beef)) (list "big" "fat" "juicy"))
  (:method :suffix ((beef dead-beef)) "yum!")
  (:method :prefix ((beef kobe-beef)) "delicious")
  (:method ((beef kobe-beef)) "Kobe")
  (:method :suffix ((beef kobe-beef)) "from Japan"))

(deftest join-strings-method-combination
  (values (describe-beef (make-instance 'dead-beef))
          (describe-beef (make-instance 'kobe-beef)))
  "big, fat, juicy, steak, yum!"
  "delicious, big, fat, juicy, Kobe, steak, yum!, from Japan")

@ The type headings will have a set of modifiers provided via boolean
initargs, since that's the easiest way to pass them down from the walker.
So we'll arrange for those initargs to be translated into a sorted list
of modifier symbols, which we'll use as prefixes to the heading name.

@l
(defclass type-heading (heading)
  ((allowable-modifiers :reader allowable-modifiers
                        :initarg :allowable-modifiers
                        :allocation :class)
   (modifiers :accessor heading-modifiers))
  (:default-initargs :allowable-modifiers nil :modifiers nil))

(defmethod initialize-instance :after ;
    ((heading type-heading) &rest initargs &key &allow-other-keys)
  (setf (heading-modifiers heading)
        (loop with allowable-modifiers = (allowable-modifiers heading)
              for (name value) on initargs by #'cddr
              when (and (member name allowable-modifiers) value)
                collect name into modifiers
              finally (return (sort modifiers
                                    (lambda (x y)
                                      (< (position x allowable-modifiers) ;
                                         (position y allowable-modifiers))))))))

(defmethod heading-name :prefix ((heading type-heading))
  (mapcar #'string-downcase (heading-modifiers heading)))

@ We'll define our type heading classes using the macro |define-type-heading|.
Its syntax is modeled on that of |defclass|: it takes a name, a list of
slot specifiers, and zero or more options. We don't bother accepting a
list of superclass names; all of the classes will be direct subclasses
of |type-heading|.

The |name| argument is what we'll call a {\it short name\/}---a symbol like
|function| or |variable|. These short names will be transformed into longer
names via |type-heading-class-name| to avoid potential conflicts; we don't
actually want to define a class named |function|. To ensure that the longer
class names never need to appear in client code, we'll accept options that
describe methods to be automatically generated that will specialize on the
class being defined.

We'll handle just two of the options accepted by |define-type-heading|
in this section. The first is |:name|, which is used to provide a default
for the |:name| initarg for instances of the defined class. It it's
omitted (the usual case), we'll generate a name from the short name.
The second option we'll handle here is |:modifiers|, which specifies an
ordered list of allowable modifiers.

@l
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun type-heading-class-name (name)
    (intern (concatenate 'string (string name) "-HEADING") ;
            (find-package "CLWEB"))))

@<Define |pop-qualifiers| macro@>

(defmacro define-type-heading (name slots &rest options &aux ;
                               (class-name (type-heading-class-name name)))
  (flet ((option (indicator) ;
           (cdr (find-if (lambda (option) (eq (car option) indicator)) ;
                         options))))
    `(progn
       (defclass ,class-name (type-heading)
         ,slots
         (:default-initargs
          :name ,(or (car (option :name)) ;
                     (substitute #\Space #\- (string-downcase name)))
          :allowable-modifiers ',(option :modifiers)))
       ,@ @<Generate specialized |compute-type-heading-class| methods@>
       ,@ @<Generate specialized |heading-name| methods@>)))

@ To instantiate a type heading class, we'll use the constructor function
|make-type-heading|, which accepts either a short name or a class.

@l
(defgeneric make-type-heading (type &rest initargs))
(defmethod make-type-heading ((type symbol) &rest initargs)
  (apply #'make-instance (type-heading-class-name type) initargs))
(defmethod make-type-heading ((type standard-class) &rest initargs)
  (apply #'make-instance type initargs))

@t@l
(deftest make-type-heading
  (every (lambda (x) (typep x 'type-heading))
         (list (make-type-heading 'type)
               (make-type-heading (find-class 'type-heading))))
  t)

@ One of the options that |define-type-heading| accepts produces specialized
methods for |heading-name|. The syntax is `(|:heading-name| \<qualifiers>$^*$
\<parameters> .~\<body>)'. The \<parameters> list should consist of a single,
unspecialized parameter name; we'll provide the appropriate class specializer.

@<Generate specialized |heading-name| methods@>=
(loop for (option-name . option) in options
      when (eq option-name :heading-name)
      collect (let ((qualifiers (pop-qualifiers option)))
                (destructuring-bind (parameters . body) option
                  (check-type parameters (cons symbol null))
                  `(defmethod heading-name ,@qualifiers ;
                       ((,(car parameters) ,class-name))
                     ,@body))))

@ Most of the type headings are associated with a small set of operators
for which they'll serve as sub-headings. For example, when we walk a |defun|
form, we'll use a |function| type heading, and so on. Rather than having
those associations spread all over the indexing walker, we'll put them right
here, with the type heading definitions themselves.

We do this via methods on the generic function |compute-type-heading-class|,
which the indexing methods can call with an operator name to determine which
type heading class to use. The class returned can then be used as the first
argument to |make-type-heading|.

@l
(defgeneric compute-type-heading-class (operator &key &allow-other-keys))

@ The |:operators| option to |define-type-heading| takes a list of symbols
and creates an eql-specialized method on |compute-type-heading-class| for
each of them. It's important that these methods return the class and not
the name of the class so that |make-type-heading| can do the right thing.

@<Generate specialized |compute-type-heading-class| methods@>=
(loop for operator in (option :operators)
      collect `(defmethod compute-type-heading-class ;
                   ((operator (eql ',operator)) &key)
                 (find-class ',class-name)))

@ {\it Et voil\`a!\/}

@l
(define-type-heading function ()
  (:modifiers :local :generic :setf)
  (:operators defun defgeneric flet labels))

(define-type-heading method
  @<Define method heading slots@>
  @<Define specialized |heading-name| for method headings@>
  (:modifiers :setf))

(define-type-heading macro ()
  (:modifiers :local)
  (:operators defmacro macrolet))

(define-type-heading symbol-macro ()
  (:modifiers :local)
  (:operators define-symbol-macro symbol-macrolet))

(define-type-heading class ()
  (:operators defclass))

(define-type-heading condition-class ()
  (:operators define-condition))

(define-type-heading structure ()
  (:operators defstruct))

(define-type-heading variable ()
  (:modifiers :special :constant))

(define-type-heading method-combination ()
  (:operators define-method-combination))

(define-type-heading compiler-macro ()
  (:operators define-compiler-macro))

@t We won't bother testing all of the type heading classes, but we'll verify
that all of the automatically generated methods are doing what they aughtta.

@l
(deftest function-heading-name
  (values (heading-name (make-type-heading 'function))
          (heading-name (make-type-heading 'function :local t))
          (heading-name (make-type-heading 'function :generic t :local nil))
          (heading-name (make-type-heading 'function :setf t))
          (heading-name (make-type-heading 'function :setf t :local t))
          (every (lambda (class) (eql (class-name class) 'function-heading))
                 (list (class-of (make-type-heading 'function))
                       (compute-type-heading-class 'defun)
                       (compute-type-heading-class 'flet))))
  "function"
  "local function"
  "generic function"
  "setf function"
  "local setf function"
  t)

@ Method headings get some special treatment. To begin with, we'll prepend
the list of qualifiers, if any; otherwise, we'll call them `primary'.

@<Define specialized |heading-name|...@>=
(:heading-name :prefix (heading)
  (mapcar #'string-downcase ;
          (or (method-heading-qualifiers heading) '(:primary))))

@t@l
(deftest method-heading-name
  (values (heading-name (make-type-heading 'method))
          (heading-name (make-type-heading 'method ;
                                           :qualifiers ;
                                           '(:before :during :after))))
  "primary method"
  "before during after method")

@ @<Define method heading slots@>=
((qualifiers :reader method-heading-qualifiers ;
             :initarg :qualifiers ;
             :initform nil))

@ Non-|setf| primary methods (i.e., methods with empty qualifier lists)
are indexed as functions so that they'll appear as definitions of the
generic function they're methods of; only methods with qualifiers and
|setf| methods get independent entries. This helps keep the index compact
without significantly affecting usability.

@l
(defmethod compute-type-heading-class ((operator (eql 'defmethod)) &key ;
                                       qualifiers function-name)
  (etypecase function-name
    (symbol (if qualifiers 'method 'function))
    (setf-function-name 'method)))

@t@l
(deftest method/function-heading
  (values (typep (make-type-heading ;
                  (compute-type-heading-class 'defmethod))
                 'function-heading)
          (typep (make-type-heading ;
                  (compute-type-heading-class 'defmethod ;
                                              :function-name '(setf foo)))
                 'method-heading)
          (typep (make-type-heading ;
                  (compute-type-heading-class 'defmethod ;
                                              :qualifiers '(:foo)))
                 'method-heading))
  t t t)

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

@ The entry trees get stored in |index| objects, for which we define a few
protocol functions: |make-index| creates a new index; |add-index-entry|
adds an entry to it, and |find-index-entries| returns the list of locators
with the given heading.

@l
(defclass index ()
  ((entries :accessor index-entries :initform nil)))

(defun make-index () (make-instance 'index))
(defgeneric add-index-entry (index heading locator &key))
(defgeneric find-index-entries (index heading))

@ We'll keep a global index around so that we can add `manual' entries (i.e.,
entries not automatically generated via the code walk) during reading.

@<Global variables@>=
(defvar *index* nil)

@ @<Initialize global variables@>=
(setq *index* (make-index))

@ This method adds an index entry for |heading| with location |section|.
A new locator is constructed only when necessary, and duplicate locators are
automatically suppressed. Definitional locators are also made to supersede
ordinary ones.

@l
(define-modify-macro orf (&rest args) or)

(defmethod add-index-entry ((index index) heading (section section) &key def)
  (flet ((make-locator ()
           (make-locator :section section :def def)))
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

@ And here's the main index entry retrieval method. In fact, this function
isn't actually used in this program (although the test suite uses it),
since all we do with the index is add entries to it and then traverse the
whole thing and print them all out.

@l
(defmethod find-index-entries ((index index) heading)
  (let ((entries (index-entries index)))
    (when entries
      (multiple-value-bind (entry present-p) ;
          (find-or-insert heading entries :insert-if-not-found nil)
        (when present-p
          (entry-locators entry))))))

@t@l
(deftest (add-index-entry 1)
  (let ((index (make-index))
        (heading 'foo)
        (*sections* (make-array 3 :fill-pointer 0)))
    (add-index-entry index heading (make-instance 'section))
    (add-index-entry index heading (make-instance 'section))
    (add-index-entry index heading (make-instance 'section))
    (sort (mapcar #'section-number
                  (mapcar #'location (find-index-entries index heading)))
          #'<))
  (0 1 2))

(deftest (add-index-entry 2)
  (let* ((index (make-index))
         (heading 'foo)
         (*sections* (make-array 1 :fill-pointer 0))
         (section (make-instance 'section)))
    (add-index-entry index heading section)
    (add-index-entry index heading section :def t) ; def should replace use
    (locator-definition-p (first (find-index-entries index heading))))
  t)

@ In order to index them properly, the walker needs to know whether a given
function name refers to an ordinary or generic function.

@l
(defun generic-function-p (function-name)
  (or (typep function-name 'generic-function)
      (and (fboundp function-name)
           (typep (fdefinition function-name) 'generic-function))))

@ The global variable |*index-lexical-variables*| controls whether or not
the indexer will create entries for lexical variables. Its value is
{\it not\/} re-initialized on each run.

@<Global variables@>=
(defvar *index-lexical-variables* nil
  "If this flag is non-nil, the indexer will index lexical variables.")

@ Here are a couple of indexing routines that we'll use in the walker below
for indexing function and variable {\it uses}. They look up the given
variable or function in a lexical environment object and add an appropriate
index entry. (We can't use this routine for definitions because the name
being indexed might not be in the environment yet.)

@l
(defgeneric index-variable (index variable env section))
(defmethod index-variable ((index index) variable env section)
  (multiple-value-bind (type local) (variable-information variable env)
    (when (or (member type '(:special :symbol-macro :constant))
              (and *index-lexical-variables* (eql type :lexical)))
      (add-index-entry
        index
        (make-heading variable
                      (ecase type
                        (:lexical (make-type-heading 'variable))
                        (:special (make-type-heading 'variable :special t))
                        (:constant (make-type-heading 'variable :constant t))
                        (:symbol-macro (make-type-heading 'symbol-macro ;
                                                          :local local))))
        section))))

(defgeneric index-funcall (index function-name form env section))
(defmethod index-funcall ((index index) function-name form env section)
  (declare (ignore form))
  (multiple-value-bind (type local) (function-information function-name env)
    (when (member type '(:function :macro))
      (add-index-entry
        index
        (make-heading function-name
                      (ecase type
                        (:function ;
                         (make-type-heading 'function
                                            :local local
                                            :generic (generic-function-p ;
                                                      function-name)))
                        (:macro (make-type-heading 'macro :local local))))
        section))))

@ To index definitions, we'll need some information from the walker about
the context in which the function name occurred. In particular, we'll get
the |car| of the defining form as the |operator| argument.

@l
(defgeneric index-defun (index function-name section &key))
(defmethod index-defun ((index index) function-name section &key ;
                        operator local generic qualifiers)
  (add-index-entry
    index
    (make-heading (etypecase function-name
                    (symbol function-name)
                    (setf-function-name (cadr function-name)))
                  (make-type-heading
                    (compute-type-heading-class operator
                                                :qualifiers qualifiers
                                                :function-name function-name)
                    :setf (setf-function-name-p function-name)
                    :local local
                    :generic (or generic (generic-function-p function-name))
                    :qualifiers qualifiers))
    section :def t))

@ We'll use this next generic function to index symbols that occur in
various contexts during the walk. The primary method provided here just
attempts to index variable use.

@l
(defgeneric index-symbol (index context symbol env &key section def))
(defmethod index-symbol (index context symbol env &key section def)
  (declare (ignore context def))
  (index-variable index symbol env section))

@ Since basically all of the methods on |index-symbol| will be after
methods that specialize on the |context| parameter and generate the
same kind of two-leveled index entries, we can use the following macro
to define them in a concise way.

@l
(defmacro define-symbol-indexer (context type &rest args)
  `(defmethod index-symbol :after ;
       (index (context (eql ,context)) symbol env &key section def)
     (declare (ignore env))
     (add-index-entry index ;
                      (make-heading symbol (make-type-heading ,type ,@args)) ;
                      section :def def)))

@ We'll define this one method for lexical bindings by hand, since we need
the conditional.

@l
(defmethod index-symbol :after ;
    (index (context (eql :binding)) symbol env &key section def)
  (declare (ignore env))
  (when *index-lexical-variables*
    (add-index-entry index ;
                     (make-heading symbol (make-type-heading 'variable)) ;
                     section :def def)))

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
occurred. We'll these uninterned symbols {\it referring symbols}.
@^referring symbols@>

First, we'll need a routine that does the substitution just described.
The substitution is done blindly and without regard to the syntax or
semantics of Common Lisp, since we can't walk pre-tangled code.

@l
(defun substitute-symbols (form section &aux symbols)
  (labels ((get-symbols (form)
             (cond ((interesting-symbol-p form)
                    (pushnew form symbols))
                   ((atom form) nil)
                   (t (get-symbols (car form))
                      (get-symbols (cdr form))))))
    (get-symbols form)
    (sublis (map 'list
                 (lambda (sym)
                   (let ((refsym (copy-symbol sym)))
                     (setf (symbol-value refsym) sym)
                     (setf (get refsym 'section) section)
                     (cons sym refsym)))
                 symbols)
            form)))

@ This next function goes the other way: given a symbol, it determines
whether it is a referring symbol, and if so, it returns the symbol referred
to and the section it came from. Otherwise, it just returns the given
symbol. This interface makes it convenient to use in a |multiple-value-bind|
form without having to apply a predicate first.
@^referring symbols@>

@l
(defun symbol-provenance (symbol)
  (let ((section (get symbol 'section)))
    (if (and (null (symbol-package symbol))
             (boundp symbol)
             section)
        (values (symbol-value symbol) section)
        symbol)))

@t@l
(deftest (symbol-provenance 1)
  (let ((*index-packages* (list (find-package "KEYWORD"))))
    (symbol-provenance (substitute-symbols :foo 1)))
  :foo 1)

(deftest (symbol-provenance 2)
  (symbol-provenance :foo)
  :foo)

@ To get referring symbols in the tangled code, we'll use an |:around|
method on |section-code| that conditions on a special variable,
|*indexing*|, that we'll bind to true while we're tangling for the
purposes of indexing.
@^referring symbols@>

We can't feed the raw section code to |substitute-symbols|, since it's
not really Lisp code: it's full of markers and such. So we'll abuse the
tangler infrastructure and use it to do marker replacement, but {\it not\/}
named-section expansion.

@l
(defmethod section-code :around ((section section))
  (let ((code (call-next-method)))
    (if *indexing*
        (substitute-symbols (tangle code :expand-named-sections nil) section)
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

@1*The indexing walker. Now we're ready to define a specialized walker that
does the actual indexing.

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

@t To test our indexing walker, we'll use the following macro.
It takes a name and options, a list of section specifiers acceptable
to |with-temporary-sections| and zero or more expected index entry
specifiers that should match the output of |all-index-entries|.

The |name-and-options| argument may be either an atom providing a name
for the test or a list of the form `(\<name> \<options>)', where \<options>
is a plist of keyword arguments. If the option |:verify-walk| is true (the
default), the test will include an assertion the walked forms match the
originals. During the walk, |*index-lexical-variables*| will be bound to
the value of the |:index-lexicals| option (false by default).

@l
(defmacro define-indexing-test (name-and-options sections &rest expected-entries)
  (destructuring-bind (name &key (verify-walk t) (index-lexicals nil)) ;
      (ensure-list name-and-options)
    `(deftest (index ,name)
       (with-temporary-sections ,sections
         (let ((tangled-code (tangle (unnamed-section-code-parts *sections*)))
               (mangled-code (tangle-code-for-indexing *sections*))
               (walker (make-instance 'indexing-walker))
               (*index-lexical-variables* ,index-lexicals))
           (loop for form in tangled-code and mangled-form in mangled-code
                 as walked-form = (walk-form walker mangled-form)
                 ,@(when verify-walk
                     `(do (assert (tree-equal walked-form form)
                                  (walked-form mangled-form form)))))
           (tree-equal (all-index-entries (walker-index walker))
                       ',expected-entries
                       :test #'equal)))
       t)))

@ We have to override the walker's macro expansion function, since the
forms that we're considering might be or contain referring symbols, which
won't have macro definitions. There are two important cases here:
  (1)~a form that is a referring symbol whose referent is a symbol macro
  in the current environment; and
  (2)~a compound form, the operator of which is a referring symbol whose
  referent is a macro in the current environment.
In both cases, we'll index the use of the (symbol) macro, then hand control
off to the next method for the actual expansion.
@^referring symbols@>

@l
(defmethod macroexpand-for-walk ((walker indexing-walker) form env)
  (typecase form
    (symbol
     (multiple-value-bind (symbol section) (symbol-provenance form)
       (cond (section
              (case (variable-information symbol env)
                (:symbol-macro
                 (index-variable (walker-index walker) symbol env section)
                 (call-next-method walker (cons symbol (cdr form)) env))
                (t form)))
             (t (call-next-method)))))
    (cons
     (multiple-value-bind (symbol section) (symbol-provenance (car form))
       (cond (section
              (case (function-information symbol env)
                (:macro
                 (index-funcall (walker-index walker) symbol form env section)
                 (call-next-method walker (cons symbol (cdr form)) env))
                (t form)))
             (t (call-next-method)))))
    (t form)))

@ The only atoms we care about indexing are referring symbols. We'll return
the referents; this is where the reverse-substitution of referring symbols
takes place. It's also where much of the actual indexing gets done, by way
of the call to |index-symbol|.
@^referring symbols@>

@l
(defmethod walk-atomic-form :around ;
    ((walker indexing-walker) context (form symbol) env &key def)
  (multiple-value-bind (symbol section) (symbol-provenance form)
    (when section
      (index-symbol (walker-index walker) context symbol env ;
                    :section section ;
                    :def def))
    (call-next-method walker context symbol env)))

@t@l
(define-indexing-test atom
  ((:section :code (*sections*)))
  ("*SECTIONS* special variable" (0)))

@ Bindings {\it are\/} definitions for lexical variables.

@l
(defmethod walk-atomic-form :around ;
    ((walker indexing-walker) (context (eql :binding)) (form symbol) env &key)
  (call-next-method walker context form env :def t))

@t@l
(define-indexing-test (variables :index-lexicals t)
  ((:section :code ((let ((foo nil) (bar nil) (baz nil))))))
  ("BAR variable" ((:def 0)))
  ("BAZ variable" ((:def 0)))
  ("FOO variable" ((:def 0))))

@ We'll index all function-call-like forms whose |operator| is a referring
symbol.

@l
(defmethod walk-compound-form :before ;
    ((walker indexing-walker) (operator symbol) form env)
  (multiple-value-bind (symbol section) (symbol-provenance operator)
    (when section
      (index-funcall (walker-index walker) symbol form env section))))

@t@l
(define-indexing-test funcall
  ((:section :code ((mapappend 'identity '(1 2 3)))))
  ("MAPAPPEND function" (0)))

@ The walker methods for all of the function-defining and binding forms
call down to this function, passing keyword arguments that describe the
context.

@l
(defmethod walk-function-name :before ;
    ((walker indexing-walker) function-name env &rest args &key def)
  (let ((index (walker-index walker)))
    (typecase function-name
      (symbol
       (multiple-value-bind (symbol section) (symbol-provenance function-name)
         (when section
           (if def
               (apply #'index-defun ;
                      index symbol section :allow-other-keys t args)
               (index-funcall index symbol nil env section)))))
      (setf-function-name
       (multiple-value-bind (symbol section) ;
           (symbol-provenance (cadr function-name))
         (when section
           (if def
               (apply #'index-defun ;
                      index `(setf ,symbol) section :allow-other-keys t args)
               (index-funcall index symbol nil env section))))))))

@t@l
(define-indexing-test function-name
  ((:section :code ((flet ((foo (x) x)))))
   (:section :code ((flet (((setf foo) (y x) y))))))
  ("FOO local function" ((:def 0)))
  ("FOO local setf function" ((:def 1))))

@ We'll treat |defun|, |defmacro|, and |define-compiler-macro| as special
forms, since otherwise they will get macro-expanded before we get a chance
to walk the function name. In fact, we won't even bother expanding them at
all, since we don't care about the implementation-specific expansions, and
we get everything we need from this simple walk.

Note in particular that we don't record the macro definition when we walk a
|defmacro| form. For the macro definition to be available during the walk,
the defining form must have been previously evaluated.

The indexing proper happens in the |walk-function-name| method we just
defined, by way of |walk-lambda-expression|.

@l
(macrolet ((define-defun-like-walker (operator)
             `(define-special-form-walker ,operator ;
                  ((walker indexing-walker) form env)
                `(,(car form)
                  ,@(walk-lambda-expression walker (cdr form) env
                                            :operator (car form)
                                            :def t)))))
  (define-defun-like-walker defun)
  (define-defun-like-walker defmacro)
  (define-defun-like-walker define-compiler-macro))

@t@l
(define-indexing-test defun
  ((:section :code ((defun foo (x) x))))
  ("FOO function" ((:def 0))))

(define-indexing-test defmacro
  ((:section :code ((defmacro foo (&body body) (mapappend 'identity body)))))
  ("FOO macro" ((:def 0)))
  ("MAPAPPEND function" (0)))

(define-indexing-test define-compiler-macro
  ((:section :code ((define-compiler-macro foo (&whole form) form))))
  ("FOO compiler macro" ((:def 0))))

@ Structure definitions also get indexed, although we won't bother to
grovel through all of the options. We'll let them expand, since we can
often pick up at least the constructor definitions that way.

@l
(define-special-form-walker defstruct ((walker indexing-walker) form env)
  (let ((name (typecase (cadr form)
                (symbol (cadr form))
                (cons (caadr form)))))
    (multiple-value-bind (symbol section) (symbol-provenance name)
      (when section
        (index-defun (walker-index walker) symbol section ;
                     :operator 'defstruct)))
    (throw form t)))

@t@l
(define-indexing-test (defstruct :verify-walk nil)
  ((:section :code ((defstruct foo)))
   (:section :code ((defstruct (bar (:type list)) a b c))))
  ("BAR structure" ((:def 1)))
  ("FOO structure" ((:def 0))))

@ The special-variable-defining forms must also be walked as if they were
special forms. Once again, we'll just skip the macro expansions.

@l
(macrolet ((define-indexing-defvar-walker (operator type)
             `(define-special-form-walker ,operator ;
                  ((walker indexing-walker) form env)
                `(,(car form)
                  ,(walk-atomic-form walker ,type (cadr form) env :def t)
                  ,@(walk-list walker (cddr form) env)))))
  (define-indexing-defvar-walker defvar :special-binding)
  (define-indexing-defvar-walker defparameter :special-binding)
  (define-indexing-defvar-walker defconstant :constant-binding))

(define-symbol-indexer :special-binding 'variable :special t)
(define-symbol-indexer :constant-binding 'variable :constant t)

@t@l
(define-indexing-test defvar
  ((:section :code ((defvar *a* t)))
   (:section :code ((defparameter *b* t)))
   (:section :code ((defconstant *c* t))))
  ("*A* special variable" ((:def 0)))
  ("*B* special variable" ((:def 1)))
  ("*C* constant variable" ((:def 2))))

@ The default method for |walk-declaration-specifiers| just returns the
given specifiers. That's not sufficient for our purposes here, though,
because we need to replace referring symbols with their referents;
otherwise, the declarations would apply to the wrong symbols.
@^referring symbols@>

Because of the shorthand notation for type declarations, walking general
declaration expressions is difficult. However, we don't care about type
declarations, since they're not allowed to affect program semantics. We
therefore just throw out everything except |special| and |optimize|
declarations. (The latter are preserved only because CCL's macro-expansion
machinery uses blatantly unsafe code, and depends on local declarations to
lower the safety level.)
@^Clozure Common Lisp@>

@l
(defmethod walk-declaration-specifiers ((walker indexing-walker) decls env)
  (loop for (identifier . data) in decls
        if (eql identifier 'special)
          collect `(special ,@(walk-list walker data env))
        else if (eql identifier 'optimize)
          collect `(optimize ,@data)))

@t All we care about are |special| and |optimize| declarations.

@l
(deftest indexing-walk-declaration-specifiers
  (equal (walk-declaration-specifiers (make-instance 'indexing-walker)
                                      '((type foo x)
                                        (special x y)
                                        (ignore z)
                                        (optimize (speed 3) (safety 0)))
                                      nil)
         '((special x y)
           (optimize (speed 3) (safety 0))))
  t)

@ Now we'll turn to the various {\sc clos} forms. We'll start with a little
macro to pull off method qualifiers from a |defgeneric| form or a method
description. Syntactically, the qualifiers are any non-list objects
preceding the specialized \L-list.

@<Define |pop-qualifiers| macro@>=
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro pop-qualifiers (place)
    `(loop until (listp (car ,place)) collect (pop ,place))))

@ For |defgeneric| forms, we're interested in the name of the generic
function being defined, the method combination type, and any methods that
may be specified as method descriptions.

@l
(define-special-form-walker defgeneric ((walker indexing-walker) form env)
  (destructuring-bind (operator function-name lambda-list &rest options) form
    `(,operator
      ,(walk-function-name walker function-name env ;
                           :operator 'defgeneric
                           :generic t
                           :def t)
      ,(walk-lambda-list walker lambda-list nil env)
      ,@(loop for form in options
              collect (case (car form)
                        (:method-combination ;
                         @<Walk the method combination option in |form|@>)
                        (:method @<Walk the method description in |form|@>)
                        (t (walk-list walker form env)))))))

@t@l
(define-indexing-test defgeneric
  ((:section :code ((defgeneric foo (x y)
                      (:documentation "foo")
                      (:method-combination progn)
                      (:method progn ((x t) y) x)
                      (:method :around (x (y (eql 't))) y)))))
  ("FOO around method" ((:def 0)))
  ("FOO generic function" ((:def 0)))
  ("FOO progn method" ((:def 0))))

@ Method descriptions are very much like |defmethod| forms with an implicit
function name; this routine walks both. The function name (if non-null) and
qualifiers (if any) should have been walked already; we'll walk the
specialized \L-list and body forms here.

@l
(defun walk-method-definition (walker operator function-name qualifiers
                               lambda-list body env)
  (multiple-value-bind (body-forms decls doc) ;
      (parse-body body :walker walker :env env)
    (multiple-value-bind (lambda-list env) ;
        (walk-specialized-lambda-list walker lambda-list decls env)
      `(,operator
        ,@(when function-name `(,function-name))
        ,@qualifiers
        ,lambda-list
        ,@(if doc `(,doc))
        ,@(if decls `((declare ,@decls)))
        ,@(walk-list walker body-forms env)))))

@ @<Walk the method description in |form|@>=
(let* ((operator (pop form))
       (qualifiers (mapcar (lambda (q)
                             (walk-atomic-form walker :method-qualifier q env))
                           (pop-qualifiers form)))
       (lambda-list (pop form))
       (body form))
  ;; This is purely for its side-effect on the index.
  (walk-function-name walker function-name env
                      :operator 'defmethod
                      :generic t
                      :qualifiers qualifiers
                      :def t)
  (walk-method-definition walker operator nil qualifiers lambda-list body env))

@ Walking a |defmethod| form is almost, but not quite, the same as walking
a method description.

@l
(define-special-form-walker defmethod
    ((walker indexing-walker) form env &aux
     (operator (pop form))
     (function-name (pop form)) ; don't walk yet: wait for the qualifiers
     (qualifiers (mapcar (lambda (q)
                           (walk-atomic-form walker :method-qualifier q env))
                         (pop-qualifiers form)))
     (lambda-list (pop form))
     (body form))
  (walk-method-definition walker operator
                          (walk-function-name walker function-name env
                                              :operator 'defmethod
                                              :generic t
                                              :qualifiers qualifiers
                                              :def t)
                          qualifiers lambda-list body env))

@t@l
(define-indexing-test defmethod
  ((:section :code ((defmethod add (x y) (+ x y))))
   (:section :code ((defmethod add :before (x y)))))
  ("ADD before method" ((:def 1)))
  ("ADD generic function" ((:def 0))))

@ We'll walk |defclass| and |define-condition| forms in order to index the
class names, super-classes, and~accessor methods.

@l
(macrolet ((define-defclass-walker (operator type)
             `(define-special-form-walker ,operator ;
                  ((walker indexing-walker) form env)
                (destructuring-bind ;
                      (operator name supers slot-specs &rest options) form
                  `(,operator
                    ,(walk-atomic-form walker ,type name env :def t)
                    ,(mapcar (lambda (super) ;
                               (walk-atomic-form walker ,type super env)) ;
                             supers)
                    ,(mapcar (lambda (spec) ;
                               (walk-slot-specifier walker spec env)) ;
                             slot-specs)
                    ,@(walk-list walker options env))))))
  (define-defclass-walker defclass :class)
  (define-defclass-walker define-condition :condition-class))

(define-symbol-indexer :class 'class)
(define-symbol-indexer :condition-class 'condition-class)

@t@l
(define-indexing-test defclass
  ((:section :code ((defclass foo ()
                      ((a :reader foo-a1 :reader foo-a2)))))
   (:section :code ((define-condition bar ()
                      ((b :accessor foo-b))))))
  ("BAR condition class" ((:def 1)))
  ("FOO class" ((:def 0)))
  ("FOO-A1 generic function" ((:def 0)))
  ("FOO-A2 generic function" ((:def 0)))
  ("FOO-B generic function" ((:def 1)))
  ("FOO-B primary setf method" ((:def 1))))

@ The only slot options we care about are |:reader|, |:writer|,
and~|:accessor|. We index the methods implicitly created by those
options.

@l
(defun walk-slot-specifier (walker spec env)
  (etypecase spec
    (symbol (walk-atomic-form walker :slot-name spec env))
    (cons (destructuring-bind (name &rest options) spec
            (loop for (opt-name opt-value) on options by #'cddr
                  if (member opt-name '(:reader :writer :accessor))
                    do @<Index |opt-value| as a slot access method@>)
            `(,(walk-atomic-form walker :slot-name name env)
              ,@(walk-list walker options env))))))

@ @<Index |opt-value| as a slot access method@>=
(multiple-value-bind (symbol section) (symbol-provenance opt-value)
  (when section
    (index-defun (walker-index walker) symbol section ;
                 :operator 'defmethod ;
                 :generic t)
    (when (eql opt-name :accessor)
      (index-defun (walker-index walker) `(setf ,symbol) section ;
                   :operator 'defmethod ;
                   :generic t))))

@ We'll also walk |define-method-combination| forms to get the names of the
method combination types. We'll skip the expansion.

@l
(define-special-form-walker define-method-combination ;
    ((walker indexing-walker) form env)
  `(,(car form)
    ,(walk-atomic-form walker :method-combination (cadr form) env :def t)
    ,@(walk-list walker (cddr form) env)))

(define-symbol-indexer :method-combination 'method-combination)

@t@l
(define-indexing-test define-method-combination
  ((:section :code ((define-method-combination foo :operator bar)))
   (:section :code ((defgeneric foo () (:method-combination foo)))))
  ("FOO generic function" ((:def 1)))
  ("FOO method combination" (1 (:def 0))))

@ We'll also index custom method combination type uses, which occur in the
|:method-combination| option given to a |defgeneric| form.

@<Walk the method combination...@>=
`(,(car form)
  ,(walk-atomic-form walker :method-combination (cadr form) env)
  ,@(walk-list walker (cddr form) env))

@ And here, finally, is the top-level indexing routine: it walks the
tangled, symbol-replaced code of the given sections and returns an index
of all of the interesting symbols so encountered.

@l
(defun index-sections (sections &key
                       (index *index*)
                       (walker (make-instance 'indexing-walker :index index)))
  (let ((*evaluating* t))
    (index-package *package*)
    (dolist (form (tangle-code-for-indexing sections) (walker-index walker))
      (walk-form walker form))))

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
    (format stream "\\hbox{~D--~D}"
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

(defmethod print-entry-heading (stream (heading type-heading) &key)
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
In this program,we define reader macro functions for most of the standard
macro characters,so it might be nice to have dedicated index entries for
those definitions.

To begin, we'll define a heading class for macro characters, a subclass for
dispatch macro characters, and a constructor function for both.

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
  (declare (ignore h1)))
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

(defmethod entry-heading-equalp ((h1 macro-char-heading) h2)
  (declare (ignore h2)))
(defmethod entry-heading-equalp (h1 (h2 macro-char-heading))
  (declare (ignore h1)))
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
         (c (make-macro-char-heading #\c))
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
|set-dispatch-macro-character| are `interesting'. (In general, this is
dangerous for symbols in the Common Lisp package, so be careful.)

@l
(defmethod interesting-symbol-p ((object (eql 'set-macro-character))) ;
  t)
(defmethod interesting-symbol-p ((object (eql 'set-dispatch-macro-character))) ;
  t)

@ And finally, we'll add some methods to |index-funcall| specialized on
those function names. Note that by overriding the default method, we
prevent the functions themselves from being indexed, which is what we
want in this case.

@l
(defmethod index-funcall ;
    ((index index) (function-name (eql 'set-macro-character)) form env section)
  (declare (ignore env))
  (when (characterp (second form))
    (add-index-entry index
                     (make-macro-char-heading (second form))
                     section :def t)))

(defmethod index-funcall ;
    ((index index) (function-name (eql 'set-dispatch-macro-character)) ;
     form env section)
  (declare (ignore env))
  (when (characterp (second form))
    (add-index-entry index
                     (make-macro-char-heading (second form) (third form))
                     section :def t)))

@t@l
(define-indexing-test macro-character
  ((:section :code ((set-macro-character #\! #'read-bang)))
   (:section :code ((set-dispatch-macro-character #\@ #\! #'read-at-bang))))
  ("!" ((:def 0)))
  ("@ !" ((:def 1))))

@*Index.

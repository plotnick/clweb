% -*-CLWEB-*-

\newif\ifzapf \zapftrue
\ifzapf
\input palatino
\input euler
\font\tenrmr=pplr8r at 10pt % for non-ASCII characters
\def\ldq{{\tenrmr \char'253}} % left guillemet
\def\rdq{{\tenrmr \char'273}} % right guillemet
\font\tenss=lopr8r at 10pt
\font\tenssi=lopri8r at 10pt
\font\tenssb=lopb8r at 10pt
\let\cmntfont=\tenssi
\mainfont
\def\({\bgroup\IB\it} % use italics for inner-Lisp mode material
\def\){\/\egroup}
{\catcode`\(=\active \catcode`\)=\active
 % borrow Palatino's parenthesis for Lisp code
 \gdef({{\tenrm\char`\(}\kern.025em}
 \gdef){{\tenrm\char`\)}\kern.025em}}
\def\csc#1{{\sc #1}}
\def\lheader{\headertrue\mainfont\the\pageno\sc\qquad\grouptitle
  \hfill\lowercase\expandafter{\jobname}\qquad
  \mainfont\topsecno} % top line on left-hand pages
\def\rheader{\headertrue\mainfont\topsecno
  \sc\qquad\lowercase\expandafter{\jobname}\hfill
  \grouptitle\qquad\mainfont\the\pageno} % top line on right-hand pages
\def\grouptitle{\let\i=I\let\j=J\lowercase\expandafter{\expandafter
                        \takethree\topmark}}
\fi

\def\pb{\.{|...|}} % program brackets
\def\v{\.{\char'174}} % vertical bar in typewriter font
\def\WEB{{\tt WEB}}
\def\CWEB{{\tt CWEB}}
\def\CLWEB{{\tt CLWEB}}
\def\EOF{\csc{eof}}
\def\etc.{{\it \char`&c.\spacefactor1000}}
\def\metasyn#1{$\langle${\it #1\/}$\rangle$} % metasyntactic variable

@*Introduction. This is \CLWEB, a literate programming system for Common
Lisp by Alex Plotnick \metasyn{plotnick@@cs.brandeis.edu}. It is modeled
after the \CWEB\ system by Silvio Levy and Donald E.~Knuth, which was in
turn adapted from Knuth's original \WEB\ system.  It shares with those
earlier systems not only their underlying philosophy, but also most of
their syntax and control codes. Readers unfamiliar with either of them---or
with literate programming in general---should consult the \CWEB\ manual or
Knuth's {\it \ldq Literate Programming\rdq}
(\csc{csli}:~1992).

This is a preliminary, $\alpha$-quality release of the system; for the
latest version, please visit\par\noindent
\.{http://www.cs.brandeis.edu/\~plotnick/clweb/}.

@ A literate programming system provides two primary operations:
{\it tangling\/} and {\it weaving\/}. The tangler prepares a literate 
program, or {\it web}, for evaluation by a machine, while the weaver
prepares it for typesetting with \TeX\ and subsequent reading by a
human. These operations reflect the two uses of a literate program, and the
two audiences by whom it must be read: the computer on the one hand, and
the human programmers that must understand and maintain it on the other.

Our tangler has two main interface functions: |tangle-file| and |load-web|.
The first is analogous to |compile-file|: given a file containing \CLWEB\
source, it produces an output file that can subsequently be loaded into a
Lisp image with |load|. The function |load-web| is analogous to |load|,
but also accepts \CLWEB\ source as input instead of ordinary Lisp source;
it loads a web into the Lisp environment.

The weaver has a single entry point: |weave| takes a web as input and
generates a file that can be fed to \TeX\ to generate a pretty-printed
version of that web.

The fourth exported symbol, |load-sections-from-temp-file|, is conceptually
part of the tangler, but is a special-purpose routine designed to be used
in conjunction with an editor such as Emacs to provide incremental
redefinition of sections; the user will generally never need to call
it directly.

@e
(defpackage "COMMON-LISP-WEB"
  (:nicknames "CLWEB")
  (:use "COMMON-LISP")
  (:export "TANGLE-FILE" "LOAD-WEB" "WEAVE" "LOAD-SECTIONS-FROM-TEMP-FILE"))
(in-package "CLWEB")

@ A \CLWEB\ source file consists of a mixture of \TeX, Lisp, and \WEB\
control codes, but which one is primary depends on your point of view.
The \CWEB\ manual, for instance, says that ``[w]riting \CWEB\ programs is
something like writing \TeX\ documents, but with an additional `C mode'
that is added to \TeX's horizontal mode, vertical mode, and math mode.''
The same applies, {\it mutatis mutandis,} to the current system, but one
might just as easily think of a web as some code with documentation blocks
and special control codes sprinkled throughout, or as a completely separate
language containing blocks that happen to have the syntax (more or less) of
\TeX\ and Lisp. For the purposes of understanding the implementation, this
last view is perhaps the most useful, since the control codes determine
which syntax to use in reading the material that follows.

The syntax of the \CLWEB\ control codes themselves is similar to that of
dispatching reader macro characters in Lisp: they all begin with
`\.{@@}$x$', where~$x$ is a single character that selects the control code.
Most of the \CLWEB\ control codes are quite similar to the ones used in
\CWEB; see the \CWEB\ manual for detailed descriptions of the individual
codes.

@*Sections. The fundamental unit of a web is the {\it section}, which may
be either {\it named\/} or~{\it unnamed\/}. Named sections are conceptually
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

Aside from a name, a section may have a {\it commentary part\/}, optionally
followed by a {\it code part}. (We don't support the `middle' part of a
section that \WEB\ and \CWEB's sections have, since the kinds of definitions
that can appear there are essentially irrelevant in Lisp.)  The commentary
part consists of \TeX\ material that describes the section; the weaver
copies it (nearly) verbatim into the \TeX\ output file, and the tangler
ignores it. The code part contains Lisp forms and named section references;
the tangler will eventually evaluate or compile those forms, while the
weaver pretty-prints them to the \TeX\ output file.

@l
(defclass section ()
  ((name :accessor section-name :initarg :name)
   (number :accessor section-number)
   (commentary :accessor section-commentary :initarg :commentary)
   (code :accessor section-code :initarg :code))
  (:default-initargs :commentary nil :name nil :code nil))

@ Two control codes begin a section: \.{@@\ } and~\.{@@*}. Sections
introduced with \.{@@*} (`starred' sections) begin a new major group of
sections, and get some special formatting during weaving. The control code
\.{@@*} should be immediately followed by a title for this group,
terminated by a period. That title will appear as a run-in heading at the
beginning of the section, as a running head on all subsequent pages until
the next starred section, and in the table of contents.

The tangler does not care about the distinction between sections with stars
and ones with none upon thars.

@l
(defclass starred-section (section) ())

@ There can also be \TeX\ text preceding the start of the first section
(i.e., before the first \.{@@\ } or \.{@@*}), called {\it limbo text}.
Limbo text is generally used to define document-specific formatting
macros, set up fonts, \etc. The weaver passes it through virtually verbatim
to the output file (only replacing occurrences of `\.{@@@@}' with~`\.{@@}'),
and the tangler ignores it completely.

A single instance of the class |limbo-section| contains the limbo text in
its |commentary| slot; it will never have a code part.

@l
(defclass limbo-section (section) ())

@ Whenever we create a section, we store it in the global |*sections*|
vector and set its number to its index therein. This means that section
objects won't be collected by the \csc{gc} even after the tangling or
weaving has completed, but there's a good reason: keeping them around
allows incremental redefinition of a web, which is important for interactive
development.

@l
(defvar *sections* (make-array 128
                               :element-type 'section
                               :adjustable t
                               :fill-pointer 0))

(defmethod initialize-instance :after ((section section) &rest initargs &key)
  (declare (ignore initargs))
  (setf (section-number section) (vector-push-extend section *sections*)))

(defun current-section ()
  (elt *sections* (1- (fill-pointer *sections*))))

@ @<Initialize global variables@>=
(setf (fill-pointer *sections*) 0)

@ We keep named sections in a binary search tree whose keys are section
names and whose values are code forms; the tangler will replace references
to those names with the associated code. We use a tree instead of, say,
a hash table so that we can support abbreviations (see below).

@l
(defclass binary-search-tree ()
  ((key :accessor node-key :initarg :key)
   (value :accessor node-value :initarg :value)
   (left-child :accessor left-child :initarg :left)
   (right-child :accessor right-child :initarg :right))
  (:default-initargs :left nil :right nil))

@ The primary interface to the \csc{bst} is the following routine, which
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

@ As mentioned above, named sections can be defined piecemeal, with the
code spread out over several sections in the \CLWEB\ source. We might think
of a named section as a sort of `virtual' section, which consists of a
name, the combined code parts of all of the physical sections with that
name, and the number of the first such section.

And that's what we store in the \csc{bst}: nodes that look like sections,
inasmuch as they have specialized |section-name|, |section-code|, and
|section-number| methods, but are not actually instances of the class
|section|.

The two additional slots, |used-by| and |see-also|, are used by the weaver
to generate cross-references. The former contains a list of all the
sections that reference this named section, and the latter contains a list
of the other sections that share this name.

@l
(defclass named-section (binary-search-tree)
  ((key :accessor section-name :initarg :name)
   (value :accessor section-code :initarg :code)
   (number :accessor section-number)
   (used-by :accessor used-by :initform '())
   (see-also :accessor see-also :initform '())))

@ When we encounter a named section that already has some code associated
with it, we normally append the new forms to the old: this allows piecemeal
definition. However, sometimes we want to override that behavior and have
the new forms replace the old, such as during interactive development.

@l
(defun set-named-section-code (section forms &optional (appendp t))
  (setf (section-code section)
        (if (and appendp (slot-boundp section 'value))
            (append (section-code section) forms)
            forms)))

@ Section names in the input file can be abbreviated by giving a prefix of
the full name followed by `$\ldots$': e.g., \.{@@<Frob...@@>} might refer
to the section named `Frob foo and tweak bar'.

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

@ Next, we need some special comparison routines for section names that
handle abbreviations. We'll use these as the |:test| and |:predicate|
functions for our \csc{bst}.

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
            (error "~<Ambiguous prefix <~A>: matches both <~A> and <~A>~:@>"
                   (list item (node-key node) (node-key alt)))
          (use-first-match ()
            :report "Use the first match."
            (return (values node t)))
          (use-alt-match ()
            :report "Use alternate match."
            (return (values alt t))))))))

@ We store our named section tree in the global variable |*named-sections*|,
which is reset before each tangling or weaving. The reason this is global is
the same as the reason |*sections*| was: to allow incremental redefinition.

@l
(defvar *named-sections* nil)

@ @<Initialize global variables@>=
(setq *named-sections* nil)

@ Section names are normalized by |squeeze|, which trims leading and
trailing whitespace and replaces all runs of one or more whitespace
characters with a single space.

@l
(defparameter *whitespace*
  #.(coerce '(#\Space #\Tab #\Newline #\Linefeed #\Page #\Return) 'string))

(defun whitespacep (char) (find char *whitespace* :test #'char=))

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

@*Reading. We recognize five distinct modes for reading. Limbo mode is
used for \TeX\ text that proceeds the first section in a file. \TeX\ mode
is used for reading the commentary that begins a section. Lisp mode is
used for reading the code part of a section; inner-Lisp mode is for
reading Lisp forms that are embedded within \TeX\ material. And finally,
restricted mode is used for reading material in section names and a few
other places.

@l
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *modes* '(:limbo :TeX :lisp :inner-lisp :restricted)))
(deftype mode () `(member ,@*modes*))

@ We use seperate readtables for each mode, which are accessed via
|readtable-for-mode|. We add an extra readtable with key |nil| that
stores a virgin copy of the standard readtable.

@l
(defvar *readtables*
  (loop for mode in (cons nil *modes*)
        collect (cons mode (copy-readtable nil))))

(defun readtable-for-mode (mode)
  (declare (type (or mode null) mode))
  (cdr (assoc mode *readtables*)))

@ The following macro is just a bit of syntactic sugar for executing the
given forms with |*readtable*| bound appropriately for the given mode.

@l
(defmacro with-mode (mode &body body)
  `(let ((*readtable* (readtable-for-mode ,mode)))
     ,@body))

@ We frequently need an object to use as the |eof-value| argument to
|read|. It need not be a symbol; it need not even be an atom.

@l
(defvar *eof* (make-symbol "EOF"))
(defun eof-p (x) (eq x *eof*))
(deftype eof () '(satisfies eof-p))

@ We'll occasionally need to know if a given character terminates a token
or not. This function answers that question, but only approximately---if
the user has frobbed the current readtable and set non-standard characters
to whitespace syntax, {\it this routine will not yield the correct
result}. There's unfortunately nothing that we can do about it portably,
since there's no way of determining the syntax of a character or of
obtaining a list of all the characters with a given syntax.

@l
(defun token-delimiter-p (char)
  (or (whitespacep char)
      (multiple-value-bind (function non-terminating-p)
          (get-macro-character char)
        (and function (not non-terminating-p)))))

@ We want the weaver to output properly indented code, but it's basically
impossible to automatically indent Common Lisp code without a complete
static analysis. And so we don't try. What we do instead is assume that the
input is indented correctly, and try to approximate that on output; we call
this process {\it indentation tracking\/}.

The way we do this is to record the the column number, or {\it character
position}, of every Lisp form in the input, and use those positions to
reconstruct the original indentation. One could use Gray streams to do
this, but we don't actually need them; the stream types provided by Common
Lisp suffice.

We'll define a {\it charpos stream\/} as an object that tracks the
character position of an underlying stream. Note that these aren't actual
streams, and can't be without relying on an extension to Common Lisp like
Gray streams. But we'll implement them by using an echo stream that takes
its input from---or a broadcast stream that sends its output to---the
original stream: we'll call these composite streams {\it proxy streams},
since they'll be passed around in place of the original, underlying stream
objects. But because they're sub-types of |stream|, they can be used with
all of the standard stream functions.

The current character position is retrieved with the \csc{gf} |charpos|.
It relies the last stored charpos (stored in the |charpos| slot) and a
buffer that stores the characters input or output since the last call to
|charpos|, retrieved with the \csc{gf} |get-charpos-stream-buffer|.

@l
(defclass charpos-stream ()
  ((charpos :initarg :charpos)
   (stream :accessor charpos-stream :initarg :stream))
  (:default-initargs :charpos 0))

(defgeneric charpos (stream))
(defgeneric get-charpos-stream-buffer (stream))

@ We need slightly different classes for input charpos streams and output
charpos streams. For tracking charpos on input streams, our proxy stream is
an echo stream that takes input from the supplied stream (the original value
of the |:stream| initarg) and sends its output to a string stream, which
we'll use as our buffer.

@l
(defclass charpos-input-stream (charpos-stream) ())

(defmethod shared-initialize :around ((instance charpos-input-stream) slot-names
                                      &rest initargs &key stream)
  (apply #'call-next-method instance slot-names
         (list* :stream (make-echo-stream
                         stream
                         (make-string-output-stream
                          :element-type (stream-element-type stream)))
                initargs)))

(defmethod get-charpos-stream-buffer ((stream charpos-input-stream))
  (get-output-stream-string
   (echo-stream-output-stream (charpos-stream stream))))

@ For the output stream case, our proxy stream is a broadcast stream to the
given stream and a fresh string stream, again used as a buffer.

@l
(defclass charpos-output-stream (charpos-stream) ())

(defmethod shared-initialize :around ((instance charpos-output-stream) slot-names
                                      &rest initargs &key stream)
  (apply #'call-next-method instance slot-names
         (list* :stream (make-broadcast-stream
                         (make-string-output-stream
                          :element-type (stream-element-type stream))
                         stream)
                initargs)))

(defmethod get-charpos-stream-buffer ((stream charpos-output-stream))
  (get-output-stream-string
   (first (broadcast-stream-streams (charpos-stream stream)))))

@ Finding the actual character position is now straightforward, and the same
for both input and output streams.

@l
(defmethod charpos ((stream charpos-stream))
  (let* ((i 0)
         (newline (position #\Newline (get-charpos-stream-buffer stream)
                            :key (lambda (x) (incf i) x)
                            :test #'char=
                            :from-end t)))
    (if newline
        (setf (slot-value stream 'charpos) i)
        (incf (slot-value stream 'charpos) i))))

@ Because we'll be passing around the proxy streams, we need to manually
maintain a mapping between them and their associated instances of
|charpos-stream|.

@l
(defvar *charpos-streams* (make-hash-table :test #'eq))

(defmethod initialize-instance :after ((instance charpos-stream) ;
                                       &rest initargs &key)
  (declare (ignore initargs))
  (setf (gethash (charpos-stream instance) *charpos-streams*) instance))

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
    (cond (present-p (setf (charpos-stream charpos-stream) nil) ; release stream
                     (remhash stream *charpos-streams*))
          (t (warn "Not tracking charpos for ~S" stream)))))

@ Here are a few convenience methods for creating charpos streams. Note that
|input-stream| and |output-stream| are stream designators.

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

@ And finally, a couple of macros that make using them easy and trouble-free.
They execute |body| in a lexical environment in which |var| is bound to a
proxy stream the tracks the character position for |stream|.

@l
(defmacro with-charpos-input-stream ((var stream &key (charpos 0)) &body body)
  `(let ((,var (charpos-stream ;
                (make-charpos-input-stream ,stream :charpos ,charpos))))
     (unwind-protect (progn ,@body)
       (release-charpos-stream ,var))))

(defmacro with-charpos-output-stream ((var stream &key (charpos 0)) &body body)
  `(let ((,var (charpos-stream ;
                (make-charpos-output-stream ,stream :charpos ,charpos))))
     (unwind-protect (progn ,@body)
       (release-charpos-stream ,var))))

@ Sometimes we'll want to look more than one character ahead in a stream.
This macro lets us do so, after a fashion: it executes |body| in a lexical
environment where |var| is bound to a stream whose input comes from
|stream| and |rewind| is a local function that `rewinds' the stream to its
state prior to any reads executed in the body.

@l
(defmacro with-rewind-stream ((var stream &optional (rewind 'rewind))
                              &body body &aux (out (gensym)))
  `(with-open-stream (,out (make-string-output-stream))
     (with-open-stream (,var (make-echo-stream ,stream ,out))
       (flet ((,rewind ()
                (setq ,var (make-concatenated-stream
                            (make-string-input-stream ;
                             (get-output-stream-string ,out))
                            ,stream))))
         ,@body))))

@ And sometimes, we'll want to call |read| on a stream, and keep a copy of
the characters that |read| actually scans. This macro reads from |stream|,
then executes the |body| forms with |values| bound to a list of the values
returned by |read|, and |echoed| bound to a variable containing the
characters so consumed. If |prefix| is supplied, it should be a string that
will be concatenated onto the front of |stream| prior to reading.

@l
(defmacro read-with-echo ((stream values echoed &key prefix) &body body &aux
                          (out (gensym)) (echo (gensym)) (rewind (gensym))
                          (raw-output (gensym)) (length (gensym)))
  `(with-open-stream (,out (make-string-output-stream))
     (with-open-stream (,echo (make-echo-stream ,stream ,out))
       (with-open-stream (,rewind (make-concatenated-stream
                                   ,@(when prefix
                                       `((make-string-input-stream ,prefix)))
                                   ,echo))
         (let* ((,values (multiple-value-list ;
                          (read-preserving-whitespace ,rewind)))
                (,raw-output (get-output-stream-string ,out))
                (,length (length ,raw-output))
                (,echoed (subseq ,raw-output
                                 0
                                 (if (or (eof-p ;
                                          (peek-char nil ,stream nil *eof*))
                                         (token-delimiter-p ;
                                          (elt ,raw-output (1- ,length))))
                                     ,length
                                     (1- ,length)))))
           (declare (ignorable ,values ,echoed))
           ,@body)))))

@ Next, we define a class of objects called {\it markers\/} that denote
abstract objects in source code. Some of these objects, such as newlines
and comments, are ones that would ordinarily be ignored by the reader.
Others, such as \.{()} and~\.{'}, are indistinguishable after reading from
other, semantically equivalent objects (here, |nil| and |quote|), but we
want to preserve the distinction in the output. In fact, nearly every
standard macro character in Common Lisp is `lossy', in the sense that the
text of the original source code can not be reliably recovered from the
object returned by |read|.

But during weaving, we want to more closely approximate the original source
code than would be possible using the standard reader. Markers are our
solution to this problem: we define reader macro functions for all of the
standard macro characters that return markers that let us reconstruct, to
varying degrees of accuracy, what was originally given in the source.

If a marker is {\it bound}---i.e., if |marker-boundp| returns non-nil when
called with it as an argument---then the tangler will call |marker-value|
to obtain the associated value. (The value need not be stored in the
|value| slot, but often is.) Otherwise, the marker will be silently dropped
from its containing form; this is used, e.g., for newlines and comments.

@l
(defclass marker ()
  ((value :reader marker-value :initarg :value)))
(defun markerp (x) (typep x 'marker))

(defgeneric marker-boundp (marker))
(defmethod marker-boundp ((marker marker))
  (slot-boundp marker 'value))

@ We also define |print-object| methods for all marker classes. These
methods are distinct from the pretty-printing routines used by the weaver,
and usually less precise, in that they don't try to approximate the original
source form. The idea of these methods to produce a printed representation of
an object that is semantically equivalent to the one originally specified.

The simple method defined here suffices for many marker types: it simply
prints the marker's value if it is bound.

@l
(defmethod print-object ((obj marker) stream)
  (when (marker-boundp obj)
    (write (marker-value obj) :stream stream)))

@ A few of the markers behave differently when tangling for the purposes
of evaluation (e.g., within a call to |load-web|) than when writing out a
tangled Lisp source file. We need this distinction only for read-time
evaluated constructs, such as \.{\#.} and~\.{\#+}/\.{\#-}.

@l
(defvar *evaluating* nil)

@ Our first marker is for newlines, which we preserve for the purposes of
indentation. They are represented in code forms by an unbound marker, so
they will simply be dropped by the tangler.

Note that we don't set a macro character for |#\Newline| in inner-Lisp mode,
since indentation is completely ignored there.

@l
(defclass newline-marker (marker)
  ((indentation :accessor indentation :initform nil)))
(defun newlinep (obj) (typep obj 'newline-marker))

(set-macro-character #\Newline
                     (lambda (stream char)
                       (declare (ignore stream char))
                       (make-instance 'newline-marker))
                     nil (readtable-for-mode :lisp))

@ The rest of the reader macro functions for standard macro characters are
defined in the order given in section~2.4 of the \csc{ansi} Common Lisp
standard. We override all of the standard macro characters except |#\)|
and~|#\"| (the former because the standard reader macro function just
signals an error, which is fine, and the latter because we don't need
markers for strings).

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
             (let ((obj (list (marker-value x))))
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
  (cond ((and (markerp x) (marker-boundp x))
         (return (marker-value x)))
        ((not (markerp x))
         (return x))))

@ We don't use |list-marker|s at all in inner-Lisp mode (since we don't do
indentation tracking there), but we still want markers for the empty list.
The function |make-list-reader| returns a closure that peeks ahead in the
given stream looking for a closing parenthesis, and either returns an
empty-list marker or invokes a full list-reading function, which is stored
in the variable |next|. For inner-Lisp mode, that function is the standard
reader macro function for |#\(|.

@l
(defun make-list-reader (next)
  (lambda (stream char)
    (if (char= (peek-char t stream t nil t) #\) )
        (progn (read-char stream t nil t) *empty-list*)
        (funcall next stream char))))

(set-macro-character #\( (make-list-reader (get-macro-character #\( nil))
                     nil (readtable-for-mode :inner-lisp))

@ In Lisp mode, we need a full list reader that records character positions
of the list elements. This would be perfectly straightforward if not for the
consing dot.

@l
(defun list-reader (stream char)
  (declare (ignore char))
  (loop with list = '()
        with charpos-list = '()
        for n from 0
        for first-char = (peek-char t stream t nil t)
        as charpos = (stream-charpos stream)
        until (char= first-char #\) )
        if (char= first-char #\.) do @<Read the next token from |stream|...@>
        else do @<Read the next object from |stream|...@>
        finally (read-char stream t nil t)
                (return (make-instance 'list-marker
                                       :length n
                                       :list (nreverse list)
                                       :charpos (nreverse charpos-list)))))

(set-macro-character #\( (make-list-reader #'list-reader)
                     nil (readtable-for-mode :lisp))

@ @<Read the next token from |stream|, which might be a consing dot@>=
(with-rewind-stream (stream stream)
  (read-char stream t) ; consume dot
  (let ((next-char (read-char stream t)))
    (cond ((token-delimiter-p next-char)
           (unless (or list *read-suppress*)
             (simple-reader-error stream "Nothing appears before . in list."))
           (push *consing-dot* list)
           (push charpos charpos-list))
          (t (rewind)
             @<Read the next object from |stream|...@>))))

@ We have to be careful here, because |read| might not return any values,
in which case we don't want to push anything.

@<Read the next object from |stream| and push it onto |list|@>=
(let ((values (multiple-value-list (read stream t nil t))))
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

@ {\it Semicolon.} Comments in Lisp code also need to be preserved for
output during weaving. We use a slot distinct from the value slot for
storing the text of the comment so that they can remain unbound and thus
be stripped during tangling.

@l
(defclass comment-marker (marker)
  ((text :reader comment-text :initarg :text)))

@ Usually, to read a comment we accumulate all of the characters starting
with the semicolon and ending just before the next newline, which we leave
for the newline reader to pick up. But as a special exception, if the
comment is empty (that is, consists solely of a single semicolon), the
newline is consumed, and we return zero values. This provides for
`soft newlines'---that is, newlines in the source file that will not
appear in the output.

@l
(defun comment-reader (stream char)
  (if (char= (peek-char nil stream nil nil t) #\Newline)
      (progn (read-char stream t nil t) (values))
      (make-instance 'comment-marker
                     :text @<Read characters up to...@>)))

(set-macro-character #\; #'comment-reader nil (readtable-for-mode :lisp))

@ @<Read characters up to, but not including, the next newline@>=
(with-output-to-string (s)
  (write-char char s) ; include the opening |#\;|
  (do ()
      ((char= (peek-char nil stream nil #\Newline t) #\Newline))
    (write-char (read-char stream t nil t) s)))

@ {\it Backquote\/} is hairy, and so we use a kludge to avoid implementing
the whole thing. Our reader macro functions for |#\`| and |#\,| do the
absolute minimum amount of processing necessary to be able to reconstruct
the forms that were read. When the tangler asks for the |marker-value| of a
backquote marker, we reconstruct the source form using the printer, and
read it back in using the standard readtable. It's a sleazy trick, but it
works. (It's also the reason we need |print-object| methods for all these
markers.)

Of course, this trick assumes read-print equivalence, but that's not
unreasonable, since without it the file tangler won't work anyway.

@l
(defclass backquote-marker (marker)
  ((form :reader backq-form :initarg :form)))

(defmethod marker-boundp ((marker backquote-marker)) t)
(defmethod marker-value ((marker backquote-marker))
  (let ((*print-pretty* nil)
        (*print-readably* t)
        (*readtable* (readtable-for-mode nil)))
    (read-from-string (prin1-to-string marker))))

(defmethod print-object ((obj backquote-marker) stream)
  (format stream "`~W" (backq-form obj)))

(defun backquote-reader (stream char)
  (declare (ignore char))
  (make-instance 'backquote-marker :form (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-macro-character #\` #'backquote-reader nil (readtable-for-mode mode)))

@ {\it Comma\/} is really just part of the backquote-syntax, and so we're
after the same goal as above: reconstructing just enough of the original
source so that the reader can do what it would have done had we not been
here in the first place.

Note that comma markers are bound, but self-evaluating: they need to be
printed and re-read as part of a backquote form to retrieve their actual
value.

@l
(defclass comma-marker (marker)
  ((form :reader comma-form :initarg :form)
   (modifier :reader comma-modifier :initarg :modifier))
  (:default-initargs :modifier nil))

(defmethod marker-boundp ((marker comma-marker)) t)
(defmethod marker-value ((marker comma-marker)) marker)

(defmethod print-object ((obj comma-marker) stream)
  (format stream ",~@[~C~]~W" (comma-modifier obj) (comma-form obj)))

(defun comma-reader (stream char)
  (declare (ignore char))
  (case (peek-char nil stream t nil t)
    ((#\@ #\.) (make-instance 'comma-marker
                              :modifier (read-char stream)
                              :form (read stream t nil t)))
    (t (make-instance 'comma-marker :form (read stream t nil t)))))

(dolist (mode '(:lisp :inner-lisp))
  (set-macro-character #\, #'comma-reader nil (readtable-for-mode mode)))

@ {\it Sharpsign\/} is the all-purpose dumping ground for Common Lisp
reader macros. Because it's a dispatching macro character, we have to
handle each sub-char individually, and unfortunately we need to override
most of them. We'll handle them in the order given in section~2.4.8
of the CL standard.

@ Sometimes we'll have to detect and report errors during reading. This
condition class and associated signaling function allow |format|-style
error reporting.

@l
(define-condition simple-reader-error (reader-error simple-condition) ()
  (:report (lambda (condition stream)
             (format stream "~S on ~S:~%~?"
                     condition (stream-error-stream condition)
                     (simple-condition-format-control condition)
                     (simple-condition-format-arguments condition)))))

(defun simple-reader-error (stream control &rest args)
  (error 'simple-reader-error
         :stream stream
         :format-control control
         :format-arguments args))

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

@ Sharpsign left-parenthesis and sharpsign asterisk create |simple-vector|s
and |simple-bit-vector|s, respectively. The feature that we care about
preserving is the length specification and consequent possible abbreviation.

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

@ Sharpsign asterisk is similar, but the token following the asterisk must
be composed entirely of \.{0}s and \.{1}s. It supports the same kind of
abbreviation that \.{\#()} does.

Note the use of the word `token' above. By defining \.{\#*} in terms of the
{\it token\/} following the \.{*}, the authors of the standard have made it
very, very difficult for a portable program to emulate the specified behavior,
since only the built-in reader knows how to tokenize for the current
readtable. What we do is resort to a dirty trick: we set up an echo stream,
use the standard reader to parse the bit vector, then build our marker from
the echoed characters.

@l
(defclass bit-vector-marker (simple-vector-marker) ()
  (:default-initargs :element-type 'bit))

(defun simple-bit-vector-reader (stream sub-char arg)
  (declare (ignore sub-char))
  (let ((*readtable* (readtable-for-mode nil)))
    (read-with-echo (stream values bits :prefix (format nil "#~@[~D~]*" arg))
      (apply #'make-instance 'bit-vector-marker
             :elements @<Build a bit vector...@>
             (if arg (list :length arg))))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\* #'simple-bit-vector-reader ;
                                (readtable-for-mode mode)))


@ The string |bits| now contains the `0' and~`1' characters that make up
the bit vector. But it might also contain the delimiter that terminates the
token, so we have to be careful.

@<Build a bit vector from the characters in |bits|@>=
(map 'bit-vector
     (lambda (c) (ecase c (#\0 0) (#\1 1)))
     (subseq bits 0 (let ((n (length bits)))
                      (case (elt bits (1- n)) ((#\0 #\1) n) (t (1- n))))))

@ Sharpsign dot permits read-time evaluation. Ordinarily, of course, the
form evaluated is lost, as only the result of the evaluation is returned.
We want to preserve the form for both weaving and tangling to a file. But
we also want to return the evaluated form as the |marker-value| when we're
tangling for evaluation. So if we're not evaluating, we return a special
`pseudo-marker' with a specialized |print-object| method. This gives us an
appropriate value in all three situations: during weaving, we have just
another marker; when tangling for evaluation, we get the read-time-evaluated
value; and in a tangled source file, we get a \.{\#.} form.

@l
(defclass read-time-eval ()
  ((form :reader read-time-eval-form :initarg :form)))

(defmethod print-object ((obj read-time-eval) stream)
  (format stream "#.~W" (read-time-eval-form obj)))

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
      (make-instance 'read-time-eval-marker :form form :value (eval form)))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\. #'sharpsign-dot-reader ;
                                (readtable-for-mode mode)))

@ Sharpsign B, O, X, and~R all represent rational numbers in a specific
radix, but the radix is discarded by the standard reader, which just
returns the number. We use the standard reader macro function for getting
the actual value, and store the radix in our marker.

@l
(defclass radix-marker (marker)
  ((base :reader radix-marker-base :initarg :base)))

(defvar *radix-prefix-alist* '((#\B . 2) (#\O . 8) (#\X . 16) (#\R . nil)))

(defun radix-reader (stream sub-char arg)
  (make-instance 'radix-marker
                 :base (or (cdr (assoc sub-char *radix-prefix-alist*)) arg) 
                 :value @<Call the standard reader macro fun...@>))

(dolist (mode '(:lisp :inner-lisp))
  (dolist (sub-char '(#\B #\O #\X #\R))
    (set-dispatch-macro-character #\# sub-char #'radix-reader ;
                                  (readtable-for-mode mode))))

@ @<Call the standard reader macro function for \.{\#\metasyn{|sub-char|}}@>=
(funcall (get-dispatch-macro-character #\# sub-char (readtable-for-mode nil))
         stream sub-char arg)

@ Sharpsign~S requires determining the standard constructor function of the
structure type named, which we simply can't do portably. So we use the same
trick we used for backquote above: we cache the form as given, then dump it
out to a string and let the standard reader parse it when we need the value.

@l
(defclass structure-marker (marker)
  ((form :reader structure-marker-form :initarg :form)))

(defmethod marker-boundp ((marker structure-marker)) t)
(defmethod marker-value ((marker structure-marker))
  (let ((*print-pretty* nil)
        (*print-readably* t)
        (*readtable* (readtable-for-mode nil)))
    (read-from-string (prin1-to-string marker))))

(defmethod print-object ((obj structure-marker) stream)
  (format stream "#S~W" (structure-marker-form obj)))

(defun structure-reader (stream sub-char arg)
  (declare (ignore sub-char arg))
  (make-instance 'structure-marker :form (read stream t nil t)))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\S #'structure-reader ;
                                (readtable-for-mode mode)))

@ Sharpsign + and~-- provide read-time conditionalization based on
feature expressions, described in section~24.1.2 of the CL standard.
This routine, adapted from SBCL, interprets such an expression.

@l
(defun featurep (x)
  (etypecase x
    (cons
     (case (car x)
       ((:not not)
        (cond
          ((cddr x)
           (error "too many subexpressions in feature expression: ~S" x))
          ((null (cdr x))
           (error "too few subexpressions in feature expression: ~S" x))
          (t (not (featurep (cadr x))))))
       ((:and and) (every #'featurep (cdr x)))
       ((:or or) (some #'featurep (cdr x)))
       (t
        (error "unknown operator in feature expression: ~S." x))))
    (symbol (not (null (member x *features* :test #'eq))))))

@ For sharpsign +/--, we use the same sort of trick we used for \.{\#.}
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

(defmethod print-object ((obj read-time-conditional) stream)
  (format stream "#~:[-~;+~]~S ~A"
          (read-time-conditional-plusp obj)
          (read-time-conditional-test obj)
          (read-time-conditional-form obj)))

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
    (read-with-echo (stream values form)
      (apply #'make-instance 'read-time-conditional-marker
             :plusp plusp :test test :form form
             (and (not *read-suppress*) values (list :value (car values)))))))

(dolist (mode '(:lisp :inner-lisp))
  (set-dispatch-macro-character #\# #\+ #'read-time-conditional-reader ;
                                (readtable-for-mode mode))
  (set-dispatch-macro-character #\# #\- #'read-time-conditional-reader ;
                                (readtable-for-mode mode)))

@ Okay, so much for the standard macro characters. Now we're ready to move
on to \WEB-specific reading. We accumulate \TeX\ mode material such as
commentary, section names, \etc. using the following function, which reads
from |stream| until encountering either \EOF\ or an element of the
|control-chars| argument, which should be a designator for a list of
 characters.

@l
(defun snarf-until-control-char (stream control-chars &aux
                                 (control-chars (if (listp control-chars)
                                                    control-chars
                                                    (list control-chars))))
  (with-output-to-string (string)
    (loop for char = (peek-char nil stream nil *eof* nil)
          until (or (eof-p char) (member char control-chars))
            do (write-char (read-char stream) string))))

@ In \TeX\ mode (including restricted contexts), we allow embedded Lisp
code to be surrounded by \pb, where it is read in inner-Lisp mode.

@l
(defun read-inner-lisp (stream char)
  (with-mode :inner-lisp
    (read-delimited-list char stream t)))

(dolist (mode '(:TeX :restricted))
  (set-macro-character #\| #'read-inner-lisp nil (readtable-for-mode mode)))

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
  ;; to signal an error, but SBCL does so; hence the |ignore-errors|.
  (ignore-errors
    (make-dispatch-macro-character #\@ t (readtable-for-mode mode))))

(defun get-control-code (sub-char mode)
  (get-dispatch-macro-character #\@ sub-char (readtable-for-mode mode)))

(defun set-control-code (sub-char function &optional (modes *modes*))
  (dolist (mode (if (listp modes) modes (list modes)))
    (set-dispatch-macro-character #\@ sub-char function ;
                                  (readtable-for-mode mode))))

@ The control code \.{@@@@} yields the string \.{"@@"} in all modes, but
it should really only be used in \TeX\ text.

@l
(set-control-code #\@ (lambda (stream sub-char arg)
                        (declare (ignore sub-char stream arg))
                        (string "@")))

@ Sections are introduced by the two section-starting control codes,
\.{@@\ } and~\.{@@*}, which differ only in the way they are output during
weaving. The reader macro functions that implement these control codes
return an instance of the appropriate section class.

@l
(defun start-section-reader (stream sub-char arg)
  (declare (ignore stream arg))
  (make-instance (ecase sub-char
                   (#\Space 'section)
                   (#\* 'starred-section))))

(dolist (sub-char '(#\Space #\*))
  (set-control-code sub-char #'start-section-reader '(:limbo :TeX :lisp)))

@ The control codes \.{@@l} and ~\.{@@p} (where `l' is for `Lisp' and `p'
is for `program'---both control codes do the same thing) begin the code
part of an unnamed section. They are recognized only in \TeX\ mode---every
section must begin with a commentary, even if it is empty.

The control code \.{@@e} (`e' for `evaluate') is similar to \.{@@l} in that
it begins the code part of an unnamed section, but every form in that part
is evaluated by both the tangler and the weaver as soon as they read it,
{\it in addition to\/} being tangled into the output file (and therefore
evaluated at run-time, and possibly compile-time, too). Sections containing
evaluated code-parts should be used only for establishing state that is
needed by the reader: package definitions, structure definitions that are
used with \.{\#S}, \etc.

@l
(defclass start-code-marker (marker)
  ((name :reader section-name :initarg :name)
   (evalp :reader evaluated-code-p :initarg :evalp))
  (:default-initargs :name nil :evalp nil))

(defun start-code-reader (stream sub-char arg)
  (declare (ignore stream arg))
  (make-instance 'start-code-marker
                 :evalp (ecase (char-downcase sub-char)
                          ((#\l #\p) nil)
                          ((#\e) t))))

(dolist (sub-char '(#\l #\p #\e))
  (set-control-code sub-char #'start-code-reader '(:TeX :lisp)))

@ Several control codes, including \.{@@<}, contain `restricted' \TeX\ text,
called {\it control text}, that extends to the next \.{@@>}. When we first
read control text, we ignore inner-Lisp material (that is, Lisp forms
surrounded by \pb). During weaving, we'll re-scan it to pick up such
material.

@l
(defvar *end-control-text* (make-symbol "@>"))
(set-control-code #\> (constantly *end-control-text*) :restricted)

(defun read-control-text (stream)
  (with-mode :restricted
    (apply #'concatenate 'string
           (loop for text = (snarf-until-control-char stream #\@)
                 as x = (read-preserving-whitespace stream t nil t)
                 collect text
                 if (eq x *end-control-text*) do (loop-finish)
                 else collect x))))

@ The control code \.{@@<} introduces a section name, which extends to the
closing \.{@@>}. Its meaning is context-dependent.

In \TeX\ mode, a name must be followed by \.{=}, which attaches the name to
the current section and begins the code part.

In Lisp and inner-Lisp modes, a name is taken to refer to the section so
named. During tangling, such references in Lisp mode will be replaced with
the code defined for that section. References in inner-Lisp mode are only
citations, and so are not expanded.

@l
(defun make-section-name-reader (definition-allowed-p)
  (lambda (stream sub-char arg)
    (declare (ignore sub-char arg))
    (let* ((name (read-control-text stream))
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
                 (pushnew (current-section) (used-by named-section))
                 named-section))))))

(set-control-code #\< (make-section-name-reader t) :TeX)
(set-control-code #\< (make-section-name-reader nil) '(:lisp :inner-lisp))

@ @<Signal an error about section definition in Lisp mode@>=
(restart-case
    (error "Can't define a named section in Lisp mode: ~A" name)
  (use-section ()
    :report "Don't define the section, just use it."
    (find-section name)))

@ @<Signal an error about section name use in \TeX\ mode@>=
(restart-case
    (error "Can't use a section name in TeX mode: ~A" name)
  (name-section ()
    :report "Name the current section and start the code part."
    (make-instance 'start-code-marker :name name))
  (cite-section ()
    :report "Assume the section is just being cited."
    (find-section name)))

@ When we're accumulating forms from the code part of a section, we'll
interpret two newlines in a row as ending a paragraph, as in \TeX.

@l
(defclass par-marker (newline-marker) ())
(defvar *par* (make-instance 'par-marker))

@ We need one last utility before coming to the main section reader.
When we're accumulating text, we don't want to bother with empty strings.
So we use the following macro, which is like |push|, but does nothing if
the new object is an empty string or |nil|.

@l
(defmacro maybe-push (obj place &aux (g (gensym)))
  `(let ((,g ,obj))
     (when (if (stringp ,g) (plusp (length ,g)) ,g)
       (push ,g ,place))))

@ We come now to the heart of the \WEB\ parser. This function is a
tiny state machine that models the global syntax of a \WEB\ file.
(We can't just use reader macros since sections and their parts lack
explicit closing delimiters.) It returns a list of |section| objects.

@l
(defun read-sections (input-stream &optional (appendp t))
  (with-charpos-input-stream (stream input-stream)
    (flet ((finish-section (section commentary code)
             @<Trim whitespace and reverse...@>
             (setf (section-commentary section) commentary)
             (setf (section-code section) code)
             (when (section-name section) @<Setup named section...@>)
             section))
      (prog (form commentary code section sections)
       limbo
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
    (setq form (read-preserving-whitespace stream nil *eof* nil))
    (typecase form
      (eof (go eof))
      (section (go commentary))
      (t (push form commentary)))))

@ @<Finish the last section and initialize section variables@>=
(push (finish-section section commentary code) sections)
(check-type form section)
(setq section form
      commentary '()
      code '())

@ The commentary part that begins a section consists of \TeX\ text and
inner-Lisp material surrounded by \pb. It is terminated by either the start
of a new section, the beginning of the code part, or \EOF. If a code part
is detected, we also set the name of the current section, which may be |nil|.

@<Accumulate \TeX-mode material in |commentary|@>=
(with-mode :TeX
  (loop
    (maybe-push (snarf-until-control-char stream '(#\@ #\|)) commentary)
    (setq form (read-preserving-whitespace stream nil *eof* nil))
    (typecase form
      (eof (go eof))
      (section (go commentary))
      (start-code-marker (setf (section-name section) (section-name form))
                         (go lisp))
      (t (push form commentary)))))

@ The code part of a section consists of zero or more Lisp forms and is
terminated by either \EOF\ or the start of a new section. If the code
part was begun by a \.{@@e} control code, we evaluate the code forms as we
read them.

@<Accumulate Lisp-mode material in |code|@>=
(check-type form start-code-marker)
(with-mode :lisp
  (let ((evalp (evaluated-code-p form)))
    (loop
      (setq form (read-preserving-whitespace stream nil *eof* nil))
      (typecase form
        (eof (go eof))
        (section (go commentary))
        (start-code-marker @<Complain about starting a section...@>)
        (newline-marker @<Maybe push the newline marker@>)
        (t (when evalp (eval (tangle form)))
           (push form code))))))

@ @<Complain about starting a section without a commentary part@>=
(cerror "Start a new unnamed section with no commentary."
        "Can't start a section with a code part.")
(setq form (make-instance 'section))
@<Finish the last section...@>

@ We won't push a newline marker if no code has been accumulated yet, and
we'll push a paragraph marker instead if there are two newlines in a row.

@<Maybe push...@>=
(unless (null code)
  (cond ((newlinep (car code))
         (pop code)
         (push *par* code))
        (t (push form code))))

@ We trim trailing whitespace from the last string in |commentary|, leading
whitespace from the first, and any trailing newline marker from |code|.
(Leading newlines are handled in |@<Accumulate Lisp-mode...@>|.)

@<Trim whitespace and reverse |commentary| and |code|@>=
(when (stringp (car commentary))
  (rplaca commentary (string-right-trim *whitespace* (car commentary))))
(setq commentary (nreverse commentary))
(when (stringp (car commentary))
  (rplaca commentary (string-left-trim *whitespace* (car commentary))))
(setq code (nreverse (member-if-not #'newlinep code)))

@ @<Setup named section code, number, and cross-references@>=
(let ((named-section (find-section (section-name section)))
      (number (section-number section))
      (code (section-code section)))
  (set-named-section-code named-section code appendp)
  (when (or (not (slot-boundp named-section 'number))
            (not appendp))
    (setf (section-number named-section) number))
  (if appendp
      (pushnew section (see-also named-section))
      (setf (see-also named-section) (list section))))

@*The tangler. Tangling involves recursively replacing each reference to a
named section with the code accumulated for that section. The function
|tangle-1| expands one level of such references, returning the
possibly-expanded form and a boolean representing whether or not any
expansions were actually performed.

Note that this is a splicing operation, like `\.{,@@}', not a simple
substitution, like normal Lisp macro expansion:
if \X$n$:foo\X$\mathrel\E$|(x y)|, then
\((tangle-1 \'(a \X$n$:foo\X\ b))\)$\;\to\;$|(a x y b)|,~|t|.

Tangling also replaces bound markers with their associated values, and
removes unbound markers.

@l
(defun tangle-1 (form)
  (typecase form
    (list-marker (values (marker-value form) t))
    (atom (values form nil))
    ((cons named-section *)
     (values (append (section-code (car form)) (tangle-1 (cdr form))) t))
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
                   (or car-expanded-p cdr-expanded-p)))))))

@ |tangle| repeatedly calls |tangle-1| on |form| until it can no longer be
expanded. Like |tangle-1|, it returns the possibly-expanded form and an
`expanded' flag. This code is adapted from SBCL's |macroexpand|.

@l
(defun tangle (form)
  (labels ((expand (form expanded)
             (multiple-value-bind (new-form newly-expanded-p)
                 (tangle-1 form)
               (if newly-expanded-p
                   (expand new-form t)
                   (values new-form expanded)))))
    (expand form nil)))

@ A little utility function invokes the main section reader and returns a
list of all of the forms in all of the unnamed sections' code parts.

@l
(defun read-code-parts (stream appendp)
  (apply #'append
         (map 'list
              #'section-code
              (remove-if #'section-name (read-sections stream appendp)))))

@ We're now ready for the high-level tangler interface. We begin with
|load-web|, which uses a helper function, |load-web-from-stream|, so
that it can handle input from a file or an arbitrary stream. The logic
is straightforward: loop over the tangled forms read from the stream,
evaluating each one in turn.

Note that like |load|, we bind |*readtable*| and |*package*| to their
current values, so that assignments to those variables in the \WEB\ code
will not effect the calling environment.

@l
(defun load-web-from-stream (stream print &optional (appendp t))
  (let (#+sbcl(sb-ext:*evaluator-mode* :compile)
        (*readtable* *readtable*)
        (*package* *package*)
        (*evaluating* t))
    (dolist (form (tangle (read-code-parts stream appendp)) t)
      (if print
          (let ((results (multiple-value-list (eval form))))
            (format t "~&; ~{~S~^, ~}~%" results))
          (eval form)))))

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
      (with-open-file (stream (merge-pathnames (make-pathname :type "CLW" ;
                                                              :case :common)
                                               filespec)
                       :direction :input
                       :external-format external-format
                       :if-does-not-exist (if if-does-not-exist :error nil))
        (load-web-from-stream stream print))))

@ This next function exists solely for the sake of front-ends that wish to
load a piece of a \WEB, such as the author's `\.{clweb.el}'. Note that it
does {\it not\/} initialize the global variables like |*named-sections*|;
this allows for incremental redefinition.

@l
(defun load-sections-from-temp-file (file appendp &aux
                                     (truename (probe-file file)))
  "Load web sections from FILE, then delete it."
  (when truename
    (unwind-protect
         (with-open-file (stream truename :direction :input)
           (load-web-from-stream stream t appendp))
      (delete-file truename))))

@ The file tangler operates by writing out the tangled code to a Lisp source
file and then invoking the file compiler on that file.

@l
(defun tangle-file (input-file &rest args &key
                    output-file
                    (verbose *compile-verbose*)
                    (print *compile-print*)
                    (external-format :default) &allow-other-keys &aux
                    (input-file (merge-pathnames (make-pathname :type "CLW" ;
                                                                :case :common)
                                                 input-file))
                    (lisp-file (merge-pathnames (make-pathname :type "LISP" ;
                                                               :case :common)
                                                input-file)))
  "Tangle and compile the web in INPUT-FILE, producing OUTPUT-FILE."
  (declare (ignore output-file print))
  (when verbose (format t "~&; tangling WEB from ~S~%" input-file))
  @<Initialize global variables@>
  (with-open-file (input input-file
                         :direction :input
                         :external-format external-format)
    (with-open-file (lisp lisp-file
                          :direction :output
                          :if-exists :supersede
                          :external-format external-format)
      (format lisp ";;;; TANGLED OUTPUT FROM WEB ~S. DO NOT EDIT." input-file)
      (let ((*evaluating* nil))
        (dolist (form (tangle (read-code-parts input t)))
          (pprint form lisp)))))
  (apply #'compile-file lisp-file args))

@*The weaver. The top-level weaver interface is modeled after |compile-file|.
The function |weave| reads the \WEB\ |input-file| and produces an output
\TeX\ file named by |output-file|. If the weaving was successful, |weave|
returns the truename of the output file. If |output-file| is not supplied
or is |nil|, a pathname will be generated from |input-file| by replacing
its |:type| component with \.{"tex"}.

If |verbose| is true, |weave| prints a message in the form of a comment to
standard output indicating what file is being woven. If |verbose| is not
supplied, the value of |*weave-verbose*| is used.

If |print| is true, the section number of each section encountered is printed
to standard output, with starred sections prefixed with \.{*}. If |print|
is not supplied, the value of |*weave-print*| is used.

Finally, the |external-format| argument specifies the external file format
to be used when opening both the input file and the output file.
{\it N.B.:} standard \TeX\ only handles 8-bit characters, and the encodings
for non-printable-\csc{ascii} characters vary widely.

@l
(defvar *weave-verbose* t)
(defvar *weave-print* t)

(defun weave (input-file &key
              (output-file nil)
              (verbose *weave-verbose*)
              (print *weave-print*)
              (if-does-not-exist t)
              (external-format :default) &aux
              (input-file (merge-pathnames (make-pathname :type "CLW" ;
                                                          :case :common)
                                           input-file))
              (output-file (merge-pathnames (make-pathname :type "TEX" ;
                                                           :case :common)
                                            (or output-file input-file))))
  "Weave the web contained in INPUT-FILE, producing the TeX file OUTPUT-FILE."
  (when verbose (format t "~&; weaving WEB from ~S~%" input-file))
  @<Initialize global variables@>
  (with-open-file (stream input-file
                   :direction :input
                   :external-format external-format
                   :if-does-not-exist (if if-does-not-exist :error nil))
    (weave-sections (read-sections stream) output-file
                    :print print
                    :external-format external-format)))

@ The following routine does the actual writing of the sections to the output
file. The individual sections and their contents are printed using the pretty
printer with a customized dispatch table.

@l
(defparameter *weave-pprint-dispatch* (copy-pprint-dispatch nil))

(defun weave-sections (sections output-file &key
                       (print *weave-print*)
                       (external-format :default))
  (with-open-file (output output-file
                   :direction :output
                   :external-format external-format
                   :if-exists :supersede)
    (format output "\\input clwebmac~%")
    (flet ((write-section (section)
             (write section
                    :stream output
                    :case :downcase
                    :escape nil
                    :pretty t
                    :pprint-dispatch *weave-pprint-dispatch*
                    :right-margin 1000)))
      (if print
          (pprint-logical-block (nil nil :per-line-prefix "; ")
            (map nil
                 (lambda (section)
                   (format t "~:[~;~:@_*~]~D~:_ "
                           (typep section 'starred-section)
                           (section-number section))
                   (write-section section))
                 sections))
          (map nil #'write-section sections)))
    (format output "~&\\bye~%")
    (truename output)))

@ The rest of the weaver consists entirely of pretty-printing routines that
are installed in |*weave-pprint-dispatch*|.

@l
(defun set-weave-dispatch (type-specifier function &optional (priority 0))
  (set-pprint-dispatch type-specifier function priority ;
                       *weave-pprint-dispatch*))

@ \TeX-mode material is represented as a list of strings containing pure
\TeX\ text and lists of (inner-)Lisp forms. We bind |*inner-lisp*| to true
when we're printing inner-Lisp-mode material so that we can adjust our
pretty-printing.

@l
(defvar *inner-lisp* nil)

(defun print-TeX (stream tex-mode-material)
  (dolist (x tex-mode-material)
    (etypecase x
      (string (write-string x stream))
      (list (let ((*inner-lisp* t))
              (dolist (form x)
                (format stream "\\(~W\\)" form)))))))

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

@ @l
(defun print-limbo (stream section)
  (let ((commentary (section-commentary section)))
    (when commentary
      (print-TeX stream commentary)
      (terpri stream))))

(set-weave-dispatch 'limbo-section #'print-limbo 1)

@ % FIXME: This needs to be broken up and documented.
@l
(defun print-section (stream section)
  (format stream "~&\\~:[M~;N{1}~]{~D}" ; \.{\{1\}} should be depth
          (typep section 'starred-section)
          (section-number section))
  (let* ((commentary (section-commentary section))
         (name (section-name section))
         (named-section (and name (find-section name)))
         (code (section-code section)))
    (print-TeX stream commentary)
    (fresh-line stream)
    (cond ((and commentary code) (format stream "\\Y\\B~%"))
          (code (format stream "\\B~%")))
    (when named-section
      (print-section-name stream named-section)
      (format stream "${}~:[\\mathrel+~;~]\\E{}$~%"
              (= (section-number section) (section-number named-section))))
    (when code
      (dolist (form code)
        (if (list-marker-p form)
            (format stream "~@<\\+~@;~W~;\\cr~:>" form)
            (format stream "~W" form)))
      (format stream "~&\\egroup~%")) ; matches \.{\\bgroup} in \.{\\B}
    (when named-section
      (print-xrefs stream #\A (remove section (see-also named-section)))
      (print-xrefs stream #\U (remove section (used-by named-section)))))
  (format stream "\\fi~%"))

(set-weave-dispatch 'section #'print-section)

@ The cross-references lists use the macros \.{\\A} (for `also'), \.{\\U}
(for `use'), \.{\\Q} (for `quote'), and their pluralized variants, along
with the conjunction macros \.{\\ET} (for two section numbers) and~\.{\\ETs}
(for between the last of three or more).

@l
(defun print-xrefs (stream kind xrefs)
  (when xrefs
    ;; This was 16 lines of code over two sections in \CWEB. I love |format|.
    (format stream "\\~C~{~#[~;~D~;s ~D\\ET~D~:;s~@{~#[~;\\ETs~D~;~D~:;~D, ~]~}~]~}.~%"
            kind (sort (mapcar #'section-number xrefs) #'<))))

@ @l
(defun print-section-name (stream named-section)
  (format stream "\\X~D:" (section-number named-section))
  (print-TeX stream (read-TeX-from-string (section-name named-section)))
  (write-string "\\X" stream))

(set-weave-dispatch 'named-section #'print-section-name)

@ Because we're outputting \TeX, we need to carefully escape characters that
\TeX\ treats as special. Unfortunately, because \TeX's syntax is so malleable
(not unlike Lisp's), it's nontrivial to decide what to escape, how, and when.

The following routine is the basis for most of the escaping. It writes
|string| to the output stream designated by |stream|, escaping the
characters given in the a-list |escape-chars|. The entries in this a-list
should be of the form `(\metasyn{characters}~.~\metasyn{replacement})',
where \metasyn{replacement} describes how to escape each of the characters
in \metasyn{characters}. Suppose $c$ is a character in |string| that
appears in one of the \metasyn{characters} strings. If the corresponding
\metasyn{replacement} is a single character, then |write-string-escaped|
will output it prior to every occurrence of $c$. If \metasyn{replacement}
is a string, it will be output {\it instead of\/} every occurrence of $c$
in the input. Otherwise, $c$ will be output without escaping.

@l
(defparameter *tex-escape-alist*
  '((" \\%&#$^_~<>" . #\\) ("{" . "$\\{$") ("}" . "$\\}$")))

(defun write-string-escaped (string &optional stream ;
                             (escape-chars *tex-escape-alist*) &aux
                             (stream (case stream
                                       ((t) *terminal-io*)
                                       ((nil) *standard-output*)
                                       (otherwise stream))))
  (loop for char across string
        as escape = (cdr (assoc char escape-chars :test #'find))
        if escape
          do (etypecase escape
               (character (write-char escape stream)
                          (write-char char stream))
               (string (write-string escape stream)))
        else
          do (write-char char stream)))

@ @l
(defun print-string (stream string)
  (write-string "\\.{\"" stream)
  (write-string-escaped string stream
                        (list* '("{*}" . #\\)
                               '("\\" . "\\\\\\\\")
                               '("\"" . "\\\\\"")
                               *tex-escape-alist*))
  (write-string "\"}" stream))

(set-weave-dispatch 'string #'print-string)

@ @l
(defun print-char (stream char)
  (let ((graphicp (and (graphic-char-p char)
                       (standard-char-p char)))
        (name (char-name char)))
    (write-string "\\#\\CH{" stream)
    (write-string-escaped (if (and name (not graphicp))
                              name
                              (make-string 1 :initial-element char))
                          stream
                          (list* '("{}" . #\\) *tex-escape-alist*))
    (write-string "}" stream)
    char))

(set-weave-dispatch 'character #'print-char)

@ Symbols are printed by first writing them out to a string, then printing
that string. This relieves us of the burden of worrying about case conversion,
package prefixes, and the like---we just let the Lisp printer handle it.

Lambda-list keywords and symbols in the `keyword' package have specialized
\TeX\ macros that add a bit of emphasis.

@l
(defun print-symbol (stream symbol)
  (let ((group-p (cond ((member symbol lambda-list-keywords)
                        (write-string "\\K{" stream))
                       ((keywordp symbol)
                        (write-string "\\:{" stream)))))
    (write-string-escaped (write-to-string symbol :escape nil :pretty nil) ;
                          stream)
    (when group-p (write-string "}" stream))))

(set-weave-dispatch 'symbol #'print-symbol)

@ Lambda gets special treatment.

@l
(set-weave-dispatch '(eql lambda)
  (lambda (stream obj)
    (declare (ignore obj))
    (write-string "\\L" stream))
  1)

@ Next, we turn to list printing, and the tricky topic of indentation. On
the assumption that the human writing the code in a \WEB\ is smarter than
any sort of automatic indentation that we might be able to do, we attempt
to approximate (but {\it not\/} duplicate) on output the indentation given
in the input by utilizing the character position values that the list
reader stores in the list markers.

We do this by breaking up lists into {\it logical blocks\/}---the same sort
of (abstract) entities that the pretty printer uses, but made concrete
here. A logical block defines a left edge for a list of forms, some of
which may be nested logical blocks.

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
          (and (eq list newline) next-indent (< next-indent block-indent)))
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
             (format stream "\\cr~:@_")
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

@ Finally, we come to the printing of markers. These are all quite
straightforward; the only thing to watch out for is the priorities.
Because |pprint-dispatch| doesn't respect sub-type relationships,
we need to set a higher priority for a sub-class than for its parent
if we want a specialized pretty-printing routine.

Many of these routines output \TeX\ macros defined in \.{clwebmac.tex},
which see.

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
    (write-string "\\C{" stream)
    (print-TeX stream (read-TeX-from-string (comment-text obj)))
    (write-string "}" stream)))

@ @l
(set-weave-dispatch 'backquote-marker
  (lambda (stream obj)
    (format stream "\\`~W" (backq-form obj))))

(set-weave-dispatch 'comma-marker
  (lambda (stream obj)
    (format stream "\\CO{~@[~C~]}~W"
            (comma-modifier obj)
            (comma-form obj))))

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
    (let ((*print-radix* nil)
          (*print-base* (radix-marker-base obj)))
      (princ (marker-value obj) stream)
      (format stream "_{~D}" *print-base*))))

@ @l
(set-weave-dispatch 'structure-marker
  (lambda (stream obj)
    (format stream "\\#S~W" (structure-marker-form obj))))

@ @l
(set-weave-dispatch 'read-time-conditional-marker
  (lambda (stream obj)
    (format stream "\\#~:[--~;+~]\\RC{~S"
            (read-time-conditional-plusp obj)
            (read-time-conditional-test obj))
    (write-char #\Space stream)
    (write-string-escaped (read-time-conditional-form obj) stream)
    (write-char #\} stream)))

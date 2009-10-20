;;;; TANGLED WEB FROM "clweb.clw". DO NOT EDIT.
(IN-PACKAGE "CLWEB")
(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL :EXECUTE)
  (REQUIRE 'RT)
  (LOOP FOR SYMBOL BEING EACH EXTERNAL-SYMBOL OF (FIND-PACKAGE "RT")
        DO (IMPORT SYMBOL)))
(DEFTEST CURRENT-SECTION
         (LET ((*SECTIONS* (MAKE-ARRAY 1 :FILL-POINTER 0)))
           (EQL (MAKE-INSTANCE 'SECTION) *CURRENT-SECTION*))
         T)
(DEFMACRO WITH-TEMPORARY-SECTIONS
          (SECTIONS
           &BODY BODY
           &AUX (SPEC (GENSYM)) (SECTION (GENSYM)) (NAME (GENSYM)))
  `(LET ((*SECTIONS* (MAKE-ARRAY 16 :ADJUSTABLE T :FILL-POINTER 0))
         (*TEST-SECTIONS* (MAKE-ARRAY 16 :ADJUSTABLE T :FILL-POINTER 0))
         (*NAMED-SECTIONS* NIL))
     (DOLIST (,SPEC ',SECTIONS)
       (LET* ((,SECTION
               (APPLY #'MAKE-INSTANCE
                      (ECASE (POP ,SPEC)
                        (:SECTION 'SECTION)
                        (:STARRED-SECTION 'STARRED-SECTION)
                        (:LIMBO 'LIMBO-SECTION))
                      ,SPEC))
              (,NAME (SECTION-NAME ,SECTION)))
         (WHEN ,NAME
           (PUSH ,SECTION (NAMED-SECTION-SECTIONS (FIND-SECTION ,NAME))))))
     ,@BODY))
(DEFTEST (BST 1)
         (LET ((TREE (MAKE-INSTANCE 'BINARY-SEARCH-TREE :KEY 0)))
           (FIND-OR-INSERT -1 TREE)
           (FIND-OR-INSERT 1 TREE)
           (VALUES (NODE-KEY TREE) (NODE-KEY (LEFT-CHILD TREE))
                   (NODE-KEY (RIGHT-CHILD TREE))))
         0 -1 1)
(DEFTEST (BST 2)
         (LET ((TREE (MAKE-INSTANCE 'BINARY-SEARCH-TREE :KEY 0))
               (NUMBERS
                (CONS 0
                      (LOOP WITH LIMIT = 1000
                            FOR I FROM 1 TO LIMIT
                            COLLECT (RANDOM LIMIT)))))
           (DOLIST (N NUMBERS) (FIND-OR-INSERT N TREE))
           (LET ((KEYS 'NIL))
             (FLET ((PUSH-KEY (NODE)
                      (PUSH (NODE-KEY NODE) KEYS)))
               (MAPTREE #'PUSH-KEY TREE)
               (EQUAL (NREVERSE KEYS)
                      (REMOVE-DUPLICATES (SORT NUMBERS #'<))))))
         T)
(DEFTEST BST-FIND-NO-INSERT
         (LET ((TREE (MAKE-INSTANCE 'BINARY-SEARCH-TREE :KEY 0)))
           (FIND-OR-INSERT -1 TREE :INSERT-IF-NOT-FOUND NIL))
         NIL NIL)
(DEFTEST NAMED-SECTION-NUMBER/CODE
         (WITH-TEMPORARY-SECTIONS ((:SECTION :NAME "foo" :CODE (1))
                                   (:SECTION :NAME "foo" :CODE (2))
                                   (:SECTION :NAME "foo" :CODE (3)))
           (LET ((SECTION (FIND-SECTION "foo")))
             (VALUES (SECTION-CODE SECTION) (SECTION-NUMBER SECTION))))
         (1 2 3) 0)
(DEFTEST (SECTION-NAME-PREFIX-P 1) (SECTION-NAME-PREFIX-P "a") NIL 1)
(DEFTEST (SECTION-NAME-PREFIX-P 2) (SECTION-NAME-PREFIX-P "ab...") T 2)
(DEFTEST (SECTION-NAME-PREFIX-P 3) (SECTION-NAME-PREFIX-P "abcd...") T 4)
(DEFTEST (SECTION-NAME-LESSP 1) (SECTION-NAME-LESSP "b" "a") NIL)
(DEFTEST (SECTION-NAME-LESSP 2) (SECTION-NAME-LESSP "b..." "a...") NIL)
(DEFTEST (SECTION-NAME-LESSP 3) (SECTION-NAME-LESSP "ab" "a...") NIL)
(DEFTEST (SECTION-NAME-EQUAL 1) (SECTION-NAME-EQUAL "a" "b") NIL)
(DEFTEST (SECTION-NAME-EQUAL 2) (SECTION-NAME-EQUAL "a" "a") T)
(DEFTEST (SECTION-NAME-EQUAL 3) (SECTION-NAME-EQUAL "a..." "ab") T)
(DEFTEST (SECTION-NAME-EQUAL 4) (SECTION-NAME-EQUAL "a..." "ab...") T)
(DEFTEST (SQUEEZE 1) (SQUEEZE "abc") "abc")
(DEFTEST (SQUEEZE 2) (SQUEEZE "ab c") "ab c")
(DEFTEST (SQUEEZE 3) (SQUEEZE (FORMAT NIL " a b ~C c " #\Tab)) "a b c")
(DEFVAR *SAMPLE-NAMED-SECTIONS*
  (WITH-TEMPORARY-SECTIONS ((:SECTION :NAME "bar" :CODE (:BAR))
                            (:SECTION :NAME "baz" :CODE (:BAZ))
                            (:SECTION :NAME "foo" :CODE (:FOO))
                            (:SECTION :NAME "qux" :CODE (:QUX)))
    *NAMED-SECTIONS*))
(DEFUN FIND-SAMPLE-SECTION (NAME)
  (FIND-OR-INSERT NAME *SAMPLE-NAMED-SECTIONS* :INSERT-IF-NOT-FOUND NIL))
(DEFTEST FIND-NAMED-SECTION (SECTION-NAME (FIND-SAMPLE-SECTION "bar")) "bar")
(DEFTEST FIND-SECTION-BY-PREFIX (SECTION-NAME (FIND-SAMPLE-SECTION "q..."))
         "qux")
(DEFTEST FIND-SECTION-BY-AMBIGUOUS-PREFIX
         (LET ((HANDLED NIL))
           (VALUES
            (SECTION-NAME
             (HANDLER-BIND ((AMBIGUOUS-PREFIX-ERROR
                             (LAMBDA (CONDITION)
                               (DECLARE (IGNORE CONDITION))
                               (SETQ HANDLED T)
                               (INVOKE-RESTART 'USE-FIRST-MATCH))))
               (FIND-SAMPLE-SECTION "b...")))
            HANDLED))
         "bar" T)
(DEFTEST FIND-SECTION
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (FIND-SECTION (FORMAT NIL " foo  bar ~C baz..." #\Tab))
           (SECTION-NAME (FIND-SECTION "foo...")))
         "foo")
(DEFTEST (READTABLE-FOR-MODE 1) (READTABLEP (READTABLE-FOR-MODE :TEX)) T)
(DEFTEST (READTABLE-FOR-MODE 2) (READTABLEP (READTABLE-FOR-MODE NIL)) T)
(DEFTEST (READTABLE-FOR-MODE 3)
         (EQL (READTABLE-FOR-MODE :TEX) (READTABLE-FOR-MODE :LISP)) NIL)
(DEFTEST WITH-MODE
         (LOOP FOR (MODE . READTABLE) IN *READTABLES*
               ALWAYS (WITH-MODE MODE
                        (EQL *READTABLE* READTABLE)))
         T)
(DEFTEST EOF-P (EOF-P (READ-FROM-STRING "" NIL *EOF*)) T)
(DEFTEST EOF-TYPE (TYPEP (READ-FROM-STRING "" NIL *EOF*) 'EOF) T)
(DEFTEST (TOKEN-DELIMITER-P 1) (NOT (TOKEN-DELIMITER-P #\ )) NIL)
(DEFTEST (TOKEN-DELIMITER-P 2) (NOT (TOKEN-DELIMITER-P #\))) NIL)
(DEFTEST CHARPOS-INPUT-STREAM
         (WITH-CHARPOS-INPUT-STREAM (S
                                     (MAKE-STRING-INPUT-STREAM
                                      (FORMAT NIL "012~%abc")))
           (VALUES (STREAM-CHARPOS S) (READ-LINE S) (STREAM-CHARPOS S)
                   (READ-CHAR S) (READ-CHAR S) (READ-CHAR S)
                   (STREAM-CHARPOS S)))
         0 "012" 0 #\a #\b #\c 3)
(DEFTEST CHARPOS-OUTPUT-STREAM
         (LET ((STRING-STREAM (MAKE-STRING-OUTPUT-STREAM)))
           (WITH-CHARPOS-OUTPUT-STREAM (S STRING-STREAM)
             (VALUES (STREAM-CHARPOS S)
                     (PROGN (WRITE-STRING "012" S) (STREAM-CHARPOS S))
                     (PROGN (WRITE-CHAR #\Newline S) (STREAM-CHARPOS S))
                     (PROGN (WRITE-STRING "abc" S) (STREAM-CHARPOS S))
                     (GET-OUTPUT-STREAM-STRING STRING-STREAM))))
         0 3 0 3 #.(FORMAT NIL "012~%abc"))
(DEFTEST REWIND-STREAM
         (WITH-REWIND-STREAM (S (MAKE-STRING-INPUT-STREAM "abcdef"))
           (VALUES (READ-CHAR S) (READ-CHAR S) (READ-CHAR S)
                   (PROGN (REWIND) (READ-CHAR S))
                   (PROGN (REWIND) (READ-LINE S))))
         #\a #\b #\c #\a "bcdef")
(DEFTEST READ-WITH-ECHO
         (READ-WITH-ECHO ((MAKE-STRING-INPUT-STREAM ":foo :bar") VALUES CHARS)
           (VALUES VALUES CHARS))
         (:FOO) ":foo ")
(DEFTEST READ-WITH-ECHO-TO-EOF
         (READ-WITH-ECHO ((MAKE-STRING-INPUT-STREAM ":foo") VALUES CHARS)
           (VALUES VALUES CHARS))
         (:FOO) ":foo")
(DEFTEST PRINT-MARKER
         (LET ((*PRINT-MARKER* T))
           (FORMAT NIL "~A" (MAKE-INSTANCE 'MARKER :VALUE :FOO)))
         "FOO")
(DEFTEST PRINT-MARKER-UNREADABLY
         (LET ((*PRINT-MARKER* NIL) (*PRINT-READABLY* T))
           (HANDLER-CASE (FORMAT NIL "~W" (MAKE-INSTANCE 'MARKER :VALUE :FOO))
                         (PRINT-NOT-READABLE (CONDITION)
                          (MARKER-VALUE
                           (PRINT-NOT-READABLE-OBJECT CONDITION)))))
         :FOO)
(DEFTEST READ-NEWLINE
         (NEWLINEP
          (WITH-INPUT-FROM-STRING (S (FORMAT NIL "~%"))
            (WITH-MODE :LISP
              (READ S))))
         T)
(DEFMACRO READ-FROM-STRING-WITH-CHARPOS
          (STRING
           &OPTIONAL (EOF-ERROR-P T) (EOF-VALUE NIL)
           &KEY (PRESERVE-WHITESPACE NIL)
           &AUX (STRING-STREAM (GENSYM)) (CHARPOS-STREAM (GENSYM)))
  `(WITH-OPEN-STREAM (,STRING-STREAM (MAKE-STRING-INPUT-STREAM ,STRING))
     (WITH-CHARPOS-INPUT-STREAM (,CHARPOS-STREAM ,STRING-STREAM)
       (IF ,PRESERVE-WHITESPACE
           (READ-PRESERVING-WHITESPACE ,CHARPOS-STREAM ,EOF-ERROR-P ,EOF-VALUE)
           (READ ,CHARPOS-STREAM ,EOF-ERROR-P ,EOF-VALUE)))))
(DEFUN READ-FORM-FROM-STRING (STRING &KEY (MODE :LISP))
  (WITH-MODE MODE
    (READ-FROM-STRING-WITH-CHARPOS STRING)))
(DEFTEST READ-EMPTY-LIST-INNER-LISP
         (TYPEP (READ-FORM-FROM-STRING "()" :MODE :INNER-LISP)
                'EMPTY-LIST-MARKER)
         T)
(DEFTEST READ-EMPTY-LIST
         (TYPEP (READ-FORM-FROM-STRING "()") 'EMPTY-LIST-MARKER) T)
(DEFTEST READ-LIST-INNER-LISP
         (LISTP (READ-FORM-FROM-STRING "(:a :b :c)" :MODE :INNER-LISP)) T)
(DEFTEST READ-LIST (MARKER-VALUE (READ-FORM-FROM-STRING "(:a :b :c)"))
         (:A :B :C))
(DEFTEST READ-DOTTED-LIST (MARKER-VALUE (READ-FORM-FROM-STRING "(:a :b . :c)"))
         (:A :B . :C))
(DEFTEST LIST-MARKER-CHARPOS
         (LIST-MARKER-CHARPOS (READ-FORM-FROM-STRING "(1 2 3)")) (1 3 5))
(DEFTEST READ-QUOTED-FORM
         (LET ((MARKER (READ-FORM-FROM-STRING "':foo")))
           (VALUES (QUOTED-FORM MARKER) (MARKER-VALUE MARKER)))
         :FOO ':FOO)
(DEFTEST READ-COMMENT
         (LET ((MARKER (READ-FORM-FROM-STRING "; foo")))
           (VALUES (COMMENT-TEXT MARKER) (MARKER-BOUNDP MARKER)))
         "; foo" NIL)
(DEFTEST READ-BACKQUOTE
         (LET ((MARKER (READ-FORM-FROM-STRING "`(:a :b :c)")))
           (AND (TYPEP MARKER 'BACKQUOTE-MARKER) (MARKER-VALUE MARKER)))
         #.(READ-FROM-STRING "`(:a :b :c)"))
(DEFTEST READ-COMMA
         (EVAL (MARKER-VALUE (READ-FORM-FROM-STRING "`(:a ,@'(:b :c) :d)")))
         (:A :B :C :D))
(DEFTEST READ-FUNCTION
         (LET ((MARKER (READ-FORM-FROM-STRING "#'identity")))
           (VALUES (QUOTED-FORM MARKER) (MARKER-VALUE MARKER)))
         IDENTITY #'IDENTITY)
(DEFTEST READ-SIMPLE-VECTOR
         (MARKER-VALUE (READ-FORM-FROM-STRING "#5(:a :b :c)"))
         #(:A :B :C :C :C))
(DEFTEST READ-BIT-VECTOR (MARKER-VALUE (READ-FORM-FROM-STRING "#5*101"))
         #*10111)
(DEFTEST (READ-TIME-EVAL 1)
         (LET* ((*READ-EVAL* T) (*EVALUATING* NIL) (*PRINT-MARKER* T))
           (PRIN1-TO-STRING
            (MARKER-VALUE (READ-FORM-FROM-STRING "#.(+ 1 1)"))))
         "#.(+ 1 1)")
(DEFTEST (READ-TIME-EVAL 2)
         (LET* ((*READ-EVAL* T) (*EVALUATING* T))
           (MARKER-VALUE (READ-FORM-FROM-STRING "#.(+ 1 1)")))
         2)
(DEFTEST (READ-RADIX 1)
         (LET ((MARKER (READ-FORM-FROM-STRING "#B1011")))
           (VALUES (RADIX-MARKER-BASE MARKER) (MARKER-VALUE MARKER)))
         2 11)
(DEFTEST (READ-RADIX 2)
         (LET ((MARKER (READ-FORM-FROM-STRING "#14R11")))
           (VALUES (RADIX-MARKER-BASE MARKER) (MARKER-VALUE MARKER)))
         14 15)
(DEFTEST FEATUREP
         (LET ((*FEATURES* '(:A :B)))
           (FEATUREP '(:AND :A (:OR :C :B) (:NOT :D))))
         T)
(DEFTEST (READ-TIME-CONDITIONAL 1)
         (LET ((*FEATURES* '(:A)) (*EVALUATING* NIL) (*PRINT-MARKER* T))
           (VALUES
            (PRIN1-TO-STRING (MARKER-VALUE (READ-FORM-FROM-STRING "#+a 1")))
            (PRIN1-TO-STRING (MARKER-VALUE (READ-FORM-FROM-STRING "#-a 1")))))
         "#+:A 1" "#-:A 1")
(DEFTEST (READ-TIME-CONDITIONAL 2)
         (LET ((*FEATURES* '(:A)) (*EVALUATING* T))
           (VALUES (MARKER-VALUE (READ-FORM-FROM-STRING "#+a 1"))
                   (MARKER-VALUE (READ-FORM-FROM-STRING "#-b 2"))
                   (MARKER-BOUNDP (READ-FORM-FROM-STRING "#-a 1"))
                   (MARKER-BOUNDP (READ-FORM-FROM-STRING "#+b 2"))))
         1 2 NIL NIL)
(DEFTEST SNARF-UNTIL-CONTROL-CHAR
         (WITH-INPUT-FROM-STRING (S "abc*123")
           (VALUES (SNARF-UNTIL-CONTROL-CHAR S #\*)
                   (SNARF-UNTIL-CONTROL-CHAR S '(#\a #\3))))
         "abc" "*12")
(DEFTEST READ-INNER-LISP
         (WITH-MODE :TEX
           (VALUES (READ-FROM-STRING "|:foo :bar|")))
         (:FOO :BAR))
(DEFTEST LITERAL-@
         (WITH-MODE :TEX
           (VALUES (READ-FROM-STRING "@@")))
         "@")
(DEFTEST SUPPRESS-LINE-BREAK
         (WITH-MODE :LISP
           (VALUES (READ-FROM-STRING (FORMAT NIL "@+~%:foo"))))
         :FOO)
(DEFTEST START-TEST-SECTION-READER
         (LET ((*TEST-SECTIONS* (MAKE-ARRAY 2 :FILL-POINTER 0)))
           (WITH-INPUT-FROM-STRING (S (FORMAT NIL "@t~%:foo @t* :bar"))
             (WITH-MODE :LISP
               (VALUES (TYPEP (READ S) 'TEST-SECTION) (READ S)
                       (TYPEP (READ S) 'STARRED-TEST-SECTION) (READ S)))))
         T :FOO T :BAR)
(DEFTEST START-CODE-MARKER
         (WITH-MODE :TEX
           (VALUES-LIST
            (MAPCAR (LAMBDA (MARKER) (TYPEP MARKER 'START-CODE-MARKER))
                    (LIST (READ-FROM-STRING "@l") (READ-FROM-STRING "@p")))))
         T T)
(DEFTEST (READ-EVALUATED-FORM 1)
         (LET ((MARKER (READ-FORM-FROM-STRING (FORMAT NIL "@e t"))))
           (AND (TYPEP MARKER 'EVALUATED-FORM-MARKER) (MARKER-VALUE MARKER)))
         T)
(DEFTEST (READ-EVALUATED-FORM 2)
         (LET ((MARKER (READ-FORM-FROM-STRING (FORMAT NIL "@e~%t"))))
           (AND (TYPEP MARKER 'EVALUATED-FORM-MARKER) (MARKER-VALUE MARKER)))
         T)
(DEFTEST READ-CONTROL-TEXT
         (WITH-INPUT-FROM-STRING (S "frob |foo|@>") (READ-CONTROL-TEXT S))
         "frob |foo|")
(DEFTEST (READ-SECTION-NAME :TEX)
         (WITH-MODE :TEX
           (SECTION-NAME (READ-FROM-STRING "@<foo@>=")))
         "foo")
(DEFTEST (READ-SECTION-NAME :LISP)
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (WITH-MODE :LISP
             (SECTION-NAME (READ-FROM-STRING "@<foo@>"))))
         "foo")
(DEFTEST SECTION-NAME-DEFINITION-ERROR
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (SECTION-NAME
            (HANDLER-BIND ((SECTION-NAME-DEFINITION-ERROR
                            (LAMBDA (CONDITION)
                              (DECLARE (IGNORE CONDITION))
                              (INVOKE-RESTART 'USE-SECTION))))
              (WITH-MODE :LISP
                (READ-FROM-STRING "@<foo@>=")))))
         "foo")
(DEFTEST SECTION-NAME-USE-ERROR
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (SECTION-NAME
            (HANDLER-BIND ((SECTION-NAME-USE-ERROR
                            (LAMBDA (CONDITION)
                              (DECLARE (IGNORE CONDITION))
                              (INVOKE-RESTART 'CITE-SECTION))))
              (WITH-MODE :TEX
                (READ-FROM-STRING "@<foo@>")))))
         "foo")
(DEFTEST MAYBE-PUSH
         (LET ((LIST 'NIL))
           (MAYBE-PUSH 'A LIST)
           (MAYBE-PUSH NIL LIST)
           (MAYBE-PUSH "" LIST)
           (MAYBE-PUSH 'B LIST)
           LIST)
         (B A))
(DEFTEST (TANGLE-1 1) (TANGLE-1 (READ-FORM-FROM-STRING ":a")) :A NIL)
(DEFTEST (TANGLE-1 2) (TANGLE-1 (READ-FORM-FROM-STRING "(:a :b :c)"))
         (:A :B :C) T)
(DEFTEST (TANGLE-1 3)
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (EQL (TANGLE-1 (READ-FORM-FROM-STRING "@<foo@>"))
                (FIND-SAMPLE-SECTION "foo")))
         T)
(DEFTEST TANGLE
         (LET ((*NAMED-SECTIONS* *SAMPLE-NAMED-SECTIONS*))
           (TANGLE (READ-FORM-FROM-STRING (FORMAT NIL "(:a @<foo@>~% :b)"))))
         (:A :FOO :B) T)
(DEFTEST (TESTS-FILE-PATHNAME 1)
         (EQUAL
          (TESTS-FILE-PATHNAME (MAKE-PATHNAME :NAME "FOO" :CASE :COMMON) "LISP"
                               :TESTS-FILE
                               (MAKE-PATHNAME :NAME "BAR" :CASE :COMMON))
          (MAKE-PATHNAME :NAME "BAR" :TYPE "LISP" :CASE :COMMON))
         T)
(DEFTEST (TESTS-FILE-PATHNAME 2)
         (EQUAL
          (TESTS-FILE-PATHNAME (MAKE-PATHNAME :NAME "FOO" :CASE :COMMON) "TEX")
          (MAKE-PATHNAME :NAME "FOO-TESTS" :TYPE "TEX" :CASE :COMMON))
         T)
(DEFTEST (TESTS-FILE-PATHNAME 3)
         (TESTS-FILE-PATHNAME (MAKE-PATHNAME :NAME "FOO" :CASE :COMMON) "LISP"
                              :TESTS-FILE NIL)
         NIL)
(DEFTEST PRINT-ESCAPED
         (WITH-OUTPUT-TO-STRING (S) (PRINT-ESCAPED S "foo#{bar}*baz"))
         "foo\\#$\\{$bar$\\}$*baz")
(DEFTEST (WALK-FUNCTION-NAME 1)
         (EQUAL (WALK-FUNCTION-NAME (MAKE-INSTANCE 'WALKER) 'FOO NIL) 'FOO) T)
(DEFTEST (WALK-FUNCTION-NAME 2)
         (EQUAL (WALK-FUNCTION-NAME (MAKE-INSTANCE 'WALKER) '(SETF FOO) NIL)
                '(SETF FOO))
         T)
(DEFTEST (WALK-FUNCTION-NAME 3)
         (LET ((ERROR-HANDLED NIL))
           (FLET ((NOTE-AND-CONTINUE (CONDITION)
                    (SETQ ERROR-HANDLED T)
                    (CONTINUE CONDITION)))
             (HANDLER-BIND ((INVALID-FUNCTION-NAME #'NOTE-AND-CONTINUE))
               (VALUES
                (EQUAL
                 (WALK-FUNCTION-NAME (MAKE-INSTANCE 'WALKER) '(FOO BAR) NIL)
                 '(FOO BAR))
                ERROR-HANDLED))))
         T T)
(DEFTEST (WALK-FUNCTION 1)
         (TREE-EQUAL (WALK-FORM (MAKE-INSTANCE 'WALKER) '#'FOO NIL) '#'FOO) T)
(DEFTEST (WALK-FUNCTION 2)
         (TREE-EQUAL (WALK-FORM (MAKE-INSTANCE 'WALKER) '#'(SETF FOO) NIL)
                     '#'(SETF FOO))
         T)
(DEFTEST (WALK-FUNCTION 3)
         (TREE-EQUAL (WALK-FORM (MAKE-INSTANCE 'WALKER) '#'(LAMBDA (X) X) NIL)
                     '#'(LAMBDA (X) X))
         T)
(DEFTEST (PARSE-BODY 1)
         (PARSE-BODY '("doc" (DECLARE (OPTIMIZE SPEED)) :FOO :BAR)
                     :DOC-STRING-ALLOWED T)
         (:FOO :BAR) ((OPTIMIZE SPEED)) "doc")
(DEFTEST (PARSE-BODY 2)
         (PARSE-BODY
          '((DECLARE (OPTIMIZE SPEED)) "doc" (DECLARE (OPTIMIZE SPACE)) :FOO
            :BAR)
          :DOC-STRING-ALLOWED T)
         (:FOO :BAR) ((OPTIMIZE SPEED) (OPTIMIZE SPACE)) "doc")
(DEFTEST (PARSE-BODY 3) (PARSE-BODY '("doc" "string") :DOC-STRING-ALLOWED T)
         ("string") NIL "doc")
(DEFTEST (PARSE-BODY 4)
         (PARSE-BODY '((DECLARE (OPTIMIZE DEBUG)) "string") :DOC-STRING-ALLOWED
                     T)
         ("string") ((OPTIMIZE DEBUG)) NIL)
(DEFTEST (PARSE-BODY 5)
         (PARSE-BODY '((DECLARE (OPTIMIZE DEBUG)) "string") :DOC-STRING-ALLOWED
                     NIL)
         ("string") ((OPTIMIZE DEBUG)) NIL)
(DEFCLASS TEST-WALKER (WALKER) NIL)
(DEFINE-SPECIAL-FORM-WALKER CHECK-BINDING
    ((WALKER TEST-WALKER) FORM ENV)
  (FLET ((CHECK-BINDING (NAME NAMESPACE ENV TYPE)
           (ASSERT
            (EQL
             (ECASE NAMESPACE
               (:FUNCTION (FUNCTION-INFORMATION NAME ENV))
               (:VARIABLE (VARIABLE-INFORMATION NAME ENV)))
             TYPE)
            (NAME NAMESPACE ENV TYPE) "~@(~A~) binding of ~A not of type ~A."
            NAMESPACE NAME TYPE)))
    (DESTRUCTURING-BIND
        (SYMBOLS NAMESPACE TYPE)
        (CDR FORM)
      (LOOP WITH SYMBOLS = (IF (LISTP SYMBOLS)
                               SYMBOLS
                               (LIST SYMBOLS))
            FOR SYMBOL IN SYMBOLS
            DO (CHECK-BINDING SYMBOL NAMESPACE ENV TYPE))
      (IF (LISTP SYMBOLS)
          (WALK-LIST WALKER SYMBOLS ENV)
          (WALK-FORM WALKER SYMBOLS ENV)))))
(DEFMACRO DEFINE-WALK-BINDING-TEST (NAME FORM WALKED-FORM)
  `(DEFTEST ,NAME
            (TREE-EQUAL (WALK-FORM (MAKE-INSTANCE 'TEST-WALKER) ',FORM)
                        ',WALKED-FORM)
            T))
(DEFINE-WALK-BINDING-TEST WALK-ORDINARY-LAMBDA-LIST
                          (LAMBDA
                              (X Y
                               &OPTIONAL
                               (O
                                (+ (CHECK-BINDING O :VARIABLE NIL)
                                   (CHECK-BINDING X :VARIABLE :SPECIAL)
                                   (CHECK-BINDING Y :VARIABLE :LEXICAL)))
                               &KEY ((SECRET K) 1 K-S-P)
                               (K2 (CHECK-BINDING K-S-P :VARIABLE :LEXICAL)) K3
                               &REST ARGS
                               &AUX W
                               (Z
                                (IF K-S-P
                                    O
                                    X)))
                            (DECLARE (SPECIAL X))
                            (CHECK-BINDING X :VARIABLE :SPECIAL)
                            (CHECK-BINDING (Y Z O K K-S-P K2 K3 ARGS W Z)
                             :VARIABLE :LEXICAL)
                            (CHECK-BINDING SECRET :VARIABLE NIL))
                          (LAMBDA
                              (X Y
                               &OPTIONAL (O (+ O X Y))
                               &KEY ((SECRET K) 1 K-S-P) (K2 K-S-P) K3
                               &REST ARGS
                               &AUX W
                               (Z
                                (IF K-S-P
                                    O
                                    X)))
                            (DECLARE (SPECIAL X))
                            X
                            (Y Z O K K-S-P K2 K3 ARGS W Z)
                            SECRET))
(DEFINE-WALK-BINDING-TEST WALK-MACRO-LAMBDA-LIST
                          (LAMBDA
                              (&WHOLE W (X Y)
                               &OPTIONAL ((O) (+ X Y))
                               &KEY ((:K (K1 K2)) (2 3) K-S-P) &ENVIRONMENT
                               ENV . BODY)
                            (CHECK-BINDING (W X Y O K1 K2 K-S-P ENV BODY)
                             :VARIABLE :LEXICAL))
                          (LAMBDA
                              (&WHOLE W (X Y)
                               &OPTIONAL ((O) (+ X Y))
                               &KEY ((:K (K1 K2)) (2 3) K-S-P) &ENVIRONMENT ENV
                               &REST BODY)
                            (W X Y O K1 K2 K-S-P ENV BODY)))
(DEFINE-WALK-BINDING-TEST WALK-LET
                          (LET ((X 1) (Y (CHECK-BINDING X :VARIABLE NIL)))
                            (DECLARE (SPECIAL X))
                            (CHECK-BINDING X :VARIABLE :SPECIAL)
                            (CHECK-BINDING Y :VARIABLE :LEXICAL))
                          (LET ((X 1) (Y X))
                            (DECLARE (SPECIAL X))
                            X
                            Y))
(DEFINE-WALK-BINDING-TEST WALK-FLET
                          (FLET ((FOO (X)
                                   (CHECK-BINDING X :VARIABLE :LEXICAL))
                                 (BAR (Y)
                                   Y))
                            (DECLARE (SPECIAL X))
                            (CHECK-BINDING X :VARIABLE :SPECIAL)
                            (CHECK-BINDING FOO :FUNCTION :FUNCTION))
                          (FLET ((FOO (X)
                                   X)
                                 (BAR (Y)
                                   Y))
                            (DECLARE (SPECIAL X))
                            X
                            FOO))
(DEFINE-WALK-BINDING-TEST WALK-MACROLET
                          (MACROLET ((FOO (X)
                                       (CHECK-BINDING X :VARIABLE :LEXICAL))
                                     (BAR (Y)
                                       Y))
                            (CHECK-BINDING FOO :FUNCTION :MACRO)
                            (FOO :FOO))
                          (MACROLET ((FOO (X)
                                       X)
                                     (BAR (Y)
                                       Y))
                            FOO
                            :FOO))
(DEFINE-WALK-BINDING-TEST WALK-SYMBOL-MACROLET
                          (SYMBOL-MACROLET ((FOO :FOO) (BAR :BAR))
                            (CHECK-BINDING (FOO BAR) :VARIABLE :SYMBOL-MACRO))
                          (SYMBOL-MACROLET ((FOO :FOO) (BAR :BAR))
                            (:FOO :BAR)))
(DEFINE-WALK-BINDING-TEST WALK-LET*
                          (LET* ((X 1) (Y (CHECK-BINDING X :VARIABLE :SPECIAL)))
                            (DECLARE (SPECIAL X))
                            (CHECK-BINDING Y :VARIABLE :LEXICAL))
                          (LET* ((X 1) (Y X))
                            (DECLARE (SPECIAL X))
                            Y))
(DEFINE-WALK-BINDING-TEST WALK-LABELS
                          (LABELS ((FOO (X)
                                     (CHECK-BINDING X :VARIABLE :LEXICAL))
                                   (BAR (Y)
                                     (CHECK-BINDING FOO :FUNCTION :FUNCTION)))
                            (DECLARE (SPECIAL X))
                            (CHECK-BINDING X :VARIABLE :SPECIAL)
                            (CHECK-BINDING FOO :FUNCTION :FUNCTION))
                          (LABELS ((FOO (X)
                                     X)
                                   (BAR (Y)
                                     FOO))
                            (DECLARE (SPECIAL X))
                            X
                            FOO))
(DEFINE-WALK-BINDING-TEST WALK-LOCALLY
                          (LET ((Y T))
                            (CHECK-BINDING Y :VARIABLE :LEXICAL)
                            (LOCALLY
                             (DECLARE (SPECIAL Y))
                             (CHECK-BINDING Y :VARIABLE :SPECIAL)))
                          (LET ((Y T))
                            Y
                            (LOCALLY (DECLARE (SPECIAL Y)) Y)))
(DEFCLASS TRACING-WALKER (WALKER) NIL)
(DEFMETHOD WALK-ATOMIC-FORM :BEFORE
           ((WALKER TRACING-WALKER) FORM ENV &OPTIONAL (EVALP T))
           (FORMAT T
                   "; walking ~:[un~;~]evaluated atomic form ~S~@[ (~(~A~) variable)~]~%"
                   EVALP FORM
                   (AND (SYMBOLP FORM) (VARIABLE-INFORMATION FORM ENV))))
(DEFMETHOD WALK-COMPOUND-FORM :BEFORE
           ((WALKER TRACING-WALKER) OPERATOR FORM ENV)
           (DECLARE (IGNORE OPERATOR ENV))
           (FORMAT T "~<; ~@;walking compound form ~W~:>~%" (LIST FORM)))
(DEFTEST ENTRY-HEADING-LESSP
         (LET ((A (MAKE-INSTANCE 'HEADING :NAME "a"))
               (B (MAKE-INSTANCE 'HEADING :NAME "b"))
               (X (MAKE-INSTANCE 'HEADING :NAME "x"))
               (Y (MAKE-INSTANCE 'HEADING :NAME "y")))
           (NOTANY #'NOT
                   (LIST (NOT (ENTRY-HEADING-LESSP A A))
                         (ENTRY-HEADING-LESSP A B)
                         (ENTRY-HEADING-LESSP A (LIST A X))
                         (ENTRY-HEADING-LESSP (LIST A X) (LIST A Y))
                         (ENTRY-HEADING-LESSP (LIST A X) (LIST B X))
                         (ENTRY-HEADING-LESSP (LIST A Y) (LIST B X))
                         (ENTRY-HEADING-LESSP (LIST A X) (LIST B Y)))))
         T)
(DEFMETHOD PRINT-OBJECT ((HEADING HEADING) STREAM)
           (PRINT-UNREADABLE-OBJECT (HEADING STREAM :TYPE T :IDENTITY NIL)
             (FORMAT STREAM "\"~A\"" (HEADING-NAME HEADING))))
(DEFTEST HEADING-NAME
         (VALUES (HEADING-NAME "foo")
                 (HEADING-NAME (MAKE-INSTANCE 'HEADING :NAME "bar"))
                 (HEADING-NAME :BAZ))
         "foo" "bar" :BAZ)
(DEFTEST FUNCTION-HEADING-NAME
         (VALUES (HEADING-NAME (MAKE-INSTANCE 'FUNCTION-HEADING))
                 (HEADING-NAME (MAKE-INSTANCE 'FUNCTION-HEADING :LOCAL T))
                 (HEADING-NAME (MAKE-INSTANCE 'FUNCTION-HEADING :GENERIC T))
                 (HEADING-NAME
                  (MAKE-INSTANCE 'SETF-FUNCTION-HEADING :LOCAL T)))
         "function" "local function" "generic function" "local setf function")
(DEFTEST VARIABLE-HEADING-NAME
         (VALUES (HEADING-NAME (MAKE-INSTANCE 'VARIABLE-HEADING))
                 (HEADING-NAME (MAKE-INSTANCE 'VARIABLE-HEADING :SPECIAL T))
                 (HEADING-NAME (MAKE-INSTANCE 'VARIABLE-HEADING :CONSTANT T)))
         "variable" "special variable" "constant variable")
(DEFTEST METHOD-HEADING-NAME
         (VALUES (HEADING-NAME (MAKE-INSTANCE 'METHOD-HEADING))
                 (HEADING-NAME
                  (MAKE-INSTANCE 'METHOD-HEADING :QUALIFIERS
                                 '(:BEFORE :DURING :AFTER))))
         "primary method" "BEFORE DURING AFTER method")
(DEFTEST MAKE-SUB-HEADING
         (NOTANY #'NULL
                 (LIST (TYPEP (MAKE-SUB-HEADING NIL) 'FUNCTION-HEADING)
                       (TYPEP (MAKE-SUB-HEADING 'DEFMETHOD) 'FUNCTION-HEADING)
                       (TYPEP
                        (MAKE-SUB-HEADING 'DEFMETHOD :QUALIFIERS '(:AFTER))
                        'METHOD-HEADING)
                       (TYPEP
                        (MAKE-SUB-HEADING 'DEFUN :FUNCTION-NAME '(SETF FOO))
                        'SETF-FUNCTION-HEADING)
                       (TYPEP (MAKE-SUB-HEADING 'DEFCLASS) 'CLASS-HEADING)))
         T)
(DEFMETHOD PRINT-OBJECT ((ENTRY INDEX-ENTRY) STREAM)
           (PRINT-UNREADABLE-OBJECT (ENTRY STREAM :TYPE T :IDENTITY NIL)
             (FORMAT STREAM "~W:" (ENTRY-HEADING ENTRY))
             (DOLIST
                 (LOCATOR
                  (SORT (COPY-LIST (ENTRY-LOCATORS ENTRY)) #'< :KEY
                        (LAMBDA (X) (SECTION-NUMBER (LOCATION X)))))
               (FORMAT STREAM " ~:[~D~;[~D]~]" (LOCATOR-DEFINITION-P LOCATOR)
                       (SECTION-NUMBER (LOCATION LOCATOR))))))
(DEFTEST (ADD-INDEX-ENTRY 1)
         (LET ((INDEX (MAKE-INDEX)) (*SECTIONS* (MAKE-ARRAY 3 :FILL-POINTER 0)))
           (ADD-INDEX-ENTRY INDEX 'FOO (MAKE-INSTANCE 'SECTION))
           (ADD-INDEX-ENTRY INDEX 'FOO (MAKE-INSTANCE 'SECTION))
           (ADD-INDEX-ENTRY INDEX 'FOO (MAKE-INSTANCE 'SECTION))
           (SORT
            (MAPCAR #'SECTION-NUMBER
                    (MAPCAR #'LOCATION (FIND-INDEX-ENTRIES INDEX 'FOO)))
            #'<))
         (0 1 2))
(DEFTEST (ADD-INDEX-ENTRY 2)
         (LET* ((INDEX (MAKE-INDEX))
                (*SECTIONS* (MAKE-ARRAY 1 :FILL-POINTER 0))
                (SECTION (MAKE-INSTANCE 'SECTION)))
           (ADD-INDEX-ENTRY INDEX 'FOO SECTION)
           (ADD-INDEX-ENTRY INDEX 'FOO SECTION :DEF T)
           (LOCATOR-DEFINITION-P (FIRST (FIND-INDEX-ENTRIES INDEX 'FOO))))
         T)
(DEFTEST (SYMBOL-PROVENANCE 1)
         (LET ((*INDEX-PACKAGES* (LIST (FIND-PACKAGE "KEYWORD"))))
           (SYMBOL-PROVENANCE (SUBSTITUTE-SYMBOLS :FOO 1)))
         :FOO 1)
(DEFTEST (SYMBOL-PROVENANCE 2) (SYMBOL-PROVENANCE :FOO) :FOO)
(DEFTEST INDEXING-WALK-DEFUN
         (WITH-TEMPORARY-SECTIONS NIL
           (LET ((WALKER (MAKE-INSTANCE 'INDEXING-WALKER))
                 (FORM
                  '(FLET ((COMPUTE-K (X Y Z)
                            (+ X Y Z)))
                     (DEFMACRO FOO
                               (&WHOLE W X Y Z &ENVIRONEMNT ENV
                                &KEY ((KEY K) (COMPUTE-K X Y Z) K-S-P)
                                &BODY BODY)
                       (DECLARE (SPECIAL K))
                       BODY)))
                 (SECTION (MAKE-INSTANCE 'SECTION))
                 (*INDEX-PACKAGES* (LIST (FIND-PACKAGE "CLWEB"))))
             (VALUES
              (TREE-EQUAL (WALK-FORM WALKER (SUBSTITUTE-SYMBOLS FORM SECTION))
                          FORM)
              (LOOP WITH INDEX = (WALKER-INDEX WALKER)
                    FOR H IN `((K
                                ,(MAKE-INSTANCE 'VARIABLE-HEADING :SPECIAL T))
                               (COMPUTE-K
                                ,(MAKE-INSTANCE 'FUNCTION-HEADING :LOCAL T))
                               (FOO ,(MAKE-INSTANCE 'MACRO-HEADING)))
                    ALWAYS (EQL (LOCATION (FIRST (FIND-INDEX-ENTRIES INDEX H)))
                                SECTION)))))
         T T)
(DEFTEST (WALK-DECLARATION-SPECIFIERS INDEXING)
         (EQUAL
          (WALK-DECLARATION-SPECIFIERS (MAKE-INSTANCE 'INDEXING-WALKER)
                                       '((TYPE FOO X) (SPECIAL X Y Z)
                                         (OPTMIZE DEBUG))
                                       NIL)
          '((SPECIAL X Y Z)))
         T)
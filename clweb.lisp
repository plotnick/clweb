;;;; TANGLED OUTPUT FROM WEB "clweb.lw".  DO NOT EDIT.
(DEFPACKAGE "COMMON-LISP-WEB" (:NICKNAMES "CLWEB") (:USE "COMMON-LISP")
            (:EXPORT "TANGLE-FILE" "LOAD-WEB" "LOAD-SECTIONS-FROM-TEMP-FILE"
             "WEAVE"))
(IN-PACKAGE "CLWEB")
(DEFCLASS SECTION NIL
          ((NUMBER :ACCESSOR SECTION-NUMBER)
           (COMMENTARY :ACCESSOR SECTION-COMMENTARY :INITARG :COMMENTARY)
           (NAME :ACCESSOR SECTION-NAME :INITARG :NAME)
           (CODE :ACCESSOR SECTION-CODE :INITARG :CODE)
           (USED-BY :ACCESSOR USED-BY :INITARG :USED-BY))
          (:DEFAULT-INITARGS :COMMENTARY NIL :NAME NIL :CODE NIL :USED-BY NIL))
(DEFCLASS LIMBO-SECTION (SECTION) NIL)
(DEFCLASS STARRED-SECTION (SECTION) NIL)
(DEFVAR *SECTIONS*
  (MAKE-ARRAY 128 :ELEMENT-TYPE 'SECTION :ADJUSTABLE T :FILL-POINTER 0))
(DEFUN CURRENT-SECTION () (ELT *SECTIONS* (1- (FILL-POINTER *SECTIONS*))))
(DEFMETHOD INITIALIZE-INSTANCE :AFTER ((SECTION SECTION) &REST INITARGS &KEY)
           (DECLARE (IGNORE INITARGS))
           (SETF (SECTION-NUMBER SECTION)
                   (VECTOR-PUSH-EXTEND SECTION *SECTIONS*)))
(DEFCLASS BINARY-SEARCH-TREE NIL
          ((KEY :ACCESSOR NODE-KEY :INITARG :KEY)
           (VALUE :ACCESSOR NODE-VALUE :INITARG :VALUE)
           (LEFT-CHILD :ACCESSOR LEFT-CHILD :INITARG :LEFT)
           (RIGHT-CHILD :ACCESSOR RIGHT-CHILD :INITARG :RIGHT))
          (:DEFAULT-INITARGS :LEFT NIL :RIGHT NIL))
(DEFGENERIC FIND-OR-INSERT (ITEM ROOT &KEY PREDICATE TEST INSERT-IF-NOT-FOUND))
(DEFMETHOD FIND-OR-INSERT
           (ITEM (ROOT BINARY-SEARCH-TREE) &KEY (PREDICATE #'<) (TEST #'EQL)
            (INSERT-IF-NOT-FOUND T))
           (FLET ((LESSP (ITEM NODE)
                    (FUNCALL PREDICATE ITEM (NODE-KEY NODE)))
                  (SAMEP (ITEM NODE)
                    (FUNCALL TEST ITEM (NODE-KEY NODE))))
             (DO ((PARENT NIL NODE)
                  (NODE ROOT
                        (IF (LESSP ITEM NODE) (LEFT-CHILD NODE)
                            (RIGHT-CHILD NODE))))
                 ((OR (NULL NODE) (SAMEP ITEM NODE))
                  (IF NODE (VALUES NODE T)
                      (IF INSERT-IF-NOT-FOUND
                          (LET ((NODE
                                 (MAKE-INSTANCE (CLASS-OF ROOT) :KEY ITEM)))
                            (WHEN PARENT
                              (IF (LESSP ITEM PARENT)
                                  (SETF (LEFT-CHILD PARENT) NODE)
                                  (SETF (RIGHT-CHILD PARENT) NODE)))
                            (VALUES NODE NIL))
                          (VALUES NIL NIL)))))))
(DEFCLASS NAMED-SECTION (BINARY-SEARCH-TREE)
          ((KEY :ACCESSOR SECTION-NAME :INITARG :NAME)
           (VALUE :ACCESSOR SECTION-CODE :INITARG :CODE)
           (NUMBER :ACCESSOR SECTION-NUMBER)
           (USED-BY :ACCESSOR USED-BY :INITFORM 'NIL)
           (SEE-ALSO :ACCESSOR SEE-ALSO :INITFORM 'NIL)))
(DEFUN SET-NAMED-SECTION-CODE (SECTION FORMS &OPTIONAL (APPEND-P T))
  (SETF (SECTION-CODE SECTION)
          (IF (AND APPEND-P (SLOT-BOUNDP SECTION 'VALUE))
              (APPEND (SECTION-CODE SECTION) FORMS) FORMS)))
(DEFMETHOD FIND-OR-INSERT
           (ITEM (ROOT NAMED-SECTION) &KEY (PREDICATE #'SECTION-NAME-LESSP)
            (TEST #'SECTION-NAME-EQUAL) (INSERT-IF-NOT-FOUND T))
           (MULTIPLE-VALUE-BIND
               (NODE PRESENT-P)
               (CALL-NEXT-METHOD ITEM ROOT :PREDICATE PREDICATE :TEST TEST
                :INSERT-IF-NOT-FOUND INSERT-IF-NOT-FOUND)
             (IF PRESENT-P
                 (OR
                  (DOLIST (CHILD (LIST (LEFT-CHILD NODE) (RIGHT-CHILD NODE)))
                    (WHEN CHILD
                      (MULTIPLE-VALUE-BIND
                          (ALT PRESENT-P)
                          (CALL-NEXT-METHOD ITEM CHILD :PREDICATE PREDICATE
                           :TEST TEST :INSERT-IF-NOT-FOUND NIL)
                        (WHEN PRESENT-P
                          (RESTART-CASE
                           (ERROR
                            "~<Ambiguous prefix <~A>: matches both <~A> and <~A>~:@>"
                            (LIST ITEM (NODE-KEY NODE) (NODE-KEY ALT)))
                           (USE-FIRST-MATCH NIL :REPORT "Use the first match."
                            (RETURN (VALUES NODE T)))
                           (USE-ALT-MATCH NIL :REPORT
                            "Use the alternate match."
                            (RETURN (VALUES ALT T))))))))
                  (VALUES NODE T))
                 (VALUES NODE NIL))))
(DEFVAR *NAMED-SECTIONS* NIL)
(DEFUN FIND-SECTION (NAME)
  (IF (NULL *NAMED-SECTIONS*)
      (VALUES (SETQ *NAMED-SECTIONS* (MAKE-INSTANCE 'NAMED-SECTION :NAME NAME))
              NIL)
      (MULTIPLE-VALUE-BIND
          (SECTION PRESENT-P)
          (FIND-OR-INSERT NAME *NAMED-SECTIONS*)
        (WHEN PRESENT-P (SETF (SECTION-NAME SECTION) NAME))
        (VALUES SECTION PRESENT-P))))
(DEFPARAMETER *WHITESPACE*
  (COERCE '(#\  #\Tab #\Newline #\Newline #\Page #\Return) 'SIMPLE-STRING))
(DEFUN SQUEEZE (STRING)
  (FLET ((WHITESPACE-P (CHAR)
           (FIND CHAR *WHITESPACE* :TEST #'CHAR=)))
    (COERCE
     (LOOP WITH SQUEEZING = NIL FOR CHAR ACROSS
           (STRING-TRIM *WHITESPACE* STRING) IF (NOT SQUEEZING) IF
           (WHITESPACE-P CHAR) DO (SETQ SQUEEZING T) AND COLLECT #\  ELSE
           COLLECT CHAR ELSE UNLESS (WHITESPACE-P CHAR) DO (SETQ SQUEEZING NIL)
           AND COLLECT CHAR)
     'SIMPLE-STRING)))
(DEFUN SECTION-NAME-PREFIX-P (NAME)
  (LET ((LEN (LENGTH NAME)))
    (IF (STRING= (SUBSEQ NAME (MAX (- LEN 3) 0) LEN) "...")
        (VALUES T (- LEN 3)) (VALUES NIL LEN))))
(DEFUN SECTION-NAME-EQUAL (NAME1 NAME2)
  (MULTIPLE-VALUE-BIND
      (PREFIX-1-P LEN1)
      (SECTION-NAME-PREFIX-P NAME1)
    (MULTIPLE-VALUE-BIND
        (PREFIX-2-P LEN2)
        (SECTION-NAME-PREFIX-P NAME2)
      (LET ((END (MIN LEN1 LEN2)))
        (IF (OR PREFIX-1-P PREFIX-2-P)
            (STRING-EQUAL NAME1 NAME2 :END1 END :END2 END)
            (STRING-EQUAL NAME1 NAME2))))))
(DEFUN SECTION-NAME-LESSP (NAME1 NAME2)
  (MULTIPLE-VALUE-BIND
      (PREFIX-1-P LEN1)
      (SECTION-NAME-PREFIX-P NAME1)
    (DECLARE (IGNORE PREFIX-1-P))
    (MULTIPLE-VALUE-BIND
        (PREFIX-2-P LEN2)
        (SECTION-NAME-PREFIX-P NAME2)
      (DECLARE (IGNORE PREFIX-2-P))
      (STRING-LESSP NAME1 NAME2 :END1 LEN1 :END2 LEN2))))
(DEFMETHOD (SETF SECTION-NAME) :AROUND (NEW-NAME (SECTION NAMED-SECTION))
           (MULTIPLE-VALUE-BIND
               (NEW-PREFIX-P NEW-LEN)
               (SECTION-NAME-PREFIX-P NEW-NAME)
             (MULTIPLE-VALUE-BIND
                 (OLD-PREFIX-P OLD-LEN)
                 (SECTION-NAME-PREFIX-P (SECTION-NAME SECTION))
               (IF
                (OR (AND OLD-PREFIX-P (NOT NEW-PREFIX-P))
                    (AND OLD-PREFIX-P NEW-PREFIX-P (< NEW-LEN OLD-LEN)))
                (CALL-NEXT-METHOD) NEW-NAME))))
(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL :EXECUTE)
  (DEFPARAMETER *MODES* '(:LIMBO :TEX :LISP :INNER-LISP :RESTRICTED)))
(DEFTYPE MODE () `(MEMBER ,@*MODES*))
(DEFVAR *READTABLES*
  (LOOP FOR MODE IN (APPEND *MODES* '(NIL)) COLLECT
        (CONS MODE (COPY-READTABLE NIL))))
(DEFUN READTABLE-FOR-MODE (MODE)
  (DECLARE (TYPE (OR MODE NULL) MODE))
  (CDR (ASSOC MODE *READTABLES*)))
(DEFMACRO WITH-MODE (MODE &BODY BODY)
  `(LET ((*READTABLE* (READTABLE-FOR-MODE ,MODE)))
     ,@BODY))
(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL :EXECUTE)
  (DEFVAR *EOF* (MAKE-SYMBOL "EOF")))
(DEFUN EOF-P (X) (EQ X *EOF*))
(DEFTYPE EOF () '(SATISFIES EOF-P))
(DEFCLASS MARKER NIL
          ((NAME :ACCESSOR MARKER-NAME :INITARG :NAME)
           (VALUE :ACCESSOR MARKER-VALUE :INITARG :VALUE))
          (:DEFAULT-INITARGS :NAME NIL))
(DEFGENERIC MARKER-BOUNDP (MARKER))
(DEFMETHOD MARKER-BOUNDP ((MARKER MARKER)) (SLOT-BOUNDP MARKER 'VALUE))
(DEFMETHOD PRINT-OBJECT ((OBJECT MARKER) STREAM)
           (LET ((NAME (MARKER-NAME OBJECT)))
             (IF NAME
                 (PRINT-UNREADABLE-OBJECT (OBJECT STREAM :TYPE T :IDENTITY NIL)
                   (PRINC NAME STREAM))
                 (PRINT-UNREADABLE-OBJECT
                     (OBJECT STREAM :TYPE T :IDENTITY T)))))
(DEFVAR *NEWLINE* (MAKE-INSTANCE 'MARKER :NAME "Newline"))
(SET-PPRINT-DISPATCH `(EQL ,*NEWLINE*)
                     (LAMBDA (STREAM OBJ)
                       (DECLARE (IGNORE OBJ))
                       (TERPRI STREAM)))
(SET-MACRO-CHARACTER #\Newline (CONSTANTLY *NEWLINE*) NIL
                     (READTABLE-FOR-MODE :LISP))
(DEFCLASS COMMENT-MARKER (MARKER) ((TEXT :READER COMMENT-TEXT :INITARG :TEXT)))
(DEFMETHOD PRINT-OBJECT ((OBJECT COMMENT-MARKER) STREAM)
           (PRINT-UNREADABLE-OBJECT (OBJECT STREAM :TYPE T :IDENTITY NIL)
             (PRIN1 (COMMENT-TEXT OBJECT) STREAM)))
(SET-PPRINT-DISPATCH 'COMMENT-MARKER
                     (LAMBDA (STREAM OBJ)
                       (WRITE-STRING (COMMENT-TEXT OBJ) STREAM)))
(DEFUN COMMENT-READER (STREAM CHAR)
  (IF (CHAR= (PEEK-CHAR NIL STREAM NIL NIL T) #\Newline)
      (PROGN (READ-CHAR STREAM T NIL T) (VALUES))
      (MAKE-INSTANCE 'COMMENT-MARKER :TEXT
                     (WITH-OUTPUT-TO-STRING (S)
                       (WRITE-CHAR CHAR S)
                       (DO ()
                           ((CHAR= (PEEK-CHAR NIL STREAM NIL #\Newline T)
                                   #\Newline))
                         (WRITE-CHAR (READ-CHAR STREAM T NIL T) S))))))
(SET-MACRO-CHARACTER #\; #'COMMENT-READER NIL (READTABLE-FOR-MODE :LISP))
(DEFVAR *EMPTY-LIST* (MAKE-INSTANCE 'MARKER :NAME "()" :VALUE 'NIL))
(SET-PPRINT-DISPATCH `(EQL ,*EMPTY-LIST*)
                     (LAMBDA (STREAM OBJ)
                       (WRITE-STRING (MARKER-VALUE OBJ) STREAM)))
(DEFUN READ-LIST (STREAM CHAR)
  (IF (CHAR= (PEEK-CHAR T STREAM T NIL T) #\))
      (PROGN (READ-CHAR STREAM T NIL T) *EMPTY-LIST*)
      (FUNCALL (GET-MACRO-CHARACTER #\( NIL) STREAM CHAR)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\( #'READ-LIST NIL (READTABLE-FOR-MODE MODE)))
(DEFCLASS QUOTE-MARKER (MARKER) ((VALUE :ACCESSOR QUOTED-FORM :INITARG :FORM)))
(DEFMETHOD PRINT-OBJECT ((OBJECT QUOTE-MARKER) STREAM)
           (PRINT-UNREADABLE-OBJECT (OBJECT STREAM :TYPE T :IDENTITY NIL)
             (FORMAT STREAM "'~S" (QUOTED-FORM OBJECT))))
(SET-PPRINT-DISPATCH 'QUOTE-MARKER
                     (LAMBDA (STREAM OBJ)
                       (FORMAT STREAM "'~W" (QUOTED-FORM OBJ))))
(DEFMETHOD MARKER-VALUE ((MARKER QUOTE-MARKER))
           (LIST 'QUOTE (QUOTED-FORM MARKER)))
(DEFUN SINGLE-QUOTE-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (MAKE-INSTANCE 'QUOTE-MARKER :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\' #'SINGLE-QUOTE-READER NIL (READTABLE-FOR-MODE MODE)))
(DEFCLASS BACKQUOTE-MARKER (MARKER)
          ((VALUE :ACCESSOR BACKQ-FORM :INITARG :FORM)))
(DEFMETHOD MARKER-VALUE ((MARKER BACKQUOTE-MARKER))
           (WITH-MODE NIL
                      (READ-FROM-STRING
                       (WITH-OUTPUT-TO-STRING (S) (PPRINT MARKER S)))))
(DEFUN BACKQUOTE-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (MAKE-INSTANCE 'BACKQUOTE-MARKER :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\` #'BACKQUOTE-READER NIL (READTABLE-FOR-MODE MODE)))
(SET-PPRINT-DISPATCH 'BACKQUOTE-MARKER
                     (LAMBDA (STREAM OBJ)
                       (FORMAT STREAM "`~W" (BACKQ-FORM OBJ))))
(DEFCLASS COMMA-MARKER (MARKER)
          ((VALUE :ACCESSOR COMMA-FORM :INITARG :FORM)
           (MODIFIER :READER COMMA-MODIFIER :INITARG :MODIFIER))
          (:DEFAULT-INITARGS :MODIFIER NIL))
(DEFMETHOD MARKER-VALUE ((MARKER COMMA-MARKER))
           (WITH-MODE NIL
                      (READ-FROM-STRING
                       (WITH-OUTPUT-TO-STRING (S) (PPRINT MARKER S)))))
(DEFUN COMMA-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (LET ((C (READ-CHAR STREAM)))
    (CASE C
      (#\@
       (MAKE-INSTANCE 'COMMA-MARKER :MODIFIER #\@ :FORM (READ STREAM T NIL T)))
      (#\.
       (MAKE-INSTANCE 'COMMA-MARKER :MODIFIER #\. :FORM (READ STREAM T NIL T)))
      (T
       (UNREAD-CHAR C STREAM)
       (MAKE-INSTANCE 'COMMA-MARKER :FORM (READ STREAM T NIL T))))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\, #'COMMA-READER NIL (READTABLE-FOR-MODE MODE)))
(SET-PPRINT-DISPATCH 'COMMA-MARKER
                     (LAMBDA (STREAM OBJ)
                       (FORMAT STREAM ",~@[~C~]~W" (COMMA-MODIFIER OBJ)
                               (COMMA-FORM OBJ))))
(DEFUN SNARF-UNTIL-CONTROL-CHAR
       (STREAM CONTROL-CHARS
        &AUX
        (CONTROL-CHARS
         (IF (LISTP CONTROL-CHARS) CONTROL-CHARS (LIST CONTROL-CHARS))))
  (WITH-OUTPUT-TO-STRING (STRING)
    (LOOP FOR CHAR = (PEEK-CHAR NIL STREAM NIL *EOF* NIL) UNTIL
          (OR (EOF-P CHAR) (MEMBER CHAR CONTROL-CHARS)) DO
          (WRITE-CHAR (READ-CHAR STREAM) STRING))))
(DEFUN READ-INNER-LISP (STREAM CHAR)
  (WITH-MODE :INNER-LISP (READ-DELIMITED-LIST CHAR STREAM T)))
(DOLIST (MODE '(:TEX :RESTRICTED))
  (SET-MACRO-CHARACTER #\| #'READ-INNER-LISP NIL (READTABLE-FOR-MODE MODE)))
(SET-MACRO-CHARACTER #\| (GET-MACRO-CHARACTER #\) NIL) NIL
                     (READTABLE-FOR-MODE :INNER-LISP))
(DOLIST (MODE *MODES*)
  (IGNORE-ERRORS
   (MAKE-DISPATCH-MACRO-CHARACTER #\@ T (READTABLE-FOR-MODE MODE))))
(DEFUN GET-CONTROL-CODE (SUB-CHAR MODE)
  (GET-DISPATCH-MACRO-CHARACTER #\@ SUB-CHAR (READTABLE-FOR-MODE MODE)))
(DEFUN SET-CONTROL-CODE (SUB-CHAR FUNCTION &OPTIONAL (MODES *MODES*))
  (DOLIST (MODE MODES)
    (SET-DISPATCH-MACRO-CHARACTER #\@ SUB-CHAR FUNCTION
                                  (READTABLE-FOR-MODE MODE))))
(SET-CONTROL-CODE #\@
                  (LAMBDA (STREAM SUB-CHAR ARG)
                    (DECLARE (IGNORE SUB-CHAR STREAM ARG))
                    (STRING "@")))
(DEFUN START-SECTION-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE STREAM ARG))
  (MAKE-INSTANCE (ECASE SUB-CHAR (#\  'SECTION) (#\* 'STARRED-SECTION))))
(DOLIST (SUB-CHAR '(#\  #\*))
  (SET-CONTROL-CODE SUB-CHAR #'START-SECTION-READER '(:LIMBO :TEX :LISP)))
(DEFCLASS START-CODE-MARKER (MARKER)
          ((EVALP :READER EVALUATED-CODE-P :INITARG :EVALP))
          (:DEFAULT-INITARGS :EVALP NIL))
(DEFUN START-CODE-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE STREAM ARG))
  (MAKE-INSTANCE 'START-CODE-MARKER :EVALP
                 (ECASE SUB-CHAR ((#\L #\P) NIL) ((#\E) T))))
(DOLIST (SUB-CHAR '(#\l #\p #\e))
  (SET-CONTROL-CODE SUB-CHAR #'START-CODE-READER '(:TEX)))
(DEFVAR *END-CONTROL-TEXT* (MAKE-SYMBOL "@>"))
(SET-CONTROL-CODE #\> (CONSTANTLY *END-CONTROL-TEXT*) '(:RESTRICTED))
(DEFUN READ-CONTROL-TEXT (STREAM)
  (WITH-MODE :RESTRICTED
             (APPLY #'CONCATENATE 'STRING
                    (LOOP FOR TEXT = (SNARF-UNTIL-CONTROL-CHAR STREAM #\@) AS X
                          = (READ-PRESERVING-WHITESPACE STREAM T NIL T) COLLECT
                          TEXT UNTIL (EQ X *END-CONTROL-TEXT*) COLLECT X))))
(DEFUN MAKE-SECTION-NAME-READER (DEFINITION-ALLOWED-P)
  (LAMBDA (STREAM SUB-CHAR ARG)
    (DECLARE (IGNORE SUB-CHAR ARG))
    (LET* ((NAME (READ-CONTROL-TEXT STREAM))
           (DEFINITION-P (EQL (PEEK-CHAR NIL STREAM NIL NIL T) #\=)))
      (IF DEFINITION-P
          (IF DEFINITION-ALLOWED-P
              (PROGN
               (READ-CHAR STREAM)
               (MAKE-INSTANCE 'START-CODE-MARKER :NAME NAME))
              (RESTART-CASE
               (ERROR "Can't define a named section in Lisp mode: ~A" NAME)
               (USE-SECTION NIL :REPORT
                "Don't define the section, just use it." (FIND-SECTION NAME))))
          (IF DEFINITION-ALLOWED-P
              (RESTART-CASE
               (ERROR "Can't use a section name in TeX mode: ~A" NAME)
               (NAME-SECTION NIL :REPORT
                "Name the current section and start the code part."
                (MAKE-INSTANCE 'START-CODE-MARKER :NAME NAME))
               (CITE-SECTION NIL :REPORT
                "Assume the section is just being cited." (FIND-SECTION NAME)))
              (LET ((NAMED-SECTION (FIND-SECTION NAME)))
                (PUSHNEW (CURRENT-SECTION) (USED-BY NAMED-SECTION))
                NAMED-SECTION))))))
(SET-CONTROL-CODE #\< (MAKE-SECTION-NAME-READER T) '(:TEX))
(SET-CONTROL-CODE #\< (MAKE-SECTION-NAME-READER NIL) '(:LISP :INNER-LISP))
(DEFMACRO MAYBE-PUSH (OBJ PLACE &AUX (G (GENSYM)))
  `(LET ((,G ,OBJ))
     (WHEN (TYPECASE ,G (STRING (PLUSP (LENGTH ,G))) (T ,G)) (PUSH ,G ,PLACE))))
(DEFUN READ-SECTIONS (STREAM APPEND-P)
  (FLET ((FINISH-SECTION (SECTION COMMENTARY CODE)
           (SETF (SECTION-COMMENTARY SECTION) (NREVERSE COMMENTARY))
           (SETF (SECTION-CODE SECTION) (NREVERSE CODE))
           (WHEN (SECTION-NAME SECTION)
             (LET ((NAMED-SECTION (FIND-SECTION (SECTION-NAME SECTION)))
                   (NUMBER (SECTION-NUMBER SECTION))
                   (CODE (SECTION-CODE SECTION)))
               (SET-NAMED-SECTION-CODE NAMED-SECTION CODE APPEND-P)
               (WHEN
                   (OR (NOT (SLOT-BOUNDP NAMED-SECTION 'NUMBER))
                       (NOT APPEND-P))
                 (SETF (SECTION-NUMBER NAMED-SECTION) NUMBER))
               (IF APPEND-P (PUSHNEW SECTION (SEE-ALSO NAMED-SECTION))
                   (SETF (SEE-ALSO NAMED-SECTION) (LIST SECTION)))))
           SECTION))
    (PROG (FORM COMMENTARY CODE SECTION SECTIONS)
     LIMBO
      (SETQ SECTION (MAKE-INSTANCE 'LIMBO-SECTION))
      (WITH-MODE :LIMBO
                 (LOOP
                  (MAYBE-PUSH (SNARF-UNTIL-CONTROL-CHAR STREAM #\@) COMMENTARY)
                  (SETQ FORM (READ-PRESERVING-WHITESPACE STREAM NIL *EOF* NIL))
                  (TYPECASE FORM
                    (EOF (GO EOF))
                    (SECTION (GO COMMENTARY))
                    (T (PUSH FORM COMMENTARY)))))
     COMMENTARY
      (PUSH (FINISH-SECTION SECTION COMMENTARY CODE) SECTIONS)
      (CHECK-TYPE FORM SECTION)
      (SETQ SECTION FORM COMMENTARY 'NIL CODE 'NIL)
      (WITH-MODE :TEX
                 (LOOP
                  (MAYBE-PUSH (SNARF-UNTIL-CONTROL-CHAR STREAM '(#\@ #\|))
                              COMMENTARY)
                  (SETQ FORM (READ-PRESERVING-WHITESPACE STREAM NIL *EOF* NIL))
                  (TYPECASE FORM
                    (EOF (GO EOF))
                    (SECTION (GO COMMENTARY))
                    (START-CODE-MARKER
                     (SETF (SECTION-NAME SECTION) (MARKER-NAME FORM))
                     (GO LISP))
                    (T (PUSH FORM COMMENTARY)))))
     LISP
      (CHECK-TYPE FORM START-CODE-MARKER)
      (WITH-MODE :LISP
                 (LET ((EVALP (EVALUATED-CODE-P FORM)))
                   (LOOP
                    (SETQ FORM
                            (READ-PRESERVING-WHITESPACE STREAM NIL *EOF* NIL))
                    (TYPECASE FORM
                      (EOF (GO EOF))
                      (SECTION (GO COMMENTARY))
                      (START-CODE-MARKER
                       (ERROR "Can't start a section with a code part"))
                      (T
                       (WHEN EVALP (EVAL (TANGLE FORM)))
                       (PUSH FORM CODE))))))
     EOF
      (PUSH (FINISH-SECTION SECTION COMMENTARY CODE) SECTIONS)
      (RETURN (NREVERSE SECTIONS)))))
(DEFUN TANGLE-1 (FORM)
  (COND ((ATOM FORM) (VALUES FORM NIL))
        ((TYPEP (CAR FORM) 'NAMED-SECTION)
         (VALUES (APPEND (SECTION-CODE (CAR FORM)) (TANGLE-1 (CDR FORM))) T))
        ((TYPEP (CAR FORM) 'MARKER)
         (VALUES
          (IF (MARKER-BOUNDP (CAR FORM))
              (CONS (MARKER-VALUE (CAR FORM)) (TANGLE-1 (CDR FORM)))
              (TANGLE-1 (CDR FORM)))
          T))
        (T
         (MULTIPLE-VALUE-BIND
             (A CAR-EXPANDED-P)
             (TANGLE-1 (CAR FORM))
           (MULTIPLE-VALUE-BIND
               (D CDR-EXPANDED-P)
               (TANGLE-1 (CDR FORM))
             (VALUES
              (IF (AND (EQL A (CAR FORM)) (EQL D (CDR FORM))) FORM (CONS A D))
              (OR CAR-EXPANDED-P CDR-EXPANDED-P)))))))
(DEFUN TANGLE (FORM)
  (LABELS ((EXPAND (FORM EXPANDED)
             (MULTIPLE-VALUE-BIND
                 (NEW-FORM NEWLY-EXPANDED-P)
                 (TANGLE-1 FORM)
               (IF NEWLY-EXPANDED-P (EXPAND NEW-FORM T)
                   (VALUES NEW-FORM EXPANDED)))))
    (EXPAND FORM NIL)))
(DEFUN READ-CODE-PARTS (STREAM APPEND-P)
  (APPLY #'APPEND
         (MAP 'LIST #'SECTION-CODE
              (REMOVE-IF #'SECTION-NAME (READ-SECTIONS STREAM APPEND-P)))))
(DEFUN LOAD-WEB-FROM-STREAM (STREAM VERBOSE PRINT &OPTIONAL (APPEND-P T))
  (WHEN VERBOSE (FORMAT T "~&; loading WEB from ~S~%" (PATHNAME STREAM)))
  (LET ((*READTABLE* *READTABLE*) (*PACKAGE* *PACKAGE*))
    (DOLIST (FORM (TANGLE (READ-CODE-PARTS STREAM APPEND-P)) T)
      (IF PRINT
          (LET ((RESULTS (MULTIPLE-VALUE-LIST (EVAL FORM))))
            (FORMAT T "~&; ~{~S~^, ~}~%" RESULTS))
          (EVAL FORM)))))
(DEFUN LOAD-WEB
       (FILESPEC
        &KEY (VERBOSE *LOAD-VERBOSE*) (PRINT *LOAD-PRINT*)
        (IF-DOES-NOT-EXIST T) (EXTERNAL-FORMAT :DEFAULT))
  (SETF (FILL-POINTER *SECTIONS*) 0)
  (SETQ *NAMED-SECTIONS* NIL)
  (IF (STREAMP FILESPEC) (LOAD-WEB-FROM-STREAM FILESPEC VERBOSE PRINT)
      (WITH-OPEN-FILE
          (STREAM FILESPEC :DIRECTION :INPUT :EXTERNAL-FORMAT EXTERNAL-FORMAT
           :IF-DOES-NOT-EXIST (IF IF-DOES-NOT-EXIST :ERROR NIL))
        (LOAD-WEB-FROM-STREAM STREAM VERBOSE PRINT))))
(DEFUN LOAD-SECTIONS-FROM-TEMP-FILE
       (FILE APPEND-P &AUX (TRUENAME (PROBE-FILE FILE)))
  (WHEN TRUENAME
    (UNWIND-PROTECT
        (WITH-OPEN-FILE (STREAM TRUENAME :DIRECTION :INPUT)
          (LOAD-WEB-FROM-STREAM STREAM NIL T APPEND-P))
      (DELETE-FILE TRUENAME))))
(DEFUN TANGLE-FILE
       (INPUT-FILE
        &REST ARGS
        &KEY OUTPUT-FILE (VERBOSE *COMPILE-VERBOSE*) (PRINT *COMPILE-PRINT*)
        (EXTERNAL-FORMAT :DEFAULT) &ALLOW-OTHER-KEYS
        &AUX
        (LISP-FILE (MERGE-PATHNAMES (MAKE-PATHNAME :TYPE "lisp") INPUT-FILE)))
  (DECLARE (IGNORE OUTPUT-FILE PRINT))
  (WHEN VERBOSE (FORMAT T "~&; tangling WEB from ~S~%" INPUT-FILE))
  (SETF (FILL-POINTER *SECTIONS*) 0)
  (SETQ *NAMED-SECTIONS* NIL)
  (WITH-OPEN-FILE
      (INPUT INPUT-FILE :DIRECTION :INPUT :EXTERNAL-FORMAT EXTERNAL-FORMAT)
    (WITH-OPEN-FILE
        (LISP LISP-FILE :DIRECTION :OUTPUT :IF-EXISTS :SUPERSEDE
         :EXTERNAL-FORMAT EXTERNAL-FORMAT)
      (FORMAT LISP ";;;; TANGLED OUTPUT FROM WEB ~S.  DO NOT EDIT." INPUT-FILE)
      (DOLIST (FORM (TANGLE (READ-CODE-PARTS INPUT T))) (PPRINT FORM LISP))))
  (APPLY #'COMPILE-FILE LISP-FILE ARGS))
(DEFPARAMETER *WEAVE-PPRINT-DISPATCH* (COPY-PPRINT-DISPATCH NIL))
(DEFUN SET-WEAVE-DISPATCH (TYPE-SPECIFIER FUNCTION &OPTIONAL (PRIORITY 0))
  (SET-PPRINT-DISPATCH TYPE-SPECIFIER FUNCTION PRIORITY
                       *WEAVE-PPRINT-DISPATCH*))
(DEFUN WEAVE
       (FILESPEC
        &KEY (OUTPUT-FILE NIL) (VERBOSE *LOAD-VERBOSE*) (PRINT *LOAD-PRINT*)
        (IF-DOES-NOT-EXIST T) (EXTERNAL-FORMAT :DEFAULT))
  (UNLESS OUTPUT-FILE
    (SETQ OUTPUT-FILE (MERGE-PATHNAMES (MAKE-PATHNAME :TYPE "tex") FILESPEC)))
  (LOAD-WEB FILESPEC :VERBOSE VERBOSE :PRINT PRINT :IF-DOES-NOT-EXIST
            IF-DOES-NOT-EXIST :EXTERNAL-FORMAT EXTERNAL-FORMAT)
  (WEAVE-SECTIONS *SECTIONS* OUTPUT-FILE))
(DEFPARAMETER *TEX-PROLOGUE* (FORMAT NIL "\\input clwebmac~%"))
(DEFUN WEAVE-SECTIONS (SECTIONS OUTPUT-FILE)
  (WITH-OPEN-FILE (OUTPUT OUTPUT-FILE :DIRECTION :OUTPUT :IF-EXISTS :SUPERSEDE)
    (PRINC *TEX-PROLOGUE* OUTPUT)
    (LOOP WITH *PRINT-CASE* = :DOWNCASE WITH *PRINT-ESCAPE* = NIL WITH
          *PRINT-PRETTY* = T WITH *PRINT-PPRINT-DISPATCH* =
          *WEAVE-PPRINT-DISPATCH* WITH *PRINT-RIGHT-MARGIN* = 1000 FOR SECTION
          ACROSS SECTIONS DO (PPRINT SECTION OUTPUT) FINALLY
          (FORMAT OUTPUT "~&\\bye~%"))))
(DEFVAR *INNER-LISP* NIL)
(DEFUN PRINT-TEX (STREAM TEX-MODE-MATERIAL)
  (DOLIST (X TEX-MODE-MATERIAL)
    (ETYPECASE X
      (STRING (WRITE-STRING X STREAM))
      (LIST
       (LET ((*INNER-LISP* T))
         (DOLIST (FORM X) (WRITE FORM :STREAM STREAM)))))))
(DEFUN READ-TEX-FROM-STRING (INPUT-STRING)
  (WITH-INPUT-FROM-STRING (STREAM INPUT-STRING)
    (WITH-MODE :RESTRICTED
               (LOOP FOR TEXT = (SNARF-UNTIL-CONTROL-CHAR STREAM #\|) FOR FORMS
                     = (READ-PRESERVING-WHITESPACE STREAM NIL *EOF* NIL)
                     COLLECT TEXT UNTIL (EOF-P FORMS) COLLECT FORMS))))
(DEFUN PRINT-LIMBO (STREAM SECTION)
  (LET ((COMMENTARY (SECTION-COMMENTARY SECTION)))
    (WHEN COMMENTARY (PRINT-TEX STREAM COMMENTARY))))
(SET-WEAVE-DISPATCH 'LIMBO-SECTION #'PRINT-LIMBO 1)
(DEFUN PRINT-SECTION (STREAM SECTION)
  (FORMAT STREAM "~&\\~:[M~;N{1}~]{~D}" (TYPEP SECTION 'STARRED-SECTION)
          (SECTION-NUMBER SECTION))
  (LET* ((COMMENTARY (SECTION-COMMENTARY SECTION))
         (NAME (SECTION-NAME SECTION))
         (NAMED-SECTION (AND NAME (FIND-SECTION NAME)))
         (CODE (SECTION-CODE SECTION)))
    (PRINT-TEX STREAM COMMENTARY)
    (WHEN (AND COMMENTARY CODE) (WRITE-STRING "\\Y" STREAM))
    (WHEN NAMED-SECTION
      (PRINT-SECTION-NAME STREAM NAMED-SECTION)
      (FORMAT STREAM "${}~:[\\mathrel+~;~]\\E{}$"
              (= (SECTION-NUMBER SECTION) (SECTION-NUMBER NAMED-SECTION))))
    (DOLIST (FORM CODE)
      (PPRINT-LOGICAL-BLOCK (STREAM FORM :PER-LINE-PREFIX "\\+" :SUFFIX "\\cr")
        (WRITE FORM :STREAM STREAM)))
    (WHEN NAMED-SECTION
      (PRINT-XREFS STREAM #\A SECTION (SEE-ALSO NAMED-SECTION))
      (PRINT-XREFS STREAM #\U SECTION (USED-BY NAMED-SECTION))))
  (WRITE-STRING "\\fi" STREAM))
(SET-WEAVE-DISPATCH 'SECTION #'PRINT-SECTION)
(DEFUN PRINT-XREFS (STREAM KIND SECTION XREFS)
  (WHEN (SETQ XREFS (REMOVE SECTION XREFS))
    (FORMAT STREAM
            "~&\\~C~{~#[~;~D~;s ~D\\ET~D~:;s~@{~#[~;\\ETs~D~;~D~:;~D, ~]~}~]~}."
            KIND (SORT (MAPCAR #'SECTION-NUMBER XREFS) #'<))))
(DEFUN PRINT-SECTION-NAME (STREAM NAMED-SECTION)
  (FORMAT STREAM "\\X~D:" (SECTION-NUMBER NAMED-SECTION))
  (PRINT-TEX STREAM (READ-TEX-FROM-STRING (SECTION-NAME NAMED-SECTION)))
  (WRITE-STRING "\\X" STREAM))
(SET-WEAVE-DISPATCH 'NAMED-SECTION #'PRINT-SECTION-NAME)
(SET-WEAVE-DISPATCH `(EQL ,*NEWLINE*)
                    (LAMBDA (STREAM OBJ)
                      (DECLARE (IGNORE OBJ))
                      (TERPRI STREAM)))
(SET-WEAVE-DISPATCH `(EQL ,*EMPTY-LIST*)
                    (LAMBDA (STREAM OBJ)
                      (DECLARE (IGNORE OBJ))
                      (WRITE-STRING "\\(\\)" STREAM)))
(SET-WEAVE-DISPATCH 'QUOTE-MARKER
                    (LAMBDA (STREAM OBJ)
                      (WRITE-STRING "\\'" STREAM)
                      (PRINT-LIST STREAM (QUOTED-FORM OBJ))))
(SET-WEAVE-DISPATCH 'COMMENT-MARKER
                    (LAMBDA (STREAM OBJ)
                      (PRINT-TEX STREAM
                                 (READ-TEX-FROM-STRING (COMMENT-TEXT OBJ)))))
(DEFUN WRITE-ESCAPED-STRING (STREAM STRING ESCAPE-CHARS)
  (DOTIMES (I (LENGTH STRING))
    (LET* ((CHAR (CHAR STRING I))
           (ESCAPE (CDR (ASSOC CHAR ESCAPE-CHARS :TEST #'FIND))))
      (ETYPECASE ESCAPE
        (CHARACTER (WRITE-CHAR ESCAPE STREAM) (WRITE-CHAR CHAR STREAM))
        (STRING (WRITE-STRING ESCAPE STREAM))
        (NULL (WRITE-CHAR CHAR STREAM))))))
(DEFPARAMETER *TEX-ESCAPE-ALIST*
  '((" \\%&#$^_|~" . #\\) ("{" . "$\\{$") ("}" . "$\\}$")))
(DEFUN PRINT-STRING (STREAM STRING)
  (WRITE-STRING "\\.{\"" STREAM)
  (WRITE-ESCAPED-STRING STREAM STRING
                        (LIST* '("{}" . #\\) '("\\" . "\\\\\\\\")
                               '("\"" . "\\\\\"") *TEX-ESCAPE-ALIST*))
  (WRITE-STRING "\"}" STREAM))
(SET-WEAVE-DISPATCH 'STRING #'PRINT-STRING)
(DEFUN PRINT-CHAR (STREAM CHAR)
  (LET ((GRAPHICP (AND (GRAPHIC-CHAR-P CHAR) (STANDARD-CHAR-P CHAR)))
        (NAME (CHAR-NAME CHAR)))
    (WRITE-STRING "{\\tt \\#\\\\" STREAM)
    (WRITE-ESCAPED-STRING STREAM
                          (IF (AND NAME (NOT GRAPHICP)) NAME
                              (MAKE-STRING 1 :INITIAL-ELEMENT CHAR))
                          (LIST* '("{}" . #\\) *TEX-ESCAPE-ALIST*))
    (WRITE-STRING "}" STREAM)))
(SET-WEAVE-DISPATCH 'CHARACTER #'PRINT-CHAR)
(DEFVAR *HIGHLIGHT-SPECIAL-SYMBOLS* NIL)
(DEFUN DEF-P (SYMBOL)
  (LET* ((NAME (SYMBOL-NAME SYMBOL)) (LEN (LENGTH NAME)))
    (AND (> LEN 3) (STRING= NAME "DEF" :END1 3))))
(DEFUN HIGHLIGHT-SYMBOL-P (SYMBOL)
  (COND
   ((OR (SPECIAL-OPERATOR-P SYMBOL) (MEMBER SYMBOL '(COND LOOP)))
    (MEMBER :SPECIAL-OPERATOR *HIGHLIGHT-SPECIAL-SYMBOLS*))
   ((OPERATOR-WITH-BODY-P SYMBOL) (MEMBER :BODY *HIGHLIGHT-SPECIAL-SYMBOLS*))
   ((MEMBER SYMBOL LAMBDA-LIST-KEYWORDS)
    (MEMBER :LAMBDA-LIST-KEYWORD *HIGHLIGHT-SPECIAL-SYMBOLS*))
   ((DEF-P SYMBOL) (MEMBER :DEF *HIGHLIGHT-SPECIAL-SYMBOLS*))))
(DEFUN PRINT-SYMBOL (STREAM SYMBOL)
  (LET ((GROUP-P
         (COND ((HIGHLIGHT-SYMBOL-P SYMBOL) (WRITE-STRING "\\&{" STREAM))
               ((KEYWORDP SYMBOL) (WRITE-STRING "\\:{" STREAM))
               (*INNER-LISP* (WRITE-STRING "\\\\{" STREAM)))))
    (WRITE-ESCAPED-STRING STREAM
                          (WRITE-TO-STRING SYMBOL :ESCAPE NIL :PRETTY NIL)
                          (LIST* '("*" . "\\/$\\ast$") '("&" . "\\AM ")
                                 *TEX-ESCAPE-ALIST*))
    (WHEN GROUP-P (WRITE-STRING "}" STREAM))))
(SET-WEAVE-DISPATCH 'SYMBOL #'PRINT-SYMBOL)
(DEFMACRO PRINT-REMAINING-OBJECTS-AND-NEWLINES
          (STREAM &KEY (FIRST NIL FIRST-SUPPLIED-P) INDENT)
  (LET ((OBJ (GENSYM)) (NEXT (GENSYM)) (INDENTATION (GENSYM)))
    `(DO ((,OBJ ,(IF FIRST-SUPPLIED-P FIRST '(PPRINT-POP)) ,NEXT)
          (,NEXT)
          (,INDENTATION ,INDENT))
         (NIL)
       (DECLARE (IGNORABLE ,INDENTATION))
       (COND
        ((EQ ,OBJ *NEWLINE*) (FORMAT ,STREAM "\\cr~:@_")
         ,@(WHEN INDENT (LIST `(WRITE-STRING ,INDENTATION ,STREAM)))
         (PPRINT-EXIT-IF-LIST-EXHAUSTED) (SETQ ,NEXT (PPRINT-POP)))
        (T (WRITE ,OBJ :STREAM ,STREAM) (PPRINT-EXIT-IF-LIST-EXHAUSTED)
         (SETQ ,NEXT (PPRINT-POP) ,@(WHEN INDENT `(,INDENTATION ,INDENT)))
         (UNLESS (EQ ,NEXT *NEWLINE*) (WRITE-CHAR ,#\  ,STREAM)))))))
(DEFUN PRINT-LIST (STREAM LIST)
  (WRITE-STRING "\\(" STREAM)
  (PPRINT-LOGICAL-BLOCK (STREAM LIST :PER-LINE-PREFIX "&" :SUFFIX "\\)")
    (PRINT-REMAINING-OBJECTS-AND-NEWLINES STREAM)))
(SET-WEAVE-DISPATCH 'CONS #'PRINT-LIST -2)
(DEFUN PRINT-FUN-CALL (STREAM FORM)
  (WRITE-STRING "\\(" STREAM)
  (PPRINT-LOGICAL-BLOCK (STREAM FORM :PER-LINE-PREFIX "&" :SUFFIX "\\)")
    (WRITE (PPRINT-POP) :STREAM STREAM)
    (PPRINT-EXIT-IF-LIST-EXHAUSTED)
    (LET ((NEXT (PPRINT-POP)))
      (COND
       ((EQ NEXT *NEWLINE*) (FORMAT STREAM "\\cr~:@_")
        (PRINT-REMAINING-OBJECTS-AND-NEWLINES STREAM))
       (T (WRITE-CHAR #\  STREAM) (PPRINT-INDENT :CURRENT 0 STREAM)
        (WRITE-CHAR #\& STREAM)
        (PRINT-REMAINING-OBJECTS-AND-NEWLINES STREAM :FIRST NEXT :INDENT
                                              "&"))))))
(SET-WEAVE-DISPATCH '(CONS (AND SYMBOL (SATISFIES FBOUNDP))) #'PRINT-FUN-CALL
                    -1)
(DEFUN PRINT-FORM-WITH-BODY (STREAM FORM)
  (WRITE-STRING "\\(" STREAM)
  (PPRINT-LOGICAL-BLOCK (STREAM FORM :PER-LINE-PREFIX "&" :SUFFIX "\\)")
    (WRITE (PPRINT-POP) :STREAM STREAM)
    (PPRINT-EXIT-IF-LIST-EXHAUSTED)
    (WRITE-CHAR #\  STREAM)
    (LET ((BODY (OR (LAMBDA-LIST-BODY (CAR FORM)) -1)) (I 0))
      (PRINT-REMAINING-OBJECTS-AND-NEWLINES STREAM :INDENT
                                            (IF (<= (INCF I) BODY) "\\2"
                                                "\\1")))))
(DEFUN OPERATOR-WITH-BODY-P (OPERATOR)
  (AND (FBOUNDP OPERATOR) (LAMBDA-LIST-BODY OPERATOR)))
(SET-WEAVE-DISPATCH '(CONS (AND SYMBOL (SATISFIES OPERATOR-WITH-BODY-P)))
                    #'PRINT-FORM-WITH-BODY 0)
(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL :EXECUTE)
  (REQUIRE 'SB-INTROSPECT)
  (IMPORT (FIND-SYMBOL "FUNCTION-ARGLIST" "SB-INTROSPECT")))
(DEFUN LAMBDA-LIST-BODY (OPERATOR)
  (LABELS ((CLEAN-ARGLIST (ARGLIST)
             (COND ((NULL ARGLIST) 'NIL)
                   ((MEMBER (CAR ARGLIST) '(&WHOLE &ENVIRONMENT))
                    (CLEAN-ARGLIST (CDDR ARGLIST)))
                   ((EQ (CAR ARGLIST) '&AUX) 'NIL)
                   (T (CONS (CAR ARGLIST) (CLEAN-ARGLIST (CDR ARGLIST)))))))
    (LET ((LAMBDA-LIST
           (REMOVE '&OPTIONAL (CLEAN-ARGLIST (FUNCTION-ARGLIST OPERATOR)))))
      (OR (POSITION '&BODY LAMBDA-LIST)
          (LET ((REST (POSITION '&REST LAMBDA-LIST)))
            (WHEN REST
              (LET ((RESTARG (SYMBOL-NAME (ELT LAMBDA-LIST (1+ REST)))))
                (WHEN (STRING= RESTARG "BODY") REST))))))))
(SET-WEAVE-DISPATCH 'BACKQUOTE-MARKER
                    (LAMBDA (STREAM MARKER)
                      (WRITE-STRING "\\`" STREAM)
                      (WRITE (BACKQ-FORM MARKER) :STREAM STREAM)))
(SET-WEAVE-DISPATCH 'COMMA-MARKER
                    (LAMBDA (STREAM MARKER)
                      (FORMAT STREAM "\\C{~@[~C~]}~W" (COMMA-MODIFIER MARKER)
                              (COMMA-FORM MARKER))))
;;;; TANGLED OUTPUT FROM WEB "clweb.lw". DO NOT EDIT.
(DECLAIM (OPTIMIZE (DEBUG 3)))
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
(DEFUN WHITESPACE-P (CHAR) (FIND CHAR *WHITESPACE* :TEST #'CHAR=))
(DEFUN SQUEEZE (STRING)
  (COERCE
   (LOOP WITH SQUEEZING = NIL FOR CHAR ACROSS (STRING-TRIM *WHITESPACE* STRING)
         IF (NOT SQUEEZING) IF (WHITESPACE-P CHAR) DO (SETQ SQUEEZING T) AND
         COLLECT #\  ELSE COLLECT CHAR ELSE UNLESS (WHITESPACE-P CHAR) DO
         (SETQ SQUEEZING NIL) AND COLLECT CHAR)
   'SIMPLE-STRING))
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
           (WHEN NEW-NAME
             (MULTIPLE-VALUE-BIND
                 (NEW-PREFIX-P NEW-LEN)
                 (SECTION-NAME-PREFIX-P NEW-NAME)
               (MULTIPLE-VALUE-BIND
                   (OLD-PREFIX-P OLD-LEN)
                   (SECTION-NAME-PREFIX-P (SECTION-NAME SECTION))
                 (IF
                  (OR (AND OLD-PREFIX-P (NOT NEW-PREFIX-P))
                      (AND OLD-PREFIX-P NEW-PREFIX-P (< NEW-LEN OLD-LEN)))
                  (CALL-NEXT-METHOD) NEW-NAME)))))
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
(DEFCLASS CHARPOS-STREAM NIL
          ((CHARPOS :INITARG :CHARPOS)
           (STREAM :ACCESSOR CHARPOS-STREAM :INITARG :STREAM))
          (:DEFAULT-INITARGS :CHARPOS 0))
(DEFGENERIC CHARPOS (STREAM))
(DEFGENERIC GET-CHARPOS-STREAM-BUFFER (STREAM))
(DEFCLASS CHARPOS-INPUT-STREAM (CHARPOS-STREAM) NIL)
(DEFMETHOD SHARED-INITIALIZE :AROUND
           ((INSTANCE CHARPOS-INPUT-STREAM) SLOT-NAMES &REST INITARGS &KEY
            STREAM)
           (APPLY #'CALL-NEXT-METHOD INSTANCE SLOT-NAMES
                  (SUBST
                   (MAKE-ECHO-STREAM STREAM
                                     (MAKE-STRING-OUTPUT-STREAM :ELEMENT-TYPE
                                                                (STREAM-ELEMENT-TYPE
                                                                 STREAM)))
                   STREAM INITARGS)))
(DEFMETHOD GET-CHARPOS-STREAM-BUFFER ((STREAM CHARPOS-INPUT-STREAM))
           (GET-OUTPUT-STREAM-STRING
            (ECHO-STREAM-OUTPUT-STREAM (CHARPOS-STREAM STREAM))))
(DEFCLASS CHARPOS-OUTPUT-STREAM (CHARPOS-STREAM) NIL)
(DEFMETHOD SHARED-INITIALIZE :AROUND
           ((INSTANCE CHARPOS-OUTPUT-STREAM) SLOT-NAMES &REST INITARGS &KEY
            STREAM)
           (APPLY #'CALL-NEXT-METHOD INSTANCE SLOT-NAMES
                  (SUBST
                   (MAKE-BROADCAST-STREAM
                    (MAKE-STRING-OUTPUT-STREAM :ELEMENT-TYPE
                                               (STREAM-ELEMENT-TYPE STREAM))
                    STREAM)
                   STREAM INITARGS)))
(DEFMETHOD GET-CHARPOS-STREAM-BUFFER ((STREAM CHARPOS-OUTPUT-STREAM))
           (GET-OUTPUT-STREAM-STRING
            (FIRST (BROADCAST-STREAM-STREAMS (CHARPOS-STREAM STREAM)))))
(DEFMETHOD CHARPOS ((STREAM CHARPOS-STREAM))
           (LET* ((I 0)
                  (NEWLINE
                   (POSITION #\Newline (GET-CHARPOS-STREAM-BUFFER STREAM) :KEY
                             (LAMBDA (X) (INCF I) X) :TEST #'CHAR= :FROM-END
                             T)))
             (SETF (SLOT-VALUE STREAM 'CHARPOS)
                     (IF NEWLINE I (+ I (SLOT-VALUE STREAM 'CHARPOS))))))
(DEFVAR *CHARPOS-STREAMS* (MAKE-HASH-TABLE :TEST #'EQ))
(DEFMETHOD INITIALIZE-INSTANCE :AFTER
           ((INSTANCE CHARPOS-STREAM) &REST INITARGS &KEY)
           (DECLARE (IGNORE INITARGS))
           (SETF (GETHASH (CHARPOS-STREAM INSTANCE) *CHARPOS-STREAMS*)
                   INSTANCE))
(DEFUN STREAM-CHARPOS (STREAM)
  (CHARPOS
   (OR (GETHASH STREAM *CHARPOS-STREAMS*)
       (ERROR "Not tracking charpos for ~S" STREAM))))
(DEFUN RELEASE-CHARPOS-STREAM (STREAM)
  (MULTIPLE-VALUE-BIND
      (CHARPOS-STREAM PRESENT-P)
      (GETHASH STREAM *CHARPOS-STREAMS*)
    (COND
     (PRESENT-P (SETF (CHARPOS-STREAM CHARPOS-STREAM) NIL)
      (REMHASH STREAM *CHARPOS-STREAMS*))
     (T (WARN "Not tracking charpos for ~S" STREAM)))))
(DEFUN MAKE-CHARPOS-INPUT-STREAM (INPUT-STREAM &KEY (CHARPOS 0))
  (MAKE-INSTANCE 'CHARPOS-INPUT-STREAM :STREAM
                 (CASE INPUT-STREAM
                   ((T) *TERMINAL-IO*)
                   ((NIL) *STANDARD-INPUT*)
                   (OTHERWISE INPUT-STREAM))
                 :CHARPOS CHARPOS))
(DEFUN MAKE-CHARPOS-OUTPUT-STREAM (OUTPUT-STREAM &KEY (CHARPOS 0))
  (MAKE-INSTANCE 'CHARPOS-OUTPUT-STREAM :STREAM
                 (CASE OUTPUT-STREAM
                   ((T) *TERMINAL-IO*)
                   ((NIL) *STANDARD-OUTPUT*)
                   (OTHERWISE OUTPUT-STREAM))
                 :CHARPOS CHARPOS))
(DEFMACRO WITH-CHARPOS-INPUT-STREAM ((VAR STREAM &KEY (CHARPOS 0)) &BODY BODY)
  `(LET ((,VAR
          (CHARPOS-STREAM
           (MAKE-CHARPOS-INPUT-STREAM ,STREAM :CHARPOS ,CHARPOS))))
     (UNWIND-PROTECT (PROGN ,@BODY) (RELEASE-CHARPOS-STREAM ,VAR))))
(DEFMACRO WITH-CHARPOS-OUTPUT-STREAM ((VAR STREAM &KEY (CHARPOS 0)) &BODY BODY)
  `(LET ((,VAR
          (CHARPOS-STREAM
           (MAKE-CHARPOS-OUTPUT-STREAM ,STREAM :CHARPOS ,CHARPOS))))
     (UNWIND-PROTECT (PROGN ,@BODY) (RELEASE-CHARPOS-STREAM ,VAR))))
(DEFUN TOKEN-DELIMITER-P (CHAR)
  (OR (WHITESPACE-P CHAR)
      (MULTIPLE-VALUE-BIND
          #'NON-TERMINATING-P
          (GET-MACRO-CHARACTER CHAR)
        (AND FUNCTION (NOT NON-TERMINATING-P)))))
(DEFMACRO WITH-REWIND-STREAM ((VAR STREAM) &BODY BODY &AUX (OUT (GENSYM)))
  `(WITH-OPEN-STREAM (,OUT (MAKE-STRING-OUTPUT-STREAM))
     (WITH-OPEN-STREAM (,VAR (MAKE-ECHO-STREAM ,STREAM ,OUT))
       (FLET ((REWIND ,NIL
                (SETQ ,VAR
                        (MAKE-CONCATENATED-STREAM
                         (MAKE-STRING-INPUT-STREAM
                          (GET-OUTPUT-STREAM-STRING ,OUT))
                         ,STREAM))))
         ,@BODY))))
(DEFMACRO READ-WITH-ECHO
          ((STREAM VALUES ECHOED &KEY PREFIX)
           &BODY BODY
           &AUX (OUT (GENSYM)) (ECHO (GENSYM)) (REWIND (GENSYM))
           (RAW-OUTPUT (GENSYM)) (LENGTH (GENSYM)))
  `(WITH-OPEN-STREAM (,OUT (MAKE-STRING-OUTPUT-STREAM))
     (WITH-OPEN-STREAM (,ECHO (MAKE-ECHO-STREAM ,STREAM ,OUT))
       (WITH-OPEN-STREAM
           (,REWIND
            (MAKE-CONCATENATED-STREAM
             ,@(WHEN PREFIX `((MAKE-STRING-INPUT-STREAM ,PREFIX))) ,ECHO))
         (LET* ((,VALUES (MULTIPLE-VALUE-LIST (READ ,REWIND)))
                (,RAW-OUTPUT (GET-OUTPUT-STREAM-STRING ,OUT))
                (,LENGTH (LENGTH ,RAW-OUTPUT))
                (,ECHOED
                 (SUBSEQ ,RAW-OUTPUT ,0
                         (IF
                          (OR (EOF-P (PEEK-CHAR ,NIL ,STREAM NIL *EOF*))
                              (TOKEN-DELIMITER-P
                               (ELT ,RAW-OUTPUT (1- ,LENGTH))))
                          ,LENGTH (1- ,LENGTH)))))
           (DECLARE (IGNORABLE ,VALUES ,ECHOED))
           ,@BODY)))))
(EVAL-WHEN (:COMPILE-TOPLEVEL :LOAD-TOPLEVEL :EXECUTE)
  (DEFVAR *EOF* (MAKE-SYMBOL "EOF")))
(DEFUN EOF-P (X) (EQ X *EOF*))
(DEFTYPE EOF () '(SATISFIES EOF-P))
(DEFCLASS MARKER NIL ((VALUE :READER MARKER-VALUE :INITARG :VALUE)))
(DEFUN MARKER-P (X) (TYPEP X 'MARKER))
(DEFGENERIC MARKER-BOUNDP (MARKER))
(DEFMETHOD MARKER-BOUNDP ((MARKER MARKER)) (SLOT-BOUNDP MARKER 'VALUE))
(DEFMETHOD PRINT-OBJECT ((OBJ MARKER) STREAM)
           (WHEN (MARKER-BOUNDP OBJ) (WRITE (MARKER-VALUE OBJ) :STREAM STREAM)))
(DEFVAR *EVALUATING* NIL)
(DEFCLASS NEWLINE-MARKER (MARKER)
          ((INDENTATION :ACCESSOR INDENTATION :INITARG :INDENTATION))
          (:DEFAULT-INITARGS :INDENTATION NIL))
(DEFUN NEWLINE-P (OBJ) (TYPEP OBJ 'NEWLINE-MARKER))
(SET-MACRO-CHARACTER #\Newline
                     (LAMBDA (STREAM CHAR)
                       (DECLARE (IGNORE STREAM CHAR))
                       (MAKE-INSTANCE 'NEWLINE-MARKER))
                     NIL (READTABLE-FOR-MODE :LISP))
(DEFCLASS EMPTY-LIST-MARKER (MARKER) NIL (:DEFAULT-INITARGS :VALUE 'NIL))
(DEFVAR *EMPTY-LIST* (MAKE-INSTANCE 'EMPTY-LIST-MARKER))
(DEFCLASS LIST-MARKER (MARKER)
          ((LENGTH :READER LIST-MARKER-LENGTH :INITARG :LENGTH)
           (LIST :READER LIST-MARKER-LIST :INITARG :LIST)
           (CHARPOS :READER LIST-MARKER-CHARPOS :INITARG :CHARPOS)))
(DEFUN LIST-MARKER-P (OBJ) (TYPEP OBJ 'LIST-MARKER))
(DEFCLASS CONSING-DOT-MARKER (MARKER) NIL)
(DEFVAR *CONSING-DOT* (MAKE-INSTANCE 'CONSING-DOT-MARKER))
(DEFMETHOD MARKER-BOUNDP ((MARKER LIST-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER LIST-MARKER))
           (DO* ((LIST (LIST NIL))
                 (TAIL LIST)
                 (MARKER-LIST (LIST-MARKER-LIST MARKER) (CDR MARKER-LIST))
                 (X (CAR MARKER-LIST) (CAR MARKER-LIST)))
                ((ENDP MARKER-LIST) (CDR LIST))
             (COND
              ((EQ X *CONSING-DOT*)
               (RPLACD TAIL
                       (DOLIST
                           (X MARKER-LIST (ERROR "Nothing after . in list"))
                         (COND
                          ((AND (MARKER-P X) (MARKER-BOUNDP X))
                           (RETURN (MARKER-VALUE X)))
                          ((NOT (MARKER-P X)) (RETURN X)))))
               (RETURN (CDR LIST)))
              ((MARKER-P X)
               (WHEN (MARKER-BOUNDP X)
                 (LET ((OBJ (LIST (MARKER-VALUE X))))
                   (RPLACD TAIL OBJ)
                   (SETQ TAIL OBJ))))
              (T
               (LET ((OBJ (LIST X)))
                 (RPLACD TAIL OBJ)
                 (SETQ TAIL OBJ))))))
(DEFUN MAKE-LIST-READER (NEXT)
  (LAMBDA (STREAM CHAR)
    (IF (CHAR= (PEEK-CHAR T STREAM T NIL T) #\))
        (PROGN (READ-CHAR STREAM T NIL T) *EMPTY-LIST*)
        (FUNCALL NEXT STREAM CHAR))))
(SET-MACRO-CHARACTER #\( (MAKE-LIST-READER (GET-MACRO-CHARACTER #\( NIL)) NIL
                     (READTABLE-FOR-MODE :INNER-LISP))
(DEFUN LIST-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (LOOP WITH LIST = 'NIL WITH CHARPOS-LIST = 'NIL FOR N FROM 0 FOR FIRST-CHAR =
        (PEEK-CHAR T STREAM T NIL T) AS CHARPOS = (STREAM-CHARPOS STREAM) UNTIL
        (CHAR= FIRST-CHAR #\)) DO
        (COND
         ((CHAR= FIRST-CHAR #\.)
          (WITH-REWIND-STREAM (REWIND STREAM) (READ-CHAR REWIND T)
                              (LET ((NEXT-CHAR (READ-CHAR REWIND T)))
                                (COND
                                 ((TOKEN-DELIMITER-P NEXT-CHAR)
                                  (UNLESS (OR LIST *READ-SUPPRESS*)
                                    (SIMPLE-READER-ERROR STREAM
                                                         "Nothing appears before . in list."))
                                  (PUSH *CONSING-DOT* LIST)
                                  (PUSH CHARPOS CHARPOS-LIST))
                                 (T (REWIND)
                                  (LET ((OBJ
                                         (MULTIPLE-VALUE-LIST
                                          (READ REWIND T NIL T))))
                                    (WHEN OBJ
                                      (PUSH (CAR OBJ) LIST)
                                      (PUSH CHARPOS CHARPOS-LIST))))))))
         (T
          (LET ((OBJ (MULTIPLE-VALUE-LIST (READ STREAM T NIL T))))
            (WHEN OBJ (PUSH (CAR OBJ) LIST) (PUSH CHARPOS CHARPOS-LIST)))))
        FINALLY (READ-CHAR STREAM T NIL T)
        (RETURN
         (MAKE-INSTANCE 'LIST-MARKER :LENGTH N :LIST (NREVERSE LIST) :CHARPOS
                        (NREVERSE CHARPOS-LIST)))))
(SET-MACRO-CHARACTER #\( (MAKE-LIST-READER #'LIST-READER) NIL
                     (READTABLE-FOR-MODE :LISP))
(DEFCLASS QUOTE-MARKER (MARKER)
          ((FORM :READER QUOTED-FORM :INITARG :FORM)
           (QUOTE :READER QUOTE-MARKER-QUOTE :INITARG :QUOTE)))
(DEFMETHOD MARKER-BOUNDP ((MARKER QUOTE-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER QUOTE-MARKER))
           (LIST (SLOT-VALUE MARKER 'QUOTE) (SLOT-VALUE MARKER 'FORM)))
(DEFMETHOD PRINT-OBJECT ((OBJ QUOTE-MARKER) STREAM)
           (FORMAT STREAM "(~W ~W)" (QUOTE-MARKER-QUOTE OBJ) (QUOTED-FORM OBJ)))
(DEFUN SINGLE-QUOTE-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (MAKE-INSTANCE 'QUOTE-MARKER :QUOTE 'QUOTE :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\' #'SINGLE-QUOTE-READER NIL (READTABLE-FOR-MODE MODE)))
(DEFCLASS COMMENT-MARKER (MARKER) ((TEXT :READER COMMENT-TEXT :INITARG :TEXT)))
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
(DEFCLASS BACKQUOTE-MARKER (MARKER) ((FORM :READER BACKQ-FORM :INITARG :FORM)))
(DEFMETHOD MARKER-BOUNDP ((MARKER BACKQUOTE-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER BACKQUOTE-MARKER))
           (LET ((*PRINT-PRETTY* NIL)
                 (*PRINT-READABLY* T)
                 (*READTABLE* (READTABLE-FOR-MODE NIL)))
             (READ-FROM-STRING (PRIN1-TO-STRING MARKER))))
(DEFMETHOD PRINT-OBJECT ((OBJ BACKQUOTE-MARKER) STREAM)
           (FORMAT STREAM "`~W" (BACKQ-FORM OBJ)))
(DEFUN BACKQUOTE-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (MAKE-INSTANCE 'BACKQUOTE-MARKER :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\` #'BACKQUOTE-READER NIL (READTABLE-FOR-MODE MODE)))
(DEFCLASS COMMA-MARKER (MARKER)
          ((FORM :READER COMMA-FORM :INITARG :FORM)
           (MODIFIER :READER COMMA-MODIFIER :INITARG :MODIFIER))
          (:DEFAULT-INITARGS :MODIFIER NIL))
(DEFMETHOD MARKER-BOUNDP ((MARKER COMMA-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER COMMA-MARKER)) MARKER)
(DEFMETHOD PRINT-OBJECT ((OBJ COMMA-MARKER) STREAM)
           (FORMAT STREAM ",~@[~C~]~W" (COMMA-MODIFIER OBJ) (COMMA-FORM OBJ)))
(DEFUN COMMA-READER (STREAM CHAR)
  (DECLARE (IGNORE CHAR))
  (CASE (PEEK-CHAR NIL STREAM T NIL T)
    ((#\@ #\.)
     (MAKE-INSTANCE 'COMMA-MARKER :MODIFIER (READ-CHAR STREAM) :FORM
                    (READ STREAM T NIL T)))
    (T (MAKE-INSTANCE 'COMMA-MARKER :FORM (READ STREAM T NIL T)))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-MACRO-CHARACTER #\, #'COMMA-READER NIL (READTABLE-FOR-MODE MODE)))
(DEFUN CALL-STANDARD-SHARPM-FUN (STREAM SUB-CHAR ARG)
  (FUNCALL (GET-DISPATCH-MACRO-CHARACTER #\# SUB-CHAR (READTABLE-FOR-MODE NIL))
           STREAM SUB-CHAR ARG))
(DEFINE-CONDITION SIMPLE-READER-ERROR (READER-ERROR SIMPLE-CONDITION) NIL
                  (:REPORT
                   (LAMBDA (CONDITION STREAM)
                     (FORMAT STREAM "~S on ~S:~%~?" CONDITION
                             (STREAM-ERROR-STREAM CONDITION)
                             (SIMPLE-CONDITION-FORMAT-CONTROL CONDITION)
                             (SIMPLE-CONDITION-FORMAT-ARGUMENTS CONDITION)))))
(DEFUN SIMPLE-READER-ERROR (STREAM CONTROL &REST ARGS)
  (ERROR 'SIMPLE-READER-ERROR :STREAM STREAM :FORMAT-CONTROL CONTROL
         :FORMAT-ARGUMENTS ARGS))
(DEFCLASS FUNCTION-MARKER (QUOTE-MARKER) NIL)
(DEFUN SHARPSIGN-QUOTE-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE SUB-CHAR ARG))
  (MAKE-INSTANCE 'FUNCTION-MARKER :QUOTE 'FUNCTION :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\' #'SHARPSIGN-QUOTE-READER
                                (READTABLE-FOR-MODE MODE)))
(DEFCLASS SIMPLE-VECTOR-MARKER (MARKER)
          ((LENGTH :INITARG :LENGTH) (ELEMENTS :INITARG :ELEMENTS)
           (ELEMENT-TYPE :INITARG :ELEMENT-TYPE))
          (:DEFAULT-INITARGS :ELEMENT-TYPE T))
(DEFMETHOD MARKER-BOUNDP ((MARKER SIMPLE-VECTOR-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER SIMPLE-VECTOR-MARKER))
           (WITH-SLOTS (ELEMENTS ELEMENT-TYPE) MARKER
                       (IF (SLOT-BOUNDP MARKER 'LENGTH)
                           (WITH-SLOTS (LENGTH) MARKER
                                       (LET ((SUPPLIED-LENGTH
                                              (LENGTH ELEMENTS)))
                                         (FILL
                                          (REPLACE
                                           (MAKE-ARRAY LENGTH :ELEMENT-TYPE
                                                       ELEMENT-TYPE)
                                           ELEMENTS)
                                          (ELT ELEMENTS (1- SUPPLIED-LENGTH))
                                          :START SUPPLIED-LENGTH)))
                           (COERCE ELEMENTS `(VECTOR ,ELEMENT-TYPE)))))
(DEFUN SIMPLE-VECTOR-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE SUB-CHAR))
  (LET* ((LIST (READ-DELIMITED-LIST #\) STREAM T))
         (LENGTH
          (HANDLER-CASE (LENGTH LIST)
                        (TYPE-ERROR (ERROR) (DECLARE (IGNORE ERROR))
                         (SIMPLE-READER-ERROR STREAM "improper list in #(): ~S"
                                              LIST)))))
    (UNLESS *READ-SUPPRESS*
      (IF ARG
          (IF (> LENGTH ARG)
              (SIMPLE-READER-ERROR STREAM
                                   "vector longer than specified length: #~S~S"
                                   ARG LIST)
              (MAKE-INSTANCE 'SIMPLE-VECTOR-MARKER :LENGTH ARG :ELEMENTS LIST))
          (MAKE-INSTANCE 'SIMPLE-VECTOR-MARKER :ELEMENTS LIST)))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\( #'SIMPLE-VECTOR-READER
                                (READTABLE-FOR-MODE MODE)))
(DEFCLASS BIT-VECTOR-MARKER (SIMPLE-VECTOR-MARKER) NIL
          (:DEFAULT-INITARGS :ELEMENT-TYPE 'BIT))
(DEFUN SIMPLE-BIT-VECTOR-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE SUB-CHAR))
  (LET ((*READTABLE* (READTABLE-FOR-MODE NIL)))
    (READ-WITH-ECHO (STREAM VALUES BITS :PREFIX (FORMAT NIL "#~@[~D~]*" ARG))
                    (APPLY #'MAKE-INSTANCE 'BIT-VECTOR-MARKER :ELEMENTS
                           (MAP 'BIT-VECTOR
                                (LAMBDA (C) (ECASE C (#\0 0) (#\1 1)))
                                (SUBSEQ BITS 0
                                        (LET ((N (LENGTH BITS)))
                                          (CASE (ELT BITS (1- N))
                                            ((#\0 #\1) N)
                                            (T (1- N))))))
                           (IF ARG (LIST :LENGTH ARG))))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\* #'SIMPLE-BIT-VECTOR-READER
                                (READTABLE-FOR-MODE MODE)))
(DEFCLASS READ-TIME-EVAL NIL
          ((FORM :READER READ-TIME-EVAL-FORM :INITARG :FORM)))
(DEFMETHOD PRINT-OBJECT ((OBJ READ-TIME-EVAL) STREAM)
           (FORMAT STREAM "#.~W" (READ-TIME-EVAL-FORM OBJ)))
(DEFCLASS READ-TIME-EVAL-MARKER (READ-TIME-EVAL MARKER) NIL)
(DEFMETHOD MARKER-BOUNDP ((MARKER READ-TIME-EVAL-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER READ-TIME-EVAL-MARKER))
           (IF *EVALUATING* (CALL-NEXT-METHOD)
               (MAKE-INSTANCE 'READ-TIME-EVAL :FORM
                              (READ-TIME-EVAL-FORM MARKER))))
(DEFUN SHARPSIGN-DOT-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE SUB-CHAR ARG))
  (LET ((FORM (READ STREAM T NIL T)))
    (UNLESS *READ-SUPPRESS*
      (UNLESS *READ-EVAL*
        (SIMPLE-READER-ERROR STREAM "can't read #. while *READ-EVAL* is NIL"))
      (MAKE-INSTANCE 'READ-TIME-EVAL-MARKER :FORM FORM :VALUE (EVAL FORM)))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\. #'SHARPSIGN-DOT-READER
                                (READTABLE-FOR-MODE MODE)))
(DEFCLASS RADIX-MARKER (MARKER)
          ((BASE :READER RADIX-MARKER-BASE :INITARG :BASE)))
(DEFVAR *RADIX-PREFIX-ALIST* '((#\B . 2) (#\O . 8) (#\X . 16) (#\R)))
(DEFUN RADIX-READER (STREAM SUB-CHAR ARG)
  (MAKE-INSTANCE 'RADIX-MARKER :BASE
                 (OR (CDR (ASSOC SUB-CHAR *RADIX-PREFIX-ALIST*)) ARG) :VALUE
                 (CALL-STANDARD-SHARPM-FUN STREAM SUB-CHAR ARG)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (DOLIST (SUB-CHAR '(#\B #\O #\X #\R))
    (SET-DISPATCH-MACRO-CHARACTER #\# SUB-CHAR #'RADIX-READER
                                  (READTABLE-FOR-MODE MODE))))
(DEFCLASS STRUCTURE-MARKER (MARKER)
          ((FORM :READER STRUCTURE-MARKER-FORM :INITARG :FORM)))
(DEFMETHOD MARKER-BOUNDP ((MARKER STRUCTURE-MARKER)) T)
(DEFMETHOD MARKER-VALUE ((MARKER STRUCTURE-MARKER))
           (WITH-STANDARD-IO-SYNTAX
            (READ-FROM-STRING (PRIN1-TO-STRING MARKER))))
(DEFMETHOD PRINT-OBJECT ((OBJ STRUCTURE-MARKER) STREAM)
           (FORMAT STREAM "#S~W" (STRUCTURE-MARKER-FORM OBJ)))
(DEFUN STRUCTURE-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE SUB-CHAR ARG))
  (MAKE-INSTANCE 'STRUCTURE-MARKER :FORM (READ STREAM T NIL T)))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\S #'STRUCTURE-READER
                                (READTABLE-FOR-MODE MODE)))
(DEFUN FEATUREP (X)
  (ETYPECASE X
    (CONS
     (CASE (CAR X)
       ((:NOT NOT)
        (COND
         ((CDDR X)
          (ERROR "too many subexpressions in feature expression: ~S" X))
         ((NULL (CDR X))
          (ERROR "too few subexpressions in feature expression: ~S" X))
         (T (NOT (FEATUREP (CADR X))))))
       ((:AND AND) (EVERY #'FEATUREP (CDR X)))
       ((:OR OR) (SOME #'FEATUREP (CDR X)))
       (T (ERROR "unknown operator in feature expression: ~S." X))))
    (SYMBOL (NOT (NULL (MEMBER X *FEATURES* :TEST #'EQ))))))
(DEFCLASS READ-TIME-CONDITIONAL NIL
          ((PLUSP :READER READ-TIME-CONDITIONAL-PLUSP :INITARG :PLUSP)
           (TEST :READER READ-TIME-CONDITIONAL-TEST :INITARG :TEST)
           (FORM :READER READ-TIME-CONDITIONAL-FORM :INITARG :FORM)))
(DEFMETHOD PRINT-OBJECT ((OBJ READ-TIME-CONDITIONAL) STREAM)
           (FORMAT STREAM "#~:[-~;+~]~S ~A" (READ-TIME-CONDITIONAL-PLUSP OBJ)
                   (READ-TIME-CONDITIONAL-TEST OBJ)
                   (READ-TIME-CONDITIONAL-FORM OBJ)))
(DEFCLASS READ-TIME-CONDITIONAL-MARKER (READ-TIME-CONDITIONAL MARKER) NIL)
(DEFMETHOD MARKER-BOUNDP ((MARKER READ-TIME-CONDITIONAL-MARKER))
           (IF *EVALUATING* (CALL-NEXT-METHOD) T))
(DEFMETHOD MARKER-VALUE ((MARKER READ-TIME-CONDITIONAL-MARKER))
           (IF *EVALUATING* (CALL-NEXT-METHOD)
               (MAKE-INSTANCE 'READ-TIME-CONDITIONAL :PLUSP
                              (READ-TIME-CONDITIONAL-PLUSP MARKER) :TEST
                              (READ-TIME-CONDITIONAL-TEST MARKER) :FORM
                              (READ-TIME-CONDITIONAL-FORM MARKER))))
(DEFUN READ-TIME-CONDITIONAL-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE ARG))
  (LET* ((PLUSP (ECASE SUB-CHAR (#\+ T) (#\- NIL)))
         (*READTABLE* (READTABLE-FOR-MODE NIL))
         (TEST
          (LET ((*PACKAGE* (FIND-PACKAGE "KEYWORD")) (*READ-SUPPRESS* NIL))
            (READ STREAM T NIL T)))
         (*READ-SUPPRESS* (IF PLUSP (NOT (FEATUREP TEST)) (FEATUREP TEST))))
    (READ-WITH-ECHO (STREAM VALUES FORM)
                    (APPLY #'MAKE-INSTANCE 'READ-TIME-CONDITIONAL-MARKER :PLUSP
                           PLUSP :TEST TEST :FORM FORM
                           (AND (NOT *READ-SUPPRESS*) VALUES
                                (LIST :VALUE (CAR VALUES)))))))
(DOLIST (MODE '(:LISP :INNER-LISP))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\+ #'READ-TIME-CONDITIONAL-READER
                                (READTABLE-FOR-MODE MODE))
  (SET-DISPATCH-MACRO-CHARACTER #\# #\- #'READ-TIME-CONDITIONAL-READER
                                (READTABLE-FOR-MODE MODE)))
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
          ((NAME :READER SECTION-NAME :INITARG :NAME)
           (EVALP :READER EVALUATED-CODE-P :INITARG :EVALP))
          (:DEFAULT-INITARGS :NAME NIL :EVALP NIL))
(DEFUN START-CODE-READER (STREAM SUB-CHAR ARG)
  (DECLARE (IGNORE STREAM ARG))
  (MAKE-INSTANCE 'START-CODE-MARKER :EVALP
                 (ECASE (CHAR-DOWNCASE SUB-CHAR) ((#\l #\p) NIL) ((#\e) T))))
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
(DEFUN READ-SECTIONS (INPUT-STREAM APPEND-P)
  (WITH-CHARPOS-INPUT-STREAM (STREAM INPUT-STREAM)
                             (FLET ((FINISH-SECTION (SECTION COMMENTARY CODE)
                                      (WHEN (STRINGP (CAR COMMENTARY))
                                        (RPLACA COMMENTARY
                                                (STRING-RIGHT-TRIM *WHITESPACE*
                                                                   (CAR
                                                                    COMMENTARY))))
                                      (SETQ COMMENTARY (NREVERSE COMMENTARY))
                                      (WHEN (STRINGP (CAR COMMENTARY))
                                        (RPLACA COMMENTARY
                                                (STRING-LEFT-TRIM *WHITESPACE*
                                                                  (CAR
                                                                   COMMENTARY))))
                                      (SETQ CODE
                                              (NREVERSE
                                               (IF (NEWLINE-P (CAR CODE))
                                                   (CDR CODE) CODE)))
                                      (SETF (SECTION-COMMENTARY SECTION)
                                              COMMENTARY)
                                      (SETF (SECTION-CODE SECTION) CODE)
                                      (WHEN (SECTION-NAME SECTION)
                                        (LET ((NAMED-SECTION
                                               (FIND-SECTION
                                                (SECTION-NAME SECTION)))
                                              (NUMBER (SECTION-NUMBER SECTION))
                                              (CODE (SECTION-CODE SECTION)))
                                          (SET-NAMED-SECTION-CODE NAMED-SECTION
                                                                  CODE
                                                                  APPEND-P)
                                          (WHEN
                                              (OR
                                               (NOT
                                                (SLOT-BOUNDP NAMED-SECTION
                                                             'NUMBER))
                                               (NOT APPEND-P))
                                            (SETF (SECTION-NUMBER
                                                   NAMED-SECTION)
                                                    NUMBER))
                                          (IF APPEND-P
                                              (PUSHNEW SECTION
                                                       (SEE-ALSO
                                                        NAMED-SECTION))
                                              (SETF (SEE-ALSO NAMED-SECTION)
                                                      (LIST SECTION)))))
                                      SECTION))
                               (PROG (FORM COMMENTARY CODE SECTION SECTIONS)
                                LIMBO
                                 (SETQ SECTION (MAKE-INSTANCE 'LIMBO-SECTION))
                                 (WITH-MODE :LIMBO
                                            (LOOP
                                             (MAYBE-PUSH
                                              (SNARF-UNTIL-CONTROL-CHAR STREAM
                                                                        #\@)
                                              COMMENTARY)
                                             (SETQ FORM
                                                     (READ-PRESERVING-WHITESPACE
                                                      STREAM NIL *EOF* NIL))
                                             (TYPECASE FORM
                                               (EOF (GO EOF))
                                               (SECTION (GO COMMENTARY))
                                               (T (PUSH FORM COMMENTARY)))))
                                COMMENTARY
                                 (PUSH (FINISH-SECTION SECTION COMMENTARY CODE)
                                       SECTIONS)
                                 (CHECK-TYPE FORM SECTION)
                                 (SETQ SECTION FORM COMMENTARY 'NIL CODE 'NIL)
                                 (WITH-MODE :TEX
                                            (LOOP
                                             (MAYBE-PUSH
                                              (SNARF-UNTIL-CONTROL-CHAR STREAM
                                                                        '(#\@
                                                                          #\|))
                                              COMMENTARY)
                                             (SETQ FORM
                                                     (READ-PRESERVING-WHITESPACE
                                                      STREAM NIL *EOF* NIL))
                                             (TYPECASE FORM
                                               (EOF (GO EOF))
                                               (SECTION (GO COMMENTARY))
                                               (START-CODE-MARKER
                                                (SETF (SECTION-NAME SECTION)
                                                        (SECTION-NAME FORM))
                                                (GO LISP))
                                               (T (PUSH FORM COMMENTARY)))))
                                LISP
                                 (CHECK-TYPE FORM START-CODE-MARKER)
                                 (WITH-MODE :LISP
                                            (LET ((EVALP
                                                   (EVALUATED-CODE-P FORM)))
                                              (LOOP
                                               (SETQ FORM
                                                       (READ-PRESERVING-WHITESPACE
                                                        STREAM NIL *EOF* NIL))
                                               (TYPECASE FORM
                                                 (EOF (GO EOF))
                                                 (SECTION (GO COMMENTARY))
                                                 (START-CODE-MARKER
                                                  (ERROR
                                                   "Can't start a section with a code part"))
                                                 (NEWLINE-MARKER
                                                  (UNLESS
                                                      (OR (NULL CODE)
                                                          (NEWLINE-P
                                                           (CAR CODE)))
                                                    (PUSH FORM CODE)))
                                                 (T
                                                  (WHEN EVALP
                                                    (EVAL (TANGLE FORM)))
                                                  (PUSH FORM CODE))))))
                                EOF
                                 (PUSH (FINISH-SECTION SECTION COMMENTARY CODE)
                                       SECTIONS)
                                 (RETURN (NREVERSE SECTIONS))))))
(DEFUN TANGLE-1 (FORM)
  (COND ((LIST-MARKER-P FORM) (VALUES (MARKER-VALUE FORM) T))
        ((ATOM FORM) (VALUES FORM NIL))
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
(DEFUN LOAD-WEB-FROM-STREAM (STREAM PRINT &OPTIONAL (APPEND-P T))
  (LET (#+:SBCL (sb-ext:*evaluator-mode* :compile)

        (*READTABLE* *READTABLE*)
        (*PACKAGE* *PACKAGE*)
        (*EVALUATING* T))
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
  (WHEN VERBOSE (FORMAT T "~&; loading WEB from ~S~%" FILESPEC))
  (IF (STREAMP FILESPEC) (LOAD-WEB-FROM-STREAM FILESPEC PRINT)
      (WITH-OPEN-FILE
          (STREAM FILESPEC :DIRECTION :INPUT :EXTERNAL-FORMAT EXTERNAL-FORMAT
           :IF-DOES-NOT-EXIST (IF IF-DOES-NOT-EXIST :ERROR NIL))
        (LOAD-WEB-FROM-STREAM STREAM PRINT))))
(DEFUN LOAD-SECTIONS-FROM-TEMP-FILE
       (FILE APPEND-P &AUX (TRUENAME (PROBE-FILE FILE)))
  (WHEN TRUENAME
    (UNWIND-PROTECT
        (WITH-OPEN-FILE (STREAM TRUENAME :DIRECTION :INPUT)
          (LOAD-WEB-FROM-STREAM STREAM T APPEND-P))
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
      (FORMAT LISP ";;;; TANGLED OUTPUT FROM WEB ~S. DO NOT EDIT." INPUT-FILE)
      (LET ((*EVALUATING* NIL))
        (DOLIST (FORM (TANGLE (READ-CODE-PARTS INPUT T)))
          (PPRINT FORM LISP)))))
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
(DEFUN WEAVE-SECTIONS (SECTIONS OUTPUT-FILE)
  (WITH-OPEN-FILE (OUTPUT OUTPUT-FILE :DIRECTION :OUTPUT :IF-EXISTS :SUPERSEDE)
    (FORMAT OUTPUT "\\input clwebmac~%")
    (LOOP WITH *PRINT-CASE* = :DOWNCASE WITH *PRINT-ESCAPE* = NIL WITH
          *PRINT-PRETTY* = T WITH *PRINT-PPRINT-DISPATCH* =
          *WEAVE-PPRINT-DISPATCH* WITH *PRINT-RIGHT-MARGIN* = 1000 FOR SECTION
          ACROSS SECTIONS DO (WRITE SECTION :STREAM OUTPUT) FINALLY
          (FORMAT OUTPUT "~&\\bye~%"))))
(DEFVAR *INNER-LISP* NIL)
(DEFUN PRINT-TEX (STREAM TEX-MODE-MATERIAL)
  (DOLIST (X TEX-MODE-MATERIAL)
    (ETYPECASE X
      (STRING (WRITE-STRING X STREAM))
      (LIST
       (LET ((*INNER-LISP* T))
         (DOLIST (FORM X) (FORMAT STREAM "{\\IB/~W}" FORM)))))))
(DEFUN READ-TEX-FROM-STRING (INPUT-STRING)
  (WITH-INPUT-FROM-STRING (INPUT-STREAM INPUT-STRING)
    (WITH-CHARPOS-INPUT-STREAM (STREAM INPUT-STREAM)
                               (WITH-MODE :RESTRICTED
                                          (LOOP FOR TEXT =
                                                (SNARF-UNTIL-CONTROL-CHAR
                                                 STREAM #\|)
                                                FOR FORMS =
                                                (READ-PRESERVING-WHITESPACE
                                                 STREAM NIL *EOF* NIL)
                                                COLLECT TEXT UNTIL
                                                (EOF-P FORMS) COLLECT FORMS)))))
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
    (FRESH-LINE STREAM)
    (COND ((AND COMMENTARY CODE) (FORMAT STREAM "\\Y\\B~%"))
          (CODE (FORMAT STREAM "\\B~%")))
    (WHEN NAMED-SECTION
      (PRINT-SECTION-NAME STREAM NAMED-SECTION)
      (FORMAT STREAM "${}~:[\\mathrel+~;~]\\E{}$~%"
              (= (SECTION-NUMBER SECTION) (SECTION-NUMBER NAMED-SECTION))))
    (WHEN CODE
      (DOLIST (FORM CODE)
        (IF (LIST-MARKER-P FORM) (FORMAT STREAM "~@<\\+~@;~W~;\\cr~:>" FORM)
            (FORMAT STREAM "~W" FORM)))
      (FORMAT STREAM "~&\\egroup~%"))
    (WHEN NAMED-SECTION
      (PRINT-XREFS STREAM #\A (REMOVE SECTION (SEE-ALSO NAMED-SECTION)))
      (PRINT-XREFS STREAM #\U (REMOVE SECTION (USED-BY NAMED-SECTION)))))
  (FORMAT STREAM "\\fi~%"))
(SET-WEAVE-DISPATCH 'SECTION #'PRINT-SECTION)
(DEFUN PRINT-XREFS (STREAM KIND XREFS)
  (WHEN XREFS
    (FORMAT STREAM
            "\\~C~{~#[~;~D~;s ~D\\ET~D~:;s~@{~#[~;\\ETs~D~;~D~:;~D, ~]~}~]~}.~%"
            KIND (SORT (MAPCAR #'SECTION-NUMBER XREFS) #'<))))
(DEFUN PRINT-SECTION-NAME (STREAM NAMED-SECTION)
  (FORMAT STREAM "\\X~D:" (SECTION-NUMBER NAMED-SECTION))
  (PRINT-TEX STREAM (READ-TEX-FROM-STRING (SECTION-NAME NAMED-SECTION)))
  (WRITE-STRING "\\X" STREAM))
(SET-WEAVE-DISPATCH 'NAMED-SECTION #'PRINT-SECTION-NAME)
(DEFUN WRITE-ESCAPED-STRING (STREAM STRING ESCAPE-CHARS)
  (DOTIMES (I (LENGTH STRING))
    (LET* ((CHAR (CHAR STRING I))
           (ESCAPE (CDR (ASSOC CHAR ESCAPE-CHARS :TEST #'FIND))))
      (ETYPECASE ESCAPE
        (CHARACTER (WRITE-CHAR ESCAPE STREAM) (WRITE-CHAR CHAR STREAM))
        (STRING (WRITE-STRING ESCAPE STREAM))
        (NULL (WRITE-CHAR CHAR STREAM))))))
(DEFPARAMETER *TEX-ESCAPE-ALIST*
  '((" \\%&#$^_~<>" . #\\) ("{" . "$\\{$") ("}" . "$\\}$")))
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
    (WRITE-STRING "\\#\\CH{" STREAM)
    (WRITE-ESCAPED-STRING STREAM
                          (IF (AND NAME (NOT GRAPHICP)) NAME
                              (MAKE-STRING 1 :INITIAL-ELEMENT CHAR))
                          (LIST* '("{}" . #\\) *TEX-ESCAPE-ALIST*))
    (WRITE-STRING "}" STREAM)
    CHAR))
(SET-WEAVE-DISPATCH 'CHARACTER #'PRINT-CHAR)
(DEFVAR *HIGHLIGHT-SPECIAL-SYMBOLS* NIL)
(DEFUN DEF-P (SYMBOL)
  (WHEN (FBOUNDP SYMBOL)
    (LET* ((NAME (SYMBOL-NAME SYMBOL)) (LEN (LENGTH NAME)))
      (AND (> LEN 3) (STRING= NAME "DEF" :END1 3)))))
(DEFUN HIGHLIGHT-SYMBOL-P (SYMBOL)
  (COND
   ((OR (SPECIAL-OPERATOR-P SYMBOL) (MEMBER SYMBOL '(COND LOOP)))
    (MEMBER :SPECIAL-OPERATOR *HIGHLIGHT-SPECIAL-SYMBOLS*))
   ((MEMBER SYMBOL LAMBDA-LIST-KEYWORDS)
    (MEMBER :LAMBDA-LIST-KEYWORD *HIGHLIGHT-SPECIAL-SYMBOLS*))
   ((DEF-P SYMBOL) (MEMBER :DEF *HIGHLIGHT-SPECIAL-SYMBOLS*))))
(DEFUN PRINT-SYMBOL (STREAM SYMBOL)
  (LET ((GROUP-P
         (COND ((HIGHLIGHT-SYMBOL-P SYMBOL) (WRITE-STRING "\\&{" STREAM))
               ((KEYWORDP SYMBOL) (WRITE-STRING "\\:{" STREAM)))))
    (WRITE-ESCAPED-STRING STREAM
                          (WRITE-TO-STRING SYMBOL :ESCAPE NIL :PRETTY NIL)
                          *TEX-ESCAPE-ALIST*)
    (WHEN GROUP-P (WRITE-STRING "}" STREAM))))
(SET-WEAVE-DISPATCH 'SYMBOL #'PRINT-SYMBOL)
(DEFSTRUCT (LOGICAL-BLOCK (:CONSTRUCTOR MAKE-LOGICAL-BLOCK (LIST))) LIST)
(DEFUN ANALYZE-INDENTATION (LIST-MARKER)
  (DECLARE (TYPE LIST-MARKER LIST-MARKER))
  (LABELS ((FIND-NEXT-NEWLINE (LIST)
             (MEMBER-IF #'NEWLINE-P LIST :KEY #'CAR))
           (NEXT-LOGICAL-BLOCK (LIST)
             (DO* ((BLOCK 'NIL)
                   (BLOCK-INDENT (CDAR LIST))
                   (INDENT BLOCK-INDENT)
                   (NEWLINE (FIND-NEXT-NEWLINE LIST))
                   (NEXT-INDENT (CDADR NEWLINE)))
                  ((OR (ENDP LIST)
                       (AND (EQ LIST NEWLINE) NEXT-INDENT
                            (< NEXT-INDENT BLOCK-INDENT)))
                   (VALUES
                    (IF (NOTANY #'NEWLINE-P BLOCK) (NREVERSE BLOCK)
                        (MAKE-LOGICAL-BLOCK (NREVERSE BLOCK)))
                    LIST))
               (IF
                (AND INDENT NEXT-INDENT (> NEXT-INDENT INDENT)
                     (= NEXT-INDENT (CDAR LIST)))
                (MULTIPLE-VALUE-BIND
                    (SUB-BLOCK TAIL)
                    (NEXT-LOGICAL-BLOCK LIST)
                  (CHECK-TYPE (CAAR TAIL) (OR NEWLINE-MARKER NULL))
                  (PUSH SUB-BLOCK BLOCK)
                  (SETQ LIST TAIL))
                (LET ((NEXT (CAR (POP LIST))))
                  (PUSH NEXT BLOCK)
                  (WHEN (AND LIST (NEWLINE-P NEXT))
                    (SETF INDENT
                            (CDAR LIST)
                          (INDENTATION NEXT)
                            (- INDENT BLOCK-INDENT)
                          NEWLINE
                            (FIND-NEXT-NEWLINE LIST)
                          NEXT-INDENT
                            (CDADR NEWLINE))))))))
    (ASSERT
     (= (LENGTH (LIST-MARKER-LIST LIST-MARKER))
        (LENGTH (LIST-MARKER-CHARPOS LIST-MARKER))))
    (NEXT-LOGICAL-BLOCK
     (MAPCAR #'CONS (LIST-MARKER-LIST LIST-MARKER)
             (LIST-MARKER-CHARPOS LIST-MARKER)))))
(DEFUN PRINT-LIST (STREAM LIST-MARKER)
  (LET ((BLOCK (ANALYZE-INDENTATION LIST-MARKER)))
    (ETYPECASE BLOCK
      (LIST (FORMAT STREAM "~<(~;~@{~W~^ ~}~;)~:>" BLOCK))
      (LOGICAL-BLOCK (FORMAT STREAM "(~W)" BLOCK)))))
(SET-WEAVE-DISPATCH 'LIST-MARKER #'PRINT-LIST)
(DEFUN PRINT-LOGICAL-BLOCK (STREAM BLOCK)
  (WRITE-STRING "\\!" STREAM)
  (PPRINT-LOGICAL-BLOCK
      (STREAM (LOGICAL-BLOCK-LIST BLOCK) :PER-LINE-PREFIX "&")
    (DO (INDENT
         NEXT
         (OBJ (PPRINT-POP) NEXT))
        (NIL)
      (COND
       ((NEWLINE-P OBJ) (FORMAT STREAM "\\cr~:@_")
        (SETQ INDENT (INDENTATION OBJ)) (PPRINT-EXIT-IF-LIST-EXHAUSTED)
        (SETQ NEXT (PPRINT-POP)))
       (T (FORMAT STREAM "~@[~[~;\\1~;\\1~:;\\2~]~]~W" INDENT OBJ)
        (SETQ INDENT NIL) (PPRINT-EXIT-IF-LIST-EXHAUSTED)
        (SETQ NEXT (PPRINT-POP))
        (UNLESS (NEWLINE-P NEXT) (WRITE-CHAR #\  STREAM)))))))
(SET-WEAVE-DISPATCH 'LOGICAL-BLOCK #'PRINT-LOGICAL-BLOCK)
(SET-WEAVE-DISPATCH 'NEWLINE-MARKER
                    (LAMBDA (STREAM OBJ)
                      (DECLARE (IGNORE OBJ))
                      (TERPRI STREAM)))
(SET-WEAVE-DISPATCH 'EMPTY-LIST-MARKER
                    (LAMBDA (STREAM OBJ)
                      (DECLARE (IGNORE OBJ))
                      (WRITE-STRING "()" STREAM)))
(SET-WEAVE-DISPATCH 'CONSING-DOT-MARKER
                    (LAMBDA (STREAM OBJ)
                      (DECLARE (IGNORE OBJ))
                      (WRITE-CHAR #\. STREAM)))
(SET-WEAVE-DISPATCH 'QUOTE-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\'~W" (QUOTED-FORM OBJ))))
(SET-WEAVE-DISPATCH 'COMMENT-MARKER
                    (LAMBDA (STREAM OBJ)
                      (WRITE-STRING "\\C{" STREAM)
                      (PRINT-TEX STREAM
                                 (READ-TEX-FROM-STRING (COMMENT-TEXT OBJ)))
                      (WRITE-STRING "}" STREAM)))
(SET-WEAVE-DISPATCH 'BACKQUOTE-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\`~W" (BACKQ-FORM OBJ))))
(SET-WEAVE-DISPATCH 'COMMA-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\CO{~@[~C~]}~W" (COMMA-MODIFIER OBJ)
                              (COMMA-FORM OBJ))))
(SET-WEAVE-DISPATCH 'FUNCTION-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#\\'~S" (QUOTED-FORM OBJ)))
                    1)
(SET-WEAVE-DISPATCH 'SIMPLE-VECTOR-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#~@[~D~]~S"
                              (AND (SLOT-BOUNDP OBJ 'LENGTH)
                                   (SLOT-VALUE OBJ 'LENGTH))
                              (SLOT-VALUE OBJ 'ELEMENTS))))
(SET-WEAVE-DISPATCH 'BIT-VECTOR-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#~@[~D~]*~{~[0~;1~]~}"
                              (AND (SLOT-BOUNDP OBJ 'LENGTH)
                                   (SLOT-VALUE OBJ 'LENGTH))
                              (MAP 'LIST #'IDENTITY
                                   (SLOT-VALUE OBJ 'ELEMENTS))))
                    1)
(SET-WEAVE-DISPATCH 'READ-TIME-EVAL-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#.~W" (READ-TIME-EVAL-FORM OBJ))))
(SET-WEAVE-DISPATCH 'RADIX-MARKER
                    (LAMBDA (STREAM OBJ)
                      (LET ((*PRINT-RADIX* NIL)
                            (*PRINT-BASE* (RADIX-MARKER-BASE OBJ)))
                        (PRINC (MARKER-VALUE OBJ) STREAM)
                        (FORMAT STREAM "_{~D}" *PRINT-BASE*))))
(SET-WEAVE-DISPATCH 'STRUCTURE-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#S~W" (STRUCTURE-MARKER-FORM OBJ))))
(SET-WEAVE-DISPATCH 'READ-TIME-CONDITIONAL-MARKER
                    (LAMBDA (STREAM OBJ)
                      (FORMAT STREAM "\\#~:[--~;+~]~S ~A"
                              (READ-TIME-CONDITIONAL-PLUSP OBJ)
                              (READ-TIME-CONDITIONAL-TEST OBJ)
                              (READ-TIME-CONDITIONAL-FORM OBJ))))
;;;; TANGLED OUTPUT FROM WEB "clweb.lw".  DO NOT EDIT.
(DEFPACKAGE "COMMON-LISP-WEB" (:NICKNAMES "CLWEB") (:USE "COMMON-LISP")
            (:EXPORT "TANGLE-FILE" "LOAD-WEB" "WEAVE"))
(IN-PACKAGE "CLWEB")
(DEFPARAMETER *SECTION-NUMBER* 0)
(DEFCLASS SECTION NIL
          ((NUMBER :READER SECTION-NUMBER :INITARG :NUMBER :INITFORM
            (INCF *SECTION-NUMBER*))
           (COMMENTARY :ACCESSOR SECTION-COMMENTARY :INITARG :COMMENTARY
            :INITFORM "")
           (NAME :ACCESSOR SECTION-NAME :INITARG :NAME :INITFORM NIL)
           (CODE :ACCESSOR SECTION-CODE :INITARG :CODE :INITFORM 'NIL)
           (USED-BY :ACCESSOR USED-BY :INITARG :USED-BY :INITFORM 'NIL)))
(DEFCLASS STARRED-SECTION (SECTION) NIL)
(DEFUN UNNAMED-SECTION-CODE (STREAM)
  (LOOP FOR SECTION IN (READ-SECTIONS STREAM) IF (SECTION-NAME SECTION) DO
        (DEFINE-SECTION (SECTION-NAME SECTION) (SECTION-CODE SECTION)) ELSE
        APPEND (SECTION-CODE SECTION)))
(DEFUN TANGLE (FORMS) FORMS)
(DEFUN LOAD-WEB-FROM-STREAM (STREAM VERBOSE PRINT)
  (WHEN VERBOSE (FORMAT T "~&; loading WEB from ~S~%" (PATHNAME STREAM)))
  (LET ((*READTABLE* *READTABLE*) (*PACKAGE* *PACKAGE*))
    (DOLIST (FORM (TANGLE (UNNAMED-SECTION-CODE STREAM)))
      (IF PRINT
          (LET ((RESULTS (MULTIPLE-VALUE-LIST (EVAL FORM))))
            (FORMAT T "~&; ~{~S~^, ~}~%" RESULTS))
          (EVAL FORM)))))
(DEFUN LOAD-WEB
       (FILESPEC
        &KEY (VERBOSE *LOAD-VERBOSE*) (PRINT *LOAD-PRINT*)
        (IF-DOES-NOT-EXIST T) (EXTERNAL-FORMAT :DEFAULT))
  (IF (STREAMP FILESPEC) (LOAD-WEB-FROM-STREAM FILESPEC VERBOSE PRINT)
      (WITH-OPEN-FILE
          (STREAM FILESPEC :DIRECTION :INPUT :EXTERNAL-FORMAT EXTERNAL-FORMAT
           :IF-DOES-NOT-EXIST (IF IF-DOES-NOT-EXIST :ERROR NIL))
        (LOAD-WEB-FROM-STREAM STREAM VERBOSE PRINT))))
(DEFUN TANGLE-FILE
       (INPUT-FILE
        &REST ARGS
        &KEY OUTPUT-FILE (VERBOSE *COMPILE-VERBOSE*) (PRINT *COMPILE-PRINT*)
        (EXTERNAL-FORMAT :DEFAULT) &ALLOW-OTHER-KEYS
        &AUX
        (LISP-FILE (MERGE-PATHNAMES (MAKE-PATHNAME :TYPE "lisp") INPUT-FILE)))
  (WHEN VERBOSE (FORMAT T "~&; tangling WEB from ~S~%" INPUT-FILE))
  (WITH-OPEN-FILE
      (INPUT INPUT-FILE :DIRECTION :INPUT :EXTERNAL-FORMAT EXTERNAL-FORMAT)
    (WITH-OPEN-FILE
        (LISP LISP-FILE :DIRECTION :OUTPUT :IF-EXISTS :SUPERSEDE
         :EXTERNAL-FORMAT EXTERNAL-FORMAT)
      (FORMAT LISP ";;;; TANGLED OUTPUT FROM WEB ~S.  DO NOT EDIT." INPUT-FILE)
      (DOLIST (FORM (TANGLE (UNNAMED-SECTION-CODE INPUT)))
        (PPRINT FORM LISP))))
  (APPLY #'COMPILE-FILE LISP-FILE ARGS))
(DEFPARAMETER *MODES* '(:LIMBO :TEX :LISP :INNER-LISP :RESTRICTED))
(DEFTYPE MODE () `(MEMBER ,@*MODES*))
(DEFVAR *READTABLES*
  (LOOP FOR MODE IN *MODES* COLLECT (CONS MODE (COPY-READTABLE NIL))))
(DEFUN READTABLE-FOR-MODE (MODE)
  (DECLARE (TYPE MODE MODE))
  (CDR (ASSOC MODE *READTABLES*)))
(DEFMACRO WITH-MODE (MODE &BODY BODY)
  `(LET ((*READTABLE* (READTABLE-FOR-MODE ,MODE)))
     ,@BODY))
(DEFVAR *EOF* (MAKE-SYMBOL "EOF"))
(DEFUN EOF-P (CHAR) (EQ CHAR *EOF*))
(DEFUN SNARF-UNTIL-CONTROL-CHAR (STREAM)
  (WITH-OUTPUT-TO-STRING (STRING)
    (LOOP FOR CHAR = (PEEK-CHAR NIL STREAM NIL *EOF* NIL) UNTIL
          (OR (EOF-P CHAR) (MEMBER CHAR '(#\@ #\|))) DO
          (WRITE-CHAR (READ-CHAR STREAM) STRING))))
(SET-MACRO-CHARACTER #\|
                     (LAMBDA (STREAM CHAR)
                       (WITH-MODE :INNER-LISP
                                  (CONS 'QUOTE
                                        (READ-DELIMITED-LIST CHAR STREAM T))))
                     NIL (READTABLE-FOR-MODE :TEX))
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
                    (DECLARE (IGNORE STREAM ARG))
                    (STRING SUB-CHAR)))
(DEFUN START-SECTION-READER (SECTION-CLASS)
  (LAMBDA (STREAM SUB-CHAR ARG)
    (DECLARE (IGNORE STREAM SUB-CHAR ARG))
    (MAKE-INSTANCE SECTION-CLASS)))
(SET-CONTROL-CODE #\  (START-SECTION-READER 'SECTION) '(:LIMBO :TEX :LISP))
(SET-CONTROL-CODE #\* (START-SECTION-READER 'STARRED-SECTION)
                  '(:LIMBO :TEX :LISP))
(DEFSTRUCT (START-CODE (:CONSTRUCTOR MAKE-START-CODE (EVALP &OPTIONAL NAME)))
  EVALP
  NAME)
(DEFUN START-CODE-READER (EVALP)
  (LAMBDA (STREAM SUB-CHAR ARG)
    (DECLARE (IGNORE STREAM SUB-CHAR ARG))
    (MAKE-START-CODE EVALP)))
(SET-CONTROL-CODE #\l (START-CODE-READER NIL) '(:TEX))
(SET-CONTROL-CODE #\p (START-CODE-READER NIL) '(:TEX))
(SET-CONTROL-CODE #\e (START-CODE-READER T) '(:TEX))
(DEFUN READ-SECTIONS (STREAM)
  (FLET ((FINISH-SECTION (SECTION COMMENTARY CODE)
           (SETF (SECTION-COMMENTARY SECTION) (NREVERSE COMMENTARY))
           (SETF (SECTION-CODE SECTION) (NREVERSE CODE))
           SECTION))
    (PROG (FORM COMMENTARY CODE SECTION SECTIONS)
     COMMENTARY
      (WHEN SECTION (PUSH (FINISH-SECTION SECTION COMMENTARY CODE) SECTIONS))
      (SETQ SECTION
              (IF (TYPEP FORM 'SECTION) FORM (MAKE-INSTANCE 'SECTION))
            COMMENTARY
              'NIL
            CODE
              'NIL)
      (WITH-MODE :TEX
                 (LOOP
                  (LET ((TEXT (SNARF-UNTIL-CONTROL-CHAR STREAM)))
                    (WHEN (PLUSP (LENGTH TEXT)) (PUSH TEXT COMMENTARY)))
                  (SETQ FORM (READ STREAM NIL *EOF* NIL))
                  (COND ((EOF-P FORM) (GO EOF))
                        ((TYPEP FORM 'SECTION) (GO COMMENTARY))
                        ((START-CODE-P FORM) (GO LISP))
                        (T (PUSH FORM COMMENTARY)))))
     LISP
      (WHEN (START-CODE-NAME FORM) (SETF (SECTION-NAME SECTION) (CADR FORM)))
      (WITH-MODE :LISP
                 (LET ((EVALP (START-CODE-EVALP FORM)))
                   (LOOP (SETQ FORM (READ STREAM NIL *EOF* NIL))
                         (COND ((EOF-P FORM) (GO EOF))
                               ((TYPEP FORM 'SECTION) (GO COMMENTARY))
                               ((START-CODE-P FORM)
                                (ERROR
                                 "Can't start a section with a code part"))
                               (T (WHEN EVALP (EVAL FORM))
                                (PUSH FORM CODE))))))
     EOF
      (PUSH (FINISH-SECTION SECTION COMMENTARY CODE) SECTIONS)
      (RETURN (NREVERSE SECTIONS)))))
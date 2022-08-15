(defpackage :dot
  (:use :cl)
  (:export "DOT"
           "ACCESS"
           "ACCESS-SET"))

(in-package :dot)

;;; Utils

(defun walk-tree-elements (fn tree)
  (labels ((walk (tr)
             (typecase tr
               (cons
                (walk (car tr))
                (walk (cdr tr)))
               (t (funcall fn tr)))))
    (walk tree)))

(defun map-tree (fn tree)
  (labels ((walk (tr)
             (typecase tr
               (cons
                (cons (walk (car tr))
                      (walk (cdr tr))))
               (t (funcall fn tr)))))
    (walk tree)))

(defun tree-contains-p (predicate tree)
  (walk-tree-elements
   (lambda (e)
     (when (funcall predicate e)
       (return-from tree-contains-p t)))
   tree))

(defun symbol-with-name-p (symbol name)
  (and (symbolp symbol)
       (string= (symbol-name symbol) name)))

;;; Access

(defgeneric access (object property))
(defgeneric access-set (object property new))
(defsetf access %set-access)
(defmacro %set-access (object property new)
  `(progn
     (setf ,object (access-set ,object ,property ,new))
     ,new))

(defmethod access ((object standard-object) property)
  (slot-value object property))

;; Choose between alist and plist.
(defmethod access ((object list) property)
  (if (consp (car object))
      (alexandria:assoc-value object property)
      (getf object property)))

(defmethod access ((object hash-table) property)
  (gethash property object))

(defmethod access ((object vector) property)
  (aref object property))

(defmethod access-set ((object standard-object) property new)
  (setf (slot-value object property) new)
  object)

(defmethod access-set ((object list) property new)
  (if (consp (car object))
      (let ((old (assoc property object)))
        (if old
            (progn
              (setf (cdr old) new)
              object)
            (cons (cons property new) object)))
      (progn
        (setf (getf object property) new)
        object)))

(defmethod access-set ((object hash-table) property new)
  (setf (gethash property object) new)
  object)

(defmethod access-set ((object vector) property new)
  (setf (aref object property) new)
  object)

;;; Dot

(defmacro dot (object operation &rest rest)
  "Applies OPERATION to OBJECT such that OBJECT becomes the first
argument to OPERATION, followed by arguments specified by
OPERATION. If REST contains more operations, then the result of the
first operation is passed to the next, and so on, until no more
operations remain.

Example:

  (dot 0 (+ 1) oddp print)

  => T

An underscore may be used to explicitly indicate where the input
object should be placed in the OPERATION.

The previous example would therefore become:

  (dot 0 (+ _ 1) (oddp _) (print _))

If the first element in an operation is one of the following symbols

  (:last :slot :set :tee :key cl:quote :esc)

then the operation is treated specially as follows:

:key KEY

  Access the property KEY of the input object using the generic
  function ACCESS.

'KEY

  Shorthand for :key.
  Example: (dot company 'ceo 'name) <=>
           (dot company (:key 'ceo) (:key 'name))

:slot SLOT-NAME

  Access the slot SLOT-NAME of the input object using CL:SLOT-VALUE.

:last &rest OPERATION

  Place the input value last in the operation form, instead of first.

  Example: (dot 1 (:last - 2)) <=> (- 2 1)

:set PLACE

  Assign to PLACE the 'current' value (_) and continue the chain with
  that value.

:tee

  Branches out a new chain using the current input object. After the
  branch has completed, execution continues along the original chain
  with the original input object.

  Example:

  (dot 1
       (+ 1)
       (:tee (* 2) print) ; prints 4
       (- 2)) ; input is the result of the (+ 1) operation.
   => 0

:esc FORM

    Evaluates FORM unmodified.

"
  (let* ((underscore-predicate
           (lambda (x)
             (and (symbolp x)
                  (symbol-with-name-p x "_"))))
         (op (cond ((symbolp operation)
                    (list operation object))

                   ((and (listp operation)
                         (eq :last (first operation)))
                    (append (rest operation) (list object)))

                   ((and (listp operation)
                         (eq :key (first operation)))
                    `(access ,object ,(second operation)))

                   ;; Shorthand for :key
                   ((and (listp operation)
                         (eq 'quote (first operation)))
                    `(access ,object ',(second operation)))

                   ((and (listp operation)
                         (eq :slot (first operation)))
                    `(slot-value ,object ,(second operation)))

                   ((and (listp operation)
                         (eq :set (first operation)))
                    `(setf ,(second operation) ,object))

                   ((and (listp operation)
                         (eq :tee (first operation)))
                    (alexandria:with-gensyms (obj)
                      `(let ((,obj ,object))
                         (dot ,obj ,@(rest operation))
                         ,obj)))

                   ((and (listp operation)
                         (eq :esc (first operation)))
                    (second operation))

                   ((and (listp operation)
                         (tree-contains-p underscore-predicate
                                          operation))
                    (alexandria:with-gensyms (obj)
                      (let ((updated (subst-if obj
                                               underscore-predicate
                                               operation)))
                        `(let ((,obj ,object))
                           ,updated))))

                   ((listp operation)
                    (list* (first operation)
                             object
                             (rest operation)))

                   (t (error "Cannot understand operation ~S." operation)))))
  (if rest
      `(dot ,op ,@rest)
      op)))

;;; Define dot

(defun try-define-dot-pattern (pattern step)
  (destructuring-bind ((op &rest args) when-match) pattern
    (case op
      (:symbol (when (eq (first args) step)
                 when-match))
      (:symbol-name (when (symbol-with-name-p step
                                              (string (first args)))
                      when-match))
      (:type (when (typep step (first args))
               (let ((parameter (second args)))
                 (subst step parameter when-match))))
      (:any (subst step (first args) when-match)))))

(defun translate-define-dot-step (patterns step)
  (or (loop :for pattern :in patterns
              :thereis (try-define-dot-pattern pattern step))
      step))

(defun translate-define-dot-path (path patterns)
  ;; Preprocess a single symbol into (:symbol sym)
  (setf patterns (loop :for (op result) :in patterns
                       :collect (if (symbolp op)
                                    (list (list :symbol op) result)
                                    (list op result))))
  (loop :for step :in path
        :collect (translate-define-dot-step patterns step)))

(defmacro define-dot (name (&key) &body patterns)
  (alexandria:with-gensyms (object path translated-path)
    `(defmacro ,name (,object &rest ,path)
       (let ((,translated-path (translate-define-dot-path ,path
                                                          ',patterns)))
         `(dot ,,object ,@,translated-path)))))

;;; Examples

(define-dot cons-dot ()
  ((:symbol left) car)
  ((:symbol right) cdr)
  ((:any form) (:esc (error "Cannot understand step: ~S." 'form))))

;; (cons-dot '(1 2 3 4) right right left)
;; => 3

(define-dot array-dot ()
  ((:type integer n) (aref _ n))
  ((:type symbol n) (aref _ n)))

;; (let ((array #(#(1 2) #(3 4)))
;;       (i 0)
;;       (j 1))
;;   (array-dot array i j (evenp _)))
;; => T

;;; Tests

(print
 (loop :for test
         :in ' ;; trick emacs because otherwise indentation gets weird
         (
          ;; (- 1)
          (= -1 (dot 1 -))

          ;; (evenp (1+ 1))
          (eq t (dot 1 1+ evenp))

          ;; (- (- (+ 0 5) 2) 3)
          (= 0 (dot 0 (+ 5) (- 2) (- 3)))

          ;; (- 2 1)
          (= 1 (dot 1 (:last - 2)))

          ;; Demonstrate underscore (_)
          (= (dot 3 (-   2) (-   1))
             (dot 3 (- _ 2) (- _ 1)))

          (= 0 (dot 0 (+ _ 1) (- (+ _ 1) 2)))

          ;; Plist access
          (= 1 (dot (list :a 1 :b 2) ':a))
          (= 1 (dot (list :a 1 :b 2) (:key :a)))

          ;; :set
          (equal (list 1 2 3)
                 (let (x y)
                   (dot 0
                        (+ 1) (:set x)
                        (+ 1) (:set y)
                        (+ 1)
                        (list x y _))))

          ;; :tee
          (equal (list 1 2 3)
                 (let (x y)
                   (dot 0
                        (:tee (+ 2) (:last setf x))
                        (:tee (+ 2) (+ 1) (setf y _))
                        (+ 1)
                        (list _ x y))))

          ;; :tee
          (equal (list 1 2 3)
                 (dot (make-hash-table)
                      (:tee (setf (gethash :a _) 1))
                      (:tee (setf (gethash :b _) 2))
                      (:tee (:last gethash :c) (setf 3))
                      (list (dot _ ':a)
                            (dot _ ':b)
                            (dot _ ':c)))))
       :collect (eval test)))

;; => (T T T T T T T T T T)

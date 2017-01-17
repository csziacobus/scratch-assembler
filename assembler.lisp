;; parse program

(defun read-assembly-file (pathname)
  (let ((eof '#:eof) program)
    (with-open-file (stream pathname :direction :input)
      (loop (let ((form (read stream nil eof)))
              (when (eq form eof)
                (return))
              (push form program)))
      (nreverse program))))

;; SEGMENT - state of the assembler
(deftype assembly-unit () '(unsigned-byte 8))
(defclass segment ()
  ((buffer :initarg :buffer :reader segment-buffer)
   (label-map :accessor segment-label-map :initarg :label-map)))
(defun make-segment
    (&optional (buffer (make-array 0 :element-type 'assembly-unit
                                     :adjustable t
                                     :fill-pointer 0))
               (label-map (make-hash-table)))
  (make-instance 'segment :buffer buffer :label-map label-map))
(defun emit-byte (segment byte)
  (vector-push-extend byte (segment-buffer segment))
  (values))

(defun emit-label (segment label)
  (setf (gethash label (segment-label-map segment))
        (segment-current-instruction-address segment)))

(defun segment-current-instruction-address (segment)
  (multiple-value-bind (q r)
      ;; FIXME magic number
      (floor (print (fill-pointer (print (segment-buffer segment)))) 2)
    (assert (zerop r))
    q))

;; Define instruction machinery
(let ((instruction-emitters (make-hash-table)))
  (defun %define-instruction-emitter (name function)
    (setf (gethash name instruction-emitters) function))
  (defun instruction-emitter-function (name)
    (gethash name instruction-emitters)))

;; Define a bitfield layout with the byte specifications listed by byte-spec
;; An emitter for the byte specification is named by the keyword :emitter.
(defmacro define-bitfield-layout (name &rest byte-specs)
  (let (args)
    (dolist (byte-spec byte-specs)
      (push (alexandria:symbolicate
             "BYTE-" (write-to-string (second byte-spec))
             "-" (write-to-string (third byte-spec)))
            args))
    (let ((args (nreverse args)))
      `(progn
         (defun ,name ,args
           (let ((byte 0))
             ,@(mapcar (lambda (byte-spec arg) `(setf (ldb ,byte-spec byte) ,arg))
                       (remove-if-not (lambda (x) (eq (first x) 'byte)) byte-specs) args)
             byte))))))

;; more options to be defined here... more general than necessary for now
(defmacro define-instruction (name lambda-list &rest options)
  (let ((option-spec (first options)))
    (multiple-value-bind (option args)
        (if (consp option-spec)
            (values (first option-spec) (rest option-spec))
            (values option-spec nil))
      (ecase option
        (:emitter `(%define-instruction-emitter ',name
                     (lambda (%%segment%% ,@lambda-list)
                       (flet ((emit (&rest bytes)
                                (dolist (byte bytes)
                                  (emit-byte %%segment%% byte)))
                              (inst (&rest args)
                                (apply 'emit-inst %%segment%% args)))
                         ,@args))))))))

;; register
(defparameter +register-encoding-map+
  #(%pc %sp %fp %ax %bx %cx %dx %ex))

(deftype register-encoding () '(unsigned-byte 3))
(defun registerp (register)
  (find register +register-encoding-map+))
(defun register-encoding (register)
  (position register +register-encoding-map+))
(deftype immediate () 'integer)
(defun immediatep (x) (typep x 'immediate))

(define-bitfield-layout byte-opcode-with-reg
    (byte 5 3) (byte 3 0))
(define-bitfield-layout byte-reg
    (byte 3 5))
(define-bitfield-layout byte-reg-reg
    (byte 3 5) (byte 3 2))
(define-bitfield-layout byte-opcode-with-reg-reg
    (byte 2 6) (byte 3 3) (byte 3 0))

(defun byte-immediate (immediate)
  (check-type immediate immediate)
  (if (minusp immediate) (+ 256 immediate) immediate))

(defun emit-word (segment word)
  (check-type word immediate)
  (emit-byte segment (ldb (byte 8 8) word))
  (emit-byte segment (ldb (byte 8 0) word)))

(defun memory-reference-p (x)
  (and (listp x) (eq (first x) '@+)))

(defun check-memory-reference-syntax (memory-reference)
  (unless (memory-reference-p memory-reference)
    (error "Not valid memory-reference syntax")))

(defun parse-memory-reference (memory-reference)
  (check-memory-reference-syntax memory-reference)
  (values (find-if #'registerp (rest memory-reference))
          (find-if #'immediatep (rest memory-reference))))

;; emit instruction to segment
(defun emit-inst (segment instruction &rest args)
  (apply (instruction-emitter-function instruction) segment args))

;; Too much code repetition still below; emitterse look roughly same
(macrolet ((define-immediate-to-reg (name opcode)
             `(define-instruction ,name (dest immediate)
                (:emitter
                 (emit (byte-opcode-with-reg ,opcode (register-encoding dest))
                       (byte-immediate immediate)))))
           (define-reg-to-reg (name opcode)
             `(define-instruction ,name (dest src)
                (:emitter
                 (emit (byte-opcode-with-reg ,opcode (register-encoding dest))
                       (byte-reg (register-encoding src)))))))
  (define-immediate-to-reg andl #b00001)
  (define-immediate-to-reg andh #b00010)
  (define-immediate-to-reg orl #b00011)
  (define-immediate-to-reg orh #b00100)
  (define-immediate-to-reg movl #b00101)
  (define-immediate-to-reg movh #b00110)
  (define-reg-to-reg not #b01000))

(define-instruction brnz (reg absolute-address)
  (:emitter
   ;; we want to emit a relative address offset. calculate that now
   ;; because emitting a byte will chagne the address (KLUDGE)
   (let ((relative-offset (- absolute-address (segment-current-instruction-address %%segment%%))))
     (emit (byte-opcode-with-reg #b00111 (register-encoding reg))
           (byte-immediate relative-offset)))))

(define-instruction add (dest arg1 &optional arg2)
  (:emitter
   (cond (arg2
          (emit (byte-opcode-with-reg #b01001 (register-encoding dest))
                (byte-reg-reg (register-encoding arg1) (register-encoding arg2))))
         (t
          (emit (byte-opcode-with-reg #b00000 (register-encoding dest))
                (byte-immediate arg1))))))

(macrolet ((def (name opcode)
             `(define-instruction ,name (reg1 reg2 reg3)
                (:emitter
                 (emit (byte-opcode-with-reg ,opcode (register-encoding reg1))
                       (byte-reg-reg (register-encoding reg2) (register-encoding reg3)))))))
  (def and #b01010)
  (def or #b01011))

(define-instruction mov (dest src)
  (:emitter
   (cond ((and (registerp dest) (registerp src))
	  (inst 'and dest src src))
         ((and (memory-reference-p dest) (registerp src))
          (multiple-value-bind (reg offset)
              (parse-memory-reference dest)
            (emit (byte-opcode-with-reg-reg #b10
                                            (register-encoding reg)
                                            (register-encoding src))
                  (byte-immediate offset))))
         ((and (memory-reference-p src) (registerp dest))
          (multiple-value-bind (reg offset)
              (parse-memory-reference src)
            (emit (byte-opcode-with-reg-reg #b11
                                            (register-encoding dest)
                                            (register-encoding reg))
                  (byte-immediate offset))))
         (t (inst 'movl dest (ldb (byte 8 0) src))
            (inst 'movh dest (ldb (byte 8 8) src))))))

;; "derived" instructions
(define-instruction push (reg)
  (:emitter
   (inst 'mov '(@+ %sp 0) reg)
   (inst 'add '%sp -1)))

;; assembler
;; labels support
(defun labelp (x)
  (and (symbolp x) (not (registerp x))))

(defun emit-instructions (segment instructions compute-labels-p)
  (flet ((resolve-label (arg)
           (if (labelp arg)
               (if compute-labels-p
                   0
                   (gethash arg (segment-label-map segment)))
               arg)))
    (dolist (instruction instructions)
      (case (first instruction)
        (.label (emit-label segment (second instruction)))
        (.print (print (second instruction)))
	(.word (emit-word segment (second instruction)))
        (otherwise
         (when compute-labels-p
           (emit-label segment (second instruction)))
         (destructuring-bind (op &rest args)
             instruction
           (apply #'emit-inst segment op
                  (mapcar #'resolve-label args))))))))

(defun assemble (segment instructions)
  ;; compute labels first, but copy the buffer to a new segment
  ;; while sharing the label map so the old buffer remains in
  ;; the original segment to avoid backpatching label addresses
  (emit-instructions (make-segment (alexandria:copy-array (segment-buffer segment))
                                   (segment-label-map segment))
                     instructions t)
  (emit-instructions segment instructions nil)
  segment)

(defun assemble-file (instructions binary-file)
  (with-open-file (stream binary-file :direction :output
                                      :element-type '(unsigned-byte 8)
                                      :if-exists :supersede)
    (write-sequence (segment-buffer (assemble (make-segment) instructions))
                    stream)))

(defun assemble-file-mif (instructions mif-file)
  (with-open-file (stream mif-file :direction :output
                                   :if-exists :supersede)
    (let ((buffer (segment-buffer (assemble (make-segment) instructions))))
      (loop for i from 0 to (fill-pointer buffer) by 2
            do (format stream "~8,'0b" (aref buffer i))
               (format stream "~8,'0b~%" (aref buffer (1+ i))))
      buffer)))

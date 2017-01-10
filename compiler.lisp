;; parse program

(defun whitespace-char-p (char)
  (member char '(#\Space #\Newline #\Tab) :test #'char=))

(defun read-instruction (stream)
  (let ((line-stream (make-string-input-stream (read-line stream)))
        (no-second-arg (cons nil nil))
        (no-third-arg (cons nil nil)))
    (let ((name (read line-stream))
          (arg (read line-stream nil no-second-arg))
          (arg2 (read line-stream nil no-third-arg)))
      (cond ((eq arg no-second-arg) (list name))
            ((or (consp arg) (symbolp arg) (numberp arg))
             (list name arg arg2))
            (t (error "Unhandled second argument to ~a: ~a" name arg))))))

(defun read-assembly-line (first-char stream)
  (cond ((alpha-char-p first-char)
         (read-instruction stream))
        ((char= #\. first-char)
         (read stream))
        ((or (char= first-char #\;)
             (whitespace-char-p first-char))
         (read-line stream)
         nil)
        (t (error "Unhandled first character to line: ~a" first-char))))

(defun read-assembly-file (pathname)
  (let (program (eof '#:eof))
    (with-open-file (stream pathname :direction :input)
      (loop (let ((char (peek-char nil stream nil eof)))
              (when (eq char eof)
                (return))
              (let ((line (read-assembly-line char stream)))
                (when line
                  (push line program)))))
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
      (floor (fill-pointer (segment-buffer segment)) 2)
    (assert (zerop r))
    q))

;; Define instruction machinery
(let ((instruction-emitters (make-hash-table)))
  (defun %define-instruction-emitter (name function)
    (setf (gethash name instruction-emitters) function))
  (defun instruction-emitter-function (name)
    (gethash name instruction-emitters)))

(defmacro define-bitfield-layout (name &rest byte-specs)
  (let ((args (mapcar (lambda (byte-spec)
                        (alexandria:symbolicate
                         "BYTE-" (write-to-string (second byte-spec))
                         "-" (write-to-string (third byte-spec))))
                      byte-specs)))
    `(defun ,name ,args
       (let ((byte 0))
         ,@(mapcar (lambda (byte-spec arg) `(setf (ldb ,byte-spec byte) ,arg))
                   byte-specs args)
         byte))))

;; more options to be defined here... more general than necessary for now
(defmacro define-instruction (name lambda-list &rest options)
  (let ((option-spec (first options)))
    (multiple-value-bind (option args)
        (if (consp option-spec)
            (values (first option-spec) (rest option-spec))
            (values option-spec nil))
      (ecase option
        (:emitter `(%define-instruction-emitter ',name (lambda ,lambda-list ,@args)))))))

;; register
(defparameter +register-encoding-map+
  #(pc ; program counter (000)
    sp ; stack counter   (001)
    fp ; frame pointer   (010)
    sr ; status register (011)
    ax ; general purpose (100)
    bx ; general purpose (101)
    cx ; general purpose (110)
    dx ; general purpose (111)
    ))

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
(define-bitfield-layout byte-opcode-with-reg-reg
  (byte 2 6) (byte 3 3) (byte 3 0))

(defun emit-opcode-with-reg (segment opcode register-encoding)
  (emit-byte segment (byte-opcode-with-reg opcode register-encoding)))

(defun emit-reg (segment register-encoding)
  (emit-byte segment (byte-reg register-encoding)))

(defun emit-opcode-with-reg-reg (segment opcode reg1 reg2)
  (emit-byte segment (byte-opcode-with-reg-reg opcode reg1 reg2)))

(defun emit-immediate (segment immediate)
  (check-type immediate immediate)
  (emit-byte segment (if (minusp immediate)
                         (+ 256 immediate)
                         immediate)))

(defun memory-reference-p (x)
  (typep x '(cons (eql @) t)))

(defun check-memory-reference-syntax (memory-reference)
  (unless (and (memory-reference-p memory-reference)
               (eq (first (second memory-reference)) '+))
    (error "Not valid memory-reference syntax")))

(defun parse-memory-reference (memory-reference)
  (check-memory-reference-syntax memory-reference)
  (values (find-if #'registerp (second memory-reference))
          (find-if #'immediatep (second memory-reference))))

;; emit instruction to segment
(defun emit-inst (segment instruction &rest args)
  (apply (instruction-emitter-function instruction) segment args))

;; Too much code repetition still below; emitterse look roughly same
(macrolet ((define-immediate-to-reg (name opcode)
             `(define-instruction ,name (segment dest immediate)
                (:emitter
                 (emit-opcode-with-reg segment ,opcode (register-encoding dest))
                 (emit-immediate segment immediate))))
           (define-reg-to-reg (name opcode)
             `(define-instruction ,name (segment dest src)
                (:emitter
                 (emit-opcode-with-reg segment ,opcode (register-encoding dest))
                 (emit-reg segment (register-encoding src))))))
  (define-immediate-to-reg mcl #b00010)
  (define-immediate-to-reg mch #b00100)
  (define-reg-to-reg nor #b01010)
  (define-reg-to-reg jnz #b01100)
  (define-reg-to-reg jlz #b01110))

(define-instruction mov (segment dest src)
  (:emitter
   (cond ((and (registerp dest) (registerp src))
          (emit-opcode-with-reg segment #b00000 (register-encoding dest))
          (emit-reg segment (register-encoding src)))
         ((and (memory-reference-p dest) (registerp src))
          (multiple-value-bind (reg offset)
              (parse-memory-reference dest)
            (emit-opcode-with-reg-reg segment
                                      #b10
                                      (register-encoding reg)
                                      (register-encoding src))
            (emit-immediate segment offset)))
         ((and (memory-reference-p src) (registerp dest))
          (multiple-value-bind (reg offset)
              (parse-memory-reference src)
            (emit-opcode-with-reg-reg segment
                                      #b11
                                      (register-encoding dest)
                                      (register-encoding reg))
            (emit-immediate segment offset)))
         (t (emit-inst segment 'mcl dest (ldb (byte 8 0) src))
            (emit-inst segment 'mch dest (ldb (byte 8 8) src))))))

(define-instruction adc (segment dest src)
  (:emitter
   (cond ((registerp src)
          (emit-opcode-with-reg segment #b01000 (register-encoding dest))
          (emit-reg segment (register-encoding src)))
         (t
          (emit-opcode-with-reg segment #b00110 (register-encoding dest))
          (emit-immediate segment src)))))

;; assembler
;; labels support
;; labels will be symbols
(defun labelp (x)
  (and (symbolp x)
       (char= (char (symbol-name x) 0) #\.)))

(defun emit-instructions (segment instructions compute-labels-p)
  (flet ((resolve-label (arg)
           (if (labelp arg)
               (if compute-labels-p
                   0
                   (gethash arg (segment-label-map segment)))
               arg)))
    (dolist (instruction instructions)
      (if (labelp instruction)
          (when compute-labels-p
            (emit-label segment instruction))
          (destructuring-bind (op &rest args)
              instruction
            (apply #'emit-inst segment op
                   (mapcar #'resolve-label args)))))))

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
    (write-sequence (segment-buffer (assemble (make-segment)
                                      instructions))
                    stream)))

(defun assemble-file-mif (instructions mif-file)
  (with-open-file (stream mif-file :direction :output
                                   :if-exists :supersede)
    (let ((buffer (segment-buffer (assemble (make-segment)
                                    instructions)))
          (*print-base* 2))
      (loop for i from 0 to (fill-pointer buffer) by 2
            do (format stream "~8,'0b" (aref buffer i))
               (format stream "~8,'0b~%" (aref buffer (1+ i))))
      buffer)))

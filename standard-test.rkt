;; this file is used for debugging.
#lang racket
(require "utilities.rkt")
(require "compiler.rkt")
(require "type-check-Cvar.rkt")


(define passes
  (list
   pe-Lvar
   uniquify
   remove-complex-opera*
   explicate-control
   type-check-Cvar ;; install local-types. needed.
   select-instructions
   uncover-live
   build-interference
   allocate-registers
;    assign-homes ; only in C2
   patch-instructions
   prelude-and-conclusion
   ))

(define program-sexp '(program () (let ([x 1]) (+ x (+ 1 2)))))
(define program-ast (parse-program program-sexp))

(define (my-compile program passes)
  (match passes
    [(? null?) program]
    [(cons pass passes)
     (my-compile (pass program) passes)]))


(define p (my-compile program-ast passes))
; (displayln (print-x86 (my-compile program-ast passes)))

; (define var->reg/stack (color-graph (dict-ref (X86Program-info p) 'conflicts)))

#|
x = 1;
return 3 + x;

movq 1 rax
movq rax x
movq 3 rax
addq x rax
|#
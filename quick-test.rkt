#lang racket
(require "utilities.rkt")
(require "compiler.rkt")
(require "type-check-Cvar.rkt")
(require graph)
(require "priority_queue.rkt")

; (define program
;   (list
;    (Instr 'movq (list (Var 'z) (Reg 'rax)))
;    (Instr 'addq (list (Var 't) (Reg 'rax)))
;    (Jmp 'conclusion)))


(define program
  (list
   (Instr 'movq (list (Imm 1) (Var 'v)))
   (Instr 'movq (list (Imm 42) (Var 'w)))
   (Instr 'movq (list (Var 'v) (Var 'x)))
   (Instr 'addq (list (Imm 7) (Var 'x)))
   (Instr 'movq (list (Var 'x) (Var 'y)))
   (Instr 'movq (list (Var 'x) (Var 'z)))
   (Instr 'addq (list (Var 'w) (Var 'z)))
   (Instr 'movq (list (Var 'y) (Var 't)))
   (Instr 'negq (list (Var 't)))
   (Instr 'movq (list (Var 'z) (Reg 'rax)))
   (Instr 'addq (list (Var 't) (Reg 'rax)))
   (Jmp 'conclusion)))

(define x86program
  (X86Program '() (list (cons 'start
                              (cons '()
                                    program)))))

(define uncover-live-program (uncover-live x86program)) 
(define conflict-graph-program (build-interference uncover-live-program))

(define graph
  (match conflict-graph-program
    [(X86Program info label-blocks)
     (dict-ref info 'conflicts)])) ; checked

; (define live-sets (instrs->live-sets program (set)))
; (collect-edges program live-sets)

; (define pq (make-pqueue <=))
; (define nd1 (pqueue-push! pq 1))
; (define nd2 (pqueue-push! pq 2))
; (define nd3 (pqueue-push! pq 3))
; (set-node-key! nd2 8)
; (pqueue-decrease-key! pq nd2)

          
(define tmp-hash (color-graph graph)) 


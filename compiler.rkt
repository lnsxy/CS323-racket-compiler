#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


; inert -> inert (also res), but neg
(define (inert-neg i)
  (match i
    [(Var x) (Prim '- (list (Var x)))]
    [(Prim '- (list (Var x))) (Var x)]
    [(Prim 'read '()) (Prim '- (list (Prim 'read '())))]
    [(Prim '- (list (Prim 'read '()))) (Prim 'read '())]
    [(Prim '+ (list e1 e2))
     (Prim '+ (list (inert-neg e1)
                    (inert-neg e2)))]
    [(Let x e1 e2)
     (Let x e1 (inert-neg e2))]))


; res -> res , but neg
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))] ; int
    [(Prim '+ (list (Int n) e)) ; int + inert
     (Prim '+ (list (Int (fx- 0 n))
                    (inert-neg e)))]
    [else (inert-neg r)])) ; inert

; res , res -> res
(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))] ; int + int

    [((Int n1) (Prim '+ (list (Int n2) e)))
     (Prim '+ (list (Int (fx+ n1 n2)) e))]

    [((Prim '+ (list (Int n2) e)) (Int n1))
     (Prim '+ (list (Int (fx+ n1 n2)) e))] ; int + (int + inert)

    [((Prim '+ (list (Int n1) e1)) (Prim '+ (list (Int n2) e2)))
     (Prim '+ (list (Int (fx+ n1 n2))
                    (Prim '+ (list e1 e2))))] ; (int + inert) + (int + inert)

    [((Int n) e) (Prim '+ (list (Int n) e))]
    [(e (Int n)) (Prim '+ (list (Int n) e))] ; int + inert

    [((Prim '+ (list (Int n) e1)) e2)
     (Prim '+ (list (Int n)
                    (Prim '+ (list e1 e2))))]
    [(e2 (Prim '+ (list (Int n) e1)))
     (Prim '+ (list (Int n)
                    (Prim '+ (list e1 e2))))] ; inert + (int + inert)

    [(e1 e2) (Prim '+ (list e1 e2))])) ; inert + inert


; Number -> Number
(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))])) ; add + neg = sub. no use of this function


;; Lvar -> Lres
(define (pe-exp e)
  (match e
    [(Int n) (Int n)] ;
    [(Prim 'read '()) (Prim 'read '())] ;
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1)
                                    (pe-neg (pe-exp e2)))]


    [(Var x) (Var x)]
    [(Let x e1 e2)
     (Let x (pe-exp e1) (pe-exp e2))]))


(define (pe-Lvar p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; uniquify, Exercise 2.1
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define newx (gensym))
       (Let newx
            ((uniquify-exp env) e)
            ((uniquify-exp (dict-set env x newx)) ; the finding order is right here. ; efficiency?
             body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify: Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove_complex_operands, Exercises 2.3
;; Lvar exp -> alist & Lmonvar atm
(define (rco-atm e)
  (match e
    [(Int n) (values '() (Int n))]
    [(Var x) (values '() (Var x))]
    [(Let x exp1 exp2)
     (let-values ([(alist atm) (rco-atm exp2)])
       (let ([let-e (rco-exp exp1)])
         (values (cons (cons x let-e)
                       alist)
                 atm)))]
    [(Prim op args)
     (let ([newx (gensym)])
       (values (list (cons newx
                           (rco-exp (Prim op args))))
               (Var newx)))]))

;; Lvar exp -> Lmonvar exp
(define (rco-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    ; turn it into an Let form.
    [(Prim op args)
     ; turn all the args to atms first. Var will be used, so an alist is needed.
     ; Input: args, '(), '(). Output: (values alist atms)
     (define (helper-args args)
       (match args
         [(? null?) (values '() '())]
         [(cons arg rest-args)
          (let-values ([(_alist _atm) (rco-atm arg)]
                       [(alist atms) (helper-args rest-args)])
            (values (append _alist alist)
                    (cons _atm atms)))]))
     (define-values (alist atms) (helper-args args))
     ; then use Let form to collect all the things.
     (define (helper-let dict body)
       (match dict
         [(? null?) body]
         [(cons (cons x e) rest-dict)
          (Let x e (helper-let rest-dict body))]))
     (helper-let alist (Prim op atms))]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))



;; Input e: atom | (Prim' func (atom-list)) | (Let var exp exp)
;; cont should be tail form.
;; Output tail.
(define (explicate-assign x e cont)
  (match e
    [(Int n) (Seq (Assign (Var x)
                          (Int n))
                  cont)]
    [(Var y) (Seq (Assign (Var x)
                          (Var y))
                  cont)]
    [(Let y e body) ; x = (let y = ?). the order should be y = e, x = body.
     (explicate-assign y e
                       (explicate-assign x body cont))]
    [(Prim op es) (Seq (Assign (Var x)
                               (Prim op es))
                       cont)]))

;; Input: atom | (Prim' func (atom-list)) | (Let var exp exp)
;; Output tail.
(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x e body)
     (let ([cont (explicate-tail body)])
       (explicate-assign x e cont))]
    [(Prim op es)
     (Return (Prim op es))]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e) 
     (CProgram info (list (cons 'start (explicate-tail e))))]))


;; some optimization can be done at this part. But the first version should be as quick as possible.
;; TODO

(define (helper-atm atom)
  (match atom
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [_ (error (format "helper-atm failed with ~a" atom))]))

;; put the value of exp to rax, return a list of instrs.
(define (helper-exp exp cont)
  (match exp
    [(Int n) (cons (Instr 'movq (list (Imm n) (Reg 'rax))) cont)]
    [(Var y) (cons (Instr 'movq (list (Var y) (Reg 'rax))) cont)] ;; perhaps skip it when x=y?
    [(Prim 'read '()) (cons (Callq 'read_int 0) cont)]
    [(Prim '- `(,atm))
     (let ([arg (helper-atm atm)])
       (append (list (Instr 'movq (list arg (Reg 'rax)))
                     (Instr 'negq (list (Reg 'rax))))
               cont))]
    [(Prim '+ `(,atm1 ,atm2))
     (let ([arg1 (helper-atm atm1)]
           [arg2 (helper-atm atm2)])
       (append (list (Instr 'movq (list arg1 (Reg 'rax)))
                     (Instr 'addq (list arg2 (Reg 'rax))))
               cont))]
    [(Prim '- `(,atm1 ,atm2))
     (let ([arg1 (helper-atm atm1)]
           [arg2 (helper-atm atm2)])
       (append (list (Instr 'movq (list arg1 (Reg 'rax)))
                     (Instr 'subq (list arg2 (Reg 'rax))))
               cont))]))

;; return a list of instrs.
(define (helper-stmt stmt)
  (match stmt
    [(Assign (Var x) exp)
     (helper-exp exp
                 (list (Instr 'movq (list (Reg 'rax) (Var x)))))]))

(define (helper-tail tail)
  (match tail
    [(Return exp)
     (helper-exp exp
                 (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (append (helper-stmt stmt)
             (helper-tail tail))]))


;; select-instructions : Cvar -> x86var
;; ??? info?
(define (select-instructions p)
  (match p
    [(CProgram info (list (cons 'start tail)))
     (X86Program info (list (cons 'start
                                  (Block '()
                                         (helper-tail tail)))))]))

(define (assign-homes-dict alist)
  (for/list ([elem alist] [i (in-naturals)])
    (match elem
      [(cons key value)
       (cons key (Deref 'rbp (* -8 (+ i 1))))])))

;; Input:  p: list of instrs
;; Output: also list of instrs
(define (helper-assign-homes info p)
  (define (helper-arg arg dict)
    (match arg
      [(Imm n) (Imm n)]
      [(Reg reg) (Reg reg)]
      [(Deref reg int) (Deref reg int)]
      [(Var x) (dict-ref dict x)]))
  (let* ([alist (dict-ref info 'locals-types)]
         [dict (assign-homes-dict alist)])
    (for/list ([instr p])
      (match instr
        [(Instr op (list arg))
         (Instr op (list (helper-arg arg dict)))]
        [(Instr op (list arg1 arg2))
         (Instr op (list (helper-arg arg1 dict)
                         (helper-arg arg2 dict)))]
        [_ instr]))))

(define (get-stack-space info)
  (let ([tmp-space (* (length (dict-ref info 'locals-types)) 8)])
    (* (ceiling (/ tmp-space 16)) 16)))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info
                 (list (cons 'start
                             (Block '()
                                    p))))
     (X86Program (cons (cons 'stack-space
                             (get-stack-space info))
                       info)
                 (list (cons 'start
                             (Block '()
                                    (helper-assign-homes info p)))))]))


;; no deref form here
(define (arg->set arg)
  (match arg
    [(Imm int) (set)]
    [(Reg reg) (set (Reg reg))]
    [(Var var) (set (Var var))]
    [_ (error "no Deref form here" arg)]))

(define (W instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (arg->set arg2)]
    [(Instr 'subq (list arg1 arg2)) (arg->set arg2)]
    [(Instr 'negq (list arg)) (arg->set arg)]
    [(Instr 'movq (list arg1 arg2)) (arg->set arg2)]
    [(Instr 'pushq (list arg)) (set)]
    [(Instr 'popq (list arg)) (arg->set arg)]
    [(Callq label n) (set (Reg 'rax) (Reg 'rcx)
                          (Reg 'rdx) (Reg 'rsi)
                          (Reg 'rdi) (Reg 'r8)
                          (Reg 'r9) (Reg 'r10)
                          (Reg 'r11))] ; caller saved registers
    [(Retq) (error "no function temporarily")]
    [(Jmp label)
     (if (equal? label 'conclusion)
         (set)
         (error "the only Jmp should be conclusion"))]))

(define (R instr)
  (match instr
    [(Instr 'addq (list arg1 arg2)) (set-union (arg->set arg1) (arg->set arg2))]
    [(Instr 'subq (list arg1 arg2)) (set-union (arg->set arg1) (arg->set arg2))]
    [(Instr 'negq (list arg)) (arg->set arg)]
    [(Instr 'movq (list arg1 arg2)) (arg->set arg1)]
    [(Instr 'pushq (list arg)) (arg->set arg)]
    [(Instr 'popq (list arg)) (set)]
    [(Callq label n)
     (apply set (take (list 'rdi 'rsi 'rdx 'rcx 'r8 'r9) n))]
    [(Retq) (error "no function temporarily")]
    [(Jmp label) ; actually should handle besides W & R function. Attention!
     (if (equal? label 'conclusion)
         (set (Reg 'rax) (Reg 'rsp))
         (error "the only Jmp should be conclusion"))]))




;; More convenient approach is to separate W and R. Don't think too many things at once in coding.
;; premature optimization is the root of all evil.
;; rule: set - W + R
(define (update-live-set instr live-set)
  (let ([set-W (W instr)]
        [set-R (R instr)])
    (set-union (set-subtract live-set set-W)
               set-R)))

;; input (list instr ...)
;; output (list set ...)
;; after set
(define (instrs->live-sets instrs init-set)
  (define (helper-instrs->live-sets reverse-instrs init-set)
    (cond
      [(null? reverse-instrs) '()]
      [else
       (let ([new-set (update-live-set (car reverse-instrs) init-set)])
         (cons new-set
               (helper-instrs->live-sets (cdr reverse-instrs)
                                         new-set)))]))
  (cdr (reverse (cons init-set
                      (helper-instrs->live-sets (reverse instrs) init-set)))))

;; x86var -> x86var
;; TODO
; (define (uncover-live p)
;   (define (helper label-blocks)
;     (match label-blocks
;       [(? null?) '()]
;       [(cons (cons label (Block info instrs))
;              rest)
;        (let* ([live-sets (instrs->live-sets instrs (set))]
;               [new-info (cons (cons 'live-sets live-sets) info)])
;          (cons (cons label (Block new-info instrs)) rest))]))
;   (match p
;     [(X86Program info label-blocks) (X86Program info (helper label-blocks))]))

(define (uncover-live p)
  (match p
    [(X86Program info label-blocks)
     (X86Program info
                 (for/list ([label-block label-blocks])
                   (match label-block
                     [(cons label (Block info instrs))
                      (let* ([live-sets (instrs->live-sets instrs (set))]
                             [new-info (cons (cons 'live-sets live-sets) info)])
                        (cons label (Block new-info instrs)))])))]))
                       
;; build-interference-graph pass
;
(define (instruction-live-set->edges instruction live-set)
  (match instruction
    [(Instr 'movq (list arg1 arg2))
     (for/list ([x live-set]
                #:when (and (not (equal? x arg1)) 
                            (not (equal? x arg2))))
       (list x arg2))]
    [else
     (for*/list ([x (W instruction)]
                 [y live-set]
                 #:when (not (equal? x y)))
       (list x y))]))

(define (collect-edges instructions live-sets)
  (match* (instructions live-sets)
    [((? null?) (? null?)) '()]
    [((cons instruction instructions)
      (cons live-set live-sets))
     (append (instruction-live-set->edges instruction live-set)
             (collect-edges instructions live-sets))]))

(define (helper-collect-edges label-blocks)
  (append* 
    (for/list ([lb label-blocks])
      (match-let ([(cons label (Block info instrs)) lb])
        (collect-edges instrs (dict-ref info 'live-sets))))))

; x86var -> x86var
(define (build-interference p)
  (match p
    [(X86Program info label-blocks)
     (X86Program (cons (cons 'conflicts
                             (undirected-graph (helper-collect-edges label-blocks)))
                       info)
                 label-blocks)]))
     

;; actually there's support code in utilites.rkt... but I don't want to change that.
(define reg->int-hash
  (make-hash
   `((,(Reg 'rcx) . 0)
     (,(Reg 'rdx) . 1)
     (,(Reg 'rsi) . 2)
     (,(Reg 'rdi) . 3)
     (,(Reg 'r8)  . 4)
     (,(Reg 'r9)  . 5)
     (,(Reg 'r10) . 6)
     (,(Reg 'rbx) . 7)
     (,(Reg 'r12) . 8)
     (,(Reg 'r13) . 9)
     (,(Reg 'r14) . 10)

     (,(Reg 'rax) . -1) ; those registers are sometimes reserved.
     (,(Reg 'rsp) . -2)
     (,(Reg 'rbp) . -3)
     (,(Reg 'r11) . -4)
     (,(Reg 'r15) . -5))))

(define int->reg-hash
  (make-hash
   (for/list ([(k v) reg->int-hash])
     (cons v k))))

(define (color->reg/stack color)
  (if (and (<= color 10)
           (>= color 0))
      (hash-ref int->reg-hash color)
      (Deref 'rbp (* -8 (- color 10)))))

(define (reg->int reg)
  (dict-ref reg->int-hash reg))

(struct node
  (v
   [color #:mutable]
   color-set)
   #:transparent)

;; graph -> alist (Var -> Reg/Stack)
(define (color-graph graph)
  
  (define (cmp node1 node2)
    (>= (set-count (node-color-set node1))
        (set-count (node-color-set node2))))
  
  (define pq (make-pqueue cmp))
  
  (define v->node-dict (make-hash))
  (define v->handle-dict (make-hash))

;   (define (print-node-dict)
;     (for/hash ([(v nd) v->node-dict])
;       (display (node-v nd))
;       (display (node-color nd))
;       (display (node-color-set nd))
;       (newline)))
  
  (define (assign-color! v color)
    (define nd (hash-ref v->node-dict v))
    (set-node-color! nd color)
    
    (for ([nb (in-neighbors graph v)])
      (define nd (hash-ref v->node-dict nb))
      (set-add! (node-color-set nd) color)
      (pqueue-decrease-key! pq (hash-ref v->handle-dict nb))))

;   (print-node-dict)
  
  (for ([v (in-vertices graph)])
    (define nd (node v empty (mutable-set)))
    (hash-set! v->node-dict v nd)
    (hash-set! v->handle-dict v (pqueue-push! pq nd)))
  
  (for ([v (in-vertices graph)])
    (match v
      [(Reg reg) (assign-color! v (reg->int v))]
      [(Var var) (void)]
      ))
  
  (define (pick-color nd)
    (for/first ([i (in-naturals)]
                #:when (not (set-member? (node-color-set nd) i)))
      i))
                                         
  (let loop ()
    (if (not (= (pqueue-count pq) 0))
        (let ([nd (pqueue-pop! pq)])
          (when (Var? (node-v nd))
            (assign-color! (node-v nd) (pick-color nd)))
          (loop))
        (make-hash
         (for/list ([(v nd) v->node-dict]
                    #:when (not (Reg? v)))
           (cons v (color->reg/stack (node-color nd)))))))) ; checked.


(define (helper-allocate-registers dict instrs)
  (define (helper-arg arg dict)
    (match arg
      [(Imm n) (Imm n)]
      [(Reg reg) (Reg reg)]
      [(Deref reg int) (Deref reg int)]
      [(Var x) (dict-ref dict (Var x))]))
  (for/list ([instr instrs])
    (match instr
      [(Instr op (list arg))
       (Instr op (list (helper-arg arg dict)))]
      [(Instr op (list arg1 arg2))
       (Instr op (list (helper-arg arg1 dict)
                       (helper-arg arg2 dict)))]
      [_ instr])))



; TODO: collect from var->reg/stack
; X86Var -> X86Var 
(define (allocate-registers p)
  (match p
    [(X86Program info label-blocks)
     (let* ([graph (dict-ref info 'conflicts)]
            [var->reg/stack (color-graph graph)]
            [used-callee (for/set ([(k v) var->reg/stack]
                                   #:when (set-member? callee-save v))
                           v)]
            [stack-location-count (set-count (for/set ([(k v) var->reg/stack]
                                                  #:when (Deref? v))
                                          k))]
            [new-info (append (list (cons 'used-callee used-callee)
                                    (cons 'stack-location-count stack-location-count))
                              info)])
       (X86Program new-info
                   (for/list ([lb label-blocks])
                     (match-let ([(cons label (Block info instrs)) lb])
                       (cons label (Block info (helper-allocate-registers var->reg/stack instrs)))))))]))
                     

;; Input:  p: list of instrs
;; Output: also list of instrs

(define (helper-patch-instructions p)
  (append*  
    (for/list ([instr p])  
      (match instr
        [(Instr 'movq (list a b))
         (if (equal? a b)
             '()
             (list instr))]
        [(Instr op (list (Deref reg1 int1)
                        (Deref reg2 int2)))
         (list 
          (Instr 'movq (list (Deref reg1 int1)
                            (Reg 'rax)))
          (Instr 'movq (list (Reg 'rax)
                            (Deref reg2 int2))))]
        [_ (list instr)]))))  


(define (patch-instructions p)
  (match p
    [(X86Program info label-blocks)
     (X86Program info
                 (for/list ([lb label-blocks])
                   (match-let ([(cons label (Block info instrs)) lb])
                     (cons label (Block info (helper-patch-instructions instrs))))))]))

;; int set -> list of instrs
(define (generate-main stack-space used-callee)
  (append
   (list (Instr 'pushq (list (Reg 'rbp)))
         (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
         (Instr 'subq (list (Imm stack-space) (Reg 'rsp))))
   (for/list ([reg used-callee])
     (Instr 'pushq reg))
   (list (Jmp 'start))))
        

(define (generate-conclusion stack-space used-callee)
  (append
   (reverse (for/list ([reg used-callee])
              (Instr 'popq reg)))
   (list (Instr 'addq (list (Imm stack-space) (Reg 'rsp)))
         (Instr 'popq (list (Reg 'rbp)))
         (Retq))))


;; prelude-and-conclusion : x86int -> x86int
;; for callee saved register, if I want to use it, I must store it first.
;; order for prelude: allocate spilled variable using subq, save callee saved registers using pushq. conclusion is in reverse order.
;; assume only one block here!
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info label-blocks)
     (let ([stack-space (- (align (+ (* 8 (dict-ref info 'stack-location-count))
                                     (* 8 (set-count (dict-ref info 'used-callee))))
                                  16)
                           (* 8 (set-count (dict-ref info 'used-callee))))])
       (X86Program info
                   (append (list  (cons 'main
                                        (Block '()
                                               (generate-main stack-space
                                                              (dict-ref info 'used-callee))))
                                  (cons 'conclusion
                                        (Block '()
                                               (generate-conclusion stack-space
                                                                    (dict-ref info 'used-callee)))))
                           label-blocks)))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("partial evaluation", pe-Lvar,interp-Lvar, type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-x86-0)
    ("uncover-live", uncover-live,interp-x86-0)
    ("build-interference",build-interference,interp-x86-0)
    ("allocate-registers",allocate-registers,interp-x86-0)
    ; ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))

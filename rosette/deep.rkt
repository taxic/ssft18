#lang rosette

(require
  rosette/lib/match
  (prefix-in s (only-in "shallow.rkt" Not And Or Iff Xor)))
 
(struct Not (a)   #:transparent)
(struct And (a b) #:transparent)
(struct Or  (a b) #:transparent)
(struct Iff (a b) #:transparent)
(struct Xor (a b) #:transparent)
 
(define (interpret prog in)
  (define reg (make-vector (+ (car prog) (length (cdr prog))) #f))
  (define (store i v) (vector-set! reg i v))
  (define (load i) (vector-ref reg i))
  (define (last) (sub1 (vector-length reg)))
  (for ([(i idx) (in-indexed in)])
    (store idx i))
  (for ([(inst idx) (in-indexed (cdr prog))])
    (store
     (+ idx (car prog))
     (match inst
       [(Not a)   (sNot (load a))]
       [(And a b) (sAnd (load a) (load b))]
       [(Or a b)  (sOr (load a) (load b))]
       [(Xor a b) (sXor (load a) (load b))]
       [(Iff a b) (sIff (load a) (load b))])))
  (load (last)))

(define (ver impl spec)
  (define-symbolic* in boolean? [(car impl)])
  (define cex
    (verify
     (assert
      (equal? (interpret impl in)
              (interpret spec in)))))
  (and (sat? cex) (evaluate in cex)))

(require rosette/lib/angelic)

(define sketch
(case-lambda
 [(n k) (sketch n k Not And Or Xor Iff)]
 [(n k . insts)
  (cons
   n
   (for/list ([i k])
     (define inst (apply choose* insts))
     (define left  (apply choose* (build-list (+ i n) identity)))
     (define right (apply choose* (build-list (+ i n) identity)))
     (match inst
     [(== Not) (Not left)]
       [op (op left right)])))]))

(define (syn impl spec)
  (define-symbolic* in boolean? [(car impl)])
  (define sol
    (synthesize
     #:forall in
     #:guarantee
     (assert
      (equal? (interpret impl in)
              (interpret spec in)))))
  (and (sat? sol) (evaluate impl sol)))

(define (superopt spec [k 1])
  (and (< k (length (cdr spec)))
       (or (syn (sketch (car spec) k) spec)
           (superopt spec (+ k 1)))))

(define NXp
  (list 4 (Xor 0 1) (Not 4) (Xor 2 3) (Not 6) (Xor 5 7)))
 
(define Niffp
  (list 4 (Iff 0 1) (Iff 2 3) (Iff 4 5) (Not 6)))
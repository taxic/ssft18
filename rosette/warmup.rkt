#lang rosette
 
(define (abs-spec x)
  (if (bvslt x (bv 0 32))
      (bvneg x)
      x))

(define (abs-impl x)
  (let* ([o1 (bvashr x (bv 31 32))]
         [o2 (bvadd x o1)]
         [o3 (bvsub o2 o1)])
    o3))

(define-symbolic x (bitvector 32))
(define cex
(verify 
 (assert (equal? (abs-impl x) (abs-spec x)))))

(require rosette/query/debug rosette/lib/render)

(define/debug (abs-impl-2 x)
  (let* ([o1 (bvashr x (bv 31 32))]
         [o2 (bvadd x o1)]
         [o3 (bvsub o2 o1)])
    o3))

(define fault (evaluate x cex))
(render
 (debug [(bitvector 32)]
        (assert (equal? (abs-impl-2 fault) (abs-spec fault)))))

(require rosette/lib/synthax)
(define (abs-impl-3 x)
  (let* ([o1 (bvashr x (bv 31 32))]
         [o2 ((choose bvadd bvand bvor bvxor bvshl bvlshr bvashr) x o1)]
         [o3 ((choose bvsub bvand bvor bvxor bvshl bvlshr bvashr) o2 o1)])
    o3))
(print-forms
 (synthesize
  #:forall x
  #:guarantee (assert (equal? (abs-impl-3 x) (abs-spec x)))))
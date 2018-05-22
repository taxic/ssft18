#lang rosette
(define (choice type)
  (define-symbolic* x integer?)
  x)
; A puzzle is represented as a list of 81 digits,
; obtained by concatenating the rows of the puzzle,
; from first to last.
(define (sudoku-check puzzle)
  (for ([digit puzzle])
    (assert (and (<= 1 digit) (<= digit 9))))  ; all digits between 1 and 9
  (for ([row (rows puzzle)])
    (assert (apply distinct? row)))            ; all digits in a row are different
  (for ([column (columns puzzle)])
    (assert (apply distinct? column)))         ; all digits in a column are different
  (for ([region (regions puzzle)])
    (assert (apply distinct? region))))        ; all digits in an 3x3 region are different
 
(define (rows puzzle [n 9])
  (if (null? puzzle)
      null
      (cons (take puzzle n)
            (rows (drop puzzle n) n))))
 
(define (columns puzzle [n 9])
  (if (null? puzzle)
      (make-list n null)
      (map cons
           (take puzzle n)
           (columns (drop puzzle n) n))))
 
(define (regions puzzle)
  (define rows3 (curryr rows 3))
  (define cols3 (curryr columns 3))
  (map flatten
       (append-map
        append
        (cols3
         (append-map
          rows3
          (cols3
           (append-map rows3 (rows puzzle))))))))
 
(define (char->digit c)
  (- (char->integer c) (char->integer #\0)))
 
(define (string->puzzle p)
  (map char->digit (string->list p)))
 
(define (show puzzle)
  (pretty-print (rows puzzle)))

(define (puzzle->sym puzzle)
  (for/list ([d puzzle])
    (if (= d 0) (choice integer?) d)))

(define (solve-puzzle puzzle)
  (define ps (puzzle->sym puzzle))
  (define sol
    (solve
     (sudoku-check ps)))
  (if (sat? sol)
      (evaluate ps sol)
      #f))

(define (valid-puzzle? puzzle)
 (define ps1 (puzzle->sym puzzle))
 (define ps2 (puzzle->sym puzzle))
  (unsat?
   (solve
    (begin
      (sudoku-check ps1)
      (sudoku-check ps2)
      (assert (not (equal? ps1 ps2)))))))

(define (generate-puzzle)
(for/fold ([p (solve-puzzle (make-list 81 0))])
          ([i (shuffle (build-list 81 values))])
  (let ([pi0 (list-set p i 0)])
    (if (valid-puzzle? pi0) pi0 p))))

; Sample solved puzzle.
(define p0 (string->puzzle "693784512487512936125963874932651487568247391741398625319475268856129743274836159"))
; Sample unsolved puzzle where 0 represents unfilled cells.
(define p1 (string->puzzle "000000010400000000020000000000050604008000300001090000300400200050100000000807000"))
(define p2 (string->puzzle "000000012000035000000600070700000300000400800100000000000120000080000040050000600"))
(define p3 (string->puzzle "000000012003600000000007000410020000000500300700000600280000040000300500000000000"))
(define p4 (string->puzzle "000000012008030000000000040120500000000004700060000000507000300000620000000100000"))
 
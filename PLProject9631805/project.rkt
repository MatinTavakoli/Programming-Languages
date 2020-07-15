;; PL Project - Fall 2019
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (b)      #:transparent)  ;; boolean constants
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus  (e1 e2)  #:transparent)  ;; subtract two expressions
(struct mult  (e1 e2)  #:transparent)  ;; multiply two expressions
(struct div  (e1 e2)  #:transparent)  ;; divide two expressions
(struct neg (e1)      #:transparent)  ;; negation
(struct andalso  (e1 e2)  #:transparent)  ;; logical conjunction
(struct orelse  (e1 e2)  #:transparent)  ;; logical disjunction
(struct cnd  (e1 e2 e3)  #:transparent)  ;; condition
(struct iseq  (e1 e2)  #:transparent)  ;; comparison
(struct ifnzero  (e1 e2 e3)  #:transparent)  ;; if not zero condition
(struct ifleq  (e1 e2 e3 e4)  #:transparent)  ;; less or equal condition
(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application
(struct with  (s e1 e2)  #:transparent)  ;; let expression
(struct apair  (e1 e2)  #:transparent)  ;; pair constructor
(struct 1st  (e1)  #:transparent)  ;; first part of a pair
(struct 2nd  (e1)  #:transparent)  ;; second part of a pair


(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e1)     #:transparent) ;; if e1 is unit then true else false
(struct closure  (env f)  #:transparent)  ;; a closure is not in "source" programs; it is what functions evaluate to
(struct letrec (s1 e1 s2 e2 e3) #:transparent) ;; a letrec expression for recursive definitions
(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k mr) #:transparent) ;; record constructor
;(struct record (k r) #:transparent) ;; record constructor
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r

;; Problem 1

;input is either null, or a racket list, or something invalid
(define (racketlist->numexlist xs)
  (cond[(null? xs) (munit)] ;null in racket is munit in NUMEX
       [(list? xs) (apair (car xs) (racketlist->numexlist (cdr xs)))] ;list in racket is apair in NUMEX(which is applied recursively)
       [else (error ("not a racket list"))]) ;shows that the input is invalid
  )

;input is either null, or a NUMEX list, or something invalid
(define (numexlist->racketlist xs)
  (cond[(munit? xs) null] ;munit in NUMEX is null in racket
       [(apair? xs) (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))] ;apair in NUMEX is list in racket(which is applied recursively)
       [else (error ("not a NUMEX list"))]) ;shows that the input is invalid
  )

;; Problem 2

;; lookup a variable in an environment
;; Complete this function
(define (envlookup env str)
  (cond [(null? env) (error "unbound variable during evaluation" str)]
        [(equal? (string? str) #f) (error ("str is not a string"))]
        [(equal?(list? env) #f) (error ("env in not a racket list"))]
        [(equal? str (car (car env))) (cdr (car env))] ;evaluation
        [else (envlookup (cdr env) str)] ;recursion
		)
 )

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)
  (cond [(var? e) 
         (cond[(string? (var-string e))(envlookup env (var-string e))]
              [else (error "NUMEX var applied to non-racket-string")])]
        [(num? e)
         (cond[(integer? (num-int e)) e]
              [else (error "NUMEX num applied to non-racket-integer")])]
        [(bool? e)
         (cond[(boolean? (bool-b e)) e]
              [else (error "NUMEX bool applied to non-racket-boolean")])]
        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (+ (num-int v1) (num-int v2)))]
                    [else (error "NUMEX addition applied to non-number")]))]

        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (- (num-int v1) (num-int v2)))]
                    [else (error "NUMEX subtraction applied to non-number")]))]
        
        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (* (num-int v1) (num-int v2)))]
                    [else (error "NUMEX multiplication applied to non-number")]))]

        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (quotient (num-int v1) (num-int v2)))] ;we only need the int value not float!
                    [else (error "NUMEX divion applied to non-number")]))]

        [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (cond [(num? v1)(num (- 0 (num-int v1)))] ;return -v(if v is a num)
                 [(bool? v1)
                  (cond[(equal? (bool-b v1) #t) (bool #f)]
                       [(equal? (bool-b v1) #f) (bool #t)])] ;negate v(if v is a bool)
                 [else (error "NUMEX negation applied to non-number")]))]

        ;short circuiting added
        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #f) v1]
                                [else (let ([v2 (eval-under-env (andalso-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX conjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env (andalso-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX conjunction applied to non-number")]))]))]

        ;short circuiting added
        [(orelse? e) 
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #t) v1]
                                [else (let ([v2 (eval-under-env (orelse-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX conjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env (orelse-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX disjunction applied to non-number")]))]))]

        [(cnd? e) 
         (let ([v1 (eval-under-env (cnd-e1 e) env)])
           (if (bool? v1)
               (cond[(equal? (bool-b v1) #t)(let ([v2 (eval-under-env (cnd-e2 e) env)]) v2)]
                    [(equal? (bool-b v1) #f)(let ([v3 (eval-under-env (cnd-e3 e) env)]) v3)])
               (error "NUMEX condition applied to non-boolean")))]

        [(iseq? e) 
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
           (cond[(and (or (bool? v1) (num? v1))(or (bool? v2) (num? v2)))(cond[(and (bool? v1) (bool? v2))(cond[(equal? (bool-b v1) (bool-b v2))(bool #t)]
                                                                                                               [else (bool #f)])]
                                                                              [(and (num? v1) (num? v2))(cond[(equal? (num-int v1) (num-int v2))(bool #t)]
                                                                                                             [else (bool #f)])]
                                                                              [else (bool #f)])]
                [else (error "NUMEX equality is applied to something other than non-booleans or non-numbers")]))]
        
        [(ifnzero? e) 
         (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
           (if (num? v1)
               (cond[(not (equal? (num-int v1) 0))(let ([v2 (eval-under-env (ifnzero-e2 e) env)]) v2)]
                    [(equal? (num-int v1) 0)(let ([v3 (eval-under-env (ifnzero-e3 e) env)]) v3)])
               (error "NUMEX ifnotzero condition applied to non-number")))]

        [(ifleq? e) 
         (let ([v1 (eval-under-env (ifleq-e1 e) env)]
               [v2 (eval-under-env (ifleq-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (cond[(> (num-int v1) (num-int v2))(let ([v4 (eval-under-env (ifleq-e4 e) env)]) v4)]
                    [(not (> (num-int v1) (num-int v2)))(let ([v3 (eval-under-env (ifleq-e3 e) env)]) v3)])
           (error "NUMEX ifleq condition applied to non-numbers")))]

        [(lam? e) 
         (closure env e)]

        [(apply? e)
          (let ([fun-closure (eval-under-env (apply-funexp e) env)]) ;evaluating funexp in apply
            ;our funexp is either a closure, or a lam
            (cond[(closure? fun-closure) (let ([fun-def (closure-f fun-closure)]) ;if it is a closure, then 
                                       (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                             (cond[(lam? fun-def)(eval-under-env (lam-body fun-def) (cons (cons (lam-formal fun-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt fun-def) fun-closure) (closure-env fun-closure))))] ;evaluate lam-body under this new enviroment
                                                  [else (error "closure function isn't lam")])))]

                 [(lam? fun-closure) (let* ([lam-closure (eval-under-env fun-closure env)] ;first we evaluate fun-closure to lam-closure
                                           [lam-def (closure-f lam-closure)]) ;if it is a closure, then 
                                       (let ([eval-actual (eval-under-env (apply-actual e) env)])
                                             (cond[(lam? lam-def)(eval-under-env (lam-body lam-def) (cons (cons (lam-formal lam-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt lam-def) lam-closure) (closure-env lam-closure))))] ;evaluate lam-body under this new enviroment
                                                  [else (error "closure function isn't lam")])))]
                 [else (error (format "NUMEX lam apply invalid"))]))]
        
        [(with? e)
         (let ([v1 (eval-under-env (with-e1 e) env)])
           ; s is either a string or null(anonymous)
           (cond[(string? (with-s e)) (eval-under-env (with-e2 e) (cons (cons (with-s e) v1) env))]
                [(null?   (with-s e)) (eval-under-env (with-e2 e) (cons v1 env))];evaluate e2 with a new enviroment which is (cons v1 env)
                [else (error "NUMEX with applied to non-string")]))]

        [(apair? e) 
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))] ;it's that simple!

        [(1st? e) 
         (let ([v1 (eval-under-env (1st-e1 e) env)])
           (if (apair? v1)
               (apair-e1 v1)
               (error "NUMEX 1st applied to non-apair")))]

        [(2nd? e) 
         (let ([v1 (eval-under-env (2nd-e1 e) env)])
           (if (apair? v1)
               (apair-e2 v1)
               (error "NUMEX 2nd applied to non-apair")))]

        [(munit? e) (munit)] ;just like that!

        [(ismunit? e)
         (let ([v1 (eval-under-env (ismunit-e1 e) env)])
           (cond[(munit? v1)(bool #t)]
                [else (bool #f)]))]

        [(closure? e) e] ;that seems all there is needed!:)

        [(letrec? e)         
               (eval-under-env (letrec-e3 e) (cons (cons (letrec-s1 e) (letrec-e1 e)) (cons (cons (letrec-s2 e) (letrec-e2 e)) env)))] ;evaluate e3 under this new enviroment (looks easy but it's not!)

        [(key? e)
         (let ([ex (eval-under-env (key-e e) env)])
               (cond[(string? (key-s e)) e]
                    [else (error "key is not a string")]))]

        [(record? e)
         (let ([k (eval-under-env (record-k e) env)]
               [mr (eval-under-env (record-mr e) env)])
               (cond[(key? k) (cond[(or (munit? (eval-exp mr)) (record? mr)) (record k mr)] ;gives back the record
                                   [else (error "value of record invalid")])]
                [else (error "key invalid")]))]

        [(value? e)
         (let ([rec (eval-under-env (value-r e) env)])
               (cond[(and (string? (value-s e)) (record? rec))
                 (define (find-key goal-str rec)
                 (let ([key-str (key-s (record-k rec))] ;string of record
                       [key-val (key-e (record-k rec))] ;value of record
                       [next-rec (record-mr rec)]) ;next record
                       (cond[(equal? goal-str key-str) key-val]
                            [(munit? (eval-exp next-rec)) (munit)]
                            [else (find-key goal-str next-rec)])))(find-key (value-s e) rec)] ;TODO
                    [else (error "NUMEX value applied to non-string")]))]

        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

;;Golden Tip: when using macros, we use NUMEX expressions and functions instead of evaluating directly!

(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3)) ;just like that! (silly mistake: used  "(munit? e1)" instead of "(ismunit e1)")

(define (with* bs e2) (let ([pair (car bs)]
                            [next-pair (cdr bs)]
                            [pair-s (car (car bs))]
                            [pair-e (cdr (car bs))])
                            (cond[(null? next-pair) (with pair-s pair-e e2)] ;just use "with" now
                                 [else (with pair-s pair-e (with* next-pair e2))]))) ;add "with" to the next pair

(define (ifneq e1 e2 e3 e4) (cnd (iseq e1 e2) e4 e3)) ;returns e4 if value of e1 equals to value of e2 and e3 otherwise 

;; Problem 4

;Again, no evaluation! just usingn NUMEX expressions and functions

(define numex-filter (lam "f" "g" (lam "h" "list" (cnd (ismunit (var "list"))
                                                          (munit) ; if it is an munit, then return (munit)
                                                          (with "val" (apply (var "g") (1st (var "list"))) (ifnzero (var "val")
                                                                                                              (apair (var "val") (apply (var "h") (2nd (var "list")))) ;if value is not zero, create an apair
                                                                                                              (apply (var "h") (2nd (var "list")))))))))           ;if value is zero, ignore and move on

(define numex-all-gt
  (with "filter" numex-filter
        (lam null "i" (lam null "list" (apply (apply (var "filter") (lam null "element" (ifleq (var "element") (var "i")
                                                                                               ;if condition is not met, pass (num 0) to numex-filter (so nothing happens!)
                                                                                               (num 0)
                                                                                               ;else, append this element
                                                                                               (var "element"))))   (var "list")))))) ;


;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;removes bound vars of env by looking them up in the freevars set
;needed to remove bound variables to shrink our enviroment
(define (remove-boundvars env freevars)
  (cond[(null? env) env]
       [else (let([car-env (car env)]
                  [cdr-env (cdr env)]
                  [var (car (car env))])
                  (cond[(set-member? freevars var)(cons car-env (remove-boundvars cdr-env freevars))] ;if var is in freevars, append it and move on(recursion)
                       [else (remove-boundvars cdr-env freevars)]))])) ;else, ignore and move on(recursion)

;; We will test this function directly, so it must do
;; as described in the assignment
(define (compute-free-vars e)
  (car (compute-free-vars-cons e))); nothing extraordinary. the real thing is down below!

;;The real magic is here!
(define (compute-free-vars-cons e)
  (cond[(var? e) (cons e (set (var-string e)))] ;free variable of var string is the string part!
       
       [(num? e) (cons e (set))] ;num has no free variable!
       
       [(bool? e) (cons e (set))] ;bool has no free variable!
       
       [(plus? e) (let([v1 (compute-free-vars-cons (plus-e1 e))]
                       [v2 (compute-free-vars-cons (plus-e2 e))])
                       (cons (plus (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(minus? e) (let([v1 (compute-free-vars-cons (minus-e1 e))]
                        [v2 (compute-free-vars-cons (minus-e2 e))])
                        (cons (minus (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(mult? e) (let([v1 (compute-free-vars-cons (mult-e1 e))]
                       [v2 (compute-free-vars-cons (mult-e2 e))])
                       (cons (mult (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(div? e) (let([v1 (compute-free-vars-cons (div-e1 e))]
                      [v2 (compute-free-vars-cons (div-e2 e))])
                      (cons (div (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]
       
       [(neg? e) (let([v1 (compute-free-vars-cons (neg-e1 e))])
                      (cons (neg (car v1)) (cdr v1)))]

       [(andalso? e) (let([v1 (compute-free-vars-cons (andalso-e1 e))]
                          [v2 (compute-free-vars-cons (andalso-e2 e))])
                          (cons (andalso (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(orelse? e) (let([v1 (compute-free-vars-cons (orelse-e1 e))]
                         [v2 (compute-free-vars-cons (orelse-e2 e))])
                         (cons (orelse (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(cnd? e) (let([v1 (compute-free-vars-cons (cnd-e1 e))]
                      [v2 (compute-free-vars-cons (cnd-e2 e))]
                      [v3 (compute-free-vars-cons (cnd-e3 e))])
                      (cons (cnd (car v1) (car v2) (car v3)) (set-union (cdr v1) (cdr v2) (cdr v3))))]

       [(iseq? e) (let([v1 (compute-free-vars-cons (iseq-e1 e))]
                       [v2 (compute-free-vars-cons (iseq-e2 e))])
                       (cons (iseq (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(ifnzero? e) (let([v1 (compute-free-vars-cons (ifnzero-e1 e))]
                          [v2 (compute-free-vars-cons (ifnzero-e2 e))]
                          [v3 (compute-free-vars-cons (ifnzero-e3 e))])
                          (cons (ifnzero (car v1) (car v2) (car v3)) (set-union (cdr v1) (cdr v2) (cdr v3))))]

       [(ifleq? e) (let([v1 (compute-free-vars-cons (ifleq-e1 e))]
                        [v2 (compute-free-vars-cons (ifleq-e2 e))]
                        [v3 (compute-free-vars-cons (ifleq-e3 e))]
                        [v4 (compute-free-vars-cons (ifleq-e4 e))])
                        (cons (ifleq (car v1) (car v2) (car v3) (car v4)) (set-union (cdr v1) (cdr v2) (cdr v3) (cdr v4))))]

       ;check if time left!(seems not)
       [(lam? e) (let([v1 (lam-nameopt e)]
                      [v2 (lam-formal e)]
                      [v3 (lam-body e)])
                          (let([lam-body-freevars (cdr (compute-free-vars-cons v3))])
                               (cons (fun-challenge v1 v2 v3 (set-remove (set-remove lam-body-freevars v1) v2)) (set-remove (set-remove lam-body-freevars v1) v2))))]


       [(apply? e) (let([v1 (compute-free-vars-cons (apply-funexp e))]
                        [v2 (compute-free-vars-cons (apply-actual e))])
                        (cons (apply (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(with? e) (let([s (with-s e)] ;because s is a string and doesn't have free variables, just evaluate it!
                       [v1 (compute-free-vars-cons (with-e1 e))]
                       [v2 (compute-free-vars-cons (with-e2 e))])
                           (cons (with s (car v1) (car v2)) (set-remove (set-union (cdr v1) (cdr v2)) s)))]

       [(apair? e) (let([v1 (compute-free-vars-cons (apair-e1 e))]
                        [v2 (compute-free-vars-cons (apair-e2 e))])
                        (cons (apair (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(1st? e) (let([v1 (compute-free-vars-cons (1st-e1 e))])
                      (cons (1st (car v1)) (cdr v1)))]

       [(2nd? e) (let([v1 (compute-free-vars-cons (2nd-e1 e))])
                      (cons (2nd (car v1)) (cdr v1)))]     
       
       [(munit? e) (cons e (set))] ;munit has no free variable!

       [(ismunit? e) (let([v1 (compute-free-vars-cons (ismunit-e1 e))])
                      (cons (ismunit (car v1)) (cdr v1)))]
       
       [(closure? e) (cons e (set))] ;closure has no free variable!

       [(letrec? e) (let([v1 (compute-free-vars-cons (letrec-s1 e))]
                         [v2 (compute-free-vars-cons (letrec-e1 e))]
                         [v3 (compute-free-vars-cons (letrec-s2 e))]
                         [v4 (compute-free-vars-cons (letrec-e2 e))]
                         [v5 (compute-free-vars-cons (letrec-e3 e))])
                         (cons (letrec (car v1) (car v2) (car v3) (car v4) (car v5)) (set-union (cdr v1) (cdr v2) (cdr v3) (cdr v4) (cdr v5))))]
      
       [(key? e) (let([v1 (compute-free-vars-cons (key-s e))]
                      [v2 (compute-free-vars-cons (key-e e))])
                      (cons (key (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(record? e) (let([v1 (compute-free-vars-cons (record-k e))]
                         [v2 (compute-free-vars-cons (record-mr e))])
                         (cons (record (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]

       [(value? e) (let([v1 (compute-free-vars-cons (value-s e))]
                        [v2 (compute-free-vars-cons (value-r e))])
                        (cons (value (car v1) (car v2)) (set-union (cdr v1) (cdr v2))))]))

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env)
  (cond [(var? e) 
         (cond[(string? (var-string e))(envlookup env (var-string e))]
              [else (error "NUMEX var applied to non-racket-string")])]
        [(num? e)
         (cond[(integer? (num-int e)) e]
              [else (error "NUMEX num applied to non-racket-integer")])]
        [(bool? e)
         (cond[(boolean? (bool-b e)) e]
              [else (error "NUMEX bool applied to non-racket-boolean")])]
        [(plus? e) 
         (let ([v1 (eval-under-env-c (plus-e1 e) env)]
               [v2 (eval-under-env-c (plus-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (+ (num-int v1) (num-int v2)))]
                    [else (error "NUMEX addition applied to non-number")]))]

        [(minus? e) 
         (let ([v1 (eval-under-env-c (minus-e1 e) env)]
               [v2 (eval-under-env-c (minus-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (- (num-int v1) (num-int v2)))]
                    [else (error "NUMEX subtraction applied to non-number")]))]
        
        [(mult? e) 
         (let ([v1 (eval-under-env-c (mult-e1 e) env)]
               [v2 (eval-under-env-c (mult-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (* (num-int v1) (num-int v2)))]
                    [else (error "NUMEX multiplication applied to non-number")]))]

        [(div? e) 
         (let ([v1 (eval-under-env-c (div-e1 e) env)]
               [v2 (eval-under-env-c (div-e2 e) env)])
               (cond[(and (num? v1)(num? v2)) (num (quotient (num-int v1) (num-int v2)))] ;we only need the int value not float!
                    [else (error "NUMEX divion applied to non-number")]))]

        [(neg? e) 
         (let ([v1 (eval-under-env-c (neg-e1 e) env)])
           (cond [(num? v1)(num (- 0 (num-int v1)))] ;return -v(if v is a num)
                 [(bool? v1)
                  (cond[(equal? (bool-b v1) #t) (bool #f)]
                       [(equal? (bool-b v1) #f) (bool #t)])] ;negate v(if v is a bool)
                 [else (error "NUMEX negation applied to non-number")]))]

        ;short circuiting added
        [(andalso? e) 
         (let ([v1 (eval-under-env-c (andalso-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #f) v1]
                                [else (let ([v2 (eval-under-env-c (andalso-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX conjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env-c (andalso-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX conjunction applied to non-number")]))]))]

        ;short circuiting added
        [(orelse? e) 
         (let ([v1 (eval-under-env-c (orelse-e1 e) env)])
           (cond[(bool? v1)(cond[(equal? (bool-b v1) #t) v1]
                                [else (let ([v2 (eval-under-env-c (orelse-e2 e) env)])
                                      (cond[(bool? v2) v2]
                                           [else (error "NUMEX conjunction applied to non-number")]))])]
                [else (let ([v2 (eval-under-env-c (orelse-e2 e) env)])
                      (cond[(bool? v2) v2]
                           [else (error "NUMEX disjunction applied to non-number")]))]))]

        [(cnd? e) 
         (let ([v1 (eval-under-env-c (cnd-e1 e) env)])
           (if (bool? v1)
               (cond[(equal? (bool-b v1) #t)(let ([v2 (eval-under-env-c (cnd-e2 e) env)]) v2)]
                    [(equal? (bool-b v1) #f)(let ([v3 (eval-under-env-c (cnd-e3 e) env)]) v3)])
               (error "NUMEX condition applied to non-boolean")))]

        [(iseq? e) 
         (let ([v1 (eval-under-env-c (iseq-e1 e) env)]
               [v2 (eval-under-env-c (iseq-e2 e) env)])
           (cond[(and (or (bool? v1) (num? v1))(or (bool? v2) (num? v2)))(cond[(and (bool? v1) (bool? v2))(cond[(equal? (bool-b v1) (bool-b v2))(bool #t)]
                                                                                                               [else (bool #f)])]
                                                                              [(and (num? v1) (num? v2))(cond[(equal? (num-int v1) (num-int v2))(bool #t)]
                                                                                                             [else (bool #f)])]
                                                                              [else (bool #f)])]
                [else (error "NUMEX equality is applied to something other than non-booleans or non-numbers")]))]
        
        [(ifnzero? e) 
         (let ([v1 (eval-under-env-c (ifnzero-e1 e) env)])
           (if (num? v1)
               (cond[(not (equal? (num-int v1) 0))(let ([v2 (eval-under-env-c (ifnzero-e2 e) env)]) v2)]
                    [(equal? (num-int v1) 0)(let ([v3 (eval-under-env-c (ifnzero-e3 e) env)]) v3)])
               (error "NUMEX ifnotzero condition applied to non-number")))]

        [(ifleq? e) 
         (let ([v1 (eval-under-env-c (ifleq-e1 e) env)]
               [v2 (eval-under-env-c (ifleq-e2 e) env)])
           (if (and (num? v1) (num? v2))
               (cond[(> (num-int v1) (num-int v2))(let ([v4 (eval-under-env-c (ifleq-e4 e) env)]) v4)]
                    [(not (> (num-int v1) (num-int v2)))(let ([v3 (eval-under-env-c (ifleq-e3 e) env)]) v3)])
           (error "NUMEX ifleq condition applied to non-numbers")))]

        [(lam? e) 
         (closure env e)]

        [(apply? e)
          (let ([fun-closure (eval-under-env-c (apply-funexp e) env)]) ;evaluating funexp in apply
            ;our funexp is either a closure, or a lam
            (cond[(closure? fun-closure) (let ([fun-def (closure-f fun-closure)]) ;if it is a closure, then 
                                       (let ([eval-actual (eval-under-env-c (apply-actual e) env)])
                                             (cond[(lam? fun-def)(eval-under-env-c (lam-body fun-def) (cons (cons (lam-formal fun-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt fun-def) fun-closure) (closure-env fun-closure))))] ;evaluate lam-body under this new enviroment
                                                  [else (error "closure function isn't lam")])))]

                 [(lam? fun-closure) (let* ([lam-closure (eval-under-env-c fun-closure env)] ;first we evaluate fun-closure to lam-closure
                                           [lam-def (closure-f lam-closure)]) ;if it is a closure, then 
                                       (let ([eval-actual (eval-under-env-c (apply-actual e) env)])
                                             (cond[(lam? lam-def)(eval-under-env-c (lam-body lam-def) (cons (cons (lam-formal lam-def) eval-actual)
                                                                                          (cons (cons (lam-nameopt lam-def) lam-closure) (closure-env lam-closure))))] ;evaluate lam-body under this new enviroment
                                                  [else (error "closure function isn't lam")])))]
                 [else (error (format "NUMEX lam apply invalid"))]))]
        
        [(with? e)
         (let ([v1 (eval-under-env-c (with-e1 e) env)])
           ; s is either a string or null(anonymous)
           (cond[(string? (with-s e)) (eval-under-env-c (with-e2 e) (cons (cons (with-s e) v1) env))]
                [(null?   (with-s e)) (eval-under-env-c (with-e2 e) (cons v1 env))];evaluate e2 with a new enviroment which is (cons v1 env)
                [else (error "NUMEX with applied to non-string")]))]

        [(apair? e) 
         (let ([v1 (eval-under-env-c (apair-e1 e) env)]
               [v2 (eval-under-env-c (apair-e2 e) env)])
           (apair v1 v2))] ;it's that simple!

        [(1st? e) 
         (let ([v1 (eval-under-env-c (1st-e1 e) env)])
           (if (apair? v1)
               (apair-e1 v1)
               (error "NUMEX 1st applied to non-apair")))]

        [(2nd? e) 
         (let ([v1 (eval-under-env-c (2nd-e1 e) env)])
           (if (apair? v1)
               (apair-e2 v1)
               (error "NUMEX 2nd applied to non-apair")))]

        [(munit? e) (munit)] ;just like that!

        [(ismunit? e)
         (let ([v1 (eval-under-env-c (ismunit-e1 e) env)])
           (cond[(munit? v1)(bool #t)]
                [else (bool #f)]))]

        [(closure? e) e] ;that seems all there is needed!:)

        [(letrec? e)         
               (eval-under-env-c (letrec-e3 e) (cons (cons (letrec-s1 e) (letrec-e1 e)) (cons (cons (letrec-s2 e) (letrec-e2 e)) env)))] ;evaluate e3 under this new enviroment (looks easy but it's not!)

        [(key? e)
         (let ([ex (eval-under-env-c (key-e e) env)])
               (cond[(string? (key-s e)) e]
                    [else (error "key is not a string")]))]

        [(record? e)
         (let ([k (eval-under-env-c (record-k e) env)]
               [mr (eval-under-env-c (record-mr e) env)])
               (cond[(key? k) (cond[(or (munit? (eval-exp mr)) (record? mr)) (record k mr)] ;gives back the record
                                   [else (error "value of record invalid")])]
                [else (error "key invalid")]))]

        [(value? e)
         (let ([rec (eval-under-env-c (value-r e) env)])
               (cond[(and (string? (value-s e)) (record? rec))
                 (define (find-key goal-str rec)
                 (let ([key-str (key-s (record-k rec))] ;string of record
                       [key-val (key-e (record-k rec))] ;value of record
                       [next-rec (record-mr rec)]) ;next record
                       (cond[(equal? goal-str key-str) key-val]
                            [(munit? (eval-exp next-rec)) (munit)]
                            [else (find-key goal-str next-rec)])))(find-key (value-s e) rec)]
                    [else (error "NUMEX value applied to non-string")]))]

        [(fun-challenge? e)
         (closure (remove-boundvars env (fun-challenge-freevars e)) e)]

        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))

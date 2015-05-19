; for compilation
#lang r5rs

;; 環境から変数と値のペアを取り出す
(define (defined x e)
  (if (null? e) #f
      (or (defined-frame x (car e))
          (defined x (cdr e)))))
(define (defined-frame x f)
  (cond ((null? f) #f)
        ((eq? x (caar f)) (car f))
        (else (defined-frame x (cdr f)))))

(define (add-variable x e)
  (if (null? (cdr e))
      (let ((t (cons x 0)))
        (begin (set-car! e (cons t (car e)))
               t))
      (add-variable x (cdr e))))




;; その他関数
(define (forall pred l)
  (if (null? l) #t
      (and (pred (car l)) (forall pred (cdr l)))))

(define (error-disp c . mes)
  (define (iter ml)
    (if (null? ml)
        (begin (newline) #f)
        (begin (display (car ml)) (iter (cdr ml)))))
  (define (context x)
    (if (symbol? x)
        (display x)
        (begin
          (context (cdr x))
          (display " -> ")
          (display (car x)))))
  (display "In : ")
  (context c)
  (newline)
  (iter mes))

(define (one-list? t)
  (and (pair? t) (null? (cdr t))))

(define (<> t1 t2) (not (= t1 t2)))


;; 構文チェックのための関数
(define (keyword? x)
  (and (symbol? x)
       (in? x keywords)))
(define (variable? x)
  (and (symbol? x)
       (not (in? x keywords))))

(define macros
  '(<- <-- clear sharp call display))

(define keywords
  (append '(def begin sub1 add1 nzero? if) macros))
(define (in? x l)
  (if (null? l)
      #f
      (or (eq? x (car l))
          (in? x (cdr l)))))


;;-------------------------------------------------------------------------------------------

;; 静的検査--構文検査＋型検査
(define (static-check t e)
  (and (syntax-check-program t 'global)
       (type-check-program t (cons '() e) 'global)))

;; 構文検査
(define (syntax-check-program t c)
  (cond ((not (list? t)) (error-disp c "syntax : all terms must be list forms, but given : " t))
        ((null? t) (error-disp c "syntax : program must be a 'begin sequence or a command, but given : " t))
        ((eq? 'begin (car t)) (syntax-check-begin (cdr t) c))
        (else (syntax-check-command t c))))

(define (syntax-check-begin t c)
  (cond ((not (list? t)) (error-disp c "syntax : all definitions/commands must be list forms, but given : " t))
        ((null? t) #t)
        ((def? (car t)) (and (syntax-check-def (cdar t) c) (syntax-check-begin (cdr t) c)))
        (else (syntax-check-commands t c))))

(define (syntax-check-commands t c)
  (if (null? t) #t
      (and (syntax-check-command (car t) c)
           (syntax-check-commands (cdr t) c))))

(define (syntax-check-def t c)
  (cond ((not (pair? t)) (error-disp c "syntax : definition must be a variable declaration or a procedure declaration, but given : " t))
        ((symbol? (car t))
         (cond ((not (null? (cdr t))) (error-disp c "syntax : variable declaration must have only one variable name, but given : " t))
               ((keyword? (car t)) (error-disp c "syntax : keywords cannot be used as variable names, but " (car t) " is used"))
               (else #t)))
        ((and (pair? (car t)) (list? (car t))
              (forall symbol? (car t)))
         (cond ((keyword? (caar t)) (error-disp c "syntax : keywords cannot be used as procedure names, but " (caar t) " is used"))
               ((forall (lambda (x) (variable? x)) (cdar t))
                (cond ((not (list? (cdr t)))
                       (error-disp c "syntax : procedure declaration format must be declared as list, but " (caar t) " is not"))
                      ((one-list? (cdr t)) (syntax-check-program (cadr t) (cons (caar t) c)))
                      (else
                       (error-disp c "syntax : procedure declaration format is not valid (body must be a single program), but " (caar t) " is declared with " (length (cdr t)) "(wrapping a body in 'begin' may solve the problem)"))))
               (else (error-disp c "syntax : keywords cannot be used as arguments, but " (caar t) " is used"))))
        (else
         (error-disp c "syntax : procedure declaration format is not valid"))))

(define (syntax-check-command t c)
  (cond ((not (list? t)) (error-disp c "syntax : all commands must be list forms"))
        ((null? t) (error-disp c "syntax : no command is described"))
        ((or (add1? t) (sub1? t))
         (if (or (not (one-list? (cdr t)))
                 (not (variable? (cadr t))))
             (error-disp c "syntax : add1/sub1 get only one variable, but given" (cdr t))
             #t))
        ((if? t)
         (cond ((< (length t) 3)
                (error-disp c "syntax : if statement has too less sub-statements"))
               ((> (length t) 4)
                (error-disp c "syntax : if statement has more sub-statements than 4"))
               ((not (list? (cadr t)))
                (error-disp c "syntax : condtion must be a list, but given : " t))
               ((not (= (length (cadr t)) 2))
                (error-disp c "syntax : condtion must be (nzero? var), but given : " (cadr t)))
               ((not (eq? 'nzero? (caadr t)))
                (error-disp c "syntax : condtion must be (nzero? var), but given : " (cadr t)))
               ((not (variable? (cadadr t))) (error-disp c "syntax : argument of 'nzero?' must be a variable, but given : " (cadadr t)))
               (else (forall (lambda (x) (syntax-check-program x c)) (cddr t)))))
        ((macro? t)
         (syntax-check-macro t c))
        (else
         (cond ((null? t) (error-disp c "syntax : nothing is called"))
               ((and (variable? (car t)) (one-list? t)) #t)
               ((variable? (car t))
                (error-disp c "syntax : procedure call does not support arguments ; use sharp or call macro instead"))
               (else (error-disp c "syntax : not procedure element is used in procedure call, given : " (car t)))))))

(define (syntax-check-macro t c)
  (cond ((eq? '<- (car t))
         (cond ((<> (length t) 3) (error-disp c "syntax : <- macro must get two arguments, but given " (- (length t) 1)))
               ((not (variable? (cadr t)))
                (error-disp c "syntax : <- macro must get two variables as arguments, but given " (cadr t) " as a first argument"))
               ((not (variable? (caddr t)))
                (error-disp c "syntax : <- macro must get two variables as arguments, but given " (caddr t) " as a second argument"))
               (else #t)))
        ((eq? '<-- (car t))
         (cond ((<> (length t) 3) (error-disp c "syntax : <-- macro must get two arguments, but given " (- (length t) 1)))
               ((not (variable? (cadr t)))
                (error-disp c "syntax : <-- macro must get a variable as a first argument, but given : " (cadr t)))
               ((not (and (integer? (caddr t)) (>= (caddr t) 0)))
                (error-disp c "syntax : <-- macro must get a natural number a second argument, but given : " (caddr t)))
               (else #t)))
        ((eq? 'clear (car t))
         (cond ((<> (length t) 2) (error-disp c "syntax : clear macro must get one argument, but given " (- (length t) 1)))
               ((variable? (cadr t)) #t)
               (else (error-disp c "syntax : clear macro must get one variable as an argument, but given : " (cadr t)))))
        ((eq? 'sharp (car t))
         (cond ((null? (cdr t)) (error-disp c "syntax : no procedure is executed in sharp macro"))
               ((not (variable? (cadr t))) (error-disp c "syntax : sharp must get a procedure name as a first argument, but given : " (cadr t)))
               ((forall (lambda (x) (or (variable? x) (and (integer? x) (>= x 0)))) (cddr t)) #t)
               (else (error-disp c "syntax : one of arguments is not a name nor a natural number"))))
        ((eq? 'call (car t))
         (cond ((null? (cdr t)) (error-disp c "syntax : no procedure is executed in call macro"))
               ((not (variable? (cadr t))) (error-disp c "syntax : sharp must get a procedure name as a first argument, but given : " (cadr t)))
               ((forall (lambda (x) (or (variable? x) (and (integer? x) (>= x 0)))) (cddr t)) #t)
               (else (error-disp c "syntax : one of arguments is not a name nor a natural number"))))
        ((eq? 'display (car t))
         (if (null? (cdr t))
             #t
             (if (null? (cddr t))
                 #t
                 (error-disp c "syntax : display macro get at most 1 arguments"))))
        (else (error-disp c "syntax : something wrong, but what happen? : " t))))




;;-----------------------------------------------------------------------------------

;; 構文検査後の判定手段--軽量判定
(define (top-symbol? t x)
  (and (pair? t)
       (eq? x (car t))))

(define (def? t) (top-symbol? t 'def))

(define (begin? t) (top-symbol? t 'begin))

(define (add1? t) (top-symbol? t 'add1))

(define (sub1? t) (top-symbol? t 'sub1))

(define (if? t) (top-symbol? t 'if))

(define (macro? t)
  (and (pair? t)
       (in? (car t) macros)))


;; 型検査
(define (proc-frame? t)
  (not (integer? (cdr t))))
(define (proc-variable? x e)
  (let ((t (defined x e)))
    (and t (proc-frame? (cdr t)))))

(define (num-variable? x e)
  (let ((t (defined x e)))
    (or (not t) (integer? (cdr t)))))

(define (type-check-program t e c)
  (if (begin? t)
      (type-check-begin (cdr t) e c)
      (type-check-command t e c)))

(define (type-check-begin t e c)
  (cond ((null? t) (type-check-proc (car e) c))
        ((def? (car t))
         (begin (eval-def (cdar t) e) (type-check-begin (cdr t) e c)))
        (else (and (type-check-proc (car e) c)
                   (type-check-commands t e c)))))

(define (type-check-proc e c)
  (cond ((null? e) #t)
        ((number? (cdar e)) (type-check-proc (cdr e) c))
        (else
         (let ((env (cadar e))
               (params (caddar e))
               (body (car (cdddar e))))
           (and (type-check-program body (entry-params params env) (cons (caar e) c))
                (type-check-proc (cdr e) c))))))

(define (entry-params params env)
  (cons (map (lambda (x) (cons x 0)) params) env))

        
(define (type-check-commands t e c)
  (if (null? t)
      #t
      (and (type-check-command (car t) e c)
           (type-check-commands (cdr t) e c))))

(define (type-check-command t e c)
  (cond ((or (add1? t) (sub1? t))
         (if (num-variable? (cadr t) e)
             #t
             (error-disp c "type : add1/sub1 must get a variable as an argument, but given an undefined variable or a procedure name : " (cadr t))))
        ((if? t)
         (if (num-variable? (cadadr t) e)
             (forall (lambda (x) (type-check-program x e c)) (cddr t))
             (error-disp c "type : nzero? must get a variable as an argument, but given an undefined variable or a procedure name : " (cadadr t))))
        ((macro? t)
         (type-check-macro t e c))
        (else
         (let ((proc (defined (car t) e)))
           (cond ((not proc)
                  (error-disp c "type : " (car t) " is not defined"))
                 ((not (proc-frame? proc))
                  (error-disp c "type : " (car t) " is not a procedure name, but a variable"))
                 (else #t))))))

(define (type-check-macro t e c)
  (cond ((eq? '<- (car t))
         (if (forall (lambda (x) (num-variable? x e)) (cdr t))
             #t
             (error-disp c "type : <- must get two variables")))
        ((eq? '<-- (car t))
         (if (num-variable? (cadr t) e)
             #t
             (error-disp c "type : <-- must get a variable and a natural number")))
        ((eq? 'clear (car t))
         (if (num-variable? (cadr t) e)
             #t
             (error-disp c "type : clear must get a variable, but given an undefined variable or a procedure name : " (cadr t))))
        ((eq? 'sharp (car t))
         (cond ((not (proc-variable? (cadr t) e))
                (error-disp c "type : sharp must get a procedure name as a first argument, but given : " (cadr t) " (a variable or undefined)"))
               ((not (forall (lambda (x) (or (not (variable? x)) (num-variable? x e))) (cddr t)))
                (error-disp c "type : sharp must get variables or natural numbers as second or later arguments"))
               ((= (length (caddr (defined (cadr t) e))) 0)
                #t)
               (else
                (error-disp c "type : sharp must call procedures having no parameters, but " (cadr t) " has parameters"))))
        ((eq? 'call (car t))
         (let ((proc (defined (cadr t) e)))
           (cond ((not proc)
                  (error-disp c "type : call must get a procedure name as a first argument, but given : " (cadr t) " (undefined)"))
                 ((not (proc-frame? proc))
                  (error-disp c "type : call must get a procedure name as a first argument, but given : " (cadr t) " (a variable)"))
                 ((not (forall (lambda (x) (or (not (variable? x)) (num-variable? x e))) (cddr t)))
                  (error-disp c "type : call must get variables or natural numbers as second or later arguments"))
                 ((= (length (cddr t)) (length (caddr proc)))
                  #t) ;; TODO 全てのXnがこの環境で定義されているかを確かめる。forall？
                 (else
                  (error-disp c "type : the number of parameters of " (cadr t) " (" (length (caddr proc)) " and that of the arguments " (length (cddr t)) " are missmatch")))))
        ((eq? 'display (car t))
           (if (null? (cdr t))
               #t
               (if (symbol? (cadr t))
                   (if (num-variable? (cadr t) e)
                       #t
                       (error-disp "type : display must get a variable if the argument is a symbol, but an undefined variable or a procedure name :" (cadr t)))
                   #t)))
        (else (error-disp c "type : what happened?"))))



;;-----------------------------------------------------------------------------------

;; 環境出力（自動の出力だと分かりづらい、手続きが環境を持つためループするので環境をスキップする）
(define (display-env e)
  (define (display-env2 e)
    (if (null? e)
        (newline)
        (begin (display "{") (newline) (display-frame (car e)) (display "}") (newline) (display-env2 (cdr e)))))
  (display "Current-environment :")
  (newline)
  (display-env2 e))
(define (display-frame e)
  (if (null? e) e (begin (display-cell (car e)) (display-frame (cdr e)))))
  
(define (display-cell e)
  (begin
    (display "(")
    (if (number? (cdr e))
        (begin (display "value ") (display (car e)) (display " : ") (display (cdr e)))
        (begin (display "proc ") (display (car e)) (display " ") (display (caddr e)) (display " : ") (display (cadddr e))))
    (display ")") (newline)))


;;-----------------------------------------------------------------------------------

;; 外部から項を読み込んで空の環境で実行
(define (execute)
  (execute-term (read)))

;; 与えられた項を空の環境で実行
(define (execute-term t)
  (execute-term-env t (list '() '())))

;; 外部から項を読み込んで与えられた環境で実行
(define (execute-env e)
  (execute-term-env (read) e))

;; 与えられた項を与えられた環境で実行
(define (execute-term-env t e)
  (if (static-check t e)
      (begin (eval-program t e)
             (display-env e))
      (display "abort with syntax error")))

;; 外部から与えられた名前のファイルから項を読み込んで空の環境で実行
(define (execute-input)
  (execute-file (symbol->string (read))))

;; ファイルから項を読み込んで空の環境で実行
(define (execute-file n)
  (execute-file-env n (list '() '())))

;; ファイルから項を読み込んで与えられた環境で実行
(define (execute-file-env n e)
  (execute-term-env (call-with-input-file n read) e))



;;-----------------------------------------------------------------------------------

;; 評価関数
(define (eval-program t e)
  (cond ((begin? t)
         (eval-begin (cdr t) e))
        (else (eval-command t e))))

(define (eval-begin t e)
  (cond ((null? t) t)
        ((def? (car t))
         (begin (eval-def (cdar t) e)
                (eval-begin (cdr t) e)))
        (else (eval-commands t e))))

;; beginのdef列終了後
(define (eval-commands t e)
  (cond ((null? t) e)
        ((one-list? t)
         (eval-command (car t) e))
        (else (begin (eval-command (car t) e)
                     (eval-commands (cdr t) e)))))

(define (eval-def t e)
  (cond ((and (one-list? t))
         (set-car! e (cons (cons (car t) 0) (car e))))
        (else (set-car! e (cons (list (caar t) e (cdar t) (cadr t)) (car e))))))

(define (eval-command t e)
  (cond ((add1? t)
         (let ((vt (defined (cadr t) e)))
           (set-cdr! vt (+ (cdr vt) 1))))
        ((sub1? t)
         (let ((vt (defined (cadr t) e)))
           (set-cdr! vt (if (= (cdr vt) 0) 0 (- (cdr vt) 1)))))
        ((if? t)
         (let ((vt (defined (cadadr t) e)))
           (if (and vt (<> (cdr vt) 0))
               (eval-program (caddr t) (cons '() e))
               (if (not (null? (cdddr t)))
                   (eval-program (cadddr t) (cons '() e))))))
        ((macro? t) (eval-macro t e))
        (else
         (let ((f (cdr (defined (car t) e))))
           (eval-program (caddr f) (cons '() (car f)))))))

(define (eval-macro t e)
  (cond ((eq? '<- (car t))
         (set-cdr! (defined (cadr t) e) (cdr (defined (caddr t) e))))
        ((eq? '<-- (car t))
         (set-cdr! (defined (cadr t) e) (caddr t)))
        ((eq? 'clear (car t))
         (set-cdr! (defined (cadr t) e) 0))
        ((eq? 'sharp (car t))
         (begin
           (entry-arguments 1 (cddr t) e)
           (let ((f (cdr (defined (cadr t) e))))
             (eval-program (caddr f) (cons '() (car f))))))
        ((eq? 'call (car t))
         (let ((f (cdr (defined (cadr t) e))))
           (eval-program (caddr f) (cons (proc-env (cddr t) (cadr f) e '()) (car f)))))
        ((eq? 'display (car t))
         (if (null? (cdr t))
             (display-env e)
             (begin
              (if (symbol? (cadr t))
                  (begin
                   (display (cadr t))
                   (display " : ")
                   (display (cdr (defined (cadr t) e))))
                  (display (cadr t)))
              (newline))))
        (else (error-disp "what happened?" ))))

(define (entry-arguments n al e)
  (if (null? al)
      #t
      (let ((v (if (integer? (car al)) (car al) (cdr (defined (car al) e))))
            (x (string->symbol (string-append (symbol->string 'X) (number->string n)))))
        (begin (set-cdr! (defined x e) v)
               (entry-arguments (+ n 1) (cdr al) e)))))

(define (proc-env args params e f)
  (if (null? args)
      f
      (let ((v (if (integer? (car args)) (car args) (cdr (defined (car args) e)))))
        (proc-env (cdr args) (cdr params) e
                  (cons (cons (car params) v) f)))))


;;-----------------------------------------------------------------------------------

;; macro-expansion
;; to-be-developed


;;-----------------------------------------------------------------------------------

;; for executable
(execute-file (symbol->string (read)))

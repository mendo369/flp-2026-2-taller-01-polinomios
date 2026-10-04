#lang eopl
;Autores: Luis David Mendoza Manzano 2067621

;; Taller 1 — Polinomios dispersos.
;; Parte 4: Batería de pruebas parametrizada.

(require rackunit)
(require rackunit/text-ui)
(require (prefix-in listas: "polinomios-listas.rkt"))
(require (prefix-in procs:  "polinomios-procedimientos.rkt"))
(require (prefix-in dt:     "polinomios-datatypes.rkt"))

;; Mensajes de error esperados
(define msg-expo   #rx"El exponente debe ser un entero no negativo")
(define msg-coef   #rx"El coeficiente debe ser un numero exacto")
(define msg-no-hay #rx"El polinomio no tiene termino con ese exponente")

;; bateria : string x procedimientos -> test-suite
(define bateria
  (lambda (nombre cero ins coef elim ->lista)
    (let* ((p (ins (ins (ins (cero 'x) 7 0) -3/2 2) 4 5))
           (c (cero 'x)))
      (test-suite nombre
        
        ;; --- Casos funcionales ---
        (test-case "construccion del enunciado"
          (check-equal? (->lista p) '(x (4 . 5) (-3/2 . 2) (7 . 0))))
        
        (test-case "el orden de insercion no importa"
          (check-equal? (->lista (ins (ins (ins c 4 5) -3/2 2) 7 0)) (->lista p))
          (check-equal? (->lista (ins (ins (ins c -3/2 2) 7 0) 4 5)) (->lista p))
          (check-equal? (->lista (ins (ins (ins c 7 0) 4 5) -3/2 2)) (->lista p)))
        
        (test-case "insertar suma coeficientes"
          (check-equal? (->lista (ins p 1 2)) '(x (4 . 5) (-1/2 . 2) (7 . 0))))
        
        (test-case "insertar al inicio, medio y final"
          (check-equal? (->lista (ins p 9 8)) '(x (9 . 8) (4 . 5) (-3/2 . 2) (7 . 0)))
          (check-equal? (->lista (ins p 2 3)) '(x (4 . 5) (2 . 3) (-3/2 . 2) (7 . 0)))
          (check-equal? (->lista (ins p 5 1)) '(x (4 . 5) (-3/2 . 2) (5 . 1) (7 . 0))))
        
        (test-case "suma de enteros y racionales"
          (check-equal? (->lista (ins (ins c 1 3) 1/2 3)) '(x (3/2 . 3)))
          (check-equal? (->lista (ins (ins c 1/2 3) 1/2 3)) '(x (1 . 3))))
        
        (test-case "exponentes grandes (disperso)"
          (check-equal? (->lista (ins (ins c 1 1000) 2 0)) '(x (1 . 1000) (2 . 0))))
        
        (test-case "inmutabilidad del original"
          (ins p 100 7)
          (check-equal? (->lista p) '(x (4 . 5) (-3/2 . 2) (7 . 0))))

        ;; --- Cancelación y Ceros ---
        (test-case "cancelacion de terminos"
          (check-equal? (->lista (ins p 3/2 2)) '(x (4 . 5) (7 . 0)))
          (check-equal? (->lista (ins p -4 5)) '(x (-3/2 . 2) (7 . 0)))
          (check-equal? (->lista (ins p -7 0)) '(x (4 . 5) (-3/2 . 2))))
        
        (test-case "cancelar todo deja polinomio nulo"
          (check-equal? (->lista (ins (ins c 5 2) -5 2)) '(x)))

        (test-case "coeficiente cero no altera"
          (check-equal? (->lista (ins p 0 3)) (->lista p))
          (check-equal? (->lista (ins p 0 2)) (->lista p))
          (check-equal? (->lista (ins c 0 4)) '(x)))

        ;; --- Polinomio Nulo ---
        (test-case "caso base: polinomio nulo"
          (check-equal? (->lista c) '(x))
          (check-equal? (->lista (ins c 7 0)) '(x (7 . 0)))
          (check-exn msg-no-hay (lambda () (coef c 0)))
          (check-exn msg-no-hay (lambda () (elim c 0))))

        ;; --- Errores ---
        (test-case "errores de validacion"
          (check-exn msg-expo (lambda () (ins p 5 -1)))
          (check-exn msg-coef (lambda () (ins p 1.5 2)))
          (check-exn msg-coef (lambda () (ins p 'a 2)))
          (check-exn msg-expo (lambda () (coef p -1)))
          (check-exn msg-no-hay (lambda () (coef p 3)))
          (check-exn msg-no-hay (lambda () (elim p 3))))))))

;; ---- Ejecución de suites ----
(define suite-listas
  (bateria "Listas" listas:polinomio-cero listas:insertar-termino
           listas:coeficiente-de listas:eliminar-termino listas:polinomio->lista))

(define suite-procs
  (bateria "Procedimientos" procs:polinomio-cero procs:insertar-termino
           procs:coeficiente-de procs:eliminar-termino procs:polinomio->lista))

(define suite-dt
  (bateria "Datatypes" dt:polinomio-cero dt:insertar-termino
           dt:coeficiente-de dt:eliminar-termino dt:polinomio->lista))

;; ---- Observadores ----
(define suite-observadores-listas
  (test-suite "Observadores Listas"
    (let ((t (listas:termino (listas:coef-rac -3 2) (listas:expo-nat 2))))
      (test-case "extractores basicos"
        (check-true (listas:termino? t))
        (check-equal? (listas:coef-rac->num (listas:termino->coef t)) -3)
        (check-equal? (listas:expo-nat->k (listas:termino->expo t)) 2)))))

(define suite-observadores-procs
  (test-suite "Observadores Procedimientos"
    (let ((t (procs:termino (procs:coef-rac -3 2) (procs:expo-nat 2))))
      (test-case "extractores basicos"
        (check-true (procs:termino? t))
        (check-equal? (procs:coef-rac->num (procs:termino->coef t)) -3)))))

;; ---- Suma (Datatypes) ----
(define suite-sumar
  (test-suite "Suma Datatypes"
    (let* ((p (dt:insertar-termino (dt:insertar-termino 
                (dt:insertar-termino (dt:polinomio-cero 'x) 7 0) -3/2 2) 4 5))
           (q (dt:insertar-termino (dt:insertar-termino 
                (dt:insertar-termino (dt:polinomio-cero 'x) 2 1) 1/2 2) -4 5))
           (c (dt:polinomio-cero 'x)))
      
      (test-case "ejemplo enunciado"
        (check-equal? (dt:polinomio->lista (dt:sumar p q)) '(x (-1 . 2) (2 . 1) (7 . 0))))
      
      (test-case "cancelacion total"
        (check-equal? (dt:polinomio->lista 
                       (dt:sumar p (dt:insertar-termino (dt:insertar-termino 
                        (dt:insertar-termino c -7 0) 3/2 2) -4 5))) '(x)))
      
      (test-case "neutro y conmutatividad"
        (check-equal? (dt:polinomio->lista (dt:sumar p c)) (dt:polinomio->lista p))
        (check-equal? (dt:polinomio->lista (dt:sumar p q)) 
                      (dt:polinomio->lista (dt:sumar q p))))
      
      (test-case "error variables distintas"
        (check-exn #rx"misma variable" 
                   (lambda () (dt:sumar p (dt:polinomio-cero 'y))))))))

;; ---- Ejecutar todo ----
(run-tests suite-listas)
(run-tests suite-procs)
(run-tests suite-dt)
(run-tests suite-observadores-listas)
(run-tests suite-observadores-procs)
(run-tests suite-sumar)
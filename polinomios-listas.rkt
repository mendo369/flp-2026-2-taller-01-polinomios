#lang eopl
;; Autores: Luis David Mendoza Manzano 2067621
;; Taller 1 — Polinomios dispersos (Representación por listas)

(provide polinomio-cero insertar-termino coeficiente-de eliminar-termino polinomio->lista
         poli poli? poli->var poli->terms nombre-var nombre-var? nombre-var->s
         sin-terminos sin-terminos? mas-terminos mas-terminos? mas-terminos->term mas-terminos->resto
         termino termino? termino->coef termino->expo
         coef-ent coef-ent? coef-ent->n coef-rac coef-rac? coef-rac->num coef-rac->den
         expo-nat expo-nat? expo-nat->k)

;; ====================================================================
;; GRAMÁTICA Y CONSTRUCTORES
;; ====================================================================

;; poli : NombreVar x Terminos -> Polinomio
(define poli (lambda (var terms) (list 'poli var terms)))
(define poli? (lambda (x) (equal? (car x) 'poli)))
(define poli->var (lambda (x) (cadr x)))
(define poli->terms (lambda (x) (caddr x)))

;; nombre-var : Symbol -> NombreVar
(define nombre-var (lambda (s) (list 'nombre-var s)))
(define nombre-var? (lambda (x) (equal? (car x) 'nombre-var)))
(define nombre-var->s (lambda (x) (cadr x)))

;; sin-terminos : () -> Terminos
(define sin-terminos (lambda () (list 'sin-terminos)))
(define sin-terminos? (lambda (x) (equal? (car x) 'sin-terminos)))

;; mas-terminos : Termino x Terminos -> Terminos
(define mas-terminos (lambda (term resto) (list 'mas-terminos term resto)))
(define mas-terminos? (lambda (x) (equal? (car x) 'mas-terminos)))
(define mas-terminos->term (lambda (x) (cadr x)))
(define mas-terminos->resto (lambda (x) (caddr x)))

;; termino : Coeficiente x Exponente -> Termino
(define termino (lambda (coef expo) (list 'termino coef expo)))
(define termino? (lambda (x) (equal? (car x) 'termino)))
(define termino->coef (lambda (x) (cadr x)))
(define termino->expo (lambda (x) (caddr x)))

;; coef-ent : Int -> Coeficiente
(define coef-ent (lambda (n) (list 'coef-ent n)))
(define coef-ent? (lambda (x) (equal? (car x) 'coef-ent)))
(define coef-ent->n (lambda (x) (cadr x)))

;; coef-rac : Int x Int -> Coeficiente
(define coef-rac (lambda (num den) (list 'coef-rac num den)))
(define coef-rac? (lambda (x) (equal? (car x) 'coef-rac)))
(define coef-rac->num (lambda (x) (cadr x)))
(define coef-rac->den (lambda (x) (caddr x)))

;; expo-nat : Nat -> Exponente
(define expo-nat (lambda (k) (list 'expo-nat k)))
(define expo-nat? (lambda (x) (equal? (car x) 'expo-nat)))
(define expo-nat->k (lambda (x) (cadr x)))

;; ====================================================================
;; UTILIDADES DE CONVERSIÓN Y VALIDACIÓN
;; ====================================================================

;; coef->numero : Coeficiente -> Number
;; Convierte representación abstracta a número exacto de Racket.
(define coef->numero
  (lambda (c)
    (if (coef-ent? c)
        (coef-ent->n c)
        (/ (coef-rac->num c) (coef-rac->den c)))))

;; numero->coef : Number -> Coeficiente
;; Construye coef-ent si es entero, coef-rac otherwise.
(define numero->coef
  (lambda (n)
    (if (integer? n)
        (coef-ent n)
        (coef-rac (numerator n) (denominator n)))))

;; termino->exponente : Termino -> Nat
(define termino->exponente
  (lambda (t)
    (expo-nat->k (termino->expo t))))

;; termino->numero : Termino -> Number
(define termino->numero
  (lambda (t)
    (coef->numero (termino->coef t))))

;; exponente-valido? : Any -> Bool
(define exponente-valido?
  (lambda (e)
    (and (integer? e) (exact? e) (>= e 0))))

;; coeficiente-valido? : Any -> Bool
(define coeficiente-valido?
  (lambda (c)
    (and (number? c) (exact? c))))

;; ====================================================================
;; INTERFAZ DEL TAD
;; ====================================================================

;; polinomio-cero : Symbol -> Polinomio
;; Crea polinomio nulo. Error si variable no es símbolo.
(define polinomio-cero
  (lambda (variable)
    (if (symbol? variable)
        (poli (nombre-var variable) (sin-terminos))
        (eopl:error 'polinomio-cero "La variable debe ser un simbolo"))))

;; insertar-en-terminos : Terminos x Number x Nat -> Terminos
;; Inserta término manteniendo orden descendente por exponente.
;; Fusiona coeficientes si el exponente existe; elimina si suma es cero.
(define insertar-en-terminos
  (lambda (ts c e)
    (if (sin-terminos? ts)
        (mas-terminos (termino (numero->coef c) (expo-nat e)) ts)
        (let ((t (mas-terminos->term ts))
              (resto (mas-terminos->resto ts)))
          (let ((e0 (termino->exponente t)))
            (cond
              ((> e e0)
               (mas-terminos (termino (numero->coef c) (expo-nat e)) ts))
              ((= e e0)
               (let ((s (+ (termino->numero t) c)))
                 (if (zero? s)
                     resto
                     (mas-terminos (termino (numero->coef s) (expo-nat e))
                                   resto))))
              (else
               (mas-terminos t (insertar-en-terminos resto c e)))))))))

;; insertar-termino : Polinomio x Number x Nat -> Polinomio
;; Retorna p + c*x^e. Ignora si c=0. Valida tipos.
(define insertar-termino
  (lambda (p c e)
    (cond
      ((not (exponente-valido? e))
       (eopl:error 'insertar-termino "El exponente debe ser un entero no negativo"))
      ((not (coeficiente-valido? c))
       (eopl:error 'insertar-termino "El coeficiente debe ser un numero exacto"))
      ((zero? c) p)
      (else
       (poli (poli->var p)
             (insertar-en-terminos (poli->terms p) c e))))))

;; buscar-coeficiente : Terminos x Nat -> Number
;; Busca coeficiente de exponente e. Aprovecha orden para early exit.
;; Error si no existe.
(define buscar-coeficiente
  (lambda (ts e)
    (if (sin-terminos? ts)
        (eopl:error 'coeficiente-de "El polinomio no tiene termino con ese exponente")
        (let ((t (mas-terminos->term ts)))
          (let ((e0 (termino->exponente t)))
            (cond
              ((= e e0) (termino->numero t))
              ((> e e0)
               (eopl:error 'coeficiente-de "El polinomio no tiene termino con ese exponente"))
              (else (buscar-coeficiente (mas-terminos->resto ts) e))))))))

;; coeficiente-de : Polinomio x Nat -> Number
;; Retorna coeficiente del término de exponente e.
(define coeficiente-de
  (lambda (p e)
    (if (exponente-valido? e)
        (buscar-coeficiente (poli->terms p) e)
        (eopl:error 'coeficiente-de "El exponente debe ser un entero no negativo"))))

;; quitar-de-terminos : Terminos x Nat -> Terminos
;; Elimina término de exponente e. Error si no existe.
(define quitar-de-terminos
  (lambda (ts e)
    (if (sin-terminos? ts)
        (eopl:error 'eliminar-termino "El polinomio no tiene termino con ese exponente")
        (let ((t (mas-terminos->term ts))
              (resto (mas-terminos->resto ts)))
          (let ((e0 (termino->exponente t)))
            (cond
              ((= e e0) resto)
              ((> e e0)
               (eopl:error 'eliminar-termino "El polinomio no tiene termino con ese exponente"))
              (else (mas-terminos t (quitar-de-terminos resto e)))))))))

;; eliminar-termino : Polinomio x Nat -> Polinomio
;; Retorna polinomio sin el término de exponente e.
(define eliminar-termino
  (lambda (p e)
    (if (exponente-valido? e)
        (poli (poli->var p) (quitar-de-terminos (poli->terms p) e))
        (eopl:error 'eliminar-termino "El exponente debe ser un entero no negativo"))))

;; ====================================================================
;; UTILIDADES DE VISUALIZACIÓN
;; ====================================================================

;; terminos->lista : Terminos -> List[(Number . Nat)]
(define terminos->lista
  (lambda (ts)
    (if (sin-terminos? ts)
        '()
        (let ((t (mas-terminos->term ts)))
          (cons (cons (termino->numero t) (termino->exponente t))
                (terminos->lista (mas-terminos->resto ts)))))))

;; polinomio->lista : Polinomio -> List[Symbol | (Number . Nat)]
;; Representación concreta para debugging/testing.
(define polinomio->lista
  (lambda (p)
    (cons (nombre-var->s (poli->var p))
          (terminos->lista (poli->terms p)))))
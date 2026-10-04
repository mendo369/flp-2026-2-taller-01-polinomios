#lang eopl
;; Autores: Luis David Mendoza Manzano 2067621
;; Taller 1 — Polinomios dispersos (Representación con define-datatype)

(provide polinomio-cero insertar-termino coeficiente-de eliminar-termino sumar
         polinomio->lista
         poli sin-terminos mas-terminos termino coef-ent coef-rac expo-nat
         nombre-var
         polinomio? variable? terminos? termino-tad? coeficiente? exponente?)

;; ====================================================================
;; GRAMÁTICA (define-datatype)
;; Nota: 'termino-tad' se usa como tipo para evitar colisión con la variante 'termino'.
;; ====================================================================

;; exponente ::= expo-nat(k: Int >= 0)
(define-datatype exponente exponente?
  (expo-nat (k (lambda (k) (and (integer? k) (>= k 0))))))

;; coeficiente ::= coef-ent(n: Int) | coef-rac(num: Int, den: Int > 0)
(define-datatype coeficiente coeficiente?
  (coef-ent (n integer?))
  (coef-rac (num integer?)
            (den (lambda (n) (and (integer? n) (> n 0))))))

;; termino-tad ::= termino(coef: Coeficiente, expo: Exponente)
(define-datatype termino-tad termino-tad?
  (termino (coef coeficiente?) (expo exponente?)))

;; terminos ::= sin-terminos() | mas-terminos(term: TerminoTad, resto: Terminos)
(define-datatype terminos terminos?
  (sin-terminos)
  (mas-terminos (term termino-tad?) (resto terminos?)))

;; variable ::= nombre-var(s: Symbol)
(define-datatype variable variable?
  (nombre-var (s symbol?)))

;; polinomio ::= poli(var: Variable, terms: Terminos)
(define-datatype polinomio polinomio?
  (poli (var variable?) (terms terminos?)))

;; ====================================================================
;; UTILIDADES DE CONVERSIÓN Y VALIDACIÓN
;; ====================================================================

;; coef->numero : Coeficiente -> Number
(define coef->numero
  (lambda (c)
    (cases coeficiente c
      (coef-ent (n) n)
      (coef-rac (num den) (/ num den)))))

;; numero->coef : Number -> Coeficiente
(define numero->coef
  (lambda (n)
    (if (integer? n)
        (coef-ent n)
        (coef-rac (numerator n) (denominator n)))))

;; termino->exponente : TerminoTad -> Nat
(define termino->exponente
  (lambda (t)
    (cases termino-tad t
      (termino (coef expo)
        (cases exponente expo
          (expo-nat (k) k))))))

;; termino->numero : TerminoTad -> Number
(define termino->numero
  (lambda (t)
    (cases termino-tad t
      (termino (coef expo) (coef->numero coef)))))

;; variable->simbolo : Variable -> Symbol
(define variable->simbolo
  (lambda (v)
    (cases variable v
      (nombre-var (s) s))))

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
(define polinomio-cero
  (lambda (variable)
    (if (symbol? variable)
        (poli (nombre-var variable) (sin-terminos))
        (eopl:error 'polinomio-cero "La variable debe ser un simbolo"))))

;; insertar-en-terminos : Terminos x Number x Nat -> Terminos
;; Inserta término manteniendo orden descendente por exponente.
(define insertar-en-terminos
  (lambda (ts c e)
    (cases terminos ts
      (sin-terminos ()
        (mas-terminos (termino (numero->coef c) (expo-nat e)) ts))
      (mas-terminos (t resto)
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
(define insertar-termino
  (lambda (p c e)
    (cond
      ((not (exponente-valido? e))
       (eopl:error 'insertar-termino "El exponente debe ser un entero no negativo"))
      ((not (coeficiente-valido? c))
       (eopl:error 'insertar-termino "El coeficiente debe ser un numero exacto"))
      ((zero? c) p)
      (else
       (cases polinomio p
         (poli (var terms)
           (poli var (insertar-en-terminos terms c e))))))))

;; buscar-coeficiente : Terminos x Nat -> Number
(define buscar-coeficiente
  (lambda (ts e)
    (cases terminos ts
      (sin-terminos ()
        (eopl:error 'coeficiente-de "El polinomio no tiene termino con ese exponente"))
      (mas-terminos (t resto)
        (let ((e0 (termino->exponente t)))
          (cond
            ((= e e0) (termino->numero t))
            ((> e e0)
             (eopl:error 'coeficiente-de "El polinomio no tiene termino con ese exponente"))
            (else (buscar-coeficiente resto e))))))))

;; coeficiente-de : Polinomio x Nat -> Number
(define coeficiente-de
  (lambda (p e)
    (if (exponente-valido? e)
        (cases polinomio p
          (poli (var terms) (buscar-coeficiente terms e)))
        (eopl:error 'coeficiente-de "El exponente debe ser un entero no negativo"))))

;; quitar-de-terminos : Terminos x Nat -> Terminos
(define quitar-de-terminos
  (lambda (ts e)
    (cases terminos ts
      (sin-terminos ()
        (eopl:error 'eliminar-termino "El polinomio no tiene termino con ese exponente"))
      (mas-terminos (t resto)
        (let ((e0 (termino->exponente t)))
          (cond
            ((= e e0) resto)
            ((> e e0)
             (eopl:error 'eliminar-termino "El polinomio no tiene termino con ese exponente"))
            (else (mas-terminos t (quitar-de-terminos resto e)))))))))

;; eliminar-termino : Polinomio x Nat -> Polinomio
(define eliminar-termino
  (lambda (p e)
    (if (exponente-valido? e)
        (cases polinomio p
          (poli (var terms) (poli var (quitar-de-terminos terms e))))
        (eopl:error 'eliminar-termino "El exponente debe ser un entero no negativo"))))

;; sumar-terminos : Terminos x Terminos -> Terminos
;; Merge paralelo de listas ordenadas. Cancela términos si suma es cero.
(define sumar-terminos
  (lambda (a b)
    (cases terminos a
      (sin-terminos () b)
      (mas-terminos (ta ra)
        (cases terminos b
          (sin-terminos () a)
          (mas-terminos (tb rb)
            (let ((ea (termino->exponente ta))
                  (eb (termino->exponente tb)))
              (cond
                ((> ea eb) (mas-terminos ta (sumar-terminos ra b)))
                ((< ea eb) (mas-terminos tb (sumar-terminos a rb)))
                (else
                 (let ((s (+ (termino->numero ta) (termino->numero tb))))
                   (if (zero? s)
                       (sumar-terminos ra rb)
                       (mas-terminos (termino (numero->coef s) (expo-nat ea))
                                     (sumar-terminos ra rb)))))))))))))

;; sumar : Polinomio x Polinomio -> Polinomio
;; Suma dos polinomios. Error si variables difieren.
(define sumar
  (lambda (p q)
    (cases polinomio p
      (poli (v1 t1)
        (cases polinomio q
          (poli (v2 t2)
            (if (eq? (variable->simbolo v1) (variable->simbolo v2))
                (poli v1 (sumar-terminos t1 t2))
                (eopl:error 'sumar "Los polinomios deben estar en la misma variable"))))))))

;; ====================================================================
;; UTILIDADES DE VISUALIZACIÓN
;; ====================================================================

;; terminos->lista : Terminos -> List[(Number . Nat)]
(define terminos->lista
  (lambda (ts)
    (cases terminos ts
      (sin-terminos () '())
      (mas-terminos (t resto)
        (cons (cons (termino->numero t) (termino->exponente t))
              (terminos->lista resto))))))

;; polinomio->lista : Polinomio -> List[Symbol | (Number . Nat)]
(define polinomio->lista
  (lambda (p)
    (cases polinomio p
      (poli (var terms)
        (cons (variable->simbolo var) (terminos->lista terms))))))
#lang eopl
;; Autores: Luis David Mendoza Manzano 2067621
;; Taller 1 — Polinomios dispersos (Representación por procedimientos)

(provide polinomio-cero insertar-termino coeficiente-de eliminar-termino polinomio->lista
         poli poli? poli->var poli->terms nombre-var nombre-var? nombre-var->s
         sin-terminos sin-terminos? mas-terminos mas-terminos? mas-terminos->term mas-terminos->resto
         termino termino? termino->coef termino->expo
         coef-ent coef-ent? coef-ent->n coef-rac coef-rac? coef-rac->num coef-rac->den
         expo-nat expo-nat? expo-nat->k)

;; ====================================================================
;; GRAMÁTICA Y CONSTRUCTORES (Procedimientos)
;; Cada dato es un closure que responde a señales (selectors).
;; Signal 0: tag, Signal 1..n: fields.
;; ====================================================================

;; poli : NombreVar x Terminos -> Polinomio
(define poli
  (lambda (var terms)
    (lambda (sel)
      (cond [(= sel 0) 'poli]
            [(= sel 1) var]
            [(= sel 2) terms]
            [else (eopl:error 'poli "Señal no valida ~s" sel)]))))
(define poli? (lambda (x) (equal? (x 0) 'poli)))
(define poli->var (lambda (x) (x 1)))
(define poli->terms (lambda (x) (x 2)))

;; nombre-var : Symbol -> NombreVar
(define nombre-var
  (lambda (s)
    (lambda (sel)
      (cond [(= sel 0) 'nombre-var]
            [(= sel 1) s]
            [else (eopl:error 'nombre-var "Señal no valida ~s" sel)]))))
(define nombre-var? (lambda (x) (equal? (x 0) 'nombre-var)))
(define nombre-var->s (lambda (x) (x 1)))

;; sin-terminos : () -> Terminos
(define sin-terminos
  (lambda ()
    (lambda (sel)
      (cond [(= sel 0) 'sin-terminos]
            [else (eopl:error 'sin-terminos "Señal no valida ~s" sel)]))))
(define sin-terminos? (lambda (x) (equal? (x 0) 'sin-terminos)))

;; mas-terminos : Termino x Terminos -> Terminos
(define mas-terminos
  (lambda (term resto)
    (lambda (sel)
      (cond [(= sel 0) 'mas-terminos]
            [(= sel 1) term]
            [(= sel 2) resto]
            [else (eopl:error 'mas-terminos "Señal no valida ~s" sel)]))))
(define mas-terminos? (lambda (x) (equal? (x 0) 'mas-terminos)))
(define mas-terminos->term (lambda (x) (x 1)))
(define mas-terminos->resto (lambda (x) (x 2)))

;; termino : Coeficiente x Exponente -> Termino
(define termino
  (lambda (coef expo)
    (lambda (sel)
      (cond [(= sel 0) 'termino]
            [(= sel 1) coef]
            [(= sel 2) expo]
            [else (eopl:error 'termino "Señal no valida ~s" sel)]))))
(define termino? (lambda (x) (equal? (x 0) 'termino)))
(define termino->coef (lambda (x) (x 1)))
(define termino->expo (lambda (x) (x 2)))

;; coef-ent : Int -> Coeficiente
(define coef-ent
  (lambda (n)
    (lambda (sel)
      (cond [(= sel 0) 'coef-ent]
            [(= sel 1) n]
            [else (eopl:error 'coef-ent "Señal no valida ~s" sel)]))))
(define coef-ent? (lambda (x) (equal? (x 0) 'coef-ent)))
(define coef-ent->n (lambda (x) (x 1)))

;; coef-rac : Int x Int -> Coeficiente
(define coef-rac
  (lambda (num den)
    (lambda (sel)
      (cond [(= sel 0) 'coef-rac]
            [(= sel 1) num]
            [(= sel 2) den]
            [else (eopl:error 'coef-rac "Señal no valida ~s" sel)]))))
(define coef-rac? (lambda (x) (equal? (x 0) 'coef-rac)))
(define coef-rac->num (lambda (x) (x 1)))
(define coef-rac->den (lambda (x) (x 2)))

;; expo-nat : Nat -> Exponente
(define expo-nat
  (lambda (k)
    (lambda (sel)
      (cond [(= sel 0) 'expo-nat]
            [(= sel 1) k]
            [else (eopl:error 'expo-nat "Señal no valida ~s" sel)]))))
(define expo-nat? (lambda (x) (equal? (x 0) 'expo-nat)))
(define expo-nat->k (lambda (x) (x 1)))

;; ====================================================================
;; UTILIDADES DE CONVERSIÓN Y VALIDACIÓN
;; ====================================================================

;; coef->numero : Coeficiente -> Number
(define coef->numero
  (lambda (c)
    (if (coef-ent? c)
        (coef-ent->n c)
        (/ (coef-rac->num c) (coef-rac->den c)))))

;; numero->coef : Number -> Coeficiente
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
(define polinomio-cero
  (lambda (variable)
    (if (symbol? variable)
        (poli (nombre-var variable) (sin-terminos))
        (eopl:error 'polinomio-cero "La variable debe ser un simbolo"))))

;; insertar-en-terminos : Terminos x Number x Nat -> Terminos
;; Inserta término manteniendo orden descendente por exponente.
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
(define coeficiente-de
  (lambda (p e)
    (if (exponente-valido? e)
        (buscar-coeficiente (poli->terms p) e)
        (eopl:error 'coeficiente-de "El exponente debe ser un entero no negativo"))))

;; quitar-de-terminos : Terminos x Nat -> Terminos
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
(define polinomio->lista
  (lambda (p)
    (cons (nombre-var->s (poli->var p))
          (terminos->lista (poli->terms p)))))
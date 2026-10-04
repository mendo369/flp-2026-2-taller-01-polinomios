# Informe de corrección — Taller 1: polinomios dispersos

**Curso:** Fundamentos de Interpretación y Compilación de Lenguajes
de Programación — Universidad del Valle, Sede Tuluá.

**Integrantes del grupo:**

| Nombre                     | Código  | Correo institucional               |
| -------------------------- | ------- | ---------------------------------- |
| Luis David Mendoza Manzano | 2067621 | mendoza.luis@correounivalle.edu.co |

> Las demostraciones se hacen una sola vez, sobre la estructura
> recursiva que define la gramática, porque la lógica de las funciones
> es la misma en las tres representaciones. Los fragmentos de código
> son los de `polinomios-listas.rkt`; en `polinomios-procedimientos.rkt`
> son idénticos, y en `polinomios-datatypes.rkt` son los mismos
> algoritmos escritos con `cases`.

---

## 1. Marco formal

### 1.1 Corrección de programas recursivos

Sea $f : A \to B$ una función y $A$ un conjunto definido
recursivamente. Sea $P_f$ un programa recursivo en Racket que pretende
calcular $f$. Decimos que $P_f$ es correcto con respecto a su
especificación si se cumple:

$$
\forall a \in A \,:\, P_f(a) = f(a)
$$

La estrategia de demostración es **inducción estructural** sobre $A$.
Aquí $A$ es el conjunto de listas de términos que genera la gramática:

- **Caso base:** $a = \text{sin-terminos}()$, y se verifica
  $P_f(a) = f(a)$ directamente.
- **Caso inductivo:** $a = \text{mas-terminos}(t, r)$. Se asume la
  **hipótesis de inducción** $P_f(r) = f(r)$ sobre el resto de la
  lista y se demuestra $P_f(a) = f(a)$.

Las tres funciones analizadas están escritas con **recursión
estructural** sobre la lista de términos (ninguna usa acumulador), de
modo que basta este esquema.

**Notación.** Escribimos $\langle\,\rangle$ para `sin-terminos` y
$t :: r$ para `mas-terminos(t, r)`. Un término es $t=(c,e)$ con
coeficiente $c(t)$ y exponente $e(t)$. Para una lista $ts$:
$\mathrm{exps}(ts)$ es el conjunto de sus exponentes y

$$
\mathrm{Ex}(ts, e) \;\equiv\; e \in \mathrm{exps}(ts)
$$

indica que el exponente $e$ aparece en $ts$. Su longitud es $|ts|$.

### 1.2 El invariante de la representación

Las cuatro condiciones del enunciado se enuncian como una única
propiedad sobre polinomios. Sea $p$ un polinomio con términos
$t_1, t_2, \ldots, t_n$, donde $t_i = (c_i, e_i)$:

$$
\mathrm{Inv}(p) \equiv
\underbrace{\forall i < n : e_i > e_{i+1}}_{\text{orden estricto}}
\ \land\
\underbrace{\forall i : c_i \neq 0}_{\text{sin ceros}}
\ \land\
\underbrace{\forall i : e_i \in \mathbb{N}}_{\text{exponentes naturales}}
\ \land\
\underbrace{\forall i : \mathrm{red}(c_i)}_{\text{racionales reducidos}}
$$

donde $\mathrm{red}\left(\frac{a}{b}\right)$ abrevia
$b > 0 \,\land\, \mathrm{mcd}(|a|, b) = 1$, y un coeficiente entero se
toma como el racional de denominador $1$.

Como la variable no interviene en el invariante, escribimos también
$\mathrm{Inv}(ts)$ para una lista de términos $ts$: es la misma
propiedad aplicada a sus términos.

### 1.3 Lemas auxiliares

Estos tres hechos se usan en todas las demostraciones.

**L1 (ida y vuelta de coeficientes).** Para todo racional exacto $n$,
`coef->numero(numero->coef(n))` $= n$.

_Prueba._ Si $n$ es entero, `numero->coef` construye `coef-ent(n)` y
`coef->numero` devuelve $n$. Si no, construye
`coef-rac(numerator(n), denominator(n))` y `coef->numero` devuelve
$\frac{\mathrm{numerator}(n)}{\mathrm{denominator}(n)} = n$. $\square$

**L2 (reducción).** Todo coeficiente producido por `numero->coef`
cumple $\mathrm{red}$.

_Prueba._ Un entero tiene denominador $1>0$ y $\mathrm{mcd}(|n|,1)=1$.
Para un racional no entero, `numerator` y `denominator` de Racket
devuelven la forma canónica: denominador positivo y
$\mathrm{mcd}(|a|,b)=1$ (la documentación de _Racket Reference,
Numbers_ lo garantiza para racionales exactos). $\square$

**L3 (cierre por subsucesiones).** Si $\mathrm{Inv}(ts)$ y $ts'$ se
obtiene de $ts$ quitando términos (sin alterar el orden relativo de
los que quedan), entonces $\mathrm{Inv}(ts')$. En particular,
$\mathrm{Inv}(t::r) \Rightarrow \mathrm{Inv}(r)$.

_Prueba._ Las cuatro condiciones son universales sobre términos o sobre
pares de términos consecutivos. Una subsucesión de una sucesión
estrictamente decreciente es estrictamente decreciente (la relación $>$
es transitiva), y las otras tres condiciones se cumplen término por
término, así que siguen valiendo para los que quedan. $\square$

**Consecuencia del orden estricto (L4).** Si $\mathrm{Inv}(t::r)$,
entonces $e(t) > e'$ para todo $e' \in \mathrm{exps}(r)$; es decir,
$e(t)=\max \mathrm{exps}(t::r)$, y cada exponente aparece en a lo sumo
un término.

---

## 2. Funciones analizadas

### 2.1 Corrección de `coeficiente-de`

**Especificación.**

- **Tipo:** `coeficiente-de : polinomio × exponente -> coeficiente`
- **Pre-condición:** $\mathrm{Inv}(p)$ y $e \in \mathbb{N}$ (entero
  exacto $\ge 0$). Con otro exponente, la función levanta un error de
  validación distinto, antes de recorrer nada.
- **Post-condición:** para $ts$ la lista de términos de $p$,

$$
\text{Post}(p, e, r) \equiv
\begin{cases}
r = c_i & \text{si } \exists\, i : e_i = e \ \ (\text{el } t_i \text{ con } e_i=e)\\
\text{la función levanta } \texttt{eopl:error} & \text{si } \neg\mathrm{Ex}(ts, e)
\end{cases}
$$

**Código.**

```racket
;; buscar-coeficiente : terminos x entero >= 0 -> número exacto
;; Propósito: coeficiente del término de exponente e. Aprovecha el
;; orden estricto: si ya pasó por exponentes menores que e, corta.
;; Error si no hay término con ese exponente.
(define buscar-coeficiente
  (lambda (ts e)
    (if (sin-terminos? ts)
        (eopl:error 'coeficiente-de
                    "El polinomio no tiene termino con ese exponente")
        (let ((t (mas-terminos->term ts)))
          (let ((e0 (termino->exponente t)))
            (cond
              ((= e e0) (termino->numero t))
              ((> e e0)
               (eopl:error 'coeficiente-de
                           "El polinomio no tiene termino con ese exponente"))
              (else (buscar-coeficiente (mas-terminos->resto ts) e))))))))

;; coeficiente-de : polinomio x exponente -> coeficiente
;; Propósito: retorna el coeficiente concreto del término de exponente
;; e. Error si el exponente no es válido o si el polinomio no lo tiene.
(define coeficiente-de
  (lambda (p e)
    (if (exponente-valido? e)
        (buscar-coeficiente (poli->terms p) e)
        (eopl:error 'coeficiente-de
                    "El exponente debe ser un entero no negativo"))))
```

**Demostración.** Sea $\mathrm{B}(ts,e)$ la función `buscar-coeficiente`.
Se prueba por inducción estructural sobre $ts$, con $\mathrm{Inv}(ts)$
y $e\in\mathbb{N}$, la propiedad

$$
Q(ts):\quad
\mathrm{Ex}(ts,e) \Rightarrow \mathrm{B}(ts,e)=c(t_e)
\ \ \land\ \
\neg\mathrm{Ex}(ts,e) \Rightarrow \mathrm{B}(ts,e)\ \text{levanta error},
$$

donde $t_e$ es el (único, por L4) término de $ts$ con exponente $e$.

- **Caso base** ($ts=\langle\,\rangle$): no hay términos, así que
  $\neg\mathrm{Ex}(\langle\rangle, e)$. El programa toma la rama
  `sin-terminos?` y levanta el error. Es exactamente lo que pide $Q$.

  $$
  \mathrm{exps}(\langle\rangle)=\varnothing
  \ \Rightarrow\ \neg\mathrm{Ex}
  \quad\text{y}\quad
  \mathrm{B}(\langle\rangle,e)=\texttt{error}
  $$

- **Caso inductivo** ($ts = t::r$, con $e_0 = e(t)$ y la **hipótesis de
  inducción** $Q(r)$, válida porque $\mathrm{Inv}(r)$ por L3). El
  programa compara $e$ con $e_0$:
  1. **$e = e_0$.** Aquí $\mathrm{Ex}(ts,e)$ es verdadero y $t$ es el
     término buscado. El programa devuelve `termino->numero(t)` $=c(t)$
     (por L1 es el coeficiente concreto). ✓

  2. **$e > e_0$.** Por L4, todo exponente de $ts$ es $\le e_0 < e$, así
     que $\neg\mathrm{Ex}(ts,e)$. El programa levanta el error. ✓
     _Esta es la razón por la que el orden estricto permite cortar la
     búsqueda:_ en cuanto el exponente buscado supera al exponente
     actual, ningún término posterior (todos menores) puede tenerlo, y
     no hace falta recorrer el resto.

  3. **$e < e_0$.** Como $e \neq e_0$, el término $t$ no puede ser el
     buscado, luego $\mathrm{Ex}(ts,e) \iff \mathrm{Ex}(r,e)$. El
     programa devuelve $\mathrm{B}(r,e)$, y por hipótesis de inducción
     $Q(r)$: si $\mathrm{Ex}(r,e)$ devuelve $c(t_e)$; si no, levanta
     error. Eso es $Q(ts)$. ✓

  $$
  \mathrm{B}(t::r, e)=
  \begin{cases}
  c(t) & e=e_0\\
  \texttt{error} & e>e_0\\
  \mathrm{B}(r,e) & e<e_0
  \end{cases}
  $$

- **Levantamiento del error.** Las únicas ramas que levantan el error
  son: caso base (donde $\neg\mathrm{Ex}$), $e>e_0$ (donde
  $\neg\mathrm{Ex}$) y, por herencia de la hipótesis de inducción, la
  llamada recursiva cuando $\neg\mathrm{Ex}(r,e)$. En las demás ramas
  $\mathrm{Ex}$ es verdadero. Por tanto el error se levanta **si y solo
  si** $\neg\mathrm{Ex}(ts,e)$.

- **Terminación.** Medida $\mu(ts) = |ts| \in \mathbb{N}$. La única
  llamada recursiva (rama 3) se hace sobre $r$ con
  $\mu(r)=\mu(ts)-1 < \mu(ts)$, y la medida tiene cota inferior $0$,
  que es el caso base, donde no hay llamada. Por buena fundación de
  $\mathbb{N}$ no hay cadenas infinitas de llamadas.

**Conclusión:** `buscar-coeficiente` satisface $Q$ para toda lista
que cumple el invariante, y `coeficiente-de`, que solo valida $e$ y
delega, cumple $\text{Post}$: retorna el coeficiente buscado cuando el
exponente existe y levanta el error cuando no existe. Además visita a
lo sumo $|ts|$ términos, una sola pasada. $\blacksquare$

---

### 2.2 Corrección de `eliminar-termino`

**Especificación.**

- **Tipo:** `eliminar-termino : polinomio × exponente -> polinomio`
- **Pre-condición:** $\mathrm{Inv}(p)$ y $e \in \mathbb{N}$.
- **Post-condición:** el resultado contiene **exactamente** los
  términos de $p$ menos el de exponente $e$. Formalmente, si
  $\mathrm{Ex}(ts,e)$ y $t_e$ es el término con exponente $e$:
  $$
  \text{terminos}(r) = \text{terminos}(p) \setminus \{t_e\}
  $$
  (y además, como secuencia, $r$ es $ts$ con $t_e$ omitido, sin
  reordenar), y la función levanta `eopl:error` si $\neg\mathrm{Ex}(ts,e)$.

**Código.**

```racket
;; quitar-de-terminos : terminos x entero >= 0 -> terminos
;; Propósito: lista de términos sin el de exponente e, en una pasada.
;; Error si no hay término con ese exponente.
(define quitar-de-terminos
  (lambda (ts e)
    (if (sin-terminos? ts)
        (eopl:error 'eliminar-termino
                    "El polinomio no tiene termino con ese exponente")
        (let ((t (mas-terminos->term ts))
              (resto (mas-terminos->resto ts)))
          (let ((e0 (termino->exponente t)))
            (cond
              ((= e e0) resto)
              ((> e e0)
               (eopl:error 'eliminar-termino
                           "El polinomio no tiene termino con ese exponente"))
              (else (mas-terminos t (quitar-de-terminos resto e)))))))))

;; eliminar-termino : polinomio x exponente -> polinomio
;; Propósito: retorna un polinomio nuevo sin el término de exponente e.
;; Error si el exponente no es válido o si el polinomio no lo tiene.
(define eliminar-termino
  (lambda (p e)
    (if (exponente-valido? e)
        (poli (poli->var p) (quitar-de-terminos (poli->terms p) e))
        (eopl:error 'eliminar-termino
                    "El exponente debe ser un entero no negativo"))))
```

**Demostración.** Sea $\mathrm{Q}(ts,e)$ la función `quitar-de-terminos`
y $ts\setminus e$ la secuencia $ts$ sin el término de exponente $e$.
Propiedad por inducción estructural, con $\mathrm{Inv}(ts)$:

$$
R(ts):\quad
\mathrm{Ex}(ts,e) \Rightarrow \mathrm{Q}(ts,e) = ts\setminus e
\ \land\ \neg\mathrm{Ex}(ts,e) \Rightarrow \mathrm{Q}(ts,e)\ \text{levanta error}.
$$

- **Caso base** ($ts=\langle\rangle$): $\neg\mathrm{Ex}$ y el programa
  levanta el error. ✓

- **Caso inductivo** ($ts=t::r$, $e_0=e(t)$, hipótesis de inducción
  $R(r)$ por L3):
  1. **$e=e_0$.** El programa devuelve $r$. Como $t$ es el término de
     exponente $e$, $r = ts\setminus e$. ✓

  2. **$e>e_0$.** Por L4, $\neg\mathrm{Ex}(ts,e)$ y el programa levanta
     el error. ✓

  3. **$e<e_0$.** $t$ no es el término buscado, y
     $\mathrm{Ex}(ts,e)\iff\mathrm{Ex}(r,e)$. El programa devuelve
     $t :: \mathrm{Q}(r,e)$. Por la hipótesis de inducción, si
     $\mathrm{Ex}(r,e)$ entonces $\mathrm{Q}(r,e)=r\setminus e$, y
     $$
     t :: (r\setminus e) = (t::r)\setminus e = ts\setminus e,
     $$
     porque $t$ conserva su posición y $t\neq t_e$. Si
     $\neg\mathrm{Ex}(r,e)$, el error sube desde la llamada recursiva.
     ✓

- **Los términos son exactamente los originales menos uno.** En las
  ramas 1 y 3 cada término de $ts$ distinto de $t_e$ aparece una vez y
  en el mismo orden; $t_e$ no aparece, y no se crea ningún término
  nuevo (solo se reutilizan $t$ y $r$). Por eso
  $\text{terminos}(r)=\text{terminos}(p)\setminus\{t_e\}$.

- **El resultado conserva el invariante.** El resultado es una
  subsucesión de $ts$ (solo se omite $t_e$), de modo que por L3
  $\mathrm{Inv}(r)$ vale: quitar un término no rompe el orden estricto
  ni introduce ceros, y los demás términos conservan exponente natural
  y coeficiente reducido.

- **Terminación.** Medida $\mu(ts)=|ts|$: la única llamada recursiva
  (rama 3) es sobre $r$ con $|r|=|ts|-1$, acotada por $0$ donde está
  el caso base.

**Conclusión:** `quitar-de-terminos` cumple $R$, y
`eliminar-termino` (que valida $e$, delega y reconstruye el
`poli` con la misma variable) cumple la post-condición, el invariante
y termina. $\blacksquare$

---

### 2.3 `insertar-termino` preserva el invariante

**Enunciado.** Si $\mathrm{Inv}(p)$ vale antes de la llamada, entonces
$\mathrm{Inv}(\texttt{insertar-termino}(p, c, e))$ vale sobre el
resultado.

**Código.**

```racket
;; insertar-en-terminos : terminos x número exacto no nulo x entero >= 0
;;                        -> terminos
;; Propósito: inserta el término (c, e) en una lista de términos que
;; cumple el invariante, en UNA sola pasada. Si el exponente es nuevo
;; lo coloca en su sitio; si ya existía suma los coeficientes y, si la
;; suma es cero, el término desaparece.
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

;; insertar-termino : polinomio x coeficiente x exponente -> polinomio
;; Propósito: retorna el polinomio p + c*x^e conservando el invariante.
;; Errores: exponente negativo o no entero; coeficiente no exacto.
;; Con c = 0 retorna p sin cambios.
(define insertar-termino
  (lambda (p c e)
    (cond
      ((not (exponente-valido? e))
       (eopl:error 'insertar-termino
                   "El exponente debe ser un entero no negativo"))
      ((not (coeficiente-valido? c))
       (eopl:error 'insertar-termino
                   "El coeficiente debe ser un numero exacto"))
      ((zero? c) p)
      (else
       (poli (poli->var p)
             (insertar-en-terminos (poli->terms p) c e))))))
```

**Demostración.** Primero los casos de la envoltura
`insertar-termino`: si $e$ no es un entero exacto $\ge 0$, o $c$ no es
un racional exacto, la función levanta un error y no devuelve ningún
polinomio (no hay nada que preservar). Si $c=0$ devuelve $p$ sin
cambios, y $\mathrm{Inv}(p)$ vale por hipótesis. Esa guarda es
necesaria: sin ella, en las ramas que crean un término nuevo se
insertaría un coeficiente $0$ y se rompería la condición «sin ceros».
Queda el caso central, $c\neq0$ y $e\in\mathbb{N}$, que se reduce al
auxiliar $\mathrm{I}(ts,c,e)$ = `insertar-en-terminos`.

La inducción sobre $ts$ necesita una propiedad un poco más fuerte
que el enunciado, porque en el paso recursivo hay que saber de qué
exponentes puede estar hecho el resultado:

$$
S(ts):\quad
\mathrm{Inv}(ts)\ \Rightarrow\
\mathrm{Inv}(\mathrm{I}(ts,c,e))
\ \land\
\mathrm{exps}(\mathrm{I}(ts,c,e)) \subseteq \mathrm{exps}(ts)\cup\{e\}.
$$

El caso $\mathrm{Inv}(\mathrm{I}(p,c,e))$ del enunciado es la primera
mitad de $S$.

- **Caso base** ($ts=\langle\rangle$). El resultado es la lista con
  un único término $(c,e)$. Es el **Caso A** (el exponente es nuevo,
  pues no hay ninguno).
  Orden estricto: una lista de un elemento lo cumple trivialmente.
  Sin ceros: $c\neq 0$. Exponente natural: $e\in\mathbb{N}$.
  Reducido: por L2, `numero->coef(c)` produce un coeficiente reducido.
  Exponentes: $\{e\}\subseteq\varnothing\cup\{e\}$. ✓

- **Caso inductivo** ($ts=t::r$, $t=(c_0,e_0)$, hipótesis de
  inducción $S(r)$, aplicable por L3). El código distingue cuatro
  ramas, exhaustivas porque $<,=,>$ cubren todas las posibilidades
  sobre $\mathbb{N}$:
  - **(i) $e>e_0$ — el exponente es nuevo (Caso A).** El resultado es
    $(c,e)::ts$. Por L4, $e_0$ es el mayor exponente de $ts$, luego
    $e>e_0>\ldots$ y el orden estricto se conserva en la nueva cabeza;
    el resto de la lista no cambió. Sin ceros ($c\neq0$), natural
    ($e\in\mathbb{N}$), reducido (L2).
    $\mathrm{exps}=\mathrm{exps}(ts)\cup\{e\}$. ✓

  - **(ii) $e=e_0$ y $s=c_0+c\neq0$ — Caso B.** El resultado es
    $(s,e_0)::r$. El término se reemplaza por otro **con el mismo
    exponente** y en la misma posición, así que las desigualdades de
    orden estricto con sus vecinos son las mismas que antes. Sin ceros:
    $s\neq0$ por la guarda de la rama. Exponente natural:
    $e_0\in\mathbb{N}$. Reducido: $s$ es un racional exacto (suma de
    racionales exactos) y por L2 `numero->coef(s)` produce un
    coeficiente reducido y con denominador positivo. Los demás términos
    no cambian, y $\mathrm{exps}$ es el mismo conjunto. ✓

  - **(iii) $e=e_0$ y $c_0+c=0$ — Caso C.** El resultado es $r$: el
    término desaparece. Es una subsucesión de $ts$, así que por L3
    vale $\mathrm{Inv}(r)$. En particular no queda ningún cero, que es
    lo que exige la segunda condición: el cero **se elimina en lugar de
    almacenarse**. $\mathrm{exps}(r)\subseteq\mathrm{exps}(ts)$. ✓

  - **(iv) $e<e_0$ — el término no cabe en la cabeza; se sigue
    buscando.** El resultado es $t::\mathrm{I}(r,c,e)$. Por hipótesis
    de inducción $S(r)$, $\mathrm{I}(r,c,e)$ cumple $\mathrm{Inv}$ y sus
    exponentes están en $\mathrm{exps}(r)\cup\{e\}$. Todos esos
    exponentes son $<e_0$: los de $r$ por L4 y $e$ por estar en la rama
    $e<e_0$. Luego $e_0$ es mayor que el exponente de la cabeza del
    resultado recursivo, y el orden estricto se conserva al anteponer
    $t$, que no cambió ($c_0\neq0$, $e_0\in\mathbb{N}$,
    $\mathrm{red}(c_0)$ por $\mathrm{Inv}(ts)$). Tampoco se pierde nada
    de las otras tres condiciones, que valen por la hipótesis de
    inducción. ✓

  **Cobertura de los tres casos del enunciado.** El **Caso A**
  (exponente nuevo) corresponde al caso base y a la rama (i), a donde
  llega la recursión (iv) cuando $e$ no estaba en la lista. El
  **Caso B** es la rama (ii) y el **Caso C** la rama (iii), a las que
  también llega la recursión (iv) cuando el exponente ya existía. Como
  la rama (iv) preserva $S$ por hipótesis de inducción, los cuatro
  casos juntos prueban $S(ts)$.

- **Terminación.** Medida $\mu(ts)=|ts|$. La única rama recursiva
  ($e<e_0$) llama sobre $r$ con $|r|=|ts|-1$, y en el caso base
  ($|ts|=0$) no hay llamada. Además cada nodo de $ts$ se visita a lo
  sumo una vez: la función recorre la lista **una sola vez**, sin
  reordenar al final.

**Conclusión:** $S(ts)$ vale para toda lista que cumple el invariante,
luego $\mathrm{Inv}(p)\Rightarrow\mathrm{Inv}(\texttt{insertar-termino}(p,c,e))$
en los tres casos A, B y C, y también cuando $c=0$. El invariante se
**conserva** en cada paso; en ningún momento se rompe para luego
restaurarse, que es la diferencia con el atajo de insertar y ordenar
después. $\blacksquare$

_Observación (corrección funcional)._ Además de preservar $\mathrm{Inv}$,
el resultado representa el polinomio $p + c\,x^e$: en los casos A y B
el término de exponente $e$ queda con coeficiente $c$ o $c_0+c$, y en
el caso C es el término nulo, que no se almacena. Los demás
términos no se tocan.

---

## 3. Equivalencia de las dos representaciones

La interfaz del TAD es el conjunto de **constructores**
(`poli`, `nombre-var`, `sin-terminos`, `mas-terminos`, `termino`,
`coef-ent`, `coef-rac`, `expo-nat`) y **observadores** (los predicados
con `?` y los extractores con `->`). La sección 2.2 de EOPL llama
_independencia de la representación_ a que el código cliente use el
TAD _solo_ a través de esa interfaz. Eso es lo que hace nuestro código.

- **Qué ve el cliente de un polinomio.** Solo puede construirlo con
  los constructores, preguntar con los predicados de qué variante es,
  y sacar sus campos con los extractores. Las funciones
  `polinomio-cero`, `insertar-termino`, `coeficiente-de` y
  `eliminar-termino` (con sus auxiliares) son _cliente_: nunca usan
  `car`, `cdr`, ni aplican un dato a una señal. No pueden
  saber si un `poli` es una lista etiquetada o un procedimiento. La
  evidencia es textual: el bloque «CLIENTE» de
  `polinomios-listas.rkt` y el de `polinomios-procedimientos.rkt` es
  idéntico carácter por carácter (se comprobó con `diff`).

- **Qué cambia entre las dos representaciones.** Solo la sección
  «REPRESENTACIÓN» de cada archivo. En listas, `(poli v ts)` es
  `(list 'poli v ts)` y `poli->terms` hace `caddr`. En procedimientos,
  `(poli v ts)` es una clausura que recibe una señal (`0` devuelve la
  etiqueta, `1` la variable y `2` los términos), y `poli->terms` aplica
  el dato a la señal `2`, igual que los ambientes de la clase 2. Ese
  cambio queda del lado de adentro porque ambas implementaciones
  cumplen **las mismas ecuaciones de la interfaz**, por ejemplo
  $\texttt{poli->terms}(\texttt{poli}(v,ts)) = ts$ y
  $\texttt{poli?}(\texttt{poli}(v,ts)) = \texttt{\#t}$, y las funciones
  cliente solo dependen de esas ecuaciones. Por eso el resultado de
  cualquier secuencia de llamadas es el mismo en ambas (lo confirma
  `pruebas-polinomios.rkt`, que corre la misma batería sobre las dos).

- **Qué habría que hacer para que el cliente notara la diferencia.**
  Tendría que saltarse la interfaz: aplicar `car` a un
  polinomio (funciona con listas, falla con procedimientos), invocarlo
  como función con una señal (funciona con procedimientos, falla con
  listas), o compararlos con `equal?` (con listas compara
  estructura; con procedimientos compara identidad, y dos polinomios
  iguales en términos darían `#f`). Cualquiera de esas operaciones usa
  un hecho que **no está en la especificación**: sería el cliente
  dependiendo de la representación, y eso significaría que la
  abstracción se rompió (cambiar la representación obligaría a
  reescribir el cliente). Por eso, en las pruebas, los resultados se
  comparan con `polinomio->lista`, que se construye _con la
  interfaz_, y no con `equal?` sobre los polinomios.

---

## 4. Referencias

- Friedman, D. P., & Wand, M. _Essentials of Programming Languages_,
  3.ª ed., MIT Press, 2008. Sección 2.1 (especificación de datos),
  sección 2.2 (representación basada en listas y basada en
  procedimientos), sección 2.4 (`define-datatype` y `cases`).
- _The Racket Reference_, Numbers: `numerator`, `denominator`,
  `exact?`. <https://docs.racket-lang.org/reference/numbers.html>
- _RackUnit, Unit Testing_. <https://docs.racket-lang.org/rackunit/>

# Taller 1 — Polinomios dispersos

Fundamentos de Interpretación y Compilación de Lenguajes de Programación
Escuela de Ingeniería de Sistemas y Computación, Universidad del Valle
Carlos Andrés Delgado Saavedra

Un TAD polinomio disperso construido tres veces con la misma interfaz: con
listas, con procedimientos y con `define-datatype`. El enunciado completo,
con la especificación, las partes y las rúbricas, está publicado en el Campus
Virtual. Este repositorio es el punto de partida del grupo.

## Integrantes

Esta tabla es lo que identifica al grupo. Sin ella, o con algún dato
incompleto, la entrega pierde el 20 %; quien no aparezca aquí no cuenta como
parte del grupo.

| Nombre completo            | Código  | Correo institucional               |
| -------------------------- | ------- | ---------------------------------- |
| Luis David Mendoza Manzano | 2067621 | mendoza.luis@correounivalle.edu.co |

## Cómo se entrega

1. **Se trabaja sobre un fork de este repositorio.** El grupo hace fork, lo
   deja público y trabaja ahí. Una entrega que no sea fork de este
   repositorio pierde el 30 % de la nota.
2. **El enlace del fork se pega en la actividad del taller en el Campus
   Virtual.** Nada más: ni archivos, ni comprimidos, ni código por correo.
3. **Se califica el último commit anterior a la fecha y hora de cierre.** Lo
   que se suba después no se tiene en cuenta.
4. Solo archivos de texto: código `.rkt` en la raíz e informes `.md` en
   `docs/`. Fórmulas en LaTeX y diagramas en Mermaid dentro del Markdown; no
   se aceptan PDF, DOCX ni imágenes.
5. Las primeras líneas de cada `.rkt` llevan los autores:
   `;Autores: Nombre1 Codigo1, Nombre2 Codigo2`.
6. El historial de commits se revisa para ver el aporte de cada integrante.
   Los cambios de puro formato o de comentarios no cuentan.

## Cómo está organizado

```
polinomios-listas.rkt            Parte 1: representación basada en listas
polinomios-procedimientos.rkt    Parte 2: representación basada en procedimientos
polinomios-datatypes.rkt         Parte 3: representación con datatypes, más la suma
pruebas-polinomios.rkt           Parte 4: pruebas con rackunit sobre las tres
docs/informe-correccion.md       Parte 5: se llena la plantilla
docs/informe-ast.md              Parte 6: se llena la plantilla
```

Los archivos de implementación exportan sus funciones con `provide` y no
contienen pruebas; el archivo de pruebas las importa con `require`. Las
plantillas de `docs/` se llenan en el mismo archivo, reemplazando los
marcadores `{{...}}` y sin quitar las secciones.

## Cómo se corre

```bash
racket pruebas-polinomios.rkt
```

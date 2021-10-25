# Entrega 3
Esta entrega comprende la implementación de tuplas, getter de valores en tuplas, mutación en el heap y se eligió la creación de records con acceso con nombres.


## Con respecto a entregas anteriores

Se pasaron todas las expresiones a ANF, esto porque ya nos estaba tirando muchos problemas haciendoló sin ANF, entonces lo decidimos cambiar a ANF.

## Objetivos concretos
### Implementaciòn de tuplas
La tuplas se implementaron almacenando esta estructura en el heap (memoria pedida en el programa `sys.c`), el almacenamiento consiste de lo siguiente `tamaño valor_pos0 valor_pos1 valor_pos2 ... valor_posn`, luego de almacenarla se pasa la dirección de memoria tageandola con su tipo para poder recuperarla más tarde. Para este tag se expandió los tag ya usados a lo siguiente: `00` para enteros, `01` para tuplas y `10` para booleanos.

Se realizaron todos los test correspondientes sobre las tuplas, además se añadieron test de verificación de tipos para todos las operaciones previamente implementadas, testeando que corte la ejecución del código cuando se obtenga una tupla cuando se espera otra cosa.

### Acceso a tuplas
La operación `(get t pos)` fue implementada, en la cual se debe entregar una tupla (`t`) y una posición (`pos`), retornando el valor en esa posición, excepto que el índice no corresponda a un indice entre `0` y el tamaño de la tupla.

Se realizaron todos los test correspondientes, tanto correctos, como de verificación que los elementos que se le entreguen al get sean del tipo correcto y verificación de que no se accese a una posición incorrecta.

### Mutación en el heap
La operación `(set t pos k)` fue implementada, en la cual se debe entregar una tupla (`t`), un índice (`pos`) y el valor nuevo (`k`), retornando la tupla con el índice dado actualizado con el valor nuevo, excepto que el índice no corresponda a un indice entre `0` y el tamaño de la tupla.

Se realizaron todos los test correspondientes, tanto correctos, como de verificación que los elementos que se le entreguen al get sean del tipo correcto y verificación de que no se mute una posición incorrecta.

### Objetivos extras

Se realizò el objetivo extra e creación de records con acceso con nombres, esto se realizó tratando el record como una tupla con nombre, generando una función que reciba los atributos y cree una tupla con esots, entonces este record `(record p x y z)` si es que hago `(p 1 2 3)` por detrás se entenderá como `(tup 1 2 3)`. 

Además se implementaron el acceso a este con nombres, transformandolo como una función por atributo, esto quiere decir que si tuviera el record anterior, dentro del assembly crearía funciones llamadas `p_x`, `p_y` y `p_z`, para así poder acceder a los valores por nombre. Y en caso que alguien intente acceder a un atributo que no exista en este record, el compilador les hará saber que se intentó acceder a un atributo que no existe dentro de este record.

A parte se realizaron todos los test correspondientes de los records, esto incluye creación, acceso con nombres, incorrecto acceso a atributos y malos tipos al intentar acceder a los atributos.

### Detalles adicionales
- Se adaptó el archivo `sys.c` para generar compatibilidad con la nueva forma de representar tipos de variables.
- 2 de los tests, los cuales prueban "print", podrían no correr en Windows debido a la diferencia en saltos de línea entre este y Linux. En Linux deberían ejecutarse correctamente y pasar.

# Entrega 1
Esta entrega comprende el agregado de booleanos y operaciones básicas entre ellos y con enteros.

## Objetivos concretos
### `let`-bindings
El operador `let` ha sido implementado para funcionar con una variable de input. Los tests correspondientes están hechos. Las operaciones `let` se pueden anidar y definen un _scope_ para todas las instrucciones declaradas en el tercer argumento.

### Tipos de datos básicos
El tipo de dato `bool` ha sido implementado. Para distinguirse del tipo `int`, se utiliza el bit menos significativo de los 64 bits disponibles. `int` tiene este bit en `0` y `bool` lo tiene en `1`.

#### Operaciones binarias
- La operación `+` para enteros está implementada y testeada. 
- La operación `and` para booleanos está implementada y testeada.
- La comparación `<=` sobre enteros está implementada y testeada.

#### Operación unaria `not`
_To be added..._

### Condicionales `if`
Nuestra implementación de los condicionales `if` cumplen con el formato solicitado y está testeada.

### Objetivos extras
La operación `and` solo procesa el segundo argumento si el primero es `false`. La forma de implementarlo permite fácilmente escalar y usar otras operaciones booleanas binarias (e.g. `or`).

### Detalles adicionales
- Se adaptó el archivo `sys.c` para generar compatibilidad con la nueva forma de representar tipos de variables.
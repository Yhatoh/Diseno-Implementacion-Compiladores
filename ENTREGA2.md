# Entrega 2
Esta entrega comprende el agregado de gestión dinámica de errores de tipos, añadir funciones externas como print y compilar funciones de primer orden.


## Objetivos concretos
### Gestión dinámica de errores de tipos
La gestión dinámica de errores de tipos se realiza como un llamado a una función externa programada en C llamada `typeError` esta función recibe el tipo de error (`1` si se esperaba un número, pero no llego un número y `2` si se esperaba un booleano, pero no llego un booleano). A nivel de assembly, lo que se hace es que cada vez que se termina de hacer una operación o almacenar un tipo en `RAX` se verifica que sea un número o booleano correspondiente. En caso que no sea se llama a la funcìón `typeError` para que termine el programa y muestre por pantalla el error.

A parte se realizaron todos los test correspondientes con cada operación tanto binaria como unaria con error de tipos y también si es que la condición del `if` no era un tipo `bool`. Todos estos tests fueron realizados en la carpeta `bbctest`.


### Función externa `print`
El llamado de la función externa `print` ha sido implementada, donde en el cual se programo una función en `rt/sys.c`, donde esta recibe un valor y lo imprime en el formato pedido, además retorna el valor que recibio después de mostrarlo por pantalla. 

Se realizaron los test adecuados de esta función tanto para la compilación como ejecución.

### Compilar funciones de primer orden
Se implementaron las funciones de primer orden de tal forma que estas puedan recibir una cantidad n de formatos, puedan llamar a otras funciones que hayan sido llamadas previentes y hacer uso de variables "globales".

Además se realizaron la gestión de errores en tiempo de compilación cuando una variable no se encuentra definida, cuando una función no se encuentra definida y cuando la cantidad de parametros no corresponde con la cantidad de los parametros de la función.

Se realizaron test tanto para la compilación correcta delas funciones y también se realizaron test para la ejecucion correcta del programa.

### Objetivos extras

Se realizó  el objetivo extra de gestión de errores de recursos (overflows, underflos y div by 0). A parte se implementaron las operaciones `-`, `*`, `/`. La gestión de errores de recursos se realizo llamado a funciones de C que recibirán parametros para luego decidir si la operación producirá overflow, underflow o la división no se puede realizar ya que se esta dividiendo por 0. 

Además para lo del flag `-safe` se agrego una variable global en el archivo `rt/sys.c` (línea 41), donde esta si vale `1` se terminará el programa en caso de que la operación produsca algunos de los errores mencionados anteriomente y si vale `0` esta no terminará el programa.

Para los tests se implementaron tests para la compilación correcta de las nuevas operaciones añadidas. También se hicieron test de correcta ejecución de estas operacion. Y finalmente se realizaron los respectivos test de errores para overflow y underflow para las operaciones `+`, `-` y `*`, y también para cuando se haga una división por 0. Por último, a estas operaciones añadidas se realizaron test para verificación de tipos.

### Detalles adicionales
- Se adaptó el archivo `sys.c` para generar compatibilidad con la nueva forma de representar tipos de variables.

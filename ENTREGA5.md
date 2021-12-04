# Entrega 5
Esta entrega considera la implementación de un recolector de basura que utiliza el algoritmo de Cheney. A continuación, se enuncian las especificaciones de la entrega.

## Implementación del algoritmo de Cheney
La versión del algoritmo es una adaptación a `C` del pseudo-código que aparece en [esta página de Wikipedia](https://en.wikipedia.org/wiki/Cheney%27s_algorithm). Su correctitud está probada en los tests.

## Asignación de memoria con GC
El compilador fue ligeramente adaptado para que, cada vez que se cree un elemento que debe ser guardado en el heap (en el caso de nuestro lenguaje, tuplas o clausuras), se efectúe una llamada al GC. Este analiza si existe suficiente espacio en la memoria restante desde el registro `R15`; si lo hay, simplemente crea la nueva estructura donde debería; si no lo hay, ejecuta el algoritmo de Cheney y verifica nuevamente si hay espacio para insertar el nuevo elemento. Si lo hay, lo inserta donde debe y si no, el programa arroja un error de memoria.

Adicionalmente, el GC ejecuta un recorrido del heap post-recolección para asegurarse de que la memoria no contiene basura (i.e. toda la información que había fue reiniciada a su valor por defecto).
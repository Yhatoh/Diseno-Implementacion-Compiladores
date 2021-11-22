# Entrega 4
La presente entrega cuenta con implementaciones según los requisitos solicitados para la entrega 4 del ramo. A continuación, se presentan los avances hechos durante esta iteración.

## Definición de funciones anónimas
La definición de funciones anónimas o _lambdas_ funciona según lo solicitado. Para crear una de ellas basta con anteponer la palabra clave `lambda` a una serie de argumentos y a una expresión correspondiente al cuerpo de esta. La definición concreta (como clausura) almacena la dirección de memoria de su llamada, además de su aridad y las variables libres utilizadas en su implementación.

Para definir una clausura, fue necesario agregar un nuevo tipo de dato, luego un nuevo identificador de tipo en la implementación. Actualmente, nuestros identificadores se definen de la siguiente forma:
- Los enteros se identifican con los LSB `00`.
- Las tuplas se identifican con los LSB `01`.
- Los booleanos se identifican con los LSB `10`.
- Las clausuras se identifican con los LSB `11`.

Notar que, al igual que en la entrega anterior, esta clasificación supone una menor cantidad de enteros (la mitad) que en el caso recomendado i.e. usar solo LSB `0` para identificarlos.

## Aplicación y manipulación de funciones anónimas
Utilizando el comando `@` antes de una clausura y una serie de parámetros (cuya cantidad debe igualar la aridad de la clausura), es posible utilizar una lambda como función. Adicionalmente, las funciones de primera clase pueden pasarse como argumento y devolverse como retorno de una función.

## Definición de clausuras recursivas
Utilizando el comando `letrec`, es posible definir funciones de primera clase que cumplan con ser recursivas. Basta con llamar a este comando una única vez para definir varias clausuras de este tipo. Adicionalmente, es posible no solo aplicar una auto-referencia, sino también una co-referencia entre funciones definidas bajo un mismo comando `letrec`.

Para implementar estas referencias recursivas, lo que se hizo fue definir un scope general con los nombres de las funciones a definir; luego, al momento de identificar las variables libres, se agregó a su scope el definido con las funciones. Finalmente, dado que estas están almacenadas por valor en las clausuras, se buscan los nombres de las funciones y se reemplaza su valor con el de la dirección del heap de la clausura correspondiente.

## Detalles adicionales
En las entregas previas, se realizaron numerosos tests unitarios exhaustivos en lo que respecta a probar el funcionamiento del compilador. Para esta entrega, solo se agregaron tests de tipo _black-box_. Esta decisión tiene dos motivos:
- Nos enteramos de que los tests de nivel así de bajo no eran requisito de las entregas
- La forma de implementar nuestro código y el estado actual de los tests impiden una escalabilidad cómoda en el proceso de testing de bajo nivel, resultando en la necesidad de corregir muchísimas líneas de código de pruebas para cada entrega, resultando un trabajo innecesariamente tedioso.

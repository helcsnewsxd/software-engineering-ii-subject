> [!note]
> This repository contains theoretical notes, practical exercises, and a final project developed for the Software Engineering II course of the Computer Science degree at FAMAF – Universidad Nacional de Córdoba.
>
> All materials are in Spanish, as they were created for academic use and course submission.

# Ingeniería del Software II

El presente repositorio contiene todo el material correspondiente a la cursada de la materia de _Ingeniería del Software II_ de 5to año de la Licenciatura en Ciencias de la Computación de FAMAF durante el año 2025.

## Información general

Los temas que trata la materia se pueden ver en el [programa](./information/study_program.pdf) de la misma. Respecto al material, este está basado en los siguientes libros:

- J. Magee y J. Kramer. Concurrency: State Models & Java Programs, 2nd edition. Wiley 2006.
- C. Baier y J.-P. Katoen. Principles of Model Checking. MIT Press, 2008.
- D. Jackson. Software Abstractions: Logic, Language, and Analysis (Revised Edition). MIT Press, 2016.
- D. Kroening y O. Strichman. Decision Procedures: An Algorithmic Point of View. 2nd. edition. Springer, 2016.
- A. Biere, M. Heule, H. van Maaren, y T. Walsh (eds.). Handbook of Satisfiability. 2nd edition. IOS press, 2021.
- M. Müller-Olm, D. Schmidt, B. Steffen. Model Checking: A Tutorial Introduction. En A. Cortesi, G. Filé (Eds.), Procs. Of SAS'99, LNCS 1694, pp. 330-354. Springer 1999.

El equipo docente está únicamente conformado por Pedro Ruben D'Argenio.

## Contenido

### Teórico

<div align="center">

| Temas                                                               | Descripción                                                                                                                                                                                       | Filminas                                                                        | Libro/Apunte                                                                                      |
| ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- |
| Introducción                                                        | Burocracia <br /> A qué apunta la materia                                                                                                                                                         | [PDF](./theory/slides/01-introduction.pdf)                                      | Magee & Kramer (1)                                                                                |
| Programación concurrente                                            | Repaso <br /> Transición de estados <br /> Semántica de FSP                                                                                                                                       | [PDF](./theory/slides/02-concurrent_programming.pdf)                            | Magee & Kramer (2, 3)                                                                             |
| Sincronización de procesos concurrentes                             | Interferencia y exclusión mutua <br /> Monitores, semáforos y buffers <br /> Simulación y bisimulación <br /> Pasaje de mensajes                                                                  | [PDF](./theory/slides/03-concurrent_programs_synchronization.pdf)               | Magee & Jramer (4, 5, 10) <br /> [Notas de clase](./theory/notes/simulation_and_bisimulation.pdf) |
| Propiedades de los sistemas reactivos y su análisis                 | Lenguajes $\omega$-regulares <br /> Safety y liveness <br /> Vista en FSP                                                                                                                         | [PDF](./theory/slides/04-properties_of_reactive_systems_and_their_analysis.pdf) | Magee & Kramer (6, 7) <br /> Alpern & Schneider (21:182-185) <br /> Baier & Katoen (3, 4)         |
| Lógica temporal lineal                                              | LTL <br /> Safety, liveness y fairness                                                                                                                                                            | [PDF](./theory/slides/05-linear_temporal_logic.pdf)                             | Baier & Katoen (4, 5)                                                                             |
| Model Checking                                                      | Autómatas de Büchi <br /> SPIN y SMV                                                                                                                                                              | [PDF](./theory/slides/06-model_checking.pdf)                                    | Müller-Olm (1, 2, 4.2, 4.4)                                                                       |
| Especificación de sistemas                                          | Especificación <br /> SAT solving (idea) <br /> Álgebra de relaciones                                                                                                                             | [PDF](./theory/slides/07-system_specification.pdf)                              |                                                                                                   |
| El lenguaje de especificación Alloy                                 | Signaturas <br /> Predicados <br /> Hechos, aserciones y predicados <br /> Cambios de estado y trazas <br /> Elección de cotas y cuantificadores universales no acotados                          | [PDF](./theory/slides/08-alloy.pdf)                                             | D. Jackson 2006 (1, 2, 3, 4) <br /> [Ejemplos](./theory/examples/alloy/)                          |
| Algoritmos para verificar satisfactibilidad en lógica proposicional | Tablas de verdad <br /> Método de tableaux <br /> Tablas de verdad reconsideradas <br /> Transformación de Tseitin (CNF equisatisfactible) <br /> Resolución <br /> Cláusulas de Horn <br /> DPLL | [PDF](./theory/slides/09-sat_solving.pdf)                                       | A.R. Bradley & Z. Manna 2007 (The Calculus of Computation)                                        |

</div>

### Práctico

<div align="center">

| Guía | Enunciados                                                                                   | Soluciones                          |
| ---- | -------------------------------------------------------------------------------------------- | ----------------------------------- |
| 1    | [PDF](./exercises/statements/01.pdf)                                                         | [PDF](./exercises/solutions/01.pdf) |
| 2    | [PDF](./exercises/statements/02.pdf) <br /> [Adicional](./exercises/statements/02-extra.pdf) | [PDF](./exercises/solutions/02.pdf) |
| 3    | [PDF](./exercises/statements/03.pdf)                                                         | [PDF](./exercises/solutions/03.pdf) |
| 4    | [PDF](./exercises/statements/04.pdf)                                                         | [PDF](./exercises/solutions/04.pdf) |
| 5    | [PDF](./exercises/statements/05.pdf)                                                         | [PDF](./exercises/solutions/05.pdf) |
| 6    | [PDF](./exercises/statements/06.pdf)                                                         |                                     |
| 7    | [PDF](./exercises/statements/07.pdf)                                                         |                                     |

</div>

### Proyecto

La información específica sobre el proyecto con sus pautas se puede encontrar en esta [presentación](./information/project_presentation.pdf). El proyecto consistió en investigar y realizar un informe acerca de una herramienta de Model Checking elegida al azar (en base a nuestras preferencias) por el profesor. En nuestro caso, se trató sobre _CBMC_.

Nuestro proyecto se enfoca en CBMC (C Bounded Model Checking), su origen, objetivo, usos, interfaz, estructura, comparaciones, casos de estudio y un caso de uso hecho por nosotros usando esta herramienta de verificación para romper un cifrado personalizado (resolver un problema de un CTF) para demostrar su potencial y versatilidad. El informe y la presentación se pueden encontrar en este [repositorio](https://github.com/helcsnewsxd/cbmc-analysis-report) público.

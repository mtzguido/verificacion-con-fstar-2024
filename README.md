# Verificación de Programas con F\*

Para instrucciones sobre cómo correr F* ver: [Ejecutar.md](./Ejecutar.md).

Para instrucciones sobre cómo usar la extensión, ver [aquí](https://github.com/FStarLang/fstar-vscode-assistant?tab=readme-ov-file#basic-navigation).

## Clases

| # |  Fecha     | Tema                        |
|---|------------|-----------------------------|
| 1 | 12/03 | Introducción a verificación, F*, tipos refinados
| 2 | 19/03 | Tipos dependientes, lógica formal, Curry-Howard
| 3 | 26/03 | Recursión, terminación, tipos inductivos (índices, parámetros, GADTS), positividad
|   | 02/04 | Feriado.
| 4 | 09/04 | Más tipos indexados, pruebas extrínsecas.
| 5 | 16/04 | SMT solvers, Codificación a SMT, verificando BSTs
| 6 | 23/04 | Más BSTs, invariantes, refinando una ED
| 7 | 30/04 | Lógica de Hoare (verificada) para Imp
|   | 07/05 | Cancelada.
| 8 | 14/05 | Weakest preconditions, construyendo un verificador (verificado)
| 9 | 23/05 | Invitada: Gabriel Ebner sobre Lean y Mathlib (en inglés)

## Bibliografía

#### Requerida

- [Proof-Oriented Programming in F\*](https://fstar-lang.org/tutorial/proof-oriented-programming-in-fstar.pdf), capítulos 1-4, 6-8 (por ahora)
- [Hoare - An axiomatic basis for computer programming (1969)](https://dl.acm.org/doi/10.1145/363235.363259)

#### Complementaria

- Métodos formales en la práctica
  - [Reid et al - Towards making formal methods normal: meeting developers where they are (2020)](https://arxiv.org/abs/2010.16345)
- Bugs famosos
  - [Bug FDIV del Pentium](https://en.wikipedia.org/wiki/Pentium_FDIV_bug)
  - [Vuelo Arianne V88](https://en.wikipedia.org/wiki/Ariane_flight_V88)
  - [Heartbleed](https://heartbleed.com/): filtración de datos en OpenSSL
  - [Maleabilidad en Bitcoin, y Hackeo a MtGox](https://arxiv.org/abs/1403.6676)
  - [Spectre](https://spectreattack.com/spectre.pdf)
     y [Meltdown](https://meltdownattack.com/meltdown.pdf): bugs de hardware relacionados a ejecución especulativa
  - [Casa Blanca EE.UU. - Back to the Building Blocks: A Path Toward Secure and Measurable Software (2024)](https://www.whitehouse.gov/wp-content/uploads/2024/02/Final-ONCD-Technical-Report.pdf)
- Verificación
  - [Dijkstra - Guarded commands, nondeterminacy and formal derivation of programs (1975)](https://dl.acm.org/doi/10.1145/360933.360975)
- Lenguajes de Programación
  - [Wadler - Theorems for free! (1989)](https://www2.cs.sfu.ca/CourseCentral/831/burton/Notes/July14/free.pdf): parametricidad y teoremas gratis
  - [Wadler - Propositions as types (2015)](https://www.youtube.com/watch?v=IOiZatlZtGU): correspondencia Curry-Howard
  - [Augustsson - Cayenne - a language with dependent types (1998)](https://dl.acm.org/doi/pdf/10.1145/289423.289451)
  - [McBride - Faking it: Simulating dependent types in Haskell (2002)](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/faking-it-simulating-dependent-types-in-haskell/A904B84CA962F2D75578445B703F199A)
- Verificación de programas con efectos
  - [Dijkstra Monads for Free (2017)](https://arxiv.org/abs/1608.06499)
  - [Dijkstra Monads for All (2019)](https://arxiv.org/abs/1903.01237)
- Verificando verificadores
  - [MetaCoq](https://metacoq.github.io/)
  - [Strub et al - Self-Certification: Bootstrapping Certified Typecheckers in F* with Coq (2012)](https://www.microsoft.com/en-us/research/publication/self-certification-bootstrapping-certified-typecheckers-in-f-with-coq/)
  - [Andrici, Ciobâcă - A Verified Implementation of the DPLL Algorithm in Dafny (2022)](https://www.mdpi.com/2227-7390/10/13/2264)

#### Proyectos

- Usando F\*
  - [HACL\*](https://github.com/hacl-star/hacl-star): criptografía verificada
  - [EverParse](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/): parsers verificados para formatos de red
- Otros proyectos importantes
  - [Mathlib de Lean4](https://github.com/leanprover-community/mathlib4)
  - [CompCert](https://compcert.org/): compilador de C verificado
  - [sel4](https://sel4.systems/): microkernel
  - [DeepSpec](https://deepspec.org/main): especificaciones profundas full-stack
  - [Z3](https://www.microsoft.com/en-us/research/project/z3-3/): SMT solver ([GitHub](https://github.com/z3prover/z3))

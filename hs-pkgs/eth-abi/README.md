## Table Of Types

| ABIType Instances   | [ABICoreType]   | Name (Selector Name)                  | Examples               |
|---------------------|-----------------|---------------------------------------|------------------------|
| *(core types)*      |                 |                                       |                        |
| NP xs               | xs'             | N-ary products ((T1, ... Tn))         | INT 1 :* true :* Nil   |
| BOOL                | [BOOL']         | Boolean (bool)                        | true, false            |
| INTx s n            | [INTx' s n]     | Fixed-precision integers (int?/uint?) | -1, 0, 42, 0xffff      |
| ADDR                | [ADDR']         | Ethereum addresses (address)          | constAddr "#0xABC5..." |
| BYTESn n            | [BYTESn']       | Binary type of n bytes (bytes?)       |                        |
| ARRAY a             | [ARRAY' a]      | Arrays (T[])                          | TODO                   |
| FIXx s m n          | [FIX m n]       | Fixed-point decimal numbers (fixed)   | TODO                   |
| *(extended types)*  |                 |                                       |                        |
| U8, U16, ... U256   | [INTx' False n] | Aliases of unsigned integers          | (see INTx)             |
| I8, I16, ... I256   | [INTx' True n]  | Aliases of signed integers            | (see INTx)             |
| B1, B2, ... B32     | [BYTESn n]      | Aliases of byte arrays                | (see BYTESn)           |
| REF a w             | [B32']          | Memory or storage references          | TODO                   |
| MAYBE a             | [MAYBE' a]      | Maybe a value                         | TODO                   |
| FUNC c sel          | [U192']         | Contract function pointer             | TODO                   |
| (a, b)              | [a', b']        | Tuples                                | (a, b)                 |
| TUPLEn n            | [a1', ... an']  | Tuples of N-elements                  | (), a, (a, b, c)       |
| STRUCT lens_xs      | xs'             | Struct with lenses                    | TODO                   |
| STRING              | [BYTES']        | UTF-8 strings                         | TODO                   |
| MAP a b             | [B32']          | Hash tables, aka. maps                | TODO                   |
| *(dependent types)* |                 |                                       |                        |
| BOOL'd v            | [BOOL']         | Dependent booleans                    | TODO                   |
| INTx'd s n v        | [INTx' s n]     | Dependent integers                    | TODO                   |
| BYTES'd l           | [BYTES']        | Length-indexed byte arrays            | TODO                   |
| ARRAY'd a l         | [ARRAY' a]      | Length-indexed arrays                 | TODO                   |
| STRING'd v          | [BYTES']        | Dependent strings                     | TODO                   |

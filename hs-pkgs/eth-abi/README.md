## Table Of Types

| ABIType Instances   | [ABICoreType]   | Name (Selector Name)                  | Examples               |
|---------------------|-----------------|---------------------------------------|------------------------|
| *(core types)*      |                 |                                       |                        |
| NP xs               | xs'             | N-ary products ((T1, ... Tn))         | INT 1 :* true :* Nil   |
| BOOL                | [BOOL']         | Boolean (bool)                        | true, false            |
| INTx s n            | [INTx' s n]     | Fixed-precision integers (int?/uint?) | -1, 0, 42, 0xffff      |
| - U8, U16, ... U256 | [INTx' False n] | Aliases of unsigned integers          | (see INTx)             |
| - I8, I16, ... I256 | [INTx' True n]  | Aliases of signed integers            | (see INTx)             |
| ADDR                | [ADDR']         | Ethereum addresses (address)          | constAddr "#0xABC5..." |
| BYTESn n            | [BYTESn']       | Binary type of n bytes (bytes?)       | ??                     |
| - B1, B2, ... B32   | [BYTESn n]      | Aliases of byte arrays                | (see BYTESn)           |
| ARRAY a             | [ARRAY' a]      | Arrays (T[])                          | 🚧                     |
| BYTES               | [BYTES']        | UTF-8 strings                         | 🚧                     |
| STRING              | [BYTES']        | UTF-8 strings                         | 🚧                     |
| FIXx s m n          | [FIX m n]       | Fixed-point decimal numbers (fixed)   | 🚧                     |
| *(extended types)*  |                 |                                       |                        |
| (a, ..,e)           | [a', .. e']     | TuplesN                               | (a, b, c)              |
| REF a w             | [B32']          | Memory or storage references          | 🚧                     |
| STRUCT lens_xs      | xs'             | Struct with lenses                    | 🚧                     |
| FUNC c sel          | [U192']         | Contract function pointer             | 🚧                     |
| *(dependent types)* |                 |                                       |                        |
| ARRAY'd a l         | [ARRAY' a]      | Length-indexed arrays                 | 🧪                     |
| INTx'd s n v        | [INTx' s n]     | Dependent integers                    | 🧪                     |
| BYTES'd l           | [BYTES']        | Length-indexed byte arrays            | 🧪                     |
| STRING'd v          | [BYTES']        | Dependent strings                     | 🧪                     |

TODO
====

> [!WARNING]
>
> YOU DON'T NEED TO LOOK AT THIS DIRTY LAUNDRY!
>
> Legend for items:
> * ⭐,🌟 - Highlighted feature.
> * 🟢 - Planned and low uncertainty;
> * 🟠 - Planned with some design decisions to be made;
> * 🔴 - Likely deferred to the future versions;
> * ❓ - To be reviewed.

## Bigger Refactoring

- [ ] Compare different sharing approach: https://paste.tomsmeding.com/CFVMMNbL
- [ ] Use sop-core; otherwise, the simple-sop doesn't have injectivity for type inferences.
- [ ] Haddock doc cleanup and prettifying.
- [ ] Use more GHC warning options https://github.com/Kleidukos/print-api/blob/main/print-api.cabal#L39-L43.

## TODOs for 0.1.0.0

### eth-abi

- CoreType
  - [x] NP (N-ary Product, type-level recursive-friendly alternative to tuple type)
  - [x] BOOL
  - [x] INTx s n
  - [x] BYTESn
  - [x] ADDR
  - [ ] 🟠 ARRAY a
  - [ ] 🟠 BYTES
  - [ ] 🟠 STRING
- ExtendedType
  - [x] TUPLEn
  - [ ] 🟠 REF, storage or memory raw reference with `constRef, keyRef`.
    - SREF for strarage.
    - Recursive `REF a b` type.
    - MREF family for memory: IMREF (immutable), LMREF (locked), and MMREF (mutable).
  - [ ] 🟢 SELECTOR
- ABICodec
  - [ ] 🟢 Compatibility with the solidity abi-spec

### yul-dsl

- YulCat
  - [x] Type conversions for `ABITypeDerivedOf, ABITypeCoercible, NP`
  - [x] SMC
  - [x] Closed cartesian.
  - [x] Co-cartesian related
    - [x] `YulAbsurd`, absurd value for building visualization code.
    - [x] `YulEmb`, embed values.
  - Control flows
    - [x] `YulMapHask`, map haskell function to exponential objects.
    - [x] `YulSwitch`, switch statement.
    - [x] `YulJmpB`, code jump for built-in yul functions.
    - [x] `YulJmpU`, code jump for user-defined yul functions.
    - [ ] 🟠 `YulArrayLen, YulMapArray`, array length and tight-loop primitives.
  - Side Effects
    - [x] `YulSGet`, `YulSPut` for raw storage operations.
      - [ ] 🟢 Support storage offset.
    - [x] `YulCall`, external function calls.
      - [ ] Call spec: Selector, Static, Delegated, Gas.
      - [ ] 🟢 external function specification: `declareExternalFn`.
  - Yul Object
    - [x] Function export modifiers resembling solidity: `pureFn, staticFn, omniFn`.
    - [x] mkYulObject
  - Type Safety
    - [x] Effect purity classification: `IsEffectNotPure, MayEffectWorld`.

- Standard Built-in Yul Functions:
  - [x] Built-in extension infrastructure
  - Value validators
    - [x] bool
    - [x] intN, uintN
    - [x] address
    - [x] `__validate_t_`
  - Integer comparators
    - [x] eq, ne, lt, le, gt, ge
  - Safe integer arithmetic
    - [x] Safe number operation wrappers for checked numbers and maybe numbers.
    - [x] add, mull, sub, abs
    - [ ] 🟢 sig, abs
    - [ ] 🟢 divMod, quotRem
    - [ ] 🟢 (complete testsuite)
  - Safe value casting
    - [ ] 🟢 Casting integers
    - [ ] 🟢 Casting ADDR to U160
    - [ ] 🟢 Casting BYTESn n to uINTn
    - [ ] 🟢 (complete testsuite)
  - ABICodec
    - [x] `__abidec_dispatcher_c_, __abidec_from_calldata_t_`
    - [x] `__abidec_from_memory_c_, __abidec_from_memory_t_`
    - [x] `__abienc_from_stack_c_, __abienc_from_stack_t_`
    - [x] `__keccak_c_` for supported types.
      - [ ] 🟢 `__keccak_c_` evaluation function using ABICodec from eth-abi.
    - [ ] 🟢 support dispatcher decoding tuples
    - [ ] 🟢 complete testsuite
  - Runtime
    - [x] `__caller`, equivalent of `msg.sender`.
    - [x] `__const_revert0_c_`, equivalent of `revert()`.
    - [ ] 🟢 `revertWithMessage`
    - [ ] 🟢 `revertWithError`
    - [ ] 🟢 (complete testsuite)

- CodeGen/YulGen
  - Function Gen:
    - [x] Yul code generator for any YulCat
    - [ ] 🟠 Fix the implementation for all embeddable values.
  - Object builder:
    - [x] Yul object dispatcher generator for exported functions.
    - [ ] 🟠 constructor support.

- Eval
  - [x] `evalFn` to evaluate `Fn` (single YulCat value styled as a function) value.
  - [ ] 🟢 handling revert
  - [ ] 🟢 testsuite

### yul-dsl-pure

- `Data` and `Control` extensions
  - [x] `Data.MPOrd` for lifted Boolean types.
  - [x] `Data.Type.Function` to work with function signatures.
  - [x] `Control.IfThenElse` for rebindable syntax.
  - [x] `Control.PatternMatchable` and the "match, is, be" verbs.
- Working with integers
  - [x] Num class with checked integer operations.
  - [x] ⭐ Maybe Num with optional integer operations and Pattern matching of support.
  - [ ] Type-safe `upCast`, and `safeCast` for down-casting to `Maybe` values.
- Additional yul objects
  - [x] BOOL. Instances: 'IfThenElse', 'PatternMatchable', 'InjectivePattern'.
  - [x] Maybe a
    - [ ] ⚠️ Expand beyond `Maybe (INTx s n)`
  - [x] NP
  - [x] TUPLEn
- Pure Effect:
  - [x] Build pure functions `$fn`.
  - [x] Call pure functions `call`, `call0`, `callN`.
- Yul Functors
  - [x] `YulFunctor`, using `HexoFunctor`.
  - [ ] `YulFoldable`
  - [ ] `YulApplicative`
  - [ ] `YulAlternative`
  - [ ] `YulTraversable`

### yul-dsl-linear-smc

- [x] 🌟🌟🌟 Linear safety for side effects.
  - [x] Compile expressions of linear _yul ports_ to YulCat
  - [x] Working with _versioned data port_ through `YLVM`, a "Linearly-Versioned Monad."
- Working with _yul ports_ using linear-smc directly.
  - [x] Build _yul ports_ functions: `$lfn $ yulports'{pp,pv,vv}`.
  - [x] Process _yul ports_ in pure yul functions: `ywith'l`.
  - [x] VersionThread API: `vtstat{_}, vtstop, vtreturn, vtkmunit, vtgulp, vtseq`.
  - [ ] 🟢 call functions using _yul_ports_: `call'l`.
- Working with _yul variables_ using `YLVM`.
  - [x] Build YLVM functions: `$lfn $ ylvm'{pp,pv,vv}`.
  - [x] Call functions in a `YLVM`: `ycall`, `ycall0`.
  - [x] Yul variables: `Uv, Rv, ver`.
  - [x] Yul variables <-> yul ports: `ymkvar{NP}, ytkvar{NP}, ytkvarv, ytakeuvN, ytkrvN`;
  - [x] `yembed`, `yreturn`.
  - [x] Process _yul variables_ in pure yul functions: `ywith{ur,rv}N{_1}`.
  - [ ] 🟠 `(rebound syntax) if, ywhen, yunless` to work with BOOL _yul variable_.
- Working with storage:
  - [x] Extensible Storage type: `SReferenceable(sget'l, sput'l)`.
  - [x] 🟢 Storage primitives:
    - `sget{NP,N}`
    - `sput (<:=), sputM (<<:=), sputMM (<<:=<<)`.
  - [x] 🟠 Storage functions working with `Referenceable` types.
- Storage Hash Map.
  - [ ] `shmapRef'l, shmapGet'l, shmapPut'l`.
  - [ ] `(.->), shmapRef`
  - [ ] `shmapGet`

**internal: lvm (linearly-versioned-monad)**

- LinearContext
- LVM
- LVM combinators: toss{1,N}, pass{1,N},
- LVMVar

### yol-suite

- yolc
  - SolidityCode Adapters
    - [ ] 🟢 Generate external function spec from solidity interface files.
    - [ ] 🟠 Solidity struct generator for types.
  - Singleton program factory
    - [x] Program interface, e.g. `interface IERC20Program`.
    - [x] Program factory, e.g. `function createERC20Program()`.
  - Program upgradability
    - [x] Non-upgreadable.
  - Contract verification support
    - [ ] 🟢 EIP-1967 compatible "stunt contract" generator. A stunt contract includes both:
          1. the program's interface necessary to interact with the program via EIP-1967-aware
             explorers,
          2. a copy of Haskell main source code in a block of solidity comments.
  - CLI
    - [x] ⭐ `yolc`, a MVP in shells script, prepares YOLC project and invoke YOLC builder.
- [-] CodeGens/GraphVizGen. (Some constructors missing)
- [x] ReplUtils: printCat, printFn, previewFn, previewCat

### DevX

- Developer communication
  - [x] Annotated ERC20 demo
- Software distributions
  - [x] Nix flake
  - [x] 🌟 yolc.dev playground
  - [ ] 🌟 github container

## TODOs beyond 0.1.0.0

### General

- First party function type.

### yul-dsl

- YulCat
  - Type safety
    - [ ] ❓ further encode total functions in type
- Eval
  - [ ] 🟠 e2e test against solidity/foundry setup

### yol-suite

- yolc
  - Advanced program deployment strategy:
    - [ ] manual logic split through delegateCall.
    - [ ] auto logic split & dispatching,
    - [ ] Shared library.
  - Program upgradability:
    - [ ] 🟠 Beacon upgradability.
  - CLI
    - [ ] Use 'THSH' to mix shell scripting and publish its haskell binary.
- attila
  - Test Pipeline: `attila test`
    - [ ] Foundry testing integration using stunt contract.
    - [ ] QuickCheck integration using Eval monad.
  - Deployment Pipeline: `attila deploy`
    - [ ] Deploy the program (program is an unit of deployment.)
    - [ ] Etherscan verification pipeline.

<!--
Local Variables:
fill-column: 100
flycheck-mode: 0
End:
-->

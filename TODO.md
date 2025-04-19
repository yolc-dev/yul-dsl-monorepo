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

- [ ] Use sop-core; otherwise, the simple-sop doesn't have injectivity for type inferences.
- [ ] Support Function object, hence closed cartesion; instead of the off-the-band NamedYuCat
      construct.
- [ ] Haddock doc cleanup and prettifying.

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
  - [x] 🟠 REF, storage or memory raw reference with `constRef, keyRef`.
    - SREF for strarage.
    - MREF family for memory: IMREF (immutable), LMREF (locked), and MMREF (mutable).
  - [ ] 🟢 SELECTOR
- ABICodec
  - [ ] 🟢 Compatibility with the solidity abi-spec

### yul-dsl

- YulCat
  - [x] Type conversions for `ABITypeDerivedOf, ABITypeCoercible, NP`
  - [x] SMC
  - Control flows
    - [x] `YulEmb`, embed values.
    - [x] `YulITE`, if-then-else.
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
    - [x] Type-level purity classification: `IsEffectNotPure, MayEffectWorld`.

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

- CodeGen
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

- `Data` & `Control` extensions
  - [x] `IfThenElse` for rebindable syntax.
  - [x] `PatternMatchable` and the "match, is, be" verbs.
  - [x] `MPOrd` for lifted Boolean types.
- Working with integers
  - [x] Num class with checked integer operations.
  - [x] ⭐ Maybe Num with optional integer operations and Pattern matching of support.
  - [ ] Type-safe `upCast`, and `safeCast` for down-casting to `Maybe` values.
- Additional yul objects
  - [x] Maybe a
    - [] ⚠️ Expand beyond `Maybe (INTx s n)`
  - [x] NP
  - [x] TUPLEn
- Working with pure effect
  - [x] Build pure functions `$fn`.
  - [x] Call pure functions `call`, `callN`.

### yul-dsl-linear-smc

- [x] 🌟🌟🌟 Linear safety for side effects
  - [x] Compile expression sof linear _data ports_ to YulCat
  - [x] Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
    - [ ] ⚠️ Removing over-serialization, to have more parallel computations. Validate using 'diagram'
          package based visualization.
  - [x] Build linear functions with `$lfn $ uncurry'lvv | $lfn $ uncurry'lpv`.
  - [ ] 🟢Call functions linearly with `call`, `ycall`, `ycallN`.
  - [ ] 🟢 Fix `ypure` and `yembed` (?).
- Working with _data ports_
  - [x] match data port and outputs new data port.
  - [ ] 🟢 `ywith` to work with data ports in pure yul functions.
  - [ ] 🟠 `(rebound) if, ywhen, yunless` to work with BOOL data port.
- Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
  - [x] Build YulMonad functions: `$lfn $ yulmonad'p` for versioned inputs, and `$lfn $ yulmonad'p`
        for pure inputs.
- Working with storage:
  - [x] Assorted storage functions: `SReferenceable(sget, sput), sgetN, (<==), sputN, (:|), (:=),
        sputs`.
    - [ ] ⚠️ YulVar variants.
    - [ ] 🟠 Storage functions working with `Referenceable` types.
  - [x] SHMap - Storage Hash Map.

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

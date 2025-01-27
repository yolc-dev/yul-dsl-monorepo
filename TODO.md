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

## General Refactoring Ideas

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
  - [ ] 🟢 REF, storage or memory raw reference with `constRef, keyRef`.
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
    - [ ] 🟢 `YulStaticCall`, static external function calls.
    - [ ] 🟢 `YulDelegateCall`, delegate external function calls.
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
    - [x] __validate_t_
  - Integer comparators
    - [x] eq, ne, lt, le, gt, ge
  - Safe integer arithmetic
    - [x] Safe number operation wrappers for checked numbers and maybe numbers.
    - [x] add, mull, sub, abs
    - [ ] 🟢 sig, abs
    - [ ] 🟢 divMod, quotRem
    - [ ] 🟢 complete testsuite
  - Safe value casting
    - [ ] 🟢 Casting integers
    - [ ] 🟢 Casting ADDR to U160
    - [ ] 🟢 Casting BYTESn n to uINTn
    - [ ] 🟢 complete testsuite
  - ABICodec
    - [x] __abidec_dispatcher_c_, __abidec_from_calldata_t_
    - [x] __abidec_from_memory_c_, __abidec_from_memory_t_
    - [x] __abienc_from_stack_c_, __abienc_from_stack_t_
    - [x] __keccak_c_ for supported types.
      - [ ] 🟢 __keccak_c_ evaluation function using ABICodec from eth-abi.
    - [ ] 🟢 support dispatcher decoding tuples
    - [ ] 🟢 complete testsuite
  - Exceptions
    - [x] `__const_revert0_c_`; solidity-equivalent of `revert()`
    - [ ] 🟢 `revertWithMessage`
    - [ ] 🟢 `revertWithError`
    - [ ] 🟢 complete testsuite

- CodeGen
  - Function Gen:
    - [x] Yul code generator for any YulCat
    - [ ] 🟠 Fix the implementation for all embeddable values.
  - Object builder:
    - [x] Yul object dispatcher generator for exported functions.
    - [ ] 🟠 constructor support.

- Evaluator
  - [x] `evalFn` to evaluate `Fn` (single YulCat value styled as a function) value.
  - [ ] 🟢 handling revert
  - [ ] 🟢 testsuite
  - [ ] 🟠 e2e test against solidity/foundry setup

### yul-dsl-pure

- YulCat syntactic sugars
  - [x] `Data.IfThenElse` with `RebindableSyntax`.
  - [x] `Data.PatternMatchable` with `match` and `liftCase`.
- Working with integers
  - [x] Num class with checked integer operations.
  - [x] ⭐ Maybe Num with optional integer operations and Pattern matching of support.
  - [ ] Type-safe upCast, and safeCast to optional values.
- Data
  - [x] MPOrd
- Working with pure effect
  - [x] Build pure functions `fn`.
    - [ ] 🟠 to be replaced with `$fn` using template haskell for generating automatic unique function id
  - [x] Call pure functions `callFn`.

### yul-dsl-linear-smc

- [x] 🌟🌟🌟 Linear safety for side effects
  - [x] Compile expression sof linear _data ports_ to YulCat
  - [x] Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
  - [x] Build linear functions with `lfn`. ⚠️ This will be replaced with `$yulMonadV, $yulMonadP`.
  - [x] Call functions linearly with `callFn'l`, `callFn'lpp`.
    - [ ] 🟢 `callFnN'l` to call function via N-tuple, in order to support calling 0-ary functions.
- Working with _data ports_
  - [x] match data port and outputs new data port.
  - [ ] 🟢 Num classes for data ports: mul, abs, sig, etc.
  - [ ] 🟠 ifThenElse through pattern matching on BOOL data port.
- Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
  - [ ] 🟢 Build YulMonad functions: `$yulMonadV` for versioned inputs, and `$yulMonadP` for pure inputs.
- Working with storage:
  - [x] Assorted storage functions: `SReferenceable(sget, sput), sgetN, (<==), sputN, (:|), (:=), sputs`.
  - [ ] 🟠 Storage functions working with `Referenceable` types.
  - [ ] 🟢 SHMap - Storage Hash Map.

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
          1. the program's interface necessary to interact with the program via EIP-1967-aware explorers,
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

# yul-dsl

- YulCat
  - Type safety
    - [ ] ❓ further encode total functions in type

# yol-suite

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

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

## TODOs for 0.1.0.0

- eth-abi
  - CoreType
    - [x] NP (N-ary Product, type-level recursive-friendly alternative to tuple type)
    - [x] BOOL
    - [x] INTx s n
    - [x] BYTESn
    - [x] ADDR
- yul-dsl
  - YulCat
    - Value functions
      - [x] All integer number types: U8, U16.. U256; I8, I16, .. I256.
      - [x] All fixed size bytes types: B1, B2... B32.
      - [ ] 🚧 ⭐ Safe number handling with
        1. checked number operations,
        2. number operations over optional values,
        3. pattern matching of optional (Haskell `Maybe` type) values
        4. type-safe upCast, and safeCast to optional values.
        - [ ] 🟢 `YulCast`, casting values between value types.
        - [x] 🟢 All `Num` and `Maybe Num` built-ins
      - [x] yulKeccak256 for supported types.
    - Side Effects
      - [x] `YulSGet`, `YulSPut` for raw storage operations.
      - [x] `YulCall`, external function calls.
    - Exceptions
      - [x] `revert0`, solidity-equivalent of `revert()`
    - Control flows
      - [x] Haskell native if-then-else expression through "RebindableSyntax".
      - [x] ⭐ Pattern matching support of optional number values.
    - Yul Object
      - [x] Function export modifiers resembling solidity: `pureFn, staticFn, externalFn`.
    - Type safety
      - [x] Type-level purity classification: `IsEffectNotPure, MayEffectWorld`.
  - Built-in Yul Functions Infrastructure
    - [ ] 🚧 🟢 Full arithmetic support
    - [ ] 🚧 🟢 Full ABICodec support
  - Working with pure effect
    - [x] Build pure functions `fn`. ⚠️ This will be replaced with `$fn`.
    - [x] Call pure functions `callFn`.
  - CodeGen
    - [x] Yul code generator for any YulCat
    - [x] Yul object dispatcher generator for exported functions.
  - Evaluator
    - `evalFn` to evaluate `Fn` (single YulCat value styled as a function) value.
- yul-dsl-linear-smc
  - [x] 🌟🌟🌟 Linear safety for side effects
    - [x] Compile expression sof linear _data ports_ to YulCat
    - [x] Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
    - [x] Build linear functions with `lfn`. ⚠️ This will be replaced with `$yulMonadV, $yulMonadP`.
    - [x] Call functions linearly with `callFn'l`, `callFn'lpp`.
      - [ ] 🟢 `callFnN'l` to call function via N-tuple, in order to support calling 0-ary functions.
  - Working with _data ports_
    - [x] 🟢 match'l for pattern matching data ports.
    - [ ] 🟢 ifThenElse through pattern matching on BOOL data port.
    - [ ] 🟢 Num classes for data ports: mul, abs, sig, etc.
  - Working with storage:
    - [x] Assorted storage functions: `sget, sput, sgetN, (<==), sputN, sputs, (:=)`.
- yol-suite
  - YOLC
    - Singleton program factory
      - [x] Program interface, e.g. `interface IERC20Program`.
      - [x] Program factory, e.g. `function createERC20Program()`.
    - Contract verification support
      - [ ] 🟢 EIP-1967 compatible "stunt contract" generator. A stunt contract includes both:
        1. the program's interface necessary to interact with the program via EIP-1967-aware explorers,
        2. a copy of Haskell main source code in a block of solidity comments.
  - CLI
    - [x] ⭐ `yolc`, a MVP in shells script, prepares YOLC project and invoke YOLC builder.
- Developer communication
  - [x] Annotated ERC20 demo
- Software distributions
  - [x] Nix flake
  - [ ] 🟢 Rudimentary github dev console

## TODOs for 0.2.0.0

- eth-abi
  - CoreType
    - [ ] 🟠 ARRAY a
    - [ ] 🟠 BYTES
    - [ ] 🟠 STRING
  - ExtendedType
    - [ ] 🟠 REF, storage or memory reference
    - [ ] 🟠 SELECTOR
    - [ ] 🟠 TUPLEn, STRUCT with named fields, etc.
  - ABICodec
    - [ ] 🟢 Compatibility with the solidity abi-spec
- yul-dsl
  - YulCat
    - Value functions
      - [ ] 🟢 yulKeccak256 evaluation function using ABICodec from eth-abi.
      - [ ] 🟢 array length built-in.
      - [ ] 🟠 Maybe support of non word values.
    - Exceptions
      - [ ] 🟢 `revertWithError`
      - [x] 🟢 `revertWithMessage`
    - Control flows
      - [ ] 🟠 `YulMapArray`, tight loop over an array.
    - Yul object
    - Side Effects
      - [ ] 🟢 `YulStaticCall`, static external calls.
      - [ ] 🟢 `YulDelegateCall`, delegate external calls.
    - Type safety
      - ❓ further encode total functions in type
  - Working with pure effect
    - [ ] 🟠 `$fn` template haskell for generating automatic unique function id.
  - CodeGen
    - Function Gen:
      - [ ] 🟠 Fix the implementation for all embeddable values.
    - Object builder:
      - [ ] 🟠 constructor support.
  - Evaluator
    - [ ] 🟢 handling exception
    - [ ] 🟢 test coverage, and check against foundry results
- yul-dsl-linear-smc
  - Working with _versioned data port_ through `YulMonad`, a "Linearly Versioned Monad."
    - [ ] 🟢 Build YulMonad functions: `$yulMonadV` for versioned inputs, and `$yulMonadP` for pure inputs.
    - [ ] 🟠 Storage functions working with `Referenceable` types.
- yol-suite
  - YOLC
    - [ ] 🟠 Solidity struct generator for types.
    - Advanced program deployment strategy:
      - [ ] 🟠 manual logic split through delegateCall.
      - [ ] 🔴 auto logic split & dispatching,
      - [ ] 🔴 Shared library.
    - Program upgradability:
      - [ ] 🟠 Beacon upgradability.
    - Contract verification support
      - [ ] 🔴 Full stunt contract generator.
  - CLI
    - [ ] 🔴 Use 'THSH' to mix shell scripting and publish its haskell binary.
- attila
  - Test Pipeline: `attila test`
    - [ ] 🟠 Foundry testing integration using stunt contract.
    - [ ] 🔴 QuickCheck integration using Eval monad.
  - Deployment Pipeline: `attila deploy`
    - [ ] 🟠 Deploy the program (program is an unit of deployment.)
    - [ ] 🔴 Etherscan verification pipeline.
- drwitch
  - ...
- Developer communication
- Software distributions
  - [ ] better github dev console
  - [ ] yolc.dev playground

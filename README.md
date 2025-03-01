Yolc - A Safe, Expressive, Fun Language for Ethereum
====================================================

<div align="center">
<h1>Welcome to YulDSL's monorepo 👋</h1>

<p>
  <img alt="Static Badge" src="https://img.shields.io/badge/AI--Free_Code-Green">
  <a href="https://twitter.com/yolc_dev" target="_blank">
    <img alt="Twitter: Superfluid_HQ" src="https://img.shields.io/twitter/follow/Superfluid_HQ.svg?style=social" />
  </a>
</p>
</div>

The key motivation behind Yolc is to strike a balance between the following values for building
Ethereum smart contracts.

*Safe*

Yolc is purely functional with linear type safety, made for the Ethereum virtual machine.

> What does *purely functional linear type safety* mean here? Read more [here](#).

*Expressive*

Yolc embeds itself in the Haskell language before being compiled into Solidity/Yul code.

> Why does *expressiveness* matter? Read more [here](#).

*Fun*

Yolc allows you to write safe code in production, a joyful experience for super coders.

> Check out these [example codes](#).

> [!TIP]
>
> Yolc is a compiler program for "YulDSL/Haskell." YulDSL is a domain-specific language (DSL) based
> on [category theory](https://category-theory.org/) for
> [Solidity/Yul](https://soliditylang.org/). YulDSL can embed itself in different languages, with
> "YulDSL/Haskell" being the first of its kind. Curiously, the name "yolc" sounds similar to "solc,"
> the compiler program for "Solidity/Yul."
>
> Do not worry if you don't understand some of these concepts. You may start with Yolc right away
> and have a rewarding, fun experience writing safer production smart contracts. However, if you do
> feel adventurous and want to delve into the inner workings of YulDSL, read
> [here](./hs-pkgs/yul-dsl/README.md).

> [!CAUTION]
>
> 🚧 While this project is still work in progress 🚧, currently it is of /technical preview/
> version, read [the introduction](https://yolc.dev/docs/getting-started/introduction/)
>
> Contact me at info@yolc.dev or join the [matrix room](https://matrix.to/#/#yolc:matrix.org) if you
> want to learn more!

------------------------------------------------------------------------------------------

Features
========

Ethereum-Compatible & Extensible Types
--------------------------------------

> [!NOTE]
>
> These include [Ethereum contract ABI
> specification](https://docs.soliditylang.org/en/latest/abi-spec.html) implemented in as *core
> types*, their *type extensions*, including *dependently typed extensions*.

Unlike solidity, and to accommodate Haskell lexical rules, types are all in capitalize letters:

* Boolean type `BOOL`, and its values `true`, `false`.
* Address type `ADDR`.
* Integers types: `I8`, `I16`, ... `I256`; `U8`, `U16`, ... `U256`.
* etc.

Full table of the types implemented and planned can be found [here](./hs-pkgs/eth-abi/README.md).

Expressive Pure Functions
-------------------------

**Haskell Native Syntax**

TODO.

**Currying Function Definition**

```haskell
-- define a pure value function
PureFn (U256 -> U256 -> U256)
foo3 = $fn
  \a b c -> a + b + c

-- call other pure value function
call_foo3 :: PureFn (U256 -> U256)
call_foo3 = $fn
  \a -> callFn foo3 a a a
```

**Pattern Matching**

```haskell
-- ⭐ pattern matching coming to Ethereum
\x y def -> match (x + y) \case
  Nothing -> def  -- number overflown
  Just z  -> z    -- just do it
```

Linear Safety For Side Effects
------------------------------

```haskell
  -- fetch balance of the account
  (to_p, balanceBefore) <- pass to_p \to_p ->
    ypure $ balanceOf `callFn'l` ver'l to_p

  -- use linear port values safely
  (to_p, amount_p) <- passN_ (to_p, amount_p) \(to_p, amount_p) ->
    -- update balance
    shmapPut balanceMap to_p (balanceBefore + ver'l amount_p)

  -- call unsafe external contract onTokenMinted
  externalCall onTokenMinted (ver'l to_p) (ver'l amount_p)
```

Foundry Integration
-------------------

Yolc leverages the power of the best tooling in the ecosystem while focusing on what it is best at:
A safe, expressive, and fun programming language. It is not a full toolkit for Ethereum
development. Hence, Yolk works best in tandem with the [foundry
toolkit](https://github.com/foundry-rs/foundry).

------------------------------------------------------------------------------------------

Packages
========

- [*eth-abi*](./hs-pkgs/eth-abi/README.md) - Ethereum contract ABI specification in Haskell
- [*yul-dsl*](./hs-pkgs/yul-dsl/README.md) - A DSL targets Solidity/Yul
- [*yul-dsl-pure*](#) - YulDSL/Haskell's support for pure effects
- [*yul-dsl-linear-smc*](./hs-pkgs/yul-dsl-linear-smc/README.md) - YulDSL/Haskell's support for side
  effects using linear types
- [*yol-suite*](./hs-pkgs/yol-suite/README.md) - A Collection of YulDSL Programs for the New Pioneer
  of Ethereum Smart Contracts Development
  - **yolc**: the evil twin of "solc"; this is the compiler program for "YulDSL/Haskell".
  - **attila**: who wields the foundy, forges his path; this is the counter part of the "forge" from
    [foundry](https://github.com/foundry-rs/foundry). However, it mostly invokes directly "forge"
    for you, since yol-suite integrates itself with the [foundry
    toolkit](https://github.com/foundry-rs/foundry).
  - **drwitch**: who persuades the tyrant, shapes our history; this is the counterpart of the
    "cast" from [foundry](https://github.com/foundry-rs/foundry).

------------------------------------------------------------------------------------------

Roadmap
=======

For the ongoing feature development, here is the complete [todo list](TODO.md).

Milestones
----------

- [x] Jan 6th, 2025: public announcement, with the first technical release (unversioned).
- [ ] End of Feb 2025: version 0.0.1.0 with major features completion.
- [ ] End of Mar 2025: version 0.0.2.0 with first live in production projects.
- ...

Research Topics
---------------

- A paper on the linearly versioned monad, the cornerstone of Yolc's linear safety, as a survey of
  comparing it to other resource management method including monadic regions, CoDensity, etc.
- Liquid Haskell integration.
- Extend core types through dependent types.
- Portable YulDSL artifact for non-Haskell language embedding and cross-languages modules.

<!--
Local Variables:
fill-column: 100
End:
-->

Yolc - A Safe, Expressive, Fun Language for Ethereum
====================================================

The main motivation behind Yolc is to strike a balance between the following values for building Ethereum smart
contracts:

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
> Yolc is a compiler program for "YulDSL/Haskell". YulDSL is a domain-specific language (DSL) based on [category
> theory](https://category-theory.org/) for [Solidity/Yul](https://soliditylang.org/). YulDSL can be embedded in
> different languages, with "YulDSL/Haskell" being the first of its kind. Curiously, the name "yolc" sounds similar to
> "solc", the compiler program for "Solidity/Yul".
>
> Do not worry if you don't understand some of these concepts, you can start with Yolc right away and have a rewarding,
> fun experience writing safer production smart contracts. However, if you do feel adventurous and want to delve into
> the inner workings of YulDSL, read [here](./hs-pkgs/yul-dsl/README.md).

> [!CAUTION]
>
> 🚧 While this project is still work in progress 🚧, currently it is of /technical preview/ version, read [the
> introduction](https://yolc.dev/docs/getting-started/introduction/)
>
> Contact me at info@yolc.dev or join the [matrix room](https://matrix.to/#/#yolc:matrix.org) if you want to learn more!

------------------------------------------------------------------------------------------

Features
========

Ethereum-Compatible & Extensible Types
--------------------------------------

> [!NOTE]
>
> These include [Ethereum contract ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
> implemented in as *core types*, their *type extensions*, including *dependently typed extensions*.

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
foo3 = fn @(Maybe U8 -> Maybe U8 -> Maybe U8 -> Maybe U8) "foo3"
  \a b c -> a + b + c

-- call other pure value function
call3 = fn @(Maybe U8 -> Maybe U8) "call3"
  \a -> call foo3 a a a
```

**Pattern Matching**

```haskell
add_maybe_int96_with_default = fn @(I96 -> I96 -> I96 -> I96) "add_maybe_int96_with_default"
  \x y def -> match (inCase (Just x) + inCase (Just y)) \case
    Nothing -> def
    Just z  -> z
```

Linear Safety For Side Effects
------------------------------

```haskell
  \account'p mintAmount'p -> LVM.do
  -- fetch balance of the account
  (account'p, balanceBefore) <- pass account'p balance_of
  -- use linear port (naming convention, "*'p") values safely
  (account'p, mintAmount'p) <- passN_ (account'p, mintAmount'p) \(account'p, mintAmount'p) ->
    -- update balance
    sput (balance_sloc account'p) (balanceBefore + ver'l mintAmount'p)
  -- call unsafe external contract onTokenMinted
  externalCall onTokenMinted (ver'l account'p) (ver'l mintAmount'p)
```

Foundry Integration
-------------------

Yolc leverages the power of the best toolking in the ecosyste, while focusing on what it is best at: a safe, expressive
and fun programming language. It is not a full toolkit for Ethereum development. Hence, it is recommended to work in
tandem with the [foundry toolkit](https://github.com/foundry-rs/foundry).

------------------------------------------------------------------------------------------

Packages
========

- [*eth-abi*](./hs-pkgs/eth-abi/README.md) - Ethereum contract ABI specification in Haskell
- [*yul-dsl*](./hs-pkgs/yul-dsl/README.md) - A DSL targets Solidity/Yul
- [*yul-dsl-pure*](#) - YulDSL/Haskell's support for pure effects
- [*yul-dsl-linear-smc*](./hs-pkgs/yul-dsl-linear-smc/README.md) - YulDSL/Haskell's support for side effects using
  linear types
- [*yol-suite*](./hs-pkgs/yol-suite/README.md) - A Collection of YulDSL Programs for the New Pioneer of Ethereum Smart
  Contracts Development
  - **yolc**: the evil twin of "solc"; this is the compiler program for "YulDSL/Haskell".
  - **attila**: who wields the foundy, forges his path; this is the counter part of the "forge" from
    [foundry](https://github.com/foundry-rs/foundry). However, it mostly invokes directly "forge" for you, since
    yol-suite integrates itself with the [foundry toolkit](https://github.com/foundry-rs/foundry).
  - **drwitch**: who persuades the tyrant, shapes our history; this is the counter part of the "cast" from
    [foundry](https://github.com/foundry-rs/foundry).

------------------------------------------------------------------------------------------

Roadmap
=======

For the ongoing feature development, here is the ccomplete [todo list](TODO.md).

Milestones
----------

- [x] Jan 6th, 2025: public announcement, with the first technical release (unversioned).
- [ ] End of Jan 2025: version 0.0.1.0 with major features completion.
- [ ] End of Feb 2025: version 0.0.2.0 with first live in production projects.
- ...

Research Topics
---------------

- A paper on the linearly versioned monad, the corner stone of the yolc linear safety, as a survey of comparing it to
  other resource management method including monadic regions, CoDensity, etc.
- Liquid haskell integration.
- Extend core types through dependent types.
- Portable YulDSL artifact for non-Haskell language embedding and cross-languages modules.

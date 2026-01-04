# Type system

Struktur's type system is strongly based on [Hindley-Milner type inference](https://en.wikipedia.org/wiki/Hindley-Milner_type_system) and [System F](https://en.wikipedia.org/wiki/System_F). It is a rank-2 predicative type system, featuring [algebraic data types](#algebraic-data-types), [type functions](#type-functions), [universal quantification](#universal-quantification), [typeclasses](#typeclasses), and [an effect system](#effect-system).

## Algebraic data types

Types can be either *product* or *sum* types.

Product types are a single type constructor that is a combination of types.

```ocaml
type Person = { Int; String }
```

Sum types are a set of one or more type constructors, each of which may represent a combination of types.

```ocaml
type Contact = Address { String }
             | Phone { Int }
```

Aliases are structural type aliases; they provide a different name for a type. An alias is entirely equivalent to its aliased type — an alias is not a distinct type.

```ocaml
alias User = Person
```

## Primitive types

### `()`

`()` or "unit" is an uninteresting single-value type. It can be conceptualized as a sum type with a single constructor.

```ocaml
type () = ()
```

### `Int`

`Int` is a 64-bit signed integer. It can be conceptualized as a sum type with 2^64 constructors.

```ocaml
type Int = 0 | 1 | 2 | ... | -1 | -2 | ...
```

### `Bool`

`Bool` is a logical boolean. It can be conceptualized as a sum type with 2 constructors.

```ocaml
type Bool = true | false
```

### `String`

`String` is a sequence of characters (representation TBD).

## Type functions

A type function is a type-level function accepting types as arguments and producing a type. They are declared like ADTs except with a list of type variables after the name.

```ocaml
type Option 'a = Some { 'a }
               | None
```

## Universal quantification

A polymorphic function can be written as

```ocaml
let id : forall 'a. 'a -> 'a
       = fun x -> x
```

`forall 'a` indicates that the type applies to any type `'a`. `forall.` can generally be omitted, however, as the quantifier is inferred.

### Higher-rank polymorphism

Struktur's type system employs rank-2 predicative polymorphism. This means that a quantifier can occur nested to the left of at most a single function arrow.

```ocaml
f : (forall 'a. 'a -> 'a) -> ()
  = fun id -> let _ = id 0 in
              let _ = id true in
              ()
```

The function `id` above is a function quantified over any type `'a`, itself passed as a parameter to the function `f`.

A rank-2 type is one taking a quantified type, a rank-1 type is itself a quantified type, and a rank-0 type is a type with no quantifiers.

```ocaml
rank2 : (forall 'a. 'a) -> ()
rank1 : forall 'a. 'a
rank0 : ()
```

## Typeclasses

**TBD**

## Effect system

**TBD**

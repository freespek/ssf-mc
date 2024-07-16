# Python to TLA+ translation rules

On the Python side, we have the `typing` package and types defined in `pyrsistent`. 

We will later define, but for now assume the existence of, a type-translation from those types to Apalache's type system.

We maintain the following convention: if `t` is the Python type, we label the corresponding Apalache type as `t^`.

## Translation rules

We will be using the [Lists](https://github.com/konnov/tlaki/blob/main/src/Lists.tla) module, in lieu of `Sequences`, to better match the 0-indexing convention of Python. To that end, we introduce the type notation:
```
List(t^) := { es: Seq(t^) }
```
that is, the instantiation of the `$list` alias defined in `Lists.tla` with the concrete type `t^`.


### Singleton vector
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L15-L16

```
    a: t
  ==========   pvector_of_one_element(a) 
    e: t^
==========================================
        List(<< e >>) : List(t^)
```

A singleton Python vector is translated to a single-element list, and annotated as such.


### Vector concatenation
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L19-L20

```
   a: PVec[t]        b: PVec[t]
 ===============   ===============   pvector_concat(a, b) 
   e: List(t^)       f: List(t^)
============================================================
                 Concat(e,f) : List(t^)
```

Vector concatenation is translated to the list concatenation.


### Set sequentialization
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L23-L24


```
         a: PSet[t]         
       ==============   from_set_to_pvector(a) 
         e: Set(t^)       
======================================================
  ApaFoldSet( Push, List(<<>>: Seq(t^)), e ) : List(t^)
```

We use fold, to create a sequence (in some order) from the set.


### Empty set
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L27-L28


```
  pset_get_empty : PSet[t]
============================
       {} : Set(t^)
```

The only relevant part here is that we need a type annotation on the Python side to correctly annotate the empty set in TLA+.


### Set union
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L31-L32


```
    a: PSet[t]       b: PSet[t]
  ==============   ==============   pset_merge(a, b) 
    e: Set(t^)       f: Set(t^)
======================================================
                e \cup f : Set(t^)
```

Set union is translated to the TLA+ native set union.

### Set flattening
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L35-L36


```
         a: PSet[PSet[t]]         
       ====================   pset_merge_flatten(a) 
         e: Set(Set(t^))       
=====================================================
                UNION e : Set(t^)
```

Set flattening is translated to the TLA+ native big UNION.


### Set intersection
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L42-L43


```
    a: PSet[t]       b: PSet[t]
  ==============   ==============   pset_intersection(a, b) 
    e: Set(t^)       f: Set(t^)
=============================================================
                   e \cap f : Set(t^)
```

Set intersection is translated to the TLA+ native set intersection.

### Set difference
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L46-L47


```
    a: PSet[t]       b: PSet[t]
  ==============   ==============   pset_difference(a, b) 
    e: Set(t^)       f: Set(t^)
===========================================================
                      e \ f : Set(t^)
```

Set difference is translated to the TLA+ native set difference


### Singleton set
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L50-L51

```
    a: t
  =========   pset_get_singleton(a) 
    e: t^
=====================================
           { e } : Set(t^)
```

A singleton Python set is translated to a TLA+ native single-element set.

### Set extension
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L54-L55


```
    a: PSet[t]       b: t
  ==============   =========  pset_add(a, b) 
    e: Set(t^)       f: t^
==============================================
            e \cup { f } : Set(t^) 
```

A set extension is translated to a combination of union and singleton-set construction. Semantically, this is the equivalence
```
pset_add(a,b) === pset_merge(a, pset_get_singleton(b))
```








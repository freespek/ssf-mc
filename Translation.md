# Python to TLA+ translation rules

Assume you have a type system `A` in python, and a type system `B` in TLA+. 

We will later define, but for now assume the existence of, a type-translation function `T` from `A` to `B`.


## Translation rules


### Singleton vector
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L15-L16

```
    a: t
  ==========   pvector_of_one_element(a) 
    e: T(t)
==========================================
            << e >> : Seq[T(t)]
```

A singleton Python vector is translated to a single-element sequence, and annotated as such (as opposed to a tuple)


### Vector concatenation
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L19-L20

```
   a: PVec[t]         b: PVec[t]
 ================   ===============   pvector_concat(a, b) 
   e: Seq[T(t)]       f: Seq[T(t)]
============================================================
                     e \o f : Seq[T(t)]
```

Vector concatenation is translated to the sequence concatenation.


### Set sequentialization
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L23-L24


```
         a: PSet[t]         
       ================   from_set_to_pvector(a) 
         e: Set[T(t)]       
========================================================
  ApaFoldSet( Append, <<>>: Seq[T(t)], e ) : Seq[T(t)]
```

We use fold, to create a sequence (in some order) from the set.


### Empty set
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L27-L28


```
  pset_get_empty : PSet[t]
============================
       {} : Set[T(t)]
```

The only relevant part here is that we need a type annotation on the Python side to correctly annotate the empty set in TLA+.


### Set union
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L31-L32


```
    a: PSet[t]         b: PSet[t]
  ================   ===============   pset_merge(a, b) 
    e: Set[T(t)]       f: Set[T(t)]
=========================================================
                  e \cup f : Set[T(t)]
```

Set union is translated to the TLA+ native set union.

### Set flattening
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L35-L36


```
         a: PSet[PSet[t]]         
       ====================   pset_merge_flatten(a) 
         e: Set[Set[T(t)]]       
========================================================
                UNION e : Set[T(t)]
```

Set flattening is translated to the TLA+ native big UNION.


### Set intersection
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L42-L43


```
    a: PSet[t]         b: PSet[t]
  ================   ===============   pset_intersection(a, b) 
    e: Set[T(t)]       f: Set[T(t)]
================================================================
                  e \cap f : Set[T(t)]
```

Set intersection is translated to the TLA+ native set intersection.

### Set difference
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L46-L47


```
    a: PSet[t]         b: PSet[t]
  ================   ===============   pset_difference(a, b) 
    e: Set[T(t)]       f: Set[T(t)]
===============================================================
                  e \ f : Set[T(t)]
```

Set difference is translated to the TLA+ native set difference


### Singleton set
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L50-L51

```
    a: t
  ==========   pset_get_singleton(a) 
    e: T(t)
======================================
         { e } : Set[T(t)]
```

A singleton Python set is translated to a TLA+ native single-element set.

### Set extension
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L54-L55


```
    a: PSet[t]         b: t
  ================   ===========  pset_add(a, b) 
    e: Set[T(t)]       f: T(t)
==================================================
             e \cup { f } : Set[T(t)] 
```

A set extension is translated to a combination of union and singleton-set construction. Semantically, this is the equivalence
```
pset_add(a,b) === pset_merge(a, pset_get_singleton(b))
```










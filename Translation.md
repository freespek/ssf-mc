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

### Element choice
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L58-L60


```
    a: PSet[t]
  ==============   pset_pick_element(a) 
    e: Set(t^)
=========================================
         CHOOSE x \in e: TRUE: t^
```

We translate this to the built in deterministic choice in TLA+. We cannot account for the dynamic non-emptiness requirement. Instead, in that scenario, the value of this expression is some unspecified element of the correct type.

### Set filter
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L63-L70


```
    a: Callable[[t], bool]        b: PSet[t]
  ===========================   ==============   pset_filter(a, b) 
         e: t^ -> bool            f: Set(t^)
====================================================================
                      { x \in f: e[x] }: Set(t^)
```

Set filtering is translated to the TLA+ native filter operation.

### Set maximum
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L74-L76


```
    a: PSet[t]       b: Callable[[t], T]        
  ==============   =======================   pset_max(a, b) 
    e: Set(t^)           f: t^ -> T^            
=============================================================
      CHOOSE max \in e: \A x \in e: Le(f[x], f[max])
```

Here, the translation depends on the type `T` (resp. type `T^`), since there is no built-in notion of ordering in TLA+. If `T^` is an integer type, then 
```
Le(x,y) == x <= y
```
However, if `T^` is a tuple type `<<int, int>>`, it is instead 

```
Le(x,y) == 
  IF x[1] > y[1]
  THEN FALSE
  ELSE IF x[1] < y[1]
       THEN TRUE
       ELSE x[2] <= y[2]
```


### Set sum
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L79-L80


```
            a: PSet[int]
          ================   pset_sum(a) 
            e: Set(int)
===========================================================
  LET Plus(x,y) == x + y IN ApaFoldSet(Plus, 0, e ): int
```

We translate a set sum with an aggregator fold.

### Set emptiness check
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L83-L84


```
     a: PSet[t]         
   ==============   pset_is_empty(a) 
     e: Set(t^)       
======================================
            e = {} : bool
```

The emptiness check is translated to a comparison with the explicitly constructed empty set.

### Vector-to-Set conversion
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L87-L88


```
    a: PVec[t]         
  ===============   from_pvector_to_pset(a) 
    e: List(t^)       
=============================================
  { At(e, i) : i \in Indices(e) }: Set(t^)            
```

We translate the set-conversion, by mapping the accessor method over `Indices`.

### Set mapping
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L91-L97


```
    a: Callable[[t1], t2]       b: PSet[t1]
  =========================   ==============   pset_map(a, b) 
        e: t1^ -> t2^           f: Set(t1^)
===============================================================
                { e[x]: x \in f}: Set(t2^)
```

Set mapping is translated to the TLA+ native map operation.

### Function domain inclusion check
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L100-L101


```
    a: PMap[t1, t2]       b: t1
  ===================   =========   pmap_has(a, b) 
     e: t1^ -> t2^        f: t1^
===================================================
              f \in DOMAIN e: bool 
```

Function domain inclusion checking is translated to the TLA+ native set-inclusion operation for `DOMAIN`.

### Function application
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L104-L106


```
    a: PMap[t1, t2]       b: t1
  ===================   =========   pmap_get(a, b) 
     e: t1^ -> t2^        f: t1^
===================================================
                  e[f]: t2^
```

Function application is translated to the TLA+ native function application. We cannot account for the dynamic domain-membership requirement. Instead, in that scenario, the value of this expression is some unspecified element of the correct type.


### Empty function
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L109-L110


```
         pmap_get_empty : PMap[t1, t2]
===============================================
  SetAsFun({}: Set(<<t1^, t2^>>)): t1^ -> t2^
```

We use Apalache's `SetAsFun`, since we only need to annotate the empty set with the correct tuple type. The native construction via `[ _ |-> _]` would require us to invent a codomain value, which we might not have access to if `t1 != t2` (but could be e.g. `Gen`'d since we know it will never be used).

### Function update
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L113-L114


```
    a: PMap[t1, t2]       b: t1       c: t2
  ===================   =========   ==========   pmap_set(a, b, c) 
     e: t1^ -> t2^        f: t1^      g: t2^
===================================================================
                [e EXCEPT ![f] = g] : t1^ -> t2^
```

Function update is translated to the TLA+ native `EXCEPT`.

### Function combination
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L117-L118


```
                a: PMap[t1, t2]       b: PMap[t1, t2]
              ===================   ===================   pmap_merge(a, b) 
                 e: t1^ -> t2^         f: t1^ -> t2^
============================================================================================
  [ x \in (DOMAIN e \cup DOMAIN f) |-> IF x \in DOMAIN f THEN f[x] ELSE e[x] ]: t1^ -> t2^
```

Function combination is translated to a new function, defined over the union of both domains. Note that the second map dominates in the case of key/domain collisions.


### Function domain
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L121-L122


```
    a: PMap[t1, t2]   
  ===================   pmap_keys(a) 
     e: t1^ -> t2^    
======================================
          DOMAIN e: Set(t1^)
```

We translate this to the TLA+ native `DOMAIN`.


### Function codomain
https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/pythonic_code_generic.py#L125-L126


```
    a: PMap[t1, t2]   
  ===================   pmap_values(a) 
     e: t1^ -> t2^    
========================================
   { e[x]: x \in DOMAIN e }: Set(t2^)
```

We translate this by mapping the function over its `DOMAIN`.


## Meta-rules

In order to facilitate translation to the TLA+ fragment supported by Apalache, we introduce a set of TLA-to-TLA rules, which allow us to

1. formulate translations from Python to TLA+ in the intuitive way, potentially introducing constructs like recursion, and then
2. pair them with a TLA-to-TLA rule, ending in a supported fragment. 

### Bounded primitive recursion rule

Assume we are given a `RECURSIVE` operator `Op` of arity `1`, s.t.
```
RECURSIVE Op(_)
\* @type (a) => a;
Op(x) ==
  IF P(x)
  THEN e
  ELSE G(x, Op(b(x))
```

If, for every `x`, there exists a sequence `x = v_1, ..., v_n`, such that
  - `n + 1` is bounded by some constant `N` (for any particular choice of `x` the constant may be different)
  - `P(v_n)` holds
  - `v_{i+1} = b(v_i)`

we can define:
```
\* @type (a, Int) => Seq(a);
Chain(x, N) ==
  LET 
    \* @type: (Seq(a), Int) => Seq(a);
    step(seq, i) == 
      IF i > Len(seq) \/ P(seq[1])
      THEN seq
      ELSE <<b(seq[1])>> \o seq \* Alternatively, we can append here and reverse the list at the end
  IN ApaFoldSeqLeft( step, <<x>>, MkSeq(N, LAMBDA i: i) )
```
We know the above assumptions hold, if `P(Chain(x)[1])` holds, as it returns the sequence `<<v_n, ..., x>>` under those circumstances.

Using `Chain` we can define a fold-based non-recursive operator `Op^`, such that `Op^(x) = Op(x)` under the above assumptions:

```
\* @type (a, Int) => a;
NonrecursiveOp(x, N) ==
LET chain == Chain(x, N) IN
LET step(cumul, v) == G(v, cumul) IN
ApaFoldSeqLeft( step, e, Tail(chain) )
```

Then, `Op^(x) = NonrecursiveOp(x, N)`. Alternatively,

```
\* @type (a, Int) => a;
NonrecursiveOp(x, N) ==
LET chain == Chain(x, N) IN
LET step(cumul, v) == G(v, cumul) IN
IF ~P(chain[1])
THEN CHOOSE x \in {}: TRUE
ELSE ApaFoldSeqLeft( step, e, Tail(chain) )
```
#### Optimization for associative `G`

In the special case where `G` is associative, that is, `G(a, G(b, c)) = G(G(a, b), c)` for all `a,b,c`, we can make the entire translation more optimized, and single-pass. Since `NonrecursiveOp(x,N)`, for sufficiently large `N`, computes 
```
G(v_1, G(v_2, ... (G(v_{n-2}, G(v_{n-1}, e)))))
```
and `G` is associative by assumption, then computing
```
G(G(G(G(v_1, v_2), ...), v_{n-1}), e)
```
gives us the same value. This computation can be done in a single pass:
```
NonrecursiveOpForAssociative(x, N) ==
  IF P(x)
  THEN e
  ELSE
    LET 
      \* @type: (<<a, a>>, Int) => <<a, a>>;
      step(pair, i) == \* we don't use the index `i`
        LET partialAppChain == pair[1]
            lastElemInSeq == pair[2]
        IN
          IF P(lastElemInSeq)
          THEN pair
          ELSE
            LET nextElemInSeq == b(lastElemInSeq)
            IN << G(partialAppChain, IF P(nextElemInSeq) e ELSE nextElemInSeq), nextElemInSeq >>
    IN ApaFoldSeqLeft( step, <<x, x>>, MkSeq(N, LAMBDA i: i) )[1]
```

Example:
```
RECURSIVE Op(_)
\* @type (Int) => Int;
Op(x) ==
  IF x <= 0
  THEN 0
  ELSE x + Op(x-1)
```
where `P(x) = x <= 0`, `G(a,b) = a + b`, and `b(x) = x - 1`. For this operator, we know that `Op(4) = 10`. By the above definitions:
```
\* @type (Int, Int) => Seq(Int);
Chain(x, N) ==
  LET 
    \* @type: (Seq(Int), Int) => Seq(Int);
    step(seq, i) == 
      IF i > Len(seq) \/ seq[1] <= 0
      THEN seq
      ELSE <<seq[1] - 1>> \o seq
  IN ApaFoldSeqLeft( step, <<x>>, MkSeq(N, LAMBDA i: i) )
```

Since we can easily tell that for `x = 4`, the recursion-depth bound is `4`, we can compute the above with two different constants `N`, 2 and 100, and observe that `Chain(4, 2) = <<2, 3, 4>` and `Chain(4, 100) = <<0, 1, 2, 3, 4>>`. Clearly, for our `P(x) = x <= 0`, we see `~P(Chain(4, 2)[1]) <=> ~P(2) <=> 2 > 0`, and `P(Chain(4, 100)[1]) <=> P(0) <=> 0 <= 0`. Continuing with the next operator:

```
\* @type (Int, Int) => Int;
NonrecursiveOp(x, N) ==
LET chain == Chain(x, N)
IN ApaFoldSeqLeft( +, 0, Tail(chain) )
```
we see that `NonrecursiveOp(4, 2) = 7 /= 10 = Op(4)`, but `NonrecursiveOp(4, 100) = 10 = Op(4)`. While `+` is associative, we omit the optimized translation for brevity.


### Mutual recursion cycles

Assume we are given a collection of `n` operators `Op_1, ..., Op_n` (using the convention `Op_{n+1} = Op_1`), with types `Op_i: (a_i) => a_{i+1}` s.t. `a_{n+1} = a_1`, in the following pattern:

```
RECURSIVE Op_i(_)
\* @type (a_i) => a_{i+1};
Op_i(x) == F_i(x, Op_{i+1}(b_i(x)))
```

Then, we can inline any one of these operators, w.l.o.g. `Op_1`, s.t. we obtain a primitive-recursive operator:
```
RECURSIVE Op(_)
\* @type: (a_1) => a_1;
Op(x) ==
  F_1(
    x, 
    F_2( 
      b_1(x),
      F_3(
        b_2(b_1(x)),
        F_4(
          ...
          F_n( 
            b_{n-1}(b_{n-2}(...(b_1(x)))),
            Op(b_n(b_{n-1}(...(b_1(x)))))
            )
          )
        )
      )
    )
```
for which `Op(x) = Op_1(x)` for all `x`, and `Op` terminates iff `Op_1` terminates.






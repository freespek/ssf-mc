---- MODULE Lists ----
(*
 * Typed lists indexed with 0.
 *
 * Igor Konnov, 2024.
 *
 * Subject to Apache 2.0. See LICENSE.
 *)

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE Apalache

(*
 * A list is an abstract type. You should not rely on its TLA+ representation.
 * The current implementation is a record that carries the sequence of elements.
 *
 * @typeAlias: list = { es: Seq(a) };
 *)
Lists_alises == TRUE

(**
 * Construct a list by providing a sequence of its elements.
 * 
 * @type: (Seq(a)) => $list;
 *)
List(elems) ==
    [ es |-> elems ]

(**
 * Construct an empty list of the same type as `example`.
 *
 * @type: $list => $list;
 *)
EmptyListLike(example) ==
    [ es |-> <<>> ]

(**
 * Append an element to end of a list.
 *
 * @type: ($list, a) => $list;
 *)
Push(lst, e) ==
    [ es |-> Append(lst.es, e) ]

(**
 * Extract the first element (at index 0) from the list,
 * if the list is non-empty. If the list is empty, the result is undefined.
 *
 * @type: $list => a;
 *)
First(lst) ==
    Head(lst.es)

(**
 * Get list that contains all the elements of the input list except the first one.
 *
 * @type: $list => $list;
 *)
Rest(lst) ==
    [ es |-> Tail(lst.es) ]

(**
 * Concatenate two lists.
 *
 * @type: ($list, $list) => $list;
 *)
Concat(lst1, lst2) ==
    [ es |-> lst1.es \o lst2.es ]

(**
 * Get the list size, also called list length.
 *
 * @type: $list => Int;
 *)
Size(lst) ==
    Len(lst.es)

(**
 * Get the element at index `i` such that `0 <= i < Len(lst)`.
 * If the index is out of bounds, the result is undefined.
 *
 * @type: ({ es: Seq(a) }, Int) => a;
 *)
At(lst, i) ==
    lst.es[1 + i]

(**
 * Replace the element at index `i` such that `0 <= i < Len(lst)`.
 * The new element value equals to `e`.
 * If the index is out of bounds, the resulting list is equal to the input.
 *
 * @type: ({ es: Seq(a) }, Int, a) => { es: Seq(a) };
 *)
SetAt(lst, i, e) ==
    [ es |-> [ lst.es EXCEPT ![1 + i] = e ] ]

(**
 * Get the list that contains all the elements of the input list
 * (in the original order)
 * whose indices belong to the range `start <= i < end_exclusive`.
 *
 * @type: ($list, Int, Int) => $list;
 *)
Slice(lst, start, end_exclusive) ==
    [ es |-> SubSeq(lst.es, start + 1, end_exclusive) ]

(**
 * Get the list that contains all the elements of the input list
 * (in the original order) that satisfy `Pred`.
 *
 * @type: ({ es: Seq(a) }, a => Bool) => { es: Seq(a) };
 *)
Filter(lst, Pred(_)) ==
    [ es |-> SelectSeq(lst.es, Pred) ]

(**
 * Fold-left a list. Starting with `base`, iteratively apply `Op`
 * to the 0th element, to the 1st element, etc.
 *
 * `Op(...Op(Op(base, At(lst, 0)), At(lst, 1))..., At(lst, Size(lst) - 1))`.
 *
 * @type: ({ es: Seq(a) }, b, (b, a) => b) => b;
 *)
Foldl(lst, base, Op(_, _)) ==
    ApaFoldSeqLeft(Op, base, lst.es)

(**
 * Get the set of list indices, that is, `0..(Size(lst) - 1)`.
 * This operator is tuned for Apalache.
 *
 * @type: $list => Set(Int);
 *)
Indices(lst) ==
    \* Using set operations instead of `0..(Size(lst) - 1)`,
    \* to keep the set bounded.
    ({ 0 } \union (DOMAIN lst.es)) \ { Size(lst) }

====
---- MODULE Tuples ----
(*
 * Typed operations over tuples. This module contains typed tuple constructors,
 * which resolve ambiguity between various versions of <<...>>.
 *
 * Igor Konnov, 2024.
 *
 * Subject to Apache 2.0. See LICENSE.
 *)

(**
 * Construct a pair.
 *
 * (a, b) => <<a, b>>;
 *)
Pair(x, y) ==
    LET \* @type: <<a, b>>;
        _res == <<x, y>>
    IN
    _res

(**
 * Construct a singleton tuple.
 *
 * (a) => <<a>>;
 *)
T1(x) ==
    LET \* @type: <<a>>;
        _res == <<x>>
    IN
    _res

(**
 * Construct a pair, same as `Pair(x, y)`.
 *
 * (a, b) => <<a, b>>;
 *)
T2(x, y) ==
    LET \* @type: <<a, b>>;
        _res == <<x, y>>
    IN
    _res

(**
 * Construct a triple.
 *
 * (a, b, c) => <<a, b, c>>;
 *)
T3(x, y, z) ==
    LET \* @type: <<a, b, c>>;
        _res == <<x, y, z>>
    IN
    _res

(**
 * Construct a 4-element tuple.
 *
 * (a1, a2, a3, a4) => <<a1, a2, a3, a4>>;
 *)
T4(e1, e2, e3, e4) ==
    LET \* @type: <<a1, a2, a3, a4>>;
        _res == <<e1, e2, e3, e4>>
    IN
    _res

(**
 * Construct a 5-element tuple.
 *
 * (a1, a2, a3, a4, a5) => <<a1, a2, a3, a4, a5>>;
 *)
T5(e1, e2, e3, e4, e5) ==
    LET \* @type: <<a1, a2, a3, a4, a5>>;
        _res == <<e1, e2, e3, e4, e5>>
    IN
    _res

(**
 * Construct a 6-element tuple.
 *
 * (a1, a2, a3, a4, a5, a6) => <<a1, a2, a3, a4, a5, a6>>;
 *)
T6(e1, e2, e3, e4, e5, e6) ==
    LET \* @type: <<a1, a2, a3, a4, a5, a6>>;
        _res == <<e1, e2, e3, e4, e5, e6>>
    IN
    _res

(**
 * Construct a 7-element tuple.
 *
 * (a1, a2, a3, a4, a5, a6, a7) => <<a1, a2, a3, a4, a5, a6, a7>>;
 *)
T7(e1, e2, e3, e4, e5, e6, e7) ==
    LET \* @type: <<a1, a2, a3, a4, a5, a6, a7>>;
        _res == <<e1, e2, e3, e4, e5, e6, e7>>
    IN
    _res

(**
 * Construct an 8-element tuple.
 *
 * (a1, a2, a3, a4, a5, a6, a7, a8) => <<a1, a2, a3, a4, a5, a6, a7, a8>>;
 *)
T8(e1, e2, e3, e4, e5, e6, e7, e8) ==
    LET \* @type: <<a1, a2, a3, a4, a5, a6, a7, a8>>;
        _res == <<e1, e2, e3, e4, e5, e6, e7, e8>>
    IN
    _res

(**
 * Construct a 9-element tuple.
 *
 * (a1, a2, a3, a4, a5, a6, a7, a8, a9) => <<a1, a2, a3, a4, a5, a6, a7, a8, a9>>;
 *)
T9(e1, e2, e3, e4, e5, e6, e7, e8, e9) ==
    LET \* @type: <<a1, a2, a3, a4, a5, a6, a7, a8, a9>>;
        _res == <<e1, e2, e3, e4, e5, e6, e7, e8, e9>>
    IN
    _res

(**
 * Construct a 10-element tuple.
 *
 * (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) => <<a1, a2, a3, a4, a5, a6, a7, a8, a9, a10>>;
 *)
T10(e1, e2, e3, e4, e5, e6, e7, e8, e9, e10) ==
    LET \* @type: <<a1, a2, a3, a4, a5, a6, a7, a8, a9, a10>>;
        _res == <<e1, e2, e3, e4, e5, e6, e7, e8, e9, e10>>
    IN
    _res

=======================
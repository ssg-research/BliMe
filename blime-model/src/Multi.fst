/// ******************
/// Multi-domain BliMe
/// ******************
///
/// Extends the analysis to multiple blindedness domains.
module Multi

open Value

/// ^^^^^^^^^^^
/// Definitions
/// ^^^^^^^^^^^

type blindedness_domain = x:FStar.UInt8.t{~(x = FStar.UInt8.zero)}

/// The ``multiBlinded`` type represents a type that may be blinded with any
/// of several blindedness domains.
type multiBlinded (#t:Type) =
  | MultiClear   : v:t
                 -> multiBlinded #t
  | MultiBlinded : v:t
                 -> d:blindedness_domain
                 -> multiBlinded #t

/// Convert a multiBlinded to a maybeBlinded by considering only blindedness
/// with respect to a single domain.
let for_domain (#t:Type) (d:blindedness_domain) (m: multiBlinded #t): maybeBlinded #t =
  match m with
  | MultiClear v     -> Clear v
  | MultiBlinded v d -> Blinded v
  | MultiBlinded v _ -> Clear v

/// Define a new notion of equivalence that applies to multi-domain
/// blinded values.
let domainwise_equiv (#t:eqtype) (d:blindedness_domain) (x y: multiBlinded #t) = equiv (for_domain d x) (for_domain d y)

let multi_bit_equiv  (#t:eqtype) (x y: multiBlinded #t)
    = match x, y with
       | MultiClear u, MultiClear v -> u = v
       | MultiBlinded u d1, MultiBlinded v d2 -> d1 = d2
       | _, _ -> false

let multi_bit_redaction (#t:eqtype) (x: multiBlinded #t) (v:t)
    = match x with
       | MultiBlinded _ d -> MultiBlinded v d
       | MultiClear v -> x

let multi_bit_unwrap (#t:eqtype) (x: multiBlinded #t)
    = match x with
       | MultiBlinded v _ -> v
       | MultiClear v -> v

/// Next, we prove the same lemmas as for single-bit blindedness.
///
/// Equivalence is an equivalence relation:
///
///  - **Reflexivity**
let equal_values_are_equivalent (t:eqtype) (lhs rhs:multiBlinded #t):
  Lemma (requires lhs = rhs)
        (ensures forall (d:blindedness_domain). domainwise_equiv d lhs rhs) =
  ()

///  - **Symmetry**
let equivalence_is_symmetric (t:eqtype) (d:blindedness_domain) (lhs rhs: multiBlinded #t):
    Lemma (requires domainwise_equiv d lhs rhs)
          (ensures  domainwise_equiv d rhs lhs)
    = ()

///  - **Transitivity**
let equivalence_is_transitive (t:eqtype) (d:blindedness_domain) (lhs mid rhs:multiBlinded #t):
    Lemma (requires (domainwise_equiv d lhs mid) /\ (domainwise_equiv d mid rhs))
          (ensures   domainwise_equiv d lhs rhs)
    = ()

/// Next, we show that equivalence on non-blinded values is just the
/// normal equality relation.
let equivalent_clear_values_are_equal (t:eqtype) (x y:multiBlinded #t):
    Lemma (requires MultiClear? x /\ MultiClear? y /\ (exists (d:blindedness_domain). domainwise_equiv d x y))
          (ensures x = y)
    = ()

/// Finally, we show that `multiBlinded` is a blinded_data_representation.
instance multi_bit_blinding (#inner:eqtype) : blinded_data_representation (multiBlinded #inner) = {
  inner = inner;
  equiv = multi_bit_equiv;
  is_blinded = (fun (x: multiBlinded #inner) -> MultiBlinded? x);
  redact = multi_bit_redaction;
  unwrap = multi_bit_unwrap;
  make_clear = MultiClear;
  properties =  ()
}

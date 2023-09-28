/// ****************
/// Blindable values
/// ****************
///
/// This module contains types to represent blindable values and operations
/// on them.
module Value

/// First, we define what a "blindable" value should look like, so that many
/// different data representations can be used in our proofs.
class blinded_data_representation (outer:eqtype) = {
  inner: eqtype;
  equiv: outer -> outer -> bool;
  is_blinded: outer -> bool;
  redact: outer -> inner -> outer;
  unwrap: outer -> inner;
  make_clear: inner -> outer;
  [@@@FStar.Tactics.Typeclasses.no_method]
  properties: squash (
    (forall (x y: outer). x = y ==> equiv x y) /\
    (forall (x y: outer). equiv x y <==> equiv y x) /\
    (forall (x y: outer). equiv x y ==> is_blinded x = is_blinded y) /\
    (forall (x y z: outer). equiv x y /\ equiv y z ==> equiv x z) /\
    (forall (x: outer) (d: inner). equiv x (redact x d)) /\
    (forall (x y: outer) (d: inner). equiv x y <==> redact x d = redact y d)
  )
}

let (≡) #a {| blinded_data_representation a |} (lhs rhs : a): bool = equiv lhs rhs

/// The ``maybeBlinded`` type represents a type that may be blinded:
type maybeBlinded (#t:Type) =
   | Clear   : v:t -> maybeBlinded #t (* Represents a non-blinded value *)
   | Blinded : v:t -> maybeBlinded #t (* Represents a blinded value *)


/// But since most software is not written with knowledge of blindable values,
/// we need a way to unwrap the blindable value and get the value inside.
let unwrap1 (#t:Type) (mb:maybeBlinded #t): t =
  match mb with
   | Clear v -> v
   | Blinded v -> v

/// -----------
/// Equivalence
/// -----------
///
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// Equivalence of blindable values
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// We define an equivalence relation on blindable values, so that two
/// values are equivalent if they are indistinguishable from one another.
///
/// This means that they must have the same blindedness, and if they aren't
/// blinded then they must have the same values too:
val equiv1 (#t:eqtype)
    (lhs:maybeBlinded #t)
    (rhs:maybeBlinded #t)
    : r:bool{r <==> (    (Blinded? lhs /\ Blinded? rhs)
                      \/ (Clear?   lhs /\ Clear?   rhs  /\ Clear?.v lhs = Clear?.v rhs) )}

let equiv1 lhs rhs
    = match lhs, rhs with
      | Clear x, Clear y -> (x = y)
      | Blinded _, Blinded _ -> true
      | _ -> false

/// Next we prove that equivalence is an equivalence relation:
///
///  - **Reflexivity**
let equal_values_are_equivalent (t:eqtype) (lhs rhs:maybeBlinded #t):
  Lemma (requires lhs = rhs)
        (ensures equiv1 lhs rhs) =
  ()

///  - **Symmetry**
let equivalence_is_symmetric (t:eqtype) (lhs rhs: maybeBlinded #t):
    Lemma (requires equiv1 lhs rhs)
          (ensures  equiv1 rhs lhs)
    = ()

///  - **Transitivity**
let equivalence_is_transitive (t:eqtype) (lhs mid rhs:maybeBlinded #t):
    Lemma (requires (equiv1 lhs mid) /\ (equiv1 mid rhs))
          (ensures   equiv1 lhs rhs)
    = ()

/// Finally, we show that equivalence on non-blinded values is just the
/// normal equality relation.
let equivalent_clear_values_are_equal (t:eqtype) (x y:maybeBlinded #t):
    Lemma (requires Clear? x /\ Clear? y /\ equiv1 x y)
          (ensures x = y)
    = ()

/// ---------
/// Redaction
/// ---------
///
/// Next we define a notion of redaction.  This replaces blinded values
/// with some fixed blinded value, so that the redaction of a blindable value
/// is a representative of its equivalence class.
let redact1 (#t:Type) (x: maybeBlinded #t) (d:t): maybeBlinded #t =
    match x with
    | Clear   v -> Clear v
    | Blinded t -> Blinded d

let _ = assert(forall (t:eqtype) (x y d: t). redact1 (Blinded x) d == redact1 (Blinded y) d)

/// The result is that we obtain an equivalent value to the input that is
/// independent of all of its sensitive values.
let values_are_equivalent_to_their_redaction (t:eqtype) (x:maybeBlinded #t) (d:t):
    Lemma (ensures equiv1 x (redact1 x d))
    = ()

/// Since the redaction of an element is a representative of its equivalence class,
/// the redaction of two values is equal if and only if they are equivalent.
let equivalent_values_have_equal_redactions (t:eqtype) (x y:maybeBlinded #t) (d:t):
    Lemma (ensures equiv1 x y <==> redact1 x d = redact1 y d)
    = ()

/// Now we can say that this maybeBlinded is a blinded_data_representation.
instance single_bit_blinding (#t:eqtype) : blinded_data_representation (maybeBlinded #t) = {
  inner = t;
  equiv = equiv1;
  is_blinded = (fun (x: maybeBlinded #t) -> Blinded? x);
  redact = redact1;
  unwrap = unwrap1;
  properties =  ();
  make_clear = Clear
}



/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// Equivalence of lists of blindable values
/// ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///
/// We then define a similar relation on lists of blindable values, where lists
/// are equivalent if each of their values are equivalent.
///
/// .. fst::
///    :name: equiv_list

let rec equiv_list #t {| blinded_data_representation t |} (lhs:list t) (rhs: list t): bool
    = match lhs, rhs with
       | Nil,      Nil      -> true
       | Nil,      Cons _ _ -> false
       | Cons _ _, Nil      -> false
       | lh :: lt,  rh :: rt  -> (lh ≡ rh) && (equiv_list lt rt)


/// First, we show that equivalent lists must have equal lengths.
let rec equivalent_lists_have_equal_lengths #t {| blinded_data_representation t |} (l1 l2:list t)
  : Lemma (requires equiv_list l1 l2)
          (ensures FStar.List.length l1 = FStar.List.length l2)
  = match l1, l2 with
    | h1 :: t1, h2 :: t2 -> equivalent_lists_have_equal_lengths t1 t2
    | _ -> ()

/// Then we show that list equivalence is an equivalence relation:
///
///  - **Reflexivity**
let rec equal_lists_are_equivalent t {| blinded_data_representation t |} (lhs rhs:list t):
    Lemma (requires lhs = rhs)
          (ensures equiv_list lhs rhs) =
    match lhs, rhs with
      | Nil, Nil -> ()
      | hl :: tl, hr :: tr -> (//equal_values_are_equivalent #t hl hr;
                             equal_lists_are_equivalent t tl tr)

///  - **Symmetry**
let rec list_equivalence_is_symmetric t {| blinded_data_representation t |} (lhs rhs: list t):
    Lemma (requires equiv_list #t lhs rhs)
          (ensures  equiv_list #t rhs lhs)
//          [SMTPat (equiv_list #t lhs rhs)]
    = match lhs, rhs  with
      | hl :: tl, hr :: tr -> list_equivalence_is_symmetric t tl tr
      | _ -> ()

///  - **Transitivity**
let rec list_equivalence_is_transitive t {| blinded_data_representation t |} (lhs mid rhs: list t):
    Lemma (requires (equiv_list lhs mid) /\ (equiv_list mid rhs))
          (ensures   equiv_list lhs rhs)
    = match lhs, mid, rhs  with
      | hl :: tl, hm :: tm, hr :: tr -> list_equivalence_is_transitive t tl tm tr
      | _ -> ()


/// For convenience, we define our own ``nth`` function to extract the value at
/// a particular index.
let nth  t {| blinded_data_representation t |} (m: list t) (n:nat{n < FStar.List.length m}): t =
  FStar.List.Tot.index m n

/// Then, we prove that extracting values from equivalent lists yields
/// equivalent values:
let rec equivalent_lists_have_equivalent_values t {| blinded_data_representation t |}
                                                (a b: list t)
                                                (n: nat{n < FStar.List.length a &&
                                                      n < FStar.List.length b}):
    Lemma (requires equiv_list a b)
          (ensures (FStar.List.Tot.index a n) ≡ (FStar.List.Tot.index b n))
    = match n, a, b  with
      | 0, _, _ -> ()
      | _, hl :: tl, hr :: tr -> equivalent_lists_have_equivalent_values _ tl tr (n - 1)
      | _ -> ()

/// We also show all lists of blinded values are equivalent to one another, so
/// long as they have the same length.
let rec all_values_are_blinded #t {| blinded_data_representation t |} (l: list t) =
  match l with
    | hd :: tl -> if not (is_blinded hd) then false else all_values_are_blinded tl
    | _ -> true

let rec lists_of_blinded_values_of_equal_length_are_equivalent #t {| blinded_data_representation t |} (a b: list (maybeBlinded #t)):
  Lemma (requires (FStar.List.length a = FStar.List.length b)
                /\ (all_values_are_blinded a) /\ (all_values_are_blinded b))
        (ensures equiv_list a b) =
  match a, b with
    | h1 :: t1, h2 :: t2 -> (
         assert(is_blinded h1 /\ is_blinded h2);
         assert(h1 ≡ h2);
         lists_of_blinded_values_of_equal_length_are_equivalent #t t1 t2
      )
    | _ -> ()

let rec any_value_is_blinded #t {| blinded_data_representation t |} (l: list t) =
  match l with
    | hd :: tl -> if is_blinded hd then true else any_value_is_blinded #t tl
    | _ -> false

let rec equivalent_lists_have_identical_any_blindedness #t {| blinded_data_representation t |} (a b: list t):
  Lemma (requires (equiv_list a b))
        (ensures (any_value_is_blinded a) = (any_value_is_blinded b))
  = match a, b with
      | hl::tl, hr::tr -> (assert(equiv hl hr);
                          assert((is_blinded hl) == (is_blinded hr));
                          equivalent_lists_have_identical_any_blindedness tl tr)
      | _ -> ()


/// We can also define redaction on lists, by redacting each of their elements.
let rec redact_list #t {| blinded_data_representation t |} (pre:list t) (d: (inner #t)):
                r:(list t){FStar.List.length r = FStar.List.length pre}
    = match pre with
      | Nil         -> Nil
      | head :: tail -> (redact head d) :: (redact_list tail d)


/// This doesn't affect the length of the list:
let rec redaction_preserves_length t {| blinded_data_representation t |} (x:list t) (d: (inner #t))
  : Lemma (ensures FStar.List.length x = FStar.List.length (redact_list x d))
  = match x with
    | Nil -> ()
    | hd :: tl -> redaction_preserves_length t tl d


/// We prove the same properties as for the redactions of individual values.
///
/// First, the redaction of a list is in the same equivalence class.
let rec lists_are_equivalent_to_their_redaction t {| blinded_data_representation t |} (x:list t) (d: (inner #t))
    : Lemma (ensures equiv_list x (redact_list x d))
    = match x with
      | Nil -> ()
      | hd :: tl -> lists_are_equivalent_to_their_redaction t tl d

/// The redaction of lists of lists are equal if and only if they are equivalent.
let rec equivalent_lists_have_equal_redactions t {| blinded_data_representation t |} (x y: list t) (d: (inner #t))
    : Lemma (ensures equiv_list x y <==> redact_list x d = redact_list y d)
    = match x, y with
       | Nil, Nil -> ()
       | Nil, Cons _ _ -> ()
       | Cons _ _, Nil -> ()
       | hl :: tl, hr :: tr -> equivalent_lists_have_equal_redactions t tl tr d

/// Redacting a list redacts each of its values.
let rec redacted_lists_have_redacted_values (t:eqtype) {| blinded_data_representation t |}
                                            (a: list t)
                                            (d: (inner #t))
                                            (n: nat{n < FStar.List.length a}):
  Lemma (ensures FStar.List.Tot.index (redact_list a d) n = redact (FStar.List.Tot.index a n) d)
        [SMTPat (FStar.List.Tot.index (redact_list a d) n)]
    = match n, a with
      | 0, _ -> ()
      | _, hl :: tl -> redacted_lists_have_redacted_values _ tl d (n - 1)
      | _ -> ()



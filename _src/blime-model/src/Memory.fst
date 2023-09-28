/// ************
/// Memory state
/// ************
///
/// This module models a memory array.
module Memory

open Value
open Multi

/// First we require a model of addresses and words.  We use a 64-bit word
/// so that there is one instruction per word.
type address = FStar.UInt64.t
type byte = FStar.UInt64.t

/// Then, we define the state of memory as a list of blindable words.
type blindedWord = multiBlinded #byte
type memoryState = list blindedWord

/// We then provide a way to read values from memory.  Rather than requiring
/// the caller to prove that their address is in range, reading from an
/// out-of-range value results in reading a clear value zero.
let rec nth (m:memoryState) (n:address) : blindedWord =
  match m, n with
    | Nil,     _   -> MultiClear 0uL
    | hd :: tl, 0uL -> hd
    | hd :: tl, n   -> nth tl (FStar.UInt64.sub n 1uL)


/// We then show that the values of equal memories are equal.
let equal_memories_have_equal_values (a b: memoryState) (n:address):
    Lemma (requires a = b)
          (ensures (nth a n) = (nth b n))
    = ()

/// Next, we show that the values of equal memories are equal.
let rec equivalent_memories_have_equivalent_values (a b: memoryState) (n: address):
    Lemma (requires equiv_list a b)
          (ensures equiv (nth a n) (nth b n))
    = match n, a, b  with
      | 0uL, _, _ -> ()
      | _, hl :: tl, hr :: tr -> equivalent_memories_have_equivalent_values tl tr (FStar.UInt64.sub n 1uL)
      | _ -> ()


/// Finally, we show that each pair of elements from a pair of equivalent memories
/// has identical blindedness.
irreducible let trigger (a b: memoryState) (n:address) = True

let rec equivalent_memories_have_identical_blindedness_somewhere (a b: memoryState) (n:address):
  Lemma (requires equiv_list a b)
        (ensures is_blinded (nth a n) <==> is_blinded (nth b n))
        [SMTPat (trigger a b n)]=
  match n, a, b with
    | 0uL, _, _ -> ()
    | _, hl :: tl, hr :: tr ->
         equivalent_memories_have_identical_blindedness_somewhere
           tl tr
           (FStar.UInt64.sub n 1uL)
    | _ -> ()


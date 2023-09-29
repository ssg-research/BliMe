/// *********
/// Model ISA
/// *********
///
/// In this file, we analyze a concrete instruction set that includes a number
/// of manually-implemented taint propagation rules.
module ISA

open FStar.Math.Lib
open FStar.Mul

open Cpu
open Memory
open InstructionDecoder
open Value
open Multi

/// ==================
/// Instruction format
/// ==================
///
/// We start by defining the instruction format.
///
/// +-----------+--------+---------+---------+---------+--------+
/// | **Field** | opcode | out1    | in1     | in2     | imm    |
/// +-----------+---+----+----+----+----+----+----+----+----+---+
/// | **Bits**  | 63| 61 | 60 | 56 | 55 | 51 | 50 | 46 | 45 | 0 |
/// +-----------+---+----+----+----+----+----+----+----+----+---+
///
/// Given this format, we then define functions to extract each component of the
/// instruction word.
///
/// First, we define a conversion function mapping a machine word to an integer.
let v = FStar.UInt64.v

/// Then we define functions that extract the various components
let parse_opcode (inst:word) = (arithmetic_shift_right (v inst) 61) % 8
let parse_out1 (inst:word): nat = (arithmetic_shift_right (v inst) 56) % 32
let parse_in1 (inst:word): nat = (arithmetic_shift_right (v inst) 51) % 32
let parse_in2 (inst:word): nat = (arithmetic_shift_right (v inst) 45) % 32

/// However, for immediate values it is more convenient to define the function
/// to extract a machine word rather than an integer.
let parse_imm (inst:word): Cpu.word =
      (FStar.UInt64.logand inst (FStar.UInt64.sub (FStar.UInt64.shift_left 1uL 46ul) 1uL))

/// ===================
/// Instruction decoder
/// ===================
///
/// Next we set up the instruction decoder, which converts an instruction word
/// into an opcode plus a set of operands.
let sample_decoder (inst:word): decodedInstruction =
  let opcode = parse_opcode inst in
  let out1 = parse_out1 inst in
  let in1 = parse_in1 inst in
  let in2 = parse_in2 inst in
  let imm = parse_imm inst in
  match opcode with
  (* Store *)
    | 0 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [] }
  (* Load *)
    | 1 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [] }
  (* Branch *)
    | 2 -> { opcode;
            input_operands  = [PC; Register in1; Register in2];
            output_operands = [PC] }
  (* Add *)
    | 3 -> { opcode;
            input_operands  = [ Register in1; Register in2; Immediate imm ];
            output_operands = [ Register out1 ] }
  (* Subtract *)
    | 4 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [ Register out1 ] }
  (* Multiply *)
    | 5 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [ Register out1 ] }
  (* Bitwise AND *)
    | 6 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [ Register out1 ] }
  (* Bitwise XOR *)
    | 7 -> { opcode;
            input_operands  = [ Register in1; Register in2 ];
            output_operands = [ Register out1 ] }

/// Later on we will need to know how many input operands each instruction has;
/// the prover can work it out, but needs a hint.
let sample_decoded_instruction_length (inst:word):
  Lemma (ensures FStar.List.length (sample_decoder inst).input_operands =
                    (match (sample_decoder inst).opcode with
                     | 0 -> 2
                     | 1 -> 2
                     | 2 -> 3
                     | 3 -> 3
                     | 4 -> 2
                     | 5 -> 2
                     | 6 -> 2
                     | 7 -> 2
                     )
        )
        [SMTPat (sample_decoder inst)] =
    match (sample_decoder inst).opcode with
        | 0 -> ()
        | 1 -> ()
        | 2 -> ()
        | 3 -> ()
        | 4 -> ()
        | 5 -> ()
        | 6 -> ()
        | 7 -> ()


/// -----------------
/// Utility functions
/// -----------------

type blindedness_state =
  | NoneBlinded : blindedness_state
  | ConsistentlyBlinded : blindedness_domain -> blindedness_state
  | InconsistentlyBlinded : blindedness_state

let rec blindedness_state_of_list_int (l : list blindedWord) (s : blindedness_state) : blindedness_state =
  if InconsistentlyBlinded? s then s else
  match l with
    | Nil -> s
    | MultiClear x :: tl -> blindedness_state_of_list_int tl s
    | MultiBlinded x d :: tl -> let s2 = match s with
                                          | NoneBlinded -> ConsistentlyBlinded d
                                          | ConsistentlyBlinded d2 -> if d = d2 then s else InconsistentlyBlinded
                                          | InconsistentlyBlinded -> InconsistentlyBlinded
                                  in
                                blindedness_state_of_list_int tl s2

let blindedness_state_of_list (l : list blindedWord) : blindedness_state =
  blindedness_state_of_list_int l NoneBlinded

let rec blind_all_values (values: list blindedWord) (d: blindedness_domain): r:(list blindedWord){FStar.List.length values = FStar.List.length r} =
    match values with
      | Nil                     -> Nil
      | MultiBlinded hd dx :: tl -> MultiBlinded hd dx :: blind_all_values tl d
      | MultiClear   hd    :: tl -> MultiBlinded hd d :: blind_all_values tl d

let rec blinding_all_values_blinds_each_value (values: list blindedWord) (d: blindedness_domain) (n:nat{n < FStar.List.length values}):
  Lemma (ensures is_blinded (FStar.List.Tot.index (blind_all_values values d) n))
        [SMTPat (is_blinded (FStar.List.Tot.index (blind_all_values values d) n))] =
  match n, values with
    | 0, _   -> ()
    | _, Nil -> ()
    | n, hd :: tl -> blinding_all_values_blinds_each_value tl d (n-1)


let rec blinding_all_values_is_idempotent  (values: list blindedWord) (d: blindedness_domain):
  Lemma (ensures (blind_all_values values d) = blind_all_values (blind_all_values values d) d) =
    match values with
      | hd :: tl -> blinding_all_values_is_idempotent tl d
      | _ -> ()

let rec blinding_all_values_blinds_all_values  (values: list blindedWord) (d: blindedness_domain):
  Lemma (ensures all_values_are_blinded (blind_all_values values d))
        [SMTPat (blind_all_values values d)] =
  match values with
    | hd :: tl -> blinding_all_values_blinds_all_values tl d
    | _ -> ()

let rec equivalent_unblinded_lists_are_equal (a b: list blindedWord):
  Lemma (requires (equiv_list a b) /\ (~(any_value_is_blinded a) \/ ~(any_value_is_blinded b)))
        (ensures a = b) =
  match a, b with
    | h1 :: t1, h2 :: t2 -> equivalent_unblinded_lists_are_equal t1 t2
    | _ -> ()


/// =====================
/// Instruction semantics
/// =====================
///
/// Now we define the behavior of each instruction.
///
/// In most cases we use a 'generic' taint propagation rule:
///
/// .. exercise ::
///
///      if any_value_is_blinded pre then Blinded result else Clear result
///
/// However, there are some instructions where a more specific rule is
/// appropriate.  For example, :math:`x \oplus x` and :math:`x \& 0` both
/// evaluate to zero, irrespective of the value of :math:`x`, meaning that
/// the result can be ``Clear 0`` even though an input may be blinded.

val sample_semantics (#n:memory_size): instruction_semantics #n #32 sample_decoder

#set-options "--z3rlimit 1000"
let sample_semantics (di:decoder_output sample_decoder)
                     (pre:(list blindedWord){
                       (exists(s: systemState). pre = get_operands di.input_operands s) /\
                       FStar.List.length pre = FStar.List.length di.input_operands})
                     : instruction_result di =
  match di.opcode with
    (* Store *)
    | 0 -> let address = (FStar.List.Tot.index pre 0) in

    { register_writes = []; memory_ops = (
      assert(FStar.List.length di.input_operands = 2);
      match (FStar.List.Tot.index di.input_operands 0), (FStar.List.Tot.index di.input_operands 1) with
        | Register d, Register s -> [Store (v (unwrap address)) s]
        | _ -> []
      ); fault = is_blinded address}
    (* Load *)
    | 1 -> let address = (FStar.List.Tot.index pre 0) in
          { register_writes = [];
            memory_ops = (match (FStar.List.Tot.index di.input_operands 0),
                                     (FStar.List.Tot.index di.input_operands 1) with
                                | Register d, Register s -> [Load (v (unwrap address)) d]
                                | _ -> []);
            fault = is_blinded address}
    (* Branch *)
    | 2 -> ( let pc = FStar.List.Tot.index pre 0 in
            let a = FStar.List.Tot.index pre 1 in
            let b = FStar.List.Tot.index pre 2 in
            let ref: blindedWord = MultiClear #word 0uL in
            { register_writes = [if a = ref then b else pc];
              memory_ops = [];
              fault = is_blinded a})
    (* Add *)
    | 3 -> ( assert(FStar.List.length pre = 3);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = (FStar.UInt64.add_mod (unwrap a) (unwrap b)) in
            let result = match blindedness_state_of_list pre with
                          | NoneBlinded -> make_clear result
                          | ConsistentlyBlinded d -> MultiBlinded result d
                          | InconsistentlyBlinded -> make_clear 0uL in
            { register_writes = [result];
              memory_ops = [];
              fault = InconsistentlyBlinded? (blindedness_state_of_list pre)})
    (* Sub *)
    | 4 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = (FStar.UInt64.sub_mod (unwrap a) (unwrap b)) in
            let result = match blindedness_state_of_list pre with
                          | NoneBlinded -> make_clear result
                          | ConsistentlyBlinded d -> MultiBlinded result d
                          | InconsistentlyBlinded -> make_clear 0uL in
            { register_writes = [result];
              memory_ops = [];
              fault = InconsistentlyBlinded? (blindedness_state_of_list pre) })
    (* MUL *)
    | 5 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result = (FStar.UInt64.mul_mod (unwrap a) (unwrap b)) in
            let result = match blindedness_state_of_list pre with
                          | NoneBlinded -> make_clear result
                          | ConsistentlyBlinded d -> MultiBlinded result d
                          | InconsistentlyBlinded -> make_clear 0uL in
           { register_writes = [result];
             memory_ops = [];
              fault = InconsistentlyBlinded? (blindedness_state_of_list pre) })
    (* AND *)
    | 6 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = FStar.UInt64.logand (unwrap a) (unwrap b) in
            let result = if (a = make_clear 0uL) || (b = make_clear 0uL) then
                            make_clear 0uL
                         else match blindedness_state_of_list pre with
                          | NoneBlinded -> make_clear result
                          | ConsistentlyBlinded d -> MultiBlinded result d
                          | InconsistentlyBlinded -> make_clear 0uL in
                         { register_writes = [result];
                           memory_ops = [];
                           fault = InconsistentlyBlinded? (blindedness_state_of_list pre)}
          )
    (* XOR *)
    | 7 -> ( assert(FStar.List.length pre = 2);
            let a = FStar.List.Tot.index pre 0 in
            let b = FStar.List.Tot.index pre 1 in
            let result: Cpu.word = (FStar.UInt64.logxor (unwrap a) (unwrap b)) in
            let result = if (FStar.List.Tot.index di.input_operands 0)
                           = (FStar.List.Tot.index di.input_operands 1) then
                            make_clear 0uL
                         else match blindedness_state_of_list pre with
                          | NoneBlinded -> make_clear result
                          | ConsistentlyBlinded d -> MultiBlinded result d
                          | InconsistentlyBlinded -> make_clear 0uL in
                         { register_writes = [result];
                           memory_ops = [];
                           fault = InconsistentlyBlinded? (blindedness_state_of_list pre)}
          )

irreducible let trigger (#n: memory_size)
  (inst:word) (pre:instruction_input #n #32 (sample_decoder inst)) = False

/// ------
/// Safety
/// ------
///
/// Now we can start to prove the safety of the instruction semantics, which we
/// do by proving their redaction-equivalence.
///
/// This is complicated slightly by the fact that we need to show that the
/// redacted inputs are also valid inputs.
///
/// We start by using an special redacting function on the instruction inputs
/// that shows that the result is also an input to said instruction.

#set-options "--z3rlimit 1000"
let sample_semantics_are_redacting_equivalent_expanded (#n: memory_size)
   (inst:word)
   (pre:instruction_input (sample_decoder inst)):
  Lemma (ensures (equiv_result (sample_semantics #n (sample_decoder inst) pre)
                               (sample_semantics #n (sample_decoder inst)
                                  (redacted_instruction_inputs_are_instruction_inputs #n #32
                                     (sample_decoder inst) pre)))
                 \/ trigger #n inst pre) =
  ()

/// Then we do the real proof of redacting-equivalence.
#set-options "--z3rlimit 10000"
let sample_semantics_are_redacting_equivalent (#n: memory_size)
    (inst:word)
    (pre:instruction_input #n #32 (sample_decoder inst)):
  Lemma (ensures is_redacting_equivalent_instruction_semantics_somewhere #n #32
                                                                         sample_decoder
                                                                         sample_semantics
                                                                         inst pre
                 \/ trigger inst pre) =
  ()

let sample_semantics_are_redacting_equivalent_everywhere (#n: memory_size):
  Lemma (ensures is_redacting_equivalent_instruction_semantics_everywhere #n #32
                   sample_decoder sample_semantics) =
  ()

/// Finally, we show that the semantics are safe.
let sample_semantics_are_safe (#n: memory_size) (cp:cache_policy n):
  Lemma (ensures is_safe #n #32
                         (loadstore_execution_unit #n #32 sample_decoder (sample_semantics #n) cp)) =
    sample_semantics_are_redacting_equivalent_everywhere #n;

    loadstore_execution_unit_with_re_instruction_semantics_is_redacting_equivalent
      sample_decoder (sample_semantics #n) cp;

    each_loadstore_execution_unit_with_redacting_equivalent_instruction_semantics_is_safe
      sample_decoder (sample_semantics #n) cp


/// -----------
/// Correctness
/// -----------
///
/// Next we prove that the instructions do the right thing.  First, addition:

let add_instruction_works_correctly
  (#n:memory_size) (inst:word)
  (pre:(list blindedWord){
    (exists(s: systemState #n).
      pre = get_operands #n #32 (sample_decoder inst).input_operands s) /\
      FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):

    Lemma (requires parse_opcode inst = 3 /\ ~(InconsistentlyBlinded? (blindedness_state_of_list pre)))
          (ensures  unwrap (FStar.List.Tot.hd
                             (sample_semantics #n (sample_decoder inst) pre).register_writes)
                     = (FStar.UInt64.add_mod (unwrap (FStar.List.Tot.index pre 0))
                                             (unwrap (FStar.List.Tot.index pre 1)))) =
    ()


/// Then exclusive or.  First we need to know that :math:`x \oplus x = 0`, since this means
/// that the output won't depend on the specific value of :math:`x`.
let xor_with_self_yields_zero (a:Cpu.word):
  Lemma (ensures (FStar.UInt64.logxor a a) = 0uL) =
    let value: FStar.UInt.uint_t 64 = v a in
    FStar.UInt.logxor_self #64 value;
    assert(FStar.UInt.logxor #64 value value == 0)

/// Then we show that the computed value really is the exclusive OR of the inputs.
let xor_instruction_works_correctly
      (#n:memory_size) (inst:word)
      (pre:(list blindedWord){
        (exists(s: systemState #n).
          pre = get_operands #n #32 (sample_decoder inst).input_operands s) /\
          FStar.List.length pre = FStar.List.length (sample_decoder inst).input_operands}):
    Lemma (requires parse_opcode inst = 7  /\ ~(InconsistentlyBlinded? (blindedness_state_of_list pre)))
          (ensures  unwrap (FStar.List.Tot.hd
                             (sample_semantics #n (sample_decoder inst) pre).register_writes)
                     = FStar.UInt64.logxor (unwrap (FStar.List.Tot.index pre 0))
                                           (unwrap (FStar.List.Tot.index pre 1)) ) =
          let di = sample_decoder inst in
          let a = FStar.List.Tot.index pre 0 in
          let b = FStar.List.Tot.index pre 1 in
          let outputs = (sample_semantics #n (sample_decoder inst) pre).register_writes in
          if (FStar.List.Tot.index di.input_operands 0)
              = (FStar.List.Tot.index di.input_operands 1) then (
            assert(a == b);
            xor_with_self_yields_zero (unwrap a) )
          else (
            let bs = blindedness_state_of_list pre in
            match bs with
                | ConsistentlyBlinded d -> assert(outputs = [MultiBlinded (FStar.UInt64.logxor (unwrap a) (unwrap b)) d])
                | NoneBlinded -> assert(outputs = [MultiClear (FStar.UInt64.logxor (unwrap a) (unwrap b))])
          )


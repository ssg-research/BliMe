/// ****************
/// Load-store model
/// ****************
///
/// This CPU model includes more detail, with each instruction having register
/// operands, and producing a set of memory operations to be carried out by a
/// load-store unit.

module InstructionDecoder

open Cpu
open Memory
open Value




/// ====================
/// Instruction operands
/// ====================
///
/// We now begin in earnest by describing how instruction operands are handled.
///
/// An instruction operand represents the target of a read or write
/// to the register file (or from an immediate).
type operand =
  | PC
  | Register: n:nat -> operand
  | Immediate: n:Cpu.word -> operand

/// -----
/// Reads
/// -----

/// The first object of analysis is the function ``get_operands``, that will
/// take a list of input operands and extract them from the system state.
let rec get_operands (#n #r: memory_size) (operands:list operand) (state:systemState #n #r):
    rv:(list blindedWord){FStar.List.length rv = FStar.List.length operands} =
  match operands with
    | Nil -> Nil
    | hd :: tl -> (match hd with
                  | PC -> make_clear state.pc
                  | Register n -> if n < FStar.List.length state.registers then
                                    (FStar.List.Tot.index state.registers n)
                                 else make_clear 0uL
                  | Immediate n -> make_clear n
                ) :: get_operands tl state



/// We start by proving that operand extraction preserves redaction.
///
/// We do this by induction.  It is convenient to first prove that extraction
/// of just one operand preserves redaction:
let get_operands_with_one_operand_on_redacted_input_has_redacted_output (#n #r: memory_size)
    (op: operand) (state:systemState #n #r):
  Lemma (ensures (let zero: (inner #blindedWord) = 0uL in
                  get_operands [op] (redact_system state) = redact_list (get_operands [op] state) zero)) =
  let head = FStar.List.Tot.hd (get_operands [op] state) in
  let head_of_redacted = FStar.List.Tot.hd (get_operands [op] (redact_system state)) in
  match op with
    | PC -> ()
    | Register n -> (
        let zero: (inner #blindedWord) = 0uL in
        lists_are_equivalent_to_their_redaction _ state.registers zero;
        equal_lists_are_equivalent _ (redact_system state).registers  (redact_list state.registers zero);
        equivalent_lists_have_equal_lengths state.registers (redact_system state).registers;
        if n >= FStar.List.length state.registers then () else ()
      )
    | Immediate n -> ()

/// In the inductive case we show that the first operand in the list will be
/// redacted as above, and then recurse by repeating this for the tail of the
/// operand list.
let rec get_operands_on_redacted_input_has_redacted_output (#n #r: memory_size)
    (operands:list operand) (state:systemState #n #r):
  Lemma (ensures (let zero: (inner #blindedWord) = 0uL in
                  get_operands operands (redact_system state)
                  = redact_list (get_operands operands state) zero))
        [SMTPat (get_operands operands (redact_system state))] =
  (
    match operands with
      | Nil -> ()
      | hd :: tl -> (
          let head = FStar.List.Tot.hd (get_operands operands state) in
          let head_of_redacted = FStar.List.Tot.hd (get_operands operands (redact_system state)) in

          get_operands_with_one_operand_on_redacted_input_has_redacted_output hd state;
          assert(redact head 0uL = head_of_redacted);

          let zero: (inner #blindedWord) = 0uL in
          let redacted_head = redact head zero in

          get_operands_on_redacted_input_has_redacted_output tl state;
          assert(get_operands tl (redact_system state) = redact_list (get_operands tl state) zero);
          assert((head_of_redacted :: (get_operands tl (redact_system state)))
            = (redacted_head :: (redact_list (get_operands tl state) zero)))
        )
)

/// We then prove that extracting operands from the state also preserves
/// equivalence, though in this case we jump to the inductive proof directly.
let rec get_operands_on_equivalent_inputs_has_equivalent_output (#m #q #n #r: memory_size)
    (operands:list operand) (state1: systemState #m #q) (state2:systemState #n #r):
  Lemma (requires (equiv_system state1 state2))
        (ensures  (equiv_list (get_operands operands state1)
                              (get_operands operands state2)))
  = match operands with
      | Nil -> ()
      | hd :: tl -> (
          let result_hd1, result_hd2: FStar.Pervasives.Native.tuple2 blindedWord blindedWord =
            match hd with
             | PC -> (
                  let head1 = FStar.List.Tot.hd (get_operands operands state1) in
                  let head2 = FStar.List.Tot.hd (get_operands operands state2) in
                  //equal_values_are_equivalent Cpu.word head1 head2;
                  head1, head2
               )
             | Register n -> (
                  assert(equiv_list state1.registers state2.registers);
                  equivalent_lists_have_equal_lengths state1.registers state2.registers;
                  if n < FStar.List.length state1.registers then (
                       equivalent_lists_have_equivalent_values _ state1.registers state2.registers n
                  )
                  else ();

                  let head1: blindedWord = FStar.List.Tot.hd (get_operands operands state1) in
                  let head2: blindedWord = FStar.List.Tot.hd (get_operands operands state2) in
                  head1, head2
               )
             | Immediate n -> (make_clear n, make_clear n) in
                 assert(equiv result_hd1 result_hd2);
                 get_operands_on_equivalent_inputs_has_equivalent_output tl state1 state2
      )


/// ------
/// Writes
/// ------
///
/// Next we look at how to write operands.  First we will define some utility functions.
///
/// The first operation that we will do is to take a list and replace a single element
/// of a list with the corresponding element of another list (if it exists).
///
/// For example:
///
///   .. example:
///
///     mux_list_single [1,2,3] [4,5,6] 1 == [1,5,6]
let rec mux_list_single (a:list blindedWord) (b:list blindedWord) (n:nat):
        list blindedWord
  = match a, b with
    | Nil, Nil -> Nil
    | hd :: tl, Nil -> a
    | Nil,     _ -> Nil
    | hd1 :: tl1, hd2 :: tl2 ->  if (n > 0)
                              then
                                hd1 :: (mux_list_single a b (n - 1))
                              else
                                hd2 :: tl1


/// Then we do the same thing with a whole list of elements to replace.
let rec mux_list (a:list blindedWord) (b:(list blindedWord)) (which_b:list nat):
    Tot (list blindedWord) (decreases which_b) =
  match which_b with
    | Nil -> a
    | index_to_change :: tl -> mux_list (mux_list_single a b index_to_change) b tl

/// Then the same again replacing the list element with a specific value.
let rec replace_list_value (orig:list blindedWord) (n:nat) (v: blindedWord):
        r:(list blindedWord){FStar.List.length r = FStar.List.length orig}
    = match orig with
      | Nil -> Nil
      | hd :: tl ->  if (n > 0)
                   then
                     hd :: (replace_list_value tl (n - 1) v)
                   else
                     v :: tl

/// We then show that replacing a list value preserves equivalence.
let rec replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists
    (orig1 orig2:list blindedWord) (n:nat) (v1 v2: blindedWord):
  Lemma (requires (equiv_list orig1 orig2) /\ (equiv v1 v2))
        (ensures (equiv_list (replace_list_value orig1 n v1) (replace_list_value orig2 n v2))) =
  match n, orig1, orig2 with
    | 0, _, _ -> ()
    | _, h1 :: t1, h2 :: t2 ->
         replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists
           t1 t2 (n-1) v1 v2
    | _ -> ()

/// We then show that replacing a list value and reading it back yields the
/// value that we wrote.
let rec replacing_then_reading_yields_original_value
    (orig: list blindedWord) (v:blindedWord) (n:nat):
  Lemma (requires n < FStar.List.length orig)
        (ensures FStar.List.Tot.index (replace_list_value orig n v) n = v)
    = match n, orig with
      | _, [] -> ()
      | 0, _ -> ()
      | _, hd :: tl -> replacing_then_reading_yields_original_value tl v (n-1)

/// Now that we have these utility functions, we can use them to write output
/// to the machine state.  First a single operand:
let set_one_operand (#n #r: memory_size)
      (operand:operand) (value:blindedWord) (state:systemState #n #r):
      systemState #n #r =
    match operand with
      | PC -> (if is_blinded value then
                 {state with pc = 0uL}
               else
                 let v = unwrap value in
                   if FStar.UInt64.v v < FStar.List.length state.memory then
                      { state with pc = v }
                   else
                     { state with pc = 0uL })
      | Register n -> if n < FStar.List.length state.registers then
                        { state with registers =
                          replace_list_value state.registers n value
                        }
                     else
                       state
      | Immediate n -> state

let setting_and_getting_one_non_faulting_operand_value_yields_original_value (#n #r: memory_size)
    (operand:operand) (value: blindedWord) (state:systemState #n #r):
  Lemma (requires ~(match operand with
                     | PC -> (if is_blinded value then True
                              else let v = unwrap value in
                                   FStar.UInt64.v v >= FStar.List.length state.memory)
                     | Register n -> n >= FStar.List.length state.registers
                     | Immediate n -> True))
        (ensures get_operands [operand] (set_one_operand operand value state) = [value]) =
  let r = get_operands [operand] (set_one_operand operand value state) in
  match operand with
    | PC -> ()
    | Register n -> replacing_then_reading_yields_original_value state.registers value n

/// As usual, we then show that writing equivalent operands preserves equivalence.
let setting_single_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (#n #r: memory_size)
    (operand       :operand)
    (value1 value2 :blindedWord)
    (state1 state2 :systemState #n #r):
    Lemma (requires (equiv_system state1 state2) /\ (equiv value1 value2))
          (ensures  (equiv_system (set_one_operand operand value1 state1)
                                  (set_one_operand operand value2 state2))) =
    match operand with
      | PC -> (if not (is_blinded value1) && not (is_blinded value2) then (
                 let v1,v2 = unwrap value1, unwrap value2 in
                       assert(v1 = v2);
                       equivalent_lists_have_equal_lengths state1.memory state2.memory;
                       let post1 = (set_one_operand operand value1 state1) in
                       let post2 = (set_one_operand operand value2 state2) in
                       assert(post1.pc = post2.pc)
                       )
               else ())
      | Register n -> (
          equivalent_lists_have_equal_lengths state1.registers state2.registers;
          if n >= FStar.List.length state1.registers then ()
          else
            replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists
              state1.registers state2.registers n value1 value2
        )
      | Immediate n -> ()

/// Then multiple operands:
let rec set_operands (#n #r: memory_size)
    (operands:list operand)
    (values:(list  blindedWord){FStar.List.length operands = FStar.List.length values})
    (state:systemState #n #r):
        systemState #n #r =
    match operands, values with
      | o :: tl_o, v :: tl_v -> set_operands tl_o tl_v (set_one_operand o v state)
      | _ -> state

#set-options "--z3rlimit 1000"
let rec setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
    (#n #r: memory_size)
    (operands       :list operand)
    (values1:(list  blindedWord){FStar.List.length operands = FStar.List.length values1})
    (values2:(list  blindedWord){FStar.List.length operands = FStar.List.length values2})
    (state1: systemState #n #r)  (state2 :systemState #n #r):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_list values1 values2))
          (ensures  (equiv_system (set_operands operands values1 state1)
                    (set_operands operands values2 state2))) =
    match operands, values1, values2 with
      | ho :: to, hv1 :: tv1, hv2 :: tv2 -> (
          assert(equiv hv1 hv2);

          let applied_head1 = set_one_operand ho hv1 state1 in
          let applied_head2 = set_one_operand ho hv2 state2 in
          setting_single_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
            ho hv1 hv2 state1 state2;
          assert(equiv_system applied_head1 applied_head2);

          let applied_tail1 = (set_operands to tv1 applied_head1) in
          let applied_tail2 = (set_operands to tv2 applied_head2) in
          setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
            to tv1 tv2 applied_head1 applied_head2;
          assert(equiv_system applied_tail1 applied_tail2)
        )
      | _ -> ()



/// =================
/// Memory operations
/// =================
///
/// Now we look at memory operations.
///
/// These are represented differently from instruction operands, because in
/// a real processor they would handled by the load-store unit, which can't
/// immediately read or write a value from memory: it always takes at least
/// one cycle.
type memory_operation =
  | Load: address:nat -> dest:nat -> memory_operation
  | Store: address:nat -> src:nat -> memory_operation


/// We also need to deal with caches.  In this case we don't want to specify
/// concretely how the cache works, but just to show that a processor is safe
/// regardless of the specific cache policy in use.
///
/// We do this by defining a type of function, a *cache policy*, that indicates
/// what a given memory operation does to the cache.
type cache_policy (n:memory_size) =
       (cache_state n) -> memory_operation -> (cache_state n)

/// As usual, we define an equivalence relation on memory operations so that
/// we can determine whether they leak information.  In this case, we say that
/// two memory operations are equivalent if they load/store the same register
/// to the same address:
let equiv_memory_operation (lhs rhs: memory_operation) =
  match lhs, rhs with
    | (Load la ld), (Load ra rd) -> (la = ra /\ ld = rd)
    | (Store la ls), (Store ra rs) -> (la = ra /\ ls = rs)
    | _, _ -> False

/// We also define equivalence of lists of memory operations, since an
/// instruction might perform several memory operations.
let rec equiv_memory_operations (lhs rhs: list memory_operation) =
  match lhs, rhs with
    | lh :: lt, rh :: rt -> (equiv_memory_operation lh rh) /\ equiv_memory_operations lt rt
    | [], [] -> True
    | _, _ -> False

/// Then we prove various properties of these relations:
///  - **Equality implies equivalence**:
let equal_memory_operations_are_equivalent (lhs rhs: memory_operation):
  Lemma (requires lhs = rhs)
        (ensures  (equiv_memory_operation lhs rhs)) =
  ()

let rec equal_memory_operation_lists_are_equivalent (lhs rhs: list memory_operation):
  Lemma (requires lhs = rhs)
        (ensures equiv_memory_operations lhs rhs) =
  match lhs, rhs with
    | hl :: tl, hr :: tr -> (
         equal_memory_operations_are_equivalent hl hr;
         equal_memory_operation_lists_are_equivalent tl tr
      )
    | _ -> ()

///  - **Symmetry**
let memory_operation_equivalence_is_symmetric (lhs rhs: memory_operation):
  Lemma (requires (equiv_memory_operation lhs rhs))
        (ensures  (equiv_memory_operation rhs lhs)) =
  ()

let rec memory_operation_list_equivalence_is_symmetric (lhs rhs: list memory_operation):
  Lemma (requires (equiv_memory_operations lhs rhs))
        (ensures  (equiv_memory_operations rhs lhs)) =
  match lhs, rhs with
   | hl :: tl, hr :: tr -> (
        memory_operation_equivalence_is_symmetric hl hr;
        memory_operation_list_equivalence_is_symmetric tl tr
     )
   | _ -> ()

///  - **Transitivity**
let memory_operation_equivalence_is_transitive (lhs mid rhs: memory_operation):
  Lemma (requires (equiv_memory_operation lhs mid) /\ (equiv_memory_operation mid rhs))
        (ensures  (equiv_memory_operation lhs rhs)) =
  ()

let rec memory_operation_list_equivalence_is_transitive (lhs mid rhs: list memory_operation):
  Lemma (requires (equiv_memory_operations lhs mid) /\ (equiv_memory_operations mid rhs))
        (ensures  (equiv_memory_operations lhs rhs)) =
  match lhs, mid, rhs with
   | hl :: tl, hm :: tm, hr :: tr -> (
        memory_operation_equivalence_is_transitive hl hm hr;
        memory_operation_list_equivalence_is_transitive tl tm tr
     )
   | _ -> ()

///  - **Equivalence of lists implies equality of length**
let rec equivalent_memory_operation_lists_have_equal_length (lhs rhs: list memory_operation):
  Lemma (requires equiv_memory_operations lhs rhs)
        (ensures (FStar.List.length lhs) = (FStar.List.length rhs)) =
  match lhs, rhs with
    | hl :: tl, hr :: tr -> equivalent_memory_operation_lists_have_equal_length tl tr
    | _, _ -> ()


/// Next, we look at how to actually complete the transactions.  A load
/// results in the register file being updated with a value from memory.
/// A store results in memory being updated with a value from the register
/// file.
let complete_one_memory_transaction (#n #r: memory_size)
    (op:memory_operation) (pre:systemState #n #r) (cp:cache_policy n): systemState #n #r =
  match op with
      | Load address register ->
             if register < FStar.List.length pre.registers
                  && address < FStar.List.length pre.memory then
                { pre with registers = replace_list_value
                                         pre.registers
                                         register
                                         (FStar.List.Tot.index pre.memory address);
                           cache_lines = cp pre.cache_lines op }
             else pre
      | Store address register ->
             if register < FStar.List.length pre.registers
                  && address < FStar.List.length pre.memory then
                { pre with memory = replace_list_value
                                      pre.memory
                                      address
                                      (FStar.List.Tot.index pre.registers register);
                           cache_lines = cp pre.cache_lines op }
             else pre

let rec complete_memory_transactions (#n #r: memory_size)
    (op:list memory_operation) (pre:systemState #n #r) (cp:cache_policy n) =
  match op with
    | hd :: tl -> (let post = (complete_one_memory_transaction hd pre cp) in
                 complete_memory_transactions tl post cp)
    | [] -> pre

/// Then, we show that our notion of equivalence of memory operations leads
/// to the conclusion that applying equivalent operations to equivalent systems
/// yields equivalent systems.
let completing_single_memory_transactions_on_equivalent_systems_yields_equivalent_systems
    (#m #q #n #r: memory_size)
    (op1:memory_operation) (op2:memory_operation)
    (state1:systemState #m #q) (state2 :systemState #n #r)
    (cp:cache_policy m):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_memory_operation op1 op2))
          (ensures  (equiv_system (complete_one_memory_transaction op1 state1 cp)
                                  (complete_one_memory_transaction op2 state2 cp))) =
                 let post1 = (complete_one_memory_transaction op1 state1 cp) in
                 let post2 = (complete_one_memory_transaction op2 state2 cp) in

                 assert(m = n /\ q = r);
                 assert(state1.cache_lines = state2.cache_lines);
                 assert(post1.cache_lines = post2.cache_lines);

                 equivalent_lists_have_equal_lengths state1.memory state2.memory;
                 equivalent_lists_have_equal_lengths state1.registers state2.registers;


                 match op1, op2 with
                  | Load a1 r1, Load a2 r2 -> (
                         assert(a1 = a2);
                         assert(r1 = r2);

                         assert(equiv_list state1.registers state2.registers);
                         assert(equiv_list state1.memory    state2.memory);


                         if (a1 < FStar.List.length state1.memory)
                                && (r1 < FStar.List.length state1.registers) then (

                           assert(a2 < FStar.List.length state2.memory);
                           assert(r2 < FStar.List.length state2.registers);

                           let mem1 = state1.memory in
                           let mem2 = state2.memory in
                           equivalent_lists_have_equivalent_values
                             blindedWord mem1 mem2 a1;

                           let write1 = (FStar.List.Tot.index state1.memory a1) in
                           let write2 = (FStar.List.Tot.index state2.memory a2) in
                           assert(equiv write1 write2);

                           assert(post1.registers = (replace_list_value state1.registers r1 write1));
                           assert(post2.registers = (replace_list_value state2.registers r2 write2));

                           replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists
                             state1.registers state2.registers r1 write1 write2;

                           assert(equiv_list post1.registers post2.registers);
                           assert(equiv_list state1.memory state2.memory);
                           assert(post1.pc = post2.pc)
                         )
                         else (
                           assert(post1 = state1);
                           assert(post2 = state2)
                           );
                         assert(equiv_system post1 post2)
                    )
                  | Store a1 r1, Store a2 r2 -> (
                         assert(a1 = a2);
                         assert(r1 = r2);

                         assert(equiv_list state1.registers state2.registers);
                         assert(equiv_list state1.memory    state2.memory);

                         if (a1 < FStar.List.length state1.memory)
                                && (r1 < FStar.List.length state1.registers) then (

                           assert(a2 < FStar.List.length state2.memory);
                           assert(r2 < FStar.List.length state2.registers);

                           let reg1 = state1.registers in
                           let reg2 = state2.registers in
                           equivalent_lists_have_equivalent_values
                             blindedWord reg1 reg2 r1;

                           let write1 = (FStar.List.Tot.index state1.registers r1) in
                           let write2 = (FStar.List.Tot.index state2.registers r2) in
                           assert(equiv write1 write2);

                           assert(post1.memory = (replace_list_value state1.memory a1 write1));
                           assert(post2.memory = (replace_list_value state2.memory a2 write2));

                           replacing_in_equivalent_lists_with_equivalent_value_yields_equivalent_lists
                             state1.memory state2.memory a1 write1 write2;

                           assert(equiv_list post1.registers post2.registers);
                           assert(equiv_list state1.memory state2.memory);
                           assert(post1.pc = post2.pc)
                           )
                         else (
                           assert(post1 = state1);
                           assert(post2 = state2)
                           );
                          assert(equiv_system post1 post2)
                    );
                 assert(equiv_system post1 post2)

let rec completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems
    (#m #q #n #r: memory_size)
    (ops1:list memory_operation)
    (ops2:(list memory_operation){FStar.List.length ops1 = FStar.List.length ops2})
    (state1:systemState #m #q) (state2 :systemState #n #r)
    (cp: cache_policy m):
    Lemma (requires (equiv_system state1 state2) /\ (equiv_memory_operations ops1 ops2))
          (ensures  (equiv_system (complete_memory_transactions ops1 state1 cp)
                                  (complete_memory_transactions ops2 state2 cp))) =
    assert(m = n /\ q = r);
    match ops1, ops2 with
     | op1 :: t1, op2 :: t2 -> (
           let post1 = complete_one_memory_transaction op1 state1 cp in
           let post2 = complete_one_memory_transaction op2 state2 cp in
           completing_single_memory_transactions_on_equivalent_systems_yields_equivalent_systems
             op1 op2 state1 state2 cp;

           completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems
             t1 t2 post1 post2 cp
       )
     | [], [] -> ()

/// ============
/// Instructions
/// ============
///
/// The next step is to define the concept of an instruction decoding.  We
/// don't want to analyze a specific ISA here, so instead we suppose that there
/// is an instruction decoder in the processor that will identify the instruction
/// operands before execution.

type decodedInstruction = { opcode: nat; input_operands: list operand; output_operands: list operand }
type decoder = (inst:word) -> decodedInstruction
type decoder_output (d:decoder) = (di:decodedInstruction{exists(inst:word). di = d inst})


/// -------
/// Outputs
/// -------
///
/// Once we know what the instruction operands are, we can define a
/// representation of the results of the instruction.  This contains a value
/// corresponding to each output operand (as identified by the instruction
/// decoder), as well as a list of memory operations.
type instruction_result (di:decodedInstruction) = {
  register_writes: (vals:(list  blindedWord){
                     FStar.List.length vals = FStar.List.length di.output_operands});
  memory_ops: (list memory_operation);
  fault: bool
}

/// We can then define an equivalence relation on instruction results to see
/// whether they leak information:
let equiv_result (#di:decodedInstruction) (lhs rhs:(instruction_result di)) = (
      (equiv_list lhs.register_writes rhs.register_writes)
    /\ (equiv_memory_operations lhs.memory_ops rhs.memory_ops)
    /\ lhs.fault = false /\ rhs.fault = false)
  \/ (lhs.fault = true /\ rhs.fault = true)

/// Then we define the usual bevy of properties:
///  - **Equality implies equivalence**:
let equal_results_are_equivalent (#di:decodedInstruction) (lhs rhs:(instruction_result di)):
  Lemma (requires lhs = rhs)
        (ensures  equiv_result lhs rhs)
  = equal_lists_are_equivalent blindedWord lhs.register_writes rhs.register_writes;
    equal_memory_operation_lists_are_equivalent lhs.memory_ops rhs.memory_ops

///  - **Symmetry**
let result_equivalence_is_symmetric (#di:decodedInstruction) (lhs rhs:(instruction_result di)):
  Lemma (requires equiv_result lhs rhs)
        (ensures equiv_result rhs lhs) =
  assert(lhs.fault = rhs.fault);
  if lhs.fault = false then (
    list_equivalence_is_symmetric blindedWord lhs.register_writes rhs.register_writes;
    memory_operation_list_equivalence_is_symmetric lhs.memory_ops rhs.memory_ops)
  else
    ()

///  - **Transitivity**
let result_equivalence_is_transitive (#di:decodedInstruction) (lhs mid rhs:(instruction_result di)):
  Lemma (requires (equiv_result lhs mid) /\ (equiv_result mid rhs))
        (ensures  (equiv_result lhs rhs)) =
  assert(lhs.fault = mid.fault && mid.fault = rhs.fault);
  if lhs.fault = false then (
    list_equivalence_is_transitive blindedWord lhs.register_writes mid.register_writes rhs.register_writes;
    memory_operation_list_equivalence_is_transitive lhs.memory_ops mid.memory_ops rhs.memory_ops)
  else ()

/// ------
/// Inputs
/// ------
///
/// We also define a type that indicates which lists of input operands are
/// compatible with a decoded instruction: some lists are just not possible,
/// either because they have the wrong number of operands for that instruction,
/// or because they conflict with each other (e.g. r1, r2, r1 → 1, 2, 3).
type instruction_input (#n #r: memory_size) (di:decodedInstruction) =
     pre:(list  blindedWord){
           (exists(s: systemState #n #r). pre = get_operands di.input_operands s)
                 /\ FStar.List.length pre = FStar.List.length di.input_operands}

/// We then show that this property is preserved by redaction.
let redacted_instruction_inputs_are_instruction_inputs  (#n #r: memory_size)
    (di:decodedInstruction) (pre:instruction_input #n #r di): instruction_input #n #r di
  = let zero: (inner #blindedWord) = 0uL in
    assert(exists (s:systemState). (pre = get_operands #n #r di.input_operands s /\
                                 (get_operands #n #r di.input_operands (redact_system s)
                   =  redact_list (get_operands di.input_operands s) zero  )  ) );
    redact_list pre zero

/// ---------
/// Semantics
/// ---------
///
/// Next we start looking at what the instructions actually do.  Earlier we
/// defined the idea of an :ref:`execution unit <execution_unit>` that maps
/// an old state to a new state according to an instruction.  Now we want do
/// define an equivalent mapping, but in terms of instruction inputs and
/// outputs:
type instruction_semantics (#n #r: memory_size) (d:decoder) =
  (di: decoder_output d) -> (pre:instruction_input #n #r di) -> instruction_result di

/// We can define a notion of redacting-equivalence for the instruction semantics too.
let is_redacting_equivalent_instruction_semantics_somewhere
      (#n #r: memory_size)
      (d:decoder)
      (s:instruction_semantics #n #r d)
      (inst:word)
      (input:instruction_input #n #r (d inst)) =
    let zero : (inner #blindedWord) = 0uL in
    redaction_preserves_length blindedWord input zero;
    let redacted_input = redacted_instruction_inputs_are_instruction_inputs (d inst) input in
    (equiv_result (s (d inst) input) (s (d inst) redacted_input))

let is_redacting_equivalent_instruction_semantics_everywhere (#n #r: memory_size)
    (d:decoder) (s:instruction_semantics #n #r d)
    = forall (inst:word) (pre:instruction_input #n #r (d inst)).
                is_redacting_equivalent_instruction_semantics_somewhere d s inst pre

/// Then as before, we show that redacting-equivalent instruction semantics
/// lead to equivalent results when applied to a redacted input.
let redacting_equivalent_instruction_semantics_on_equivalent_inputs_yields_equivalent_results_somewhere
      (#n #r: memory_size)
      (d:decoder)
      (s:instruction_semantics #n #r d)
      (inst:word)
      (input1 input2:instruction_input #n #r (d inst)):
  Lemma (requires (is_redacting_equivalent_instruction_semantics_everywhere d s)
                  /\ (equiv_list input1 input2))
        (ensures  equiv_result (s (d inst) input1) (s (d inst) input2)) =
  let zero : (inner #blindedWord) = 0uL in
  let result1 = (s (d inst) input1) in
  let result2 = (s (d inst) input2) in
  let redacted_result1 = (s (d inst) (redact_list input1 zero)) in
  let redacted_result2 = (s (d inst) (redact_list input2 zero)) in

  equivalent_lists_have_equal_redactions blindedWord input1 input2 zero;
  assert(redacted_result1 = redacted_result2);
  equal_results_are_equivalent redacted_result1 redacted_result2;

  result_equivalence_is_symmetric result2 redacted_result1;

  assert(equiv_result result1 redacted_result1);
  assert(equiv_result redacted_result1 result2);

  result_equivalence_is_transitive result1 redacted_result1 result2;
  assert(equiv_result result1 result2)


/// .. _loadstore_execution_model:
///
/// ===============
/// Execution model
/// ===============
///
/// We now define the :ref:`execution unit <execution_unit>` in terms of an instruction
/// semantics function.  This execution unit
///
/// #. decodes the instruction,
/// #. reads the input operands from the register file,
/// #. performs the computation,
/// #. increments the program counter, and
/// #. writes the result to the system's register file.
///
let loadstore_execution_unit (#n #r: memory_size)
    (d:decoder) (s:instruction_semantics #n #r d) (cp: cache_policy n)
    (inst:word) (pre:systemState #n #r): systemState #n #r =
    let decoded = d inst in
    let input_operand_values = (get_operands decoded.input_operands pre) in
    let instruction_output = (s decoded input_operand_values) in
    if instruction_output.fault then { pre with pc = 0uL } else
    let output_operand_values = instruction_output.register_writes in
    let pre_with_incremented_pc =
          { pre with pc = (
                if FStar.UInt64.v pre.pc < FStar.List.length pre.memory - 1
                then
                  FStar.UInt64.add pre.pc 1uL
                else
                  0uL
            ) } in
    let intermediate_with_updated_registers =
      set_operands decoded.output_operands output_operand_values pre_with_incremented_pc in
    complete_memory_transactions instruction_output.memory_ops intermediate_with_updated_registers cp

/// We need this for technical reasons, to trigger the inclusion of some lemmas
/// into the proof state.
irreducible let trigger (#n #r: memory_size)
  (d:decoder) (s:instruction_semantics #n #r d) (cp:cache_policy n)
  (inst:word) (pre:systemState #n #r) = False


/// ---------------------------
/// Redacting-equivalent safety
/// ---------------------------
///
/// Now we are at the point that we can start to prove security properties of this execution unit, when applied to instruction semantics that are also redacting-equivalent.
///
/// First, that it is redacting equivalent for specific instructions and system states.
let loadstore_execution_unit_with_re_instruction_semantics_is_redacting_equivalent_somewhere
      (#n #r: memory_size)
      (d:decoder)
      (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s})
      (cp:cache_policy n)
      (inst:word)
      (pre:systemState #n #r):
    Lemma (ensures (equiv_system (loadstore_execution_unit d s cp inst pre)
                                 (loadstore_execution_unit d s cp inst (redact_system pre))))
    [SMTPat (trigger d s cp inst pre)] =
      let decoded = d inst in
      let input_operand_values = (get_operands decoded.input_operands pre) in
      let redacted_input_operand_values = (get_operands decoded.input_operands (redact_system pre)) in
      let instruction_output = (s decoded input_operand_values) in
      let redacted_instruction_output = (s decoded redacted_input_operand_values) in
      let pre_with_incremented_pc = { pre with pc = (
                                      if FStar.UInt64.v pre.pc < FStar.List.length pre.memory - 1 then
                                         FStar.UInt64.add pre.pc 1uL
                                      else
                                        0uL
                                      ) } in

      systems_are_equivalent_to_their_redaction pre;

      get_operands_on_equivalent_inputs_has_equivalent_output
        decoded.input_operands
        pre
        (redact_system pre);

      assert(equiv_list input_operand_values redacted_input_operand_values);

      redacting_equivalent_instruction_semantics_on_equivalent_inputs_yields_equivalent_results_somewhere
        d s inst input_operand_values redacted_input_operand_values;

      assert(equiv_result instruction_output redacted_instruction_output);

      assert(instruction_output.fault = redacted_instruction_output.fault);
      if instruction_output.fault then
        (
          let post_with_fault = { pre with pc = 0uL } in
          let post_redacted_with_fault = { (redact_system pre) with pc = 0uL } in
          assert(equiv_system #n #r #n #r post_with_fault post_redacted_with_fault)
        )
      else (
        let zero : (inner #blindedWord) = 0uL in
        lists_are_equivalent_to_their_redaction blindedWord input_operand_values zero;

        assert(equiv_list input_operand_values (get_operands decoded.input_operands (redact_system pre)));

        list_equivalence_is_symmetric blindedWord input_operand_values redacted_input_operand_values;
        assert(equiv_list redacted_input_operand_values input_operand_values);
        list_equivalence_is_transitive blindedWord redacted_input_operand_values
          input_operand_values
          (get_operands decoded.input_operands (redact_system pre));

        assert(equiv_list redacted_input_operand_values
                          (get_operands decoded.input_operands (redact_system pre)));

        assert(equiv_list instruction_output.register_writes redacted_instruction_output.register_writes);

        let post1 = set_operands decoded.output_operands
                                 instruction_output.register_writes
                                 pre_with_incremented_pc in
        let post_redacted1 = set_operands decoded.output_operands
                                          redacted_instruction_output.register_writes
                                          (redact_system pre_with_incremented_pc) in

        systems_are_equivalent_to_their_redaction pre_with_incremented_pc;
        assert(equiv_system pre_with_incremented_pc (redact_system pre_with_incremented_pc));

        setting_equivalent_operand_values_on_equivalent_systems_yields_equivalent_systems
          decoded.output_operands instruction_output.register_writes
          redacted_instruction_output.register_writes
          pre_with_incremented_pc
          (redact_system pre_with_incremented_pc);

        assert(equiv_system post1 post_redacted1);

        let post2: systemState #n #r = complete_memory_transactions instruction_output.memory_ops
                                                                    post1
                                                                    cp in
        let post_redacted2: systemState #n #r =
          complete_memory_transactions redacted_instruction_output.memory_ops post_redacted1 cp in

        assert(equiv_memory_operations instruction_output.memory_ops
                                       redacted_instruction_output.memory_ops);
        equivalent_memory_operation_lists_have_equal_length
          instruction_output.memory_ops redacted_instruction_output.memory_ops;

        completing_equivalent_memory_transactions_on_equivalent_systems_yields_equivalent_systems
          instruction_output.memory_ops
          redacted_instruction_output.memory_ops
          post1
          post_redacted1
          cp;
        assert(equiv_system post2 post_redacted2)
    )

/// Next, that it is redacting equivalent for all instructions and system states.
let loadstore_execution_unit_with_re_instruction_semantics_is_redacting_equivalent
    (#n #r: memory_size)
    (d:decoder)
    (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s})
    (cp:cache_policy n):
  Lemma (ensures forall(pre:systemState #n #r) (inst:word).
                 (equiv_system (loadstore_execution_unit d s cp inst pre)
                               (loadstore_execution_unit d s cp inst (redact_system pre)))
                 \/ (trigger d s cp inst pre) )
    = ()

/// -------------------
/// Main safety theorem
/// -------------------

/// Finally, we show that the decoding execution unit is safe.
let each_loadstore_execution_unit_with_redacting_equivalent_instruction_semantics_is_safe
      (#n #r: memory_size)
      (d:decoder)
      (s:(instruction_semantics #n #r d){is_redacting_equivalent_instruction_semantics_everywhere d s})
      (cp:cache_policy n):
  Lemma (ensures is_safe (loadstore_execution_unit d s cp))
  = loadstore_execution_unit_with_re_instruction_semantics_is_redacting_equivalent d s cp;
    redacting_equivalent_execution_units_are_safe (loadstore_execution_unit d s cp)

(****** A simple specification about program 'simple_arm.S' *******)

needs "arm/proofs/base.ml";;

(* save_literal_from_elf "bytelist.txt" "simple_arm.o";; *)
let simple_arm_mc = define_assert_from_elf "simple_arm_mc" "simple_arm.o"
[
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0x91000400;       (* arm_ADD X0 X0 (rvalue (word 1)) *)
  0xf1000c1f;       (* arm_CMP X0 (rvalue (word 3)) *)
  0x54ffffc1        (* arm_BNE (word 2097144) *)
];;
let EXEC = ARM_MK_EXEC_RULE simple_arm_mc;;

let SIMPLE_SPEC = prove(
  `!pc.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) simple_arm_mc /\
         read PC s = word (pc+4) /\
         read X0 s = word 1)
    // Postcondition
    (\s. read PC s = word (pc+8) /\
         read X0 s = word 2)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X0] ,, MAYCHANGE SOME_FLAGS)`,
  (* Unravel ARM flag registers! *)
  REWRITE_TAC[SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Symbolically run one instruction *)
  ARM_STEPS_TAC EXEC (1--1) THEN
  (* Try to prove the postcondition as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Some unproven parts can be proven using ASM_REWRITE_TAC[]. *)
  ASM_REWRITE_TAC[]);;

(****** A simple specification about program 'simple_arm.S' *******)

(* If you are using HOL Light Online, this line is not necessary: *)
(* needs "arm/proofs/base.ml";; *)

let simple_arm_mc = new_definition `simple_arm_mc = [
    word 0x22; word 0x00; word 0x00; word 0x8b; // add x2, x1, x0
    word 0x42; word 0x00; word 0x01; word 0xcb  // sub x2, x2, x1
  ]:((8)word)list`;;
(* Or, you can read .o file and store the byte list as follows:
let simple_arm_mc = define_assert_from_elf "simple_arm_mc" "simple_arm.o"
[
  0x8b000022;       (* arm_ADD X2 X1 X0 *)
  0xcb010042        (* arm_SUB X2 X2 X1 *)
];; *)

let EXEC = ARM_MK_EXEC_RULE simple_arm_mc;;

(*
  In s2n-bignum, a specification (ensures) has three components:
  1. precondition: assume that a program starts from some program state satisfying the critera
  2. postcondition: the program must reach to a program state satisfying the criteria
  3. frame: the start program state and end program state must satisfy this relation
     (e.g., this program only changes callee-save register)
  In this file,
  1. precondition is:
    - the 'simple_arm' binary is loaded at some location in memory, say 'pc'
    - the arm program counter register, PC, has value pc
    - the arm register X0 has a symbolic value a and X1 has a symbolic value b
  2. postcondition is:
    - the arm program counter register, PC, has value pc+8
      (meaning that two instructions have been executed)
    - the arm register X2 has value b
  3. frame is:
    - the register values of PC and X2 must have been changed
*)
let SIMPLE_SPEC = prove(
  `!pc a b.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) simple_arm_mc /\
         read PC s = word pc /\
         read X0 s = word a /\
         read X1 s = word b)
    // Postcondition
    (\s. read PC s = word (pc+8) /\
         read X2 s = word a)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X2])`,
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN
  (* Symbolically run two instructions *)
  ARM_STEPS_TAC EXEC (1--2) THEN
  (* Try to prove the postcondition as much as possible *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Use ASM_REWRITE_TAC[] to rewrite the goal using equalities in assumptions. *)
  ASM_REWRITE_TAC[] THEN
  (* We need to prove this:
     `word_sub (word_add (word b) (word a)) (word b) = word a`
     Use an automated prover for words in HOL Light *)
  CONV_TAC WORD_RULE);;

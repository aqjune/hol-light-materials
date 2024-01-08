(****** A simple specification about program 'simple_arm.S' *******)

(* If you are using HOL Light Online, this line is not necessary. *)
(* needs "arm/proofs/base.ml";; *)

let simple_arm_mc = new_definition `simple_arm_mc = [
    word 0xe0; word 0x03; word 0x1f; word 0xaa; // arm_MOV X0 XZR
    word 0x00; word 0x04; word 0x00; word 0x91; // arm_ADD X0 X0 (rvalue (word 1))
    word 0x1f; word 0x0c; word 0x00; word 0xf1; // arm_CMP X0 (rvalue (word 3))
    word 0xc1; word 0xff; word 0xff; word 0x54  // arm_BNE (word 2097144)
  ]:((8)word)list`;;
(* Or, you can read .o file and store the byte list as follows:
let simple_arm_mc = define_assert_from_elf "simple_arm_mc" "simple_arm.o"
[
  0xaa1f03e0;       (* arm_MOV X0 XZR *)
  0x91000400;       (* arm_ADD X0 X0 (rvalue (word 1)) *)
  0xf1000c1f;       (* arm_CMP X0 (rvalue (word 3)) *)
  0x54ffffc1        (* arm_BNE (word 2097144) *)
];; *)

let EXEC = ARM_MK_EXEC_RULE simple_arm_mc;;

(*
  In s2n-bignum, a specification (ensures) has three components:
  1. precondition: assume that a program starts from some program state satisfying the critera
  2. postcondition: the program must reach to a program state satisfying the criteria
  3. frame: the start program state and end program state must satisfy this relation (e.g., only changes callee-save register)
  In this file,
  1. precondition is:
    - the 'simple_arm' binary is loaded at some location in memory, say 'pc'
    - the arm program counter register, PC, has value pc+4
    - the arm register X0 has value 1
  2. postcondition is:
    - the arm program counter register, PC, has value pc+8 (meaning that one instruction has been executed)
    - the arm register X0 has value 2
  3. frame is:
    - the register values of PC, X0 and flags must have been changed
*)
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

(* If you want to explore the process line by line, follow here: *)
g `!pc.
  ensures arm
    // Precondition
    (\s. aligned_bytes_loaded s (word pc) simple_arm_mc /\
         read PC s = word (pc+4) /\
         read X0 s = word 1)
    // Postcondition
    (\s. read PC s = word (pc+8) /\
         read X0 s = word 2)
    // Registers (and memory locations) that may change after execution
    (MAYCHANGE [PC;X0] ,, MAYCHANGE SOME_FLAGS)`;;
(* Unravel ARM flag registers! *)
e(REWRITE_TAC[SOME_FLAGS]);;
e(REPEAT STRIP_TAC);;
(* Start symbolic execution with state 's0' *)
e(ENSURES_INIT_TAC "s0");;
(* Symbolically run one instruction *)
e(ARM_STEPS_TAC EXEC (1--1));;
(* Try to prove the postcondition as much as possible *)
e(ENSURES_FINAL_STATE_TAC);;
(* Some unproven parts can be proven using ASM_REWRITE_TAC[]. *)
e(ASM_REWRITE_TAC[]);;

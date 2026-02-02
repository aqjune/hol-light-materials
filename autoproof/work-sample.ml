(* Theorem: multiplication of two 64-bit vectors equals splitting each 64-bit
   vector into two high and low 32-bit vectors, multiplying each arm, and
   adding together with shifts.

   High-level proof structure:
   1. Formalize the statement in terms of word operations
   2. Reduce to val equality using VAL_EQ
   3. Expand word operations to numeric form
   4. Use the decomposition val(x) = x_lo + 2^32 * x_hi
   5. Show the arithmetic identity using MOD properties

   IMPORTANT NOTE: The original formalization was incorrect because:
   - word_zx(word_mul a b) only gives the low 32 bits of a*b
   - But a*b can be up to 64 bits even when a,b are 32-bit values

   The correct formalization uses widening multiplication for the low term:
   - word_mul (word_zx a : 64 word) (word_zx b : 64 word)
   This first extends to 64 bits, then multiplies, giving the full product.
*)

needs "Library/words.ml";;

(* Key lemma: val of word_zx from 32 to 64 bits equals val of the 32-bit word *)
let VAL_WORD_ZX_32_64 = prove(
  `!w:(32)word. val((word_zx w):(64)word) = val(w)`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN ARITH_TAC);;

(* Helper: (2^32 * (a MOD 2^32)) MOD 2^64 = (2^32 * a) MOD 2^64 *)
let MOD_SHIFT_32 = prove(
  `!a. (2 EXP 32 * (a MOD 2 EXP 32)) MOD 2 EXP 64 = (2 EXP 32 * a) MOD 2 EXP 64`,
  GEN_TAC THEN
  MP_TAC(SPECL [`a:num`; `2 EXP 32`] DIVISION) THEN
  SIMP_TAC[ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 EXP 32 * x * 2 EXP 32 = x * 2 EXP 64`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SIMP_TAC[MOD_MULT_ADD; ARITH_RULE `~(2 EXP 64 = 0)`]);;

(* Key decomposition lemma: a 64-bit value equals its low 32 bits plus 2^32 times high 32 bits *)
let VAL_64_DECOMP = prove(
  `!x:(64)word. val x = val x MOD 2 EXP 32 + 2 EXP 32 * (val x DIV 2 EXP 32)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`val(x:(64)word)`; `2 EXP 32`] DIVISION) THEN
  SIMP_TAC[ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  ARITH_TAC);;

(* For 64-bit words, val x DIV 2^32 < 2^32, so the MOD is identity *)
let VAL_64_HIGH_MOD = prove(
  `!x:(64)word. (val x DIV 2 EXP 32) MOD 2 EXP 32 = val x DIV 2 EXP 32`,
  GEN_TAC THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `x:(64)word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ARITH_TAC);;

(* Pure numeric arithmetic identity for 64-bit multiplication decomposition *)
let MUL_DECOMP_NUM = prove(
  `!x_lo x_hi y_lo y_hi.
    ((x_lo + 2 EXP 32 * x_hi) * (y_lo + 2 EXP 32 * y_hi)) MOD 2 EXP 64 =
    (x_lo * y_lo + 2 EXP 32 * x_lo * y_hi + 2 EXP 32 * x_hi * y_lo) MOD 2 EXP 64`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[MULT_AC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[GSYM EXP_ADD; ARITH_RULE `32 + 32 = 64`] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  MP_TAC(SPECL [`x_hi * y_hi`;
                `2 EXP 64`;
                `x_lo * y_lo + (x_lo * y_hi) * 2 EXP 32 + (x_hi * y_lo) * 2 EXP 32`]
               (el 2 (CONJUNCTS MOD_MULT_ADD))) THEN
  REWRITE_TAC[ADD_ASSOC]);;

(* Main arithmetic identity for the decomposition *)
(* Key: explicit type annotation on quantifiers and normalize with ADD_AC first *)
let MUL_64_DECOMP_ARITH = prove(
  `!(x:(64)word) (y:(64)word).
    (val x * val y) MOD 2 EXP 64 =
    ((2 EXP 32 * val x DIV 2 EXP 32 * val y MOD 2 EXP 32 +
      2 EXP 32 * val x MOD 2 EXP 32 * val y DIV 2 EXP 32) +
     val x MOD 2 EXP 32 * val y MOD 2 EXP 32) MOD 2 EXP 64`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ADD_AC] THEN
  MP_TAC(SPECL [`val(x:(64)word) MOD 2 EXP 32`;
                `val(x:(64)word) DIV 2 EXP 32`;
                `val(y:(64)word) MOD 2 EXP 32`;
                `val(y:(64)word) DIV 2 EXP 32`] MUL_DECOMP_NUM) THEN
  REWRITE_TAC[GSYM VAL_64_DECOMP; ADD_AC]);;

(* Main theorem: 64-bit multiplication decomposition using widening multiplication for low term *)
let WORD_MUL_64_DECOMP = prove(
  `!x y:(64)word.
    word_mul x y =
      word_add (word_add
        (word_shl (word_zx (word_mul (word_subword x (32,32):(32)word)
                                      (word_subword y (0,32):(32)word)):(64)word) 32)
        (word_shl (word_zx (word_mul (word_subword x (0,32):(32)word)
                                      (word_subword y (32,32):(32)word)):(64)word) 32))
      (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
                (word_zx (word_subword y (0,32):(32)word):(64)word))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_ADD; VAL_WORD_SHL] THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD_ZX_32_64] THEN
  REWRITE_TAC[VAL_WORD_MUL; VAL_WORD_SUBWORD] THEN
  SIMP_TAC[DIMINDEX_64; DIMINDEX_32; ARITH_RULE `MIN 32 32 = 32 /\ 2 EXP 0 = 1`; DIV_1] THEN
  REWRITE_TAC[MOD_SHIFT_32] THEN
  SIMP_TAC[MOD_ADD_MOD; MOD_MOD_REFL; ARITH_RULE `~(2 EXP 64 = 0)`] THEN
  REWRITE_TAC[VAL_64_HIGH_MOD] THEN
  MESON_TAC[MOD_ADD_MOD; MUL_64_DECOMP_ARITH]);;

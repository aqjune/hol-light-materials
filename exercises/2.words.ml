(* Exercises for proving theorems regarding words (bit-vectors) *)

(* As 'CONV_TAC ARITH_RULE' solves many problems regarding natural numbers,
   HOL Light provides conversions (equivalent to ARITH_RULE) for word
   problems.
   There are four conversions you can use at 'CONV_TAC <here>':
   - WORD_RULE for simple algebraic properties
   - WORD_BITWISE_RULE for bitwise-type properties of logical operations
   - WORD_ARITH for things involving numerical values
   - WORD_BLAST for fixed-size bitwise expansions followed by arithmetic

   https://github.com/jrh13/hol-light/blob/dcd765c6032f52a0c0bf21fce5da4794a823e880/Library/words.ml#L27-L30
*)


(* 1. WORD_SUBWORD_JOIN *)

g `!(x32:(32)word) (y32:(32)word).
    word_subword (word_join x32 y32: (64)word) (0,32) = y32 /\
    word_subword (word_join x32 y32: (64)word) (32,32) = x32`;;
e(CHEAT_TAC);;

(* 2. WORD_ADD_ASSOC_CONSTS *)
g `!(x:(N)word) n m.
    (word_add (word_add x (word n)) (word m)) = (word_add x (word (n+m)))`;;
e(CHEAT_TAC);;

(* 3. WORD_OR_ADD_DISJ *)
g `! (x:(64)word) (y:(64)word).
    word_or (word_shl x 32) (word_and y (word 4294967295)) =
    word_add (word_shl x 32) (word_and y (word 4294967295))`;;
(* Feel free to use online search.
   Don't forget to choose 'Use HOL Light with Library/words.ml' *)
e(CHEAT_TAC);;

(* 4. VAL_WORD_NUM *)
(* Conversion between a word and natural number *)
g `! (n:num). val (word n:(64)word) = n MOD 2 EXP 64`;;
(* You will want to use search again, two times *)
e(CHEAT_TAC);;

(* 5. WORD_MUL_EQ (Advanced) *)
g `!(x:(64)word) (y:(64)word). word_mul x y = word ((val x * val y) MOD 2 EXP 64)`;;
e(CHEAT_TAC);;

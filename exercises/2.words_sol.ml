(* Exercises for proving theorems regarding words (bit-vectors) *)

(* 1. WORD_SUBWORD_JOIN *)
g `!(x32:(32)word) (y32:(32)word).
    word_subword (word_join x32 y32: (64)word) (0,32) = y32 /\
    word_subword (word_join x32 y32: (64)word) (32,32) = x32`;;
e(CONV_TAC WORD_BLAST);;

(* 2. WORD_ADD_ASSOC_CONSTS *)
g `!(x:(N)word) n m.
    (word_add (word_add x (word n)) (word m)) = (word_add x (word (n+m)))`;;
e(CONV_TAC WORD_RULE);;

(* 3. WORD_OR_ADD_DISJ *)
g `! (x:(64)word) (y:(64)word).
    word_or (word_shl x 32) (word_and y (word 4294967295)) =
    word_add (word_shl x 32) (word_and y (word 4294967295))`;;
(* Feel free to use online search.
   Don't forget to choose 'Use HOL Light with Library/words.ml' *)
e(REPEAT GEN_TAC THEN
  IMP_REWRITE_TAC[WORD_ADD_OR] THEN
  CONV_TAC WORD_BLAST);;

(* 4. VAL_WORD_NUM *)
(* Conversion between a word and natural number *)
g `! (n:num). val (word n:(64)word) = n MOD 2 EXP 64`;;
(* You will want to use search again, two times *)
e(REWRITE_TAC[VAL_WORD;DIMINDEX_64]);;

(* 5. WORD_MUL_EQ (Advanced) *)
g `!(x:(64)word) (y:(64)word). word_mul x y = word ((val x * val y) MOD 2 EXP 64)`;;
e(REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
              MOD_MOD_REFL; MOD_MOD_EXP_MIN]
  THEN CONV_TAC(DEPTH_CONV NUM_MIN_CONV)
  THEN MESON_TAC[]);;

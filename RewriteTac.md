(TODO)

(TODO: `TARGET_REWRITE_TAC`)

```ocaml
(* Given a goal that is `w1:int64 = w2 /\ w3:int64 = w4`, convert this to
   `val w1 = val w2 /\ val w3 = val w4` using `GSYM VAL_EQ`.
   This works even if the goal has more than one conjunction. *)
GEN_REWRITE_TAC (DEPTH_BINOP_CONV `(/\):bool->bool->bool`) [GSYM VAL_EQ]
```

  mov x0, xzr
loop:
  add x0, x0, #1
  cmp x0, #3
  bne loop


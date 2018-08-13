  ;cta 0xA1
  ;out a
  ;ctb 0xF
  ;add b
  ;out a
  ;cta 0xA1
  ;out a
  ;ctb 0xF
  ;add b
  ;out a
  ;cta 0xA1
  ;out a
  ;ctb 0xF
  ;add b
  ;not a
  ;out a

  ;cta 5
  ;mov b
  ;jmp 1
  ;ctb 4
  ;cta 2
  ;add b
  ;out a

  ;cta 4
  ;ctd 253
  ;add d
  ;jc 5
  ;jc 7
  ;ctd 4
  ;out d
  ;halt
  ;ctb 1
  ;out b
  ;halt
  ;ctc 2
  ;out c
  ;halt


  ; test all

  nop
  cta 10
  ctb 0x10
  ctc -10
  ctd 255

  out a
  out b
  out c
  out d

  add c
  cta 3
  ctb 3
  ctc 2
  shl b
  out a
  shr c
  out a
  and b
  or d
  xor b
  ; why is carry flag set??

  jmp 2
  jz 2
  jg 2
  jl 2
  jc 2
  out a

  mov b
  mov c
  mov d

  neg b
  not c

; initialize
ctd 0
out d
out b
cta 1
ctb 0
out a

; main loop
mov c
add b
jc 8
out d
out a
mov b
add c
out d
out a
jmp -9
halt
 ;test

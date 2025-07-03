;#Safe
@i = global i32 1

define i32 @main() {
entry:
  %0 = load i32, ptr @i, align 4
 
  ret i32 0
}

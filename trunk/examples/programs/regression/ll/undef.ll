;#Safe
define i32 @main() {
entry:
  %div = sdiv i32 undef, 5                          
  ret i32 undef
}


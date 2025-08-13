;#Safe
define i32 @main() {
entry:
  %sub = sub nsw i32 77, -13
  %sub1 = sub nsw i32 %sub, 42605               
  ret i32 0
}


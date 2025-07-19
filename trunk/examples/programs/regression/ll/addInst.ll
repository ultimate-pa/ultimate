;#Safe
define i32 @main() {
entry:
  %inc = add nsw i32 7, 1
  %add = add nsw i32 7, 5
  %dec = add nsw i32 %inc, -1
  ret i32 0
}


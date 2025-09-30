; #Safe
@i = global i32 1

define i32 @main() {
entry:
  %0 = load i32, ptr @i, align 4
  %cmp = icmp eq i32 %0, 1
  switch i1 %cmp, label %entry.unreachabledefault [
    i1 0, label %while.cond
    i1 1, label %while.cond4
  ]

while.cond:                                          ; preds = %entry
  unreachable

while.cond4:                                                ; No predecessors!
  unreachable

entry.unreachabledefault:                                          ; preds = %1, %entry
  ret i32 0
}


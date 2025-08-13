; #Safe
define i32 @main()  {
entry:
  %cmp = icmp eq i32 0, 0
  br i1 %cmp, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %entry 
  unreachable

0:                                                ; No predecessors!
  br label %lor.end

lor.end:                                          ; preds = %0, %entry
  %1 = phi i1 [ true, %entry ], [ false, %0 ]
  %lor.ext = zext i1 %1 to i32
  %cmp1 = icmp eq i32 0, 0
  br i1 %cmp1, label %lor.end3, label %lor.rhs2

lor.rhs2:                                         ; preds = %lor.end
  unreachable

2:                                                ; No predecessors!
  br label %lor.end3

lor.end3:                                         ; preds = %2, %lor.end
  %3 = phi i1 [ true, %lor.end ], [ false, %2 ]
  %lor.ext4 = zext i1 %3 to i32
  ret i32 0
}









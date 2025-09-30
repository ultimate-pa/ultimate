; #Safe
; ModuleID = 'output_folder/ACSL-quantifierArray.ll'

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_ushort()
  %conv = sext i32 %call to i64
  %mul = mul i64 %conv, 4
  %call1 = call ptr @malloc(i64 noundef %mul) #2
  br label %for.cond

for.cond:                                         ; preds = %for.body, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.body ]
  %cmp = icmp slt i32 %i.0, %call
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %idxprom = sext i32 %i.0 to i64
  %arrayidx = getelementptr inbounds i32, ptr %call1, i64 %idxprom
  store i32 42, ptr %arrayidx, align 4
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 0
}

declare i32 @__VERIFIER_nondet_ushort(...) #0

; Function Attrs: allocsize(0)
declare ptr @malloc(i64 noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





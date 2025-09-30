; #Safe
; ModuleID = 'c5/ACSL-array_loop_invariant.c'

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca ptr, align 8
  store i32 0, ptr %retval, align 4
  %call = call noalias ptr @malloc(i64 noundef 4) #4
  store ptr %call, ptr %a, align 8
  %0 = load ptr, ptr %a, align 8
  %arrayidx = getelementptr inbounds i32, ptr %0, i64 0
  store i32 7, ptr %arrayidx, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %call1 = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call1, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %1 = load ptr, ptr %a, align 8
  %2 = load i32, ptr %1, align 4
  %cmp = icmp eq i32 %2, 7
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %while.end
  br label %if.end

if.else:                                          ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #5
  unreachable

if.end:                                           ; preds = %if.then
  %3 = load i32, ptr %retval, align 4
  ret i32 %3
}

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #1

declare i32 @__VERIFIER_nondet_int(...) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #3
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





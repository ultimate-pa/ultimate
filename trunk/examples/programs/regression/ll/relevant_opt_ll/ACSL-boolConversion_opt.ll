; #Safe
; ModuleID = 'output_folder/ACSL-boolConversion.ll'

define dso_local i32 @main() {
entry:
  br label %while.cond

while.cond:                                       ; preds = %while.cond, %entry
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %while.cond, label %while.end, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %tobool1 = icmp ne i32 2, 0
  br i1 %tobool1, label %if.end, label %if.else

if.else:                                          ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %while.end
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





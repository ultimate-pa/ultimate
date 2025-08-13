; #Safe
; ModuleID = 'output_folder/AffineTerms.ll'
source_filename = "c5/AffineTerms.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_int()
  %call1 = call i32 @__VERIFIER_nondet_int()
  %call2 = call i32 @__VERIFIER_nondet_int()
  %add = add nsw i32 %call, %call1
  %add3 = add nsw i32 %add, %call2
  %cmp = icmp sgt i32 %add3, 0
  br i1 %cmp, label %while.cond, label %if.end9

while.cond:                                       ; preds = %while.cond, %entry
  %call4 = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call4, 0
  br i1 %tobool, label %while.cond, label %while.end, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %add5 = add nsw i32 %call, %call1
  %add6 = add nsw i32 %add5, %call2
  %cmp7 = icmp sle i32 %add6, 0
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end9:                                          ; preds = %while.end, %entry
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





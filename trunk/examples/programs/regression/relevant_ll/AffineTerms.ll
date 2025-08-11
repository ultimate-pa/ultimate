; #Safe
; ModuleID = 'c5/AffineTerms.c'
source_filename = "c5/AffineTerms.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i32 @__VERIFIER_nondet_int()
  store i32 %call, ptr %x, align 4
  %call1 = call i32 @__VERIFIER_nondet_int()
  store i32 %call1, ptr %y, align 4
  %call2 = call i32 @__VERIFIER_nondet_int()
  store i32 %call2, ptr %z, align 4
  %0 = load i32, ptr %x, align 4
  %1 = load i32, ptr %y, align 4
  %add = add nsw i32 %0, %1
  %2 = load i32, ptr %z, align 4
  %add3 = add nsw i32 %add, %2
  %cmp = icmp sgt i32 %add3, 0
  br i1 %cmp, label %if.then, label %if.end9

if.then:                                          ; preds = %entry
  br label %while.cond

while.cond:                                       ; preds = %while.body, %if.then
  %call4 = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call4, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %3 = load i32, ptr %x, align 4
  %4 = load i32, ptr %y, align 4
  %add5 = add nsw i32 %3, %4
  %5 = load i32, ptr %z, align 4
  %add6 = add nsw i32 %add5, %5
  %cmp7 = icmp sle i32 %add6, 0
  br i1 %cmp7, label %if.then8, label %if.end

if.then8:                                         ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %while.end
  br label %if.end9

if.end9:                                          ; preds = %if.end, %entry
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





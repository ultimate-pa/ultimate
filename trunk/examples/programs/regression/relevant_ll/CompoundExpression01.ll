; #Safe
; ModuleID = 'c5/CompoundExpression01.c'
source_filename = "c5/CompoundExpression01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %a = alloca i32, align 4
  %tmp = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i16 @__VERIFIER_nondet_short()
  %conv = sext i16 %call to i32
  store i32 %conv, ptr %x, align 4
  %0 = load i32, ptr %x, align 4
  store i32 %0, ptr %a, align 4
  %1 = load i32, ptr %a, align 4
  store i32 %1, ptr %tmp, align 4
  %2 = load i32, ptr %tmp, align 4
  store i32 %2, ptr %y, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %call1 = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call1, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %3 = load i32, ptr %x, align 4
  %4 = load i32, ptr %y, align 4
  %cmp = icmp eq i32 %3, %4
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %while.end
  br label %if.end

if.else:                                          ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

declare i16 @__VERIFIER_nondet_short() #1

declare i32 @__VERIFIER_nondet_int() #1

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





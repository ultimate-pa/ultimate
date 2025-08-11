; #Safe
; ModuleID = './ACSL-shift.c'
source_filename = "./ACSL-shift.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, ptr %x, align 4
  %call = call i32 @__VERIFIER_nondet_int()
  store i32 %call, ptr %y, align 4
  %0 = load i32, ptr %x, align 4
  %1 = load i32, ptr %y, align 4
  %shr = ashr i32 %0, %1
  %cmp = icmp eq i32 %shr, 0
  br i1 %cmp, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %entry
  %2 = load i32, ptr %x, align 4
  %3 = load i32, ptr %y, align 4
  %shl = shl i32 %2, %3
  %cmp1 = icmp eq i32 %shl, 0
  br i1 %cmp1, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true
  br label %if.end

if.else:                                          ; preds = %land.lhs.true, %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int() #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Safe
; ModuleID = 'c5/BitwiseShiftOperators01.c'
source_filename = "c5/BitwiseShiftOperators01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i32, align 4
  %e = alloca i32, align 4
  %f = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 5, ptr %a, align 4
  %0 = load i32, ptr %a, align 4
  %shl = shl i32 %0, 4
  store i32 %shl, ptr %b, align 4
  %1 = load i32, ptr %b, align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %1)
  %2 = load i32, ptr %b, align 4
  %cmp = icmp ne i32 %2, 80
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  store i32 -2147483647, ptr %c, align 4
  %3 = load i32, ptr %c, align 4
  %shl1 = shl i32 %3, 1
  store i32 %shl1, ptr %d, align 4
  %4 = load i32, ptr %d, align 4
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, i32 noundef %4)
  %5 = load i32, ptr %d, align 4
  %cmp3 = icmp ne i32 %5, 2
  br i1 %cmp3, label %if.then4, label %if.end5

if.then4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 23, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end5:                                          ; preds = %if.end
  store i32 5, ptr %e, align 4
  %6 = load i32, ptr %e, align 4
  %shr = ashr i32 %6, 1
  store i32 %shr, ptr %f, align 4
  %7 = load i32, ptr %f, align 4
  %call6 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %7)
  %8 = load i32, ptr %f, align 4
  %cmp7 = icmp ne i32 %8, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end5
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end9:                                          ; preds = %if.end5
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





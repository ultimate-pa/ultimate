; #Safe
; ModuleID = 'c5/NutzTransformation02.c'
source_filename = "c5/NutzTransformation02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 -1, ptr %a, align 4
  %0 = load i32, ptr %a, align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %0)
  %1 = load i32, ptr %a, align 4
  %div = udiv i32 %1, 1024
  store i32 %div, ptr %b, align 4
  %2 = load i32, ptr %b, align 4
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %2)
  %3 = load i32, ptr %b, align 4
  %cmp = icmp ne i32 %3, 4194303
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  store i32 -32, ptr %c, align 4
  %4 = load i32, ptr %c, align 4
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %4)
  %5 = load i32, ptr %c, align 4
  %rem = urem i32 %5, 13
  store i32 %rem, ptr %d, align 4
  %6 = load i32, ptr %d, align 4
  %call3 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %6)
  %7 = load i32, ptr %d, align 4
  %cmp4 = icmp ne i32 %7, 3
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end6:                                          ; preds = %if.end
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





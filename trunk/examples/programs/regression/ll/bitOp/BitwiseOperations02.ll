; #Unsafe
; ModuleID = 'c5/BitwiseOperations02.c'
source_filename = "c5/BitwiseOperations02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 1, ptr %y, align 4
  store i32 2, ptr %z, align 4
  %0 = load i32, ptr %x, align 4
  %1 = load i32, ptr %y, align 4
  %and = and i32 %0, %1
  store i32 %and, ptr %x, align 4
  %2 = load i32, ptr %x, align 4
  %3 = load i32, ptr %y, align 4
  %or = or i32 %2, %3
  store i32 %or, ptr %x, align 4
  %4 = load i32, ptr %x, align 4
  %5 = load i32, ptr %y, align 4
  %xor = xor i32 %4, %5
  store i32 %xor, ptr %x, align 4
  %6 = load i32, ptr %x, align 4
  %7 = load i32, ptr %y, align 4
  %shl = shl i32 %6, %7
  store i32 %shl, ptr %x, align 4
  %8 = load i32, ptr %x, align 4
  %9 = load i32, ptr %y, align 4
  %shr = ashr i32 %8, %9
  store i32 %shr, ptr %x, align 4
  %10 = load i32, ptr %y, align 4
  %11 = load i32, ptr %x, align 4
  %and1 = and i32 %11, %10
  store i32 %and1, ptr %x, align 4
  %12 = load i32, ptr %y, align 4
  %13 = load i32, ptr %x, align 4
  %or2 = or i32 %13, %12
  store i32 %or2, ptr %x, align 4
  %14 = load i32, ptr %y, align 4
  %15 = load i32, ptr %x, align 4
  %xor3 = xor i32 %15, %14
  store i32 %xor3, ptr %x, align 4
  %16 = load i32, ptr %y, align 4
  %17 = load i32, ptr %x, align 4
  %shl4 = shl i32 %17, %16
  store i32 %shl4, ptr %x, align 4
  %18 = load i32, ptr %y, align 4
  %19 = load i32, ptr %x, align 4
  %shr5 = ashr i32 %19, %18
  store i32 %shr5, ptr %x, align 4
  %20 = load i32, ptr %x, align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %20)
  %21 = load i32, ptr %x, align 4
  %cmp = icmp eq i32 %21, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
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





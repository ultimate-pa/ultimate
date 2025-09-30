; #Safe
; ModuleID = './arrayPointerComparison.c'
source_filename = "./arrayPointerComparison.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@x = dso_local global [2 x i32] [i32 1, i32 2], align 4

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %y = alloca ptr, align 8
  store i32 0, ptr %retval, align 4
  %call = call ptr @malloc(i64 noundef 4) #3
  store ptr %call, ptr %y, align 8
  %0 = load ptr, ptr %y, align 8
  %cmp = icmp eq ptr @x, %0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %call1 = call i32 @reach_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  %1 = load i32, ptr %retval, align 4
  ret i32 %1
}

; Function Attrs: allocsize(0)
declare ptr @malloc(i64 noundef) #1

declare i32 @reach_error(...) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





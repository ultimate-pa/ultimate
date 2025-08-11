; #Unsafe
; ModuleID = 'c5/bitwiseOrUnsignedMinimal.c'
source_filename = "c5/bitwiseOrUnsignedMinimal.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %left = alloca i32, align 4
  %right = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 -1, ptr %left, align 4
  store i32 1, ptr %right, align 4
  %0 = load i32, ptr %left, align 4
  %1 = load i32, ptr %right, align 4
  %cmp = icmp ne i32 %1, 0
  %conv = zext i1 %cmp to i32
  %or = or i32 %0, %conv
  %tobool = icmp ne i32 %or, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret i32 0
}

declare void @__VERIFIER_error() #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





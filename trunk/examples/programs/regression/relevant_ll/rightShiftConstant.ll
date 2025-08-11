; #Unsafe
; ModuleID = 'c5/rightShiftConstant.c'
source_filename = "c5/rightShiftConstant.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %uc = alloca i8, align 1
  store i32 0, ptr %retval, align 4
  %call = call i8 @__VERIFIER_nondet_uchar()
  store i8 %call, ptr %uc, align 1
  %0 = load i8, ptr %uc, align 1
  %conv = zext i8 %0 to i32
  %add = add i32 %conv, -1
  %shr = lshr i32 %add, 2
  %cmp = icmp ult i32 %shr, 8
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret i32 0
}

declare i8 @__VERIFIER_nondet_uchar() #1

declare void @__VERIFIER_error() #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





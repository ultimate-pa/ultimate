; #Safe
; ModuleID = 'c5/GnuC128BitIntegers01.c'
source_filename = "c5/GnuC128BitIntegers01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %largestUint128 = alloca i128, align 16
  %someULong = alloca i64, align 8
  store i32 0, ptr %retval, align 4
  store i128 -1, ptr %largestUint128, align 16
  %call = call i64 @__VERIFIER_nondet_ulong()
  store i64 %call, ptr %someULong, align 8
  %0 = load i128, ptr %largestUint128, align 16
  %1 = load i64, ptr %someULong, align 8
  %conv = zext i64 %1 to i128
  %cmp = icmp ugt i128 %0, %conv
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

declare i64 @__VERIFIER_nondet_ulong(...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





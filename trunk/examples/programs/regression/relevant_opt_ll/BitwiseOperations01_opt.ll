; #Safe
; ModuleID = 'output_folder/BitwiseOperations01.ll'
source_filename = "c5/BitwiseOperations01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %and = and i32 undef, 1
  %or = or i32 %and, 1
  %xor = xor i32 %or, 1
  %shl = shl i32 %xor, 1
  %shr = ashr i32 %shl, 1
  %and1 = and i32 %shr, 1
  %or2 = or i32 %and1, 1
  %xor3 = xor i32 %or2, 1
  %shl4 = shl i32 %xor3, 1
  %shr5 = ashr i32 %shl4, 1
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %shr5)
  %cmp = icmp ne i32 %shr5, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





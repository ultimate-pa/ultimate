; #Safe
; ModuleID = 'output_folder/BitwiseShiftOperators01.ll'
source_filename = "c5/BitwiseShiftOperators01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %shl = shl i32 5, 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %shl)
  %cmp = icmp ne i32 %shl, 80
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %shl1 = shl i32 -2147483647, 1
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, i32 noundef %shl1)
  %cmp3 = icmp ne i32 %shl1, 2
  br i1 %cmp3, label %if.then4, label %if.end5

if.then4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 23, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end5:                                          ; preds = %if.end
  %shr = ashr i32 5, 1
  %call6 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %shr)
  %cmp7 = icmp ne i32 %shr, 2
  br i1 %cmp7, label %if.then8, label %if.end9

if.then8:                                         ; preds = %if.end5
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end9:                                          ; preds = %if.end5
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





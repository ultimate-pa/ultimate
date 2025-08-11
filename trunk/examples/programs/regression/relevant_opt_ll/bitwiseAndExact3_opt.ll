; #Safe
; ModuleID = 'output_folder/bitwiseAndExact3.ll'
source_filename = "c5/bitwiseAndExact3.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %and = and i32 undef, -4
  %cmp = icmp slt i32 undef, 4
  %cmp1 = icmp sgt i32 undef, 7
  %or.cond = or i1 %cmp, %cmp1
  %cmp3 = icmp eq i32 %and, 4
  %or.cond3 = or i1 %or.cond, %cmp3
  br i1 %or.cond3, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





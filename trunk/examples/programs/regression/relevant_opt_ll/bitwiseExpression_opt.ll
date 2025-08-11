; #Safe
; ModuleID = 'output_folder/bitwiseExpression.ll'
source_filename = "./bitwiseExpression.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %cmp = icmp slt i32 undef, 0
  br i1 %cmp, label %if.end5, label %if.end

if.end:                                           ; preds = %entry
  %and = and i32 undef, undef
  %sub = sub nsw i32 %and, 1
  %cmp2 = icmp slt i32 %sub, undef
  br i1 %cmp2, label %if.end5, label %if.else

if.else:                                          ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end5:                                          ; preds = %if.end, %entry
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





; #Safe
; ModuleID = 'output_folder/NegationInt_safe.ll'
source_filename = "c5/NegationInt_safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %tobool = icmp ne i32 0, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  %tobool1 = icmp ne i32 1, 0
  %lnot2 = xor i1 %tobool1, true
  %lnot.ext3 = zext i1 %lnot2 to i32
  %tobool4 = icmp ne i32 2, 0
  %lnot5 = xor i1 %tobool4, true
  %lnot.ext6 = zext i1 %lnot5 to i32
  %cmp = icmp eq i32 %lnot.ext, 1
  %cmp7 = icmp eq i32 %lnot.ext3, 0
  %or.cond = and i1 %cmp, %cmp7
  %cmp9 = icmp eq i32 %lnot.ext6, 0
  %or.cond1 = and i1 %or.cond, %cmp9
  br i1 %or.cond1, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #1
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





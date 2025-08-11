; #Safe
; ModuleID = 'output_folder/SideEffectInReturn.ll'
source_filename = "c5/SideEffectInReturn.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@g = dso_local global i32 0, align 4

define dso_local i32 @proc() {
entry:
  %0 = load i32, ptr @g, align 4
  %inc = add nsw i32 %0, 1
  store i32 %inc, ptr @g, align 4
  ret i32 %0
}

define dso_local i32 @main() {
entry:
  %call = call i32 @proc()
  %cmp = icmp eq i32 %call, 0
  %0 = load i32, ptr @g, align 4
  %cmp1 = icmp eq i32 %0, 1
  %or.cond = select i1 %cmp, i1 %cmp1, i1 false
  br i1 %or.cond, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #1
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





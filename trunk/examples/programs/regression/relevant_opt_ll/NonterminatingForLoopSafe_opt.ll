; #Safe
; ModuleID = 'output_folder/NonterminatingForLoopSafe.ll'
source_filename = "c5/NonterminatingForLoopSafe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.cond, %entry
  %i.0 = phi i32 [ 5, %entry ], [ %add, %for.cond ]
  %add = add nsw i32 %i.0, 0
  %cmp = icmp eq i32 %add, 5
  br i1 %cmp, label %for.cond, label %if.else

if.else:                                          ; preds = %for.cond
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





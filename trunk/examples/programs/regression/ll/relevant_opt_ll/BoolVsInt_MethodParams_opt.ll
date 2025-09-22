; #Safe
; ModuleID = 'output_folder/BoolVsInt_MethodParams.ll'
source_filename = "c5/BoolVsInt_MethodParams.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @test(i32 noundef %a, i32 noundef %b, i1 noundef %c, i1 noundef %d, i32 noundef %e, i32 noundef %f) {
entry:
  %frombool = zext i1 %c to i8
  %frombool1 = zext i1 %d to i8
  %tobool = trunc i8 %frombool1 to i1
  %. = select i1 %tobool, i32 0, i32 -1
  ret i32 %.
}

define dso_local i32 @main() {
entry:
  %call = call i32 @test(i32 noundef 1, i32 noundef 2, i1 noundef false, i1 noundef true, i32 noundef 5, i32 noundef 6)
  %cmp = icmp eq i32 %call, 0
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 19, ptr noundef @__PRETTY_FUNCTION__.main) #1
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





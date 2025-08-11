; #Safe
; ModuleID = 'output_folder/NutzTransformation01.ll'
source_filename = "c5/NutzTransformation01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -2147483648)
  %add = add i32 -2147483648, -2147483648
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %add)
  %cmp = icmp ne i32 %add, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %conv = zext i32 %add to i64
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, i64 noundef %conv)
  %cmp3 = icmp ne i64 %conv, 0
  br i1 %cmp3, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 36, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end6:                                          ; preds = %if.end
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





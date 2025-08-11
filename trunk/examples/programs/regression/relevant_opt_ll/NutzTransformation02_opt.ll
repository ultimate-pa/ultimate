; #Safe
; ModuleID = 'output_folder/NutzTransformation02.ll'
source_filename = "c5/NutzTransformation02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -1)
  %div = udiv i32 -1, 1024
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %div)
  %cmp = icmp ne i32 %div, 4194303
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef -32)
  %rem = urem i32 -32, 13
  %call3 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %rem)
  %cmp4 = icmp ne i32 %rem, 3
  br i1 %cmp4, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.main) #2
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





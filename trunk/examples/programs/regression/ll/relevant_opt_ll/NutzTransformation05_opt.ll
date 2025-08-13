; #Safe
; ModuleID = 'output_folder/NutzTransformation05.ll'
source_filename = "c5/NutzTransformation05.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %conv = zext i8 -1 to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %conv1 = zext i8 -1 to i32
  %conv2 = zext i8 -1 to i32
  %add = add nsw i32 %conv1, %conv2
  %cmp = icmp slt i32 %add, 500
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 29, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %conv4 = zext i8 -1 to i32
  %conv5 = zext i8 -1 to i32
  %add6 = add nsw i32 %conv4, %conv5
  %call7 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, i32 noundef %add6)
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





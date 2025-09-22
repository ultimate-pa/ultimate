; #Safe
; ModuleID = 'output_folder/Bool02.ll'
source_filename = "c5/Bool02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %tobool = trunc i8 1 to i1
  %conv = zext i1 %tobool to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %tobool1 = trunc i8 1 to i1
  %conv2 = zext i1 %tobool1 to i32
  %cmp = icmp eq i32 %conv2, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 19, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %tobool4 = icmp ne i64 4294967296, 0
  %frombool = zext i1 %tobool4 to i8
  %tobool5 = trunc i8 %frombool to i1
  %conv6 = zext i1 %tobool5 to i32
  %call7 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv6)
  %tobool8 = trunc i8 %frombool to i1
  %conv9 = zext i1 %tobool8 to i32
  %cmp10 = icmp eq i32 %conv9, 0
  br i1 %cmp10, label %if.then12, label %if.end13

if.then12:                                        ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end13:                                         ; preds = %if.end
  %tobool14 = icmp ne i64 4294967296, 0
  %frombool15 = zext i1 %tobool14 to i8
  %tobool16 = trunc i8 %frombool15 to i1
  %conv17 = zext i1 %tobool16 to i32
  %call18 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv17)
  %tobool19 = trunc i8 %frombool15 to i1
  %conv20 = zext i1 %tobool19 to i32
  %cmp21 = icmp eq i32 %conv20, 0
  br i1 %cmp21, label %if.then23, label %if.end24

if.then23:                                        ; preds = %if.end13
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 31, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end24:                                         ; preds = %if.end13
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





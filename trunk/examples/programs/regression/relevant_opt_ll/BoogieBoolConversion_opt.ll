; #Safe
; ModuleID = 'output_folder/BoogieBoolConversion.ll'
source_filename = "erw/BoogieBoolConversion.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %cmp = icmp eq i32 2, 2
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  %cmp1 = icmp eq i32 1, 1
  br i1 %cmp1, label %if.end8, label %if.else3

if.else3:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end8:                                          ; preds = %if.end
  %cmp9 = icmp eq i64 1, 1
  br i1 %cmp9, label %if.end12, label %if.else11

if.else11:                                        ; preds = %if.end8
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.1, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end12:                                         ; preds = %if.end8
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





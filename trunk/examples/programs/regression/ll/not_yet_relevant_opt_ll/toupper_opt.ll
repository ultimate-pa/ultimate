; #Safe
; ModuleID = 'output_folder/toupper.ll'
source_filename = "c5/toupper.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i8 @__VERIFIER_nondet_uchar()
  %conv = zext i8 %call to i32
  %call1 = call i32 @toupper(i32 noundef %conv) #3
  %cmp = icmp sge i32 %conv, 97
  %cmp3 = icmp sle i32 %conv, 122
  %or.cond = and i1 %cmp, %cmp3
  br i1 %or.cond, label %if.then, label %if.else8

if.then:                                          ; preds = %entry
  %add = add nsw i32 %call1, 32
  %cmp5 = icmp eq i32 %add, %conv
  br i1 %cmp5, label %if.end14, label %if.else

if.else:                                          ; preds = %if.then
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.else8:                                         ; preds = %entry
  %cmp9 = icmp eq i32 %conv, %call1
  br i1 %cmp9, label %if.end14, label %if.else12

if.else12:                                        ; preds = %if.else8
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end14:                                         ; preds = %if.else8, %if.then
  ret i32 0
}

declare i8 @__VERIFIER_nondet_uchar() #0

; Function Attrs: nounwind willreturn memory(read)
declare i32 @toupper(i32 noundef) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





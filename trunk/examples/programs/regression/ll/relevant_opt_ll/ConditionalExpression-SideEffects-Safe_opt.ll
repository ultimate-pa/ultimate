; #Safe
; ModuleID = 'output_folder/ConditionalExpression-SideEffects-Safe.ll'
source_filename = "c5/ConditionalExpression-SideEffects-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @foo(i32 noundef %a, i32 noundef %b, i32 noundef %c) {
entry:
  %inc = add nsw i32 %a, 1
  %cmp = icmp eq i32 %a, 0
  %inc1 = add nsw i32 %b, 1
  %inc2 = add nsw i32 %c, 1
  %y.0 = select i1 %cmp, i32 %inc1, i32 %b
  %z.0 = select i1 %cmp, i32 %c, i32 %inc2
  %cond = select i1 %cmp, i32 %b, i32 %c
  %add = add nsw i32 %a, 1
  %cmp3 = icmp eq i32 %inc, %add
  br i1 %cmp3, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.foo) #1
  unreachable

if.end:                                           ; preds = %entry
  %cond15 = icmp eq i32 %a, 0
  br i1 %cond15, label %cond.true5, label %cond.true20

cond.true5:                                       ; preds = %if.end
  %cmp6 = icmp eq i32 %cond, %b
  br i1 %cmp6, label %if.end10, label %if.else9

if.else9:                                         ; preds = %cond.true5
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.foo) #1
  unreachable

if.end10:                                         ; preds = %cond.true5
  %cond16 = icmp eq i32 %a, 0
  br i1 %cond16, label %cond.true12, label %cond.true20

cond.true12:                                      ; preds = %if.end10
  %add13 = add nsw i32 %b, 1
  %cmp14 = icmp eq i32 %y.0, %add13
  br i1 %cmp14, label %if.end18, label %if.else17

if.else17:                                        ; preds = %cond.true12
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.foo) #1
  unreachable

if.end18:                                         ; preds = %cond.true12
  %cond17 = icmp eq i32 %a, 0
  br i1 %cond17, label %if.end33, label %cond.true20

cond.true20:                                      ; preds = %if.end18, %if.end10, %if.end
  %cmp21 = icmp eq i32 %cond, %c
  br i1 %cmp21, label %if.end25, label %if.else24

if.else24:                                        ; preds = %cond.true20
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.foo) #1
  unreachable

if.end25:                                         ; preds = %cond.true20
  %cmp26 = icmp eq i32 %a, 0
  %add28 = add nsw i32 %c, 1
  %cmp29 = icmp eq i32 %z.0, %add28
  %or.cond = select i1 %cmp26, i1 true, i1 %cmp29
  br i1 %or.cond, label %if.end33, label %if.else32

if.else32:                                        ; preds = %if.end25
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.foo) #1
  unreachable

if.end33:                                         ; preds = %if.end18, %if.end25
  ret i32 %cond
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0

define dso_local i32 @main() {
entry:
  %call = call i32 @foo(i32 noundef undef, i32 noundef undef, i32 noundef undef)
  ret i32 0
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





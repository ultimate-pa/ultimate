; #Safe
; ModuleID = 'output_folder/BoolVsInt.ll'
source_filename = "c5/BoolVsInt.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %tobool = icmp ne i32 1, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  %cmp = icmp eq i32 %lnot.ext, 0
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 11, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  %tobool1 = icmp ne i32 %lnot.ext, 0
  %lnot2 = xor i1 %tobool1, true
  %lnot.ext3 = zext i1 %lnot2 to i32
  %cmp4 = icmp ne i32 %lnot.ext3, 0
  br i1 %cmp4, label %if.end7, label %if.else6

if.else6:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end7:                                          ; preds = %if.end
  %cmp8 = icmp ne i32 1, 0
  br i1 %cmp8, label %if.end15, label %if.else10

if.else10:                                        ; preds = %if.end7
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end15:                                         ; preds = %if.end7
  %cmp16 = icmp eq i32 0, 0
  br i1 %cmp16, label %if.end19, label %if.else18

if.else18:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end19:                                         ; preds = %if.end15
  %cmp20 = icmp ne i32 1, 0
  br i1 %cmp20, label %if.end23, label %if.else22

if.else22:                                        ; preds = %if.end19
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end23:                                         ; preds = %if.end19
  %cmp24 = icmp eq i32 0, 0
  br i1 %cmp24, label %if.end27, label %if.else26

if.else26:                                        ; preds = %if.end23
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 31, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end27:                                         ; preds = %if.end23
  %cmp28 = icmp ne i32 1, 0
  br i1 %cmp28, label %if.end31, label %if.else30

if.else30:                                        ; preds = %if.end27
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 34, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end31:                                         ; preds = %if.end27
  %cmp32 = icmp eq i32 0, 0
  br i1 %cmp32, label %if.end39, label %if.else34

if.else34:                                        ; preds = %if.end31
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end39:                                         ; preds = %if.end31
  %cmp40 = icmp eq i32 1, 1
  br i1 %cmp40, label %if.end43, label %if.else42

if.else42:                                        ; preds = %if.end39
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 47, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end43:                                         ; preds = %if.end39
  %tobool44 = icmp ne i32 0, 0
  %spec.select = select i1 %tobool44, i32 1, i32 0
  %cmp47 = icmp eq i32 %spec.select, 0
  br i1 %cmp47, label %if.end50, label %if.else49

if.else49:                                        ; preds = %if.end43
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 57, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end50:                                         ; preds = %if.end43
  %tobool51 = icmp ne i32 0, 0
  %spec.select35 = select i1 %tobool51, i32 0, i32 1
  %cmp54 = icmp eq i32 %spec.select35, 1
  br i1 %cmp54, label %if.end57, label %if.else56

if.else56:                                        ; preds = %if.end50
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 63, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end57:                                         ; preds = %if.end50
  %cmp58 = icmp eq i32 1, 1
  br i1 %cmp58, label %if.end61, label %if.else60

if.else60:                                        ; preds = %if.end57
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 69, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end61:                                         ; preds = %if.end57
  %cmp62 = icmp eq i32 0, 0
  %cmp66 = icmp eq i32 0, 0
  br i1 %cmp66, label %if.end69, label %if.else68

if.else68:                                        ; preds = %if.end61
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 75, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end69:                                         ; preds = %if.end61
  %add = add nsw i32 0, 1
  %tobool70 = icmp ne i32 %add, 0
  %spec.select36 = select i1 %tobool70, i32 1, i32 0
  %cmp73 = icmp eq i32 %spec.select36, 1
  br i1 %cmp73, label %while.cond, label %if.else75

if.else75:                                        ; preds = %if.end69
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 81, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

while.cond:                                       ; preds = %if.end69, %while.body
  %i.4 = phi i32 [ %sub, %while.body ], [ 2, %if.end69 ]
  %tobool77 = icmp ne i32 %i.4, 0
  br i1 %tobool77, label %while.body, label %while.body83

while.body:                                       ; preds = %while.cond
  %sub = sub nsw i32 %i.4, 1
  br label %while.cond, !llvm.loop !6

while.body83:                                     ; preds = %while.cond
  %sub84 = sub nsw i32 2, 1
  %cmp86 = icmp eq i32 %sub84, 1
  br i1 %cmp86, label %while.cond90, label %if.else88

if.else88:                                        ; preds = %while.body83
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 98, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

while.cond90:                                     ; preds = %while.body83, %while.body92
  %i.5 = phi i32 [ %sub93, %while.body92 ], [ 2, %while.body83 ]
  %tobool91 = icmp ne i32 %i.5, 0
  br i1 %tobool91, label %while.body92, label %do.body

while.body92:                                     ; preds = %while.cond90
  %sub93 = sub nsw i32 %i.5, 1
  br label %while.cond90, !llvm.loop !8

do.body:                                          ; preds = %while.cond90, %do.body
  %i.6 = phi i32 [ %sub99, %do.body ], [ 2, %while.cond90 ]
  %sub99 = sub nsw i32 %i.6, 1
  %tobool100 = icmp ne i32 %sub99, 0
  br i1 %tobool100, label %do.body, label %if.end104, !llvm.loop !9

if.end104:                                        ; preds = %do.body
  ret i32 %sub99
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}





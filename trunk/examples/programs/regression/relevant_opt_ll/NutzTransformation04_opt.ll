; #Safe
; ModuleID = 'output_folder/NutzTransformation04.ll'
source_filename = "c5/NutzTransformation04.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %conv = zext i16 0 to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %tobool = icmp ne i16 0, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  %cmp = icmp eq i32 %lnot.ext, 1
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %conv2 = zext i16 0 to i32
  %tobool3 = icmp ne i32 %conv2, 0
  %spec.select = select i1 %tobool3, i1 true, i1 false
  %land.ext = zext i1 %spec.select to i32
  %cmp4 = icmp eq i32 %land.ext, 0
  br i1 %cmp4, label %if.end8, label %if.else7

if.else7:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 24, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end8:                                          ; preds = %if.end
  %conv9 = zext i16 0 to i32
  %tobool10 = icmp ne i32 %conv9, 0
  %spec.select9 = select i1 %tobool10, i1 true, i1 false
  %lor.ext = zext i1 %spec.select9 to i32
  %cmp11 = icmp eq i32 %lor.ext, 0
  br i1 %cmp11, label %if.end15, label %if.else14

if.else14:                                        ; preds = %if.end8
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end15:                                         ; preds = %if.end8
  %conv16 = zext i16 0 to i32
  %tobool17 = icmp ne i32 %conv16, 0
  %0 = zext i1 %tobool17 to i64
  %cond = select i1 %tobool17, i32 5, i32 17
  %cmp18 = icmp eq i32 %cond, 17
  br i1 %cmp18, label %if.end22, label %if.else21

if.else21:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end22:                                         ; preds = %if.end15
  %tobool23 = icmp ne i16 0, 0
  br i1 %tobool23, label %if.then24, label %do.body

if.then24:                                        ; preds = %if.end22
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

do.body:                                          ; preds = %if.end22, %do.body
  %i.0 = phi i32 [ %inc, %do.body ], [ 0, %if.end22 ]
  %inc = add nsw i32 %i.0, 1
  %tobool27 = icmp ne i16 0, 0
  br i1 %tobool27, label %do.body, label %do.end, !llvm.loop !6

do.end:                                           ; preds = %do.body
  %cmp28 = icmp eq i32 %inc, 1
  br i1 %cmp28, label %if.end32, label %if.else31

if.else31:                                        ; preds = %do.end
  call void @__assert_fail(ptr noundef @.str.7, ptr noundef @.str.2, i32 noundef 44, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end32:                                         ; preds = %do.end
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
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





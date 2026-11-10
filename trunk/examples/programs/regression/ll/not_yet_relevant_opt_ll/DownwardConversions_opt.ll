; #Unsafe
; ModuleID = 'output_folder/DownwardConversions.ll'
source_filename = "c5/DownwardConversions.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  br label %while.cond

while.cond:                                       ; preds = %while.cond, %entry
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %while.cond, label %while.cond1, !llvm.loop !6

while.cond1:                                      ; preds = %while.cond1, %while.cond
  %call2 = call i32 @__VERIFIER_nondet_int()
  %tobool3 = icmp ne i32 %call2, 0
  br i1 %tobool3, label %while.cond1, label %while.cond6, !llvm.loop !8

while.cond6:                                      ; preds = %while.cond6, %while.cond1
  %call7 = call i32 @__VERIFIER_nondet_int()
  %tobool8 = icmp ne i32 %call7, 0
  br i1 %tobool8, label %while.cond6, label %while.end10, !llvm.loop !9

while.end10:                                      ; preds = %while.cond6
  %conv = trunc i64 -1 to i32
  br label %while.cond11

while.cond11:                                     ; preds = %while.cond11, %while.end10
  %call12 = call i32 @__VERIFIER_nondet_int()
  %tobool13 = icmp ne i32 %call12, 0
  br i1 %tobool13, label %while.cond11, label %while.end15, !llvm.loop !10

while.end15:                                      ; preds = %while.cond11
  %conv16 = trunc i32 %conv to i16
  br label %while.cond17

while.cond17:                                     ; preds = %while.cond17, %while.end15
  %call18 = call i32 @__VERIFIER_nondet_int()
  %tobool19 = icmp ne i32 %call18, 0
  br i1 %tobool19, label %while.cond17, label %while.end21, !llvm.loop !11

while.end21:                                      ; preds = %while.cond17
  %conv22 = trunc i16 %conv16 to i8
  br label %while.cond23

while.cond23:                                     ; preds = %while.cond23, %while.end21
  %call24 = call i32 @__VERIFIER_nondet_int()
  %tobool25 = icmp ne i32 %call24, 0
  br i1 %tobool25, label %while.cond23, label %while.end27, !llvm.loop !12

while.end27:                                      ; preds = %while.cond23
  %tobool28 = icmp ne i8 %conv22, 0
  %frombool = zext i1 %tobool28 to i8
  %tobool29 = trunc i8 %frombool to i1
  br i1 %tobool29, label %if.then, label %if.end

if.then:                                          ; preds = %while.end27
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 46, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %while.end27
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #0

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
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}
!10 = distinct !{!10, !7}
!11 = distinct !{!11, !7}
!12 = distinct !{!12, !7}





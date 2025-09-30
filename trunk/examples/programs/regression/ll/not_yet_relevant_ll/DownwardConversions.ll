; #Unsafe
; ModuleID = 'c5/DownwardConversions.c'
source_filename = "c5/DownwardConversions.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i64, align 8
  %b = alloca i64, align 8
  %c = alloca i64, align 8
  %d = alloca i32, align 4
  %e = alloca i16, align 2
  %f = alloca i8, align 1
  %g = alloca i8, align 1
  store i32 0, ptr %retval, align 4
  store i64 -1, ptr %a, align 8
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %0 = load i64, ptr %a, align 8
  store i64 %0, ptr %b, align 8
  br label %while.cond1

while.cond1:                                      ; preds = %while.body4, %while.end
  %call2 = call i32 @__VERIFIER_nondet_int()
  %tobool3 = icmp ne i32 %call2, 0
  br i1 %tobool3, label %while.body4, label %while.end5

while.body4:                                      ; preds = %while.cond1
  br label %while.cond1, !llvm.loop !8

while.end5:                                       ; preds = %while.cond1
  %1 = load i64, ptr %b, align 8
  store i64 %1, ptr %c, align 8
  br label %while.cond6

while.cond6:                                      ; preds = %while.body9, %while.end5
  %call7 = call i32 @__VERIFIER_nondet_int()
  %tobool8 = icmp ne i32 %call7, 0
  br i1 %tobool8, label %while.body9, label %while.end10

while.body9:                                      ; preds = %while.cond6
  br label %while.cond6, !llvm.loop !9

while.end10:                                      ; preds = %while.cond6
  %2 = load i64, ptr %c, align 8
  %conv = trunc i64 %2 to i32
  store i32 %conv, ptr %d, align 4
  br label %while.cond11

while.cond11:                                     ; preds = %while.body14, %while.end10
  %call12 = call i32 @__VERIFIER_nondet_int()
  %tobool13 = icmp ne i32 %call12, 0
  br i1 %tobool13, label %while.body14, label %while.end15

while.body14:                                     ; preds = %while.cond11
  br label %while.cond11, !llvm.loop !10

while.end15:                                      ; preds = %while.cond11
  %3 = load i32, ptr %d, align 4
  %conv16 = trunc i32 %3 to i16
  store i16 %conv16, ptr %e, align 2
  br label %while.cond17

while.cond17:                                     ; preds = %while.body20, %while.end15
  %call18 = call i32 @__VERIFIER_nondet_int()
  %tobool19 = icmp ne i32 %call18, 0
  br i1 %tobool19, label %while.body20, label %while.end21

while.body20:                                     ; preds = %while.cond17
  br label %while.cond17, !llvm.loop !11

while.end21:                                      ; preds = %while.cond17
  %4 = load i16, ptr %e, align 2
  %conv22 = trunc i16 %4 to i8
  store i8 %conv22, ptr %f, align 1
  br label %while.cond23

while.cond23:                                     ; preds = %while.body26, %while.end21
  %call24 = call i32 @__VERIFIER_nondet_int()
  %tobool25 = icmp ne i32 %call24, 0
  br i1 %tobool25, label %while.body26, label %while.end27

while.body26:                                     ; preds = %while.cond23
  br label %while.cond23, !llvm.loop !12

while.end27:                                      ; preds = %while.cond23
  %5 = load i8, ptr %f, align 1
  %tobool28 = icmp ne i8 %5, 0
  %frombool = zext i1 %tobool28 to i8
  store i8 %frombool, ptr %g, align 1
  %6 = load i8, ptr %g, align 1
  %tobool29 = trunc i8 %6 to i1
  br i1 %tobool29, label %if.then, label %if.end

if.then:                                          ; preds = %while.end27
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 46, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %while.end27
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
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





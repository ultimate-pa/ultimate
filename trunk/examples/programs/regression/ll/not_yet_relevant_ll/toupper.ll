; #Safe
; ModuleID = 'c5/toupper.c'
source_filename = "c5/toupper.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i8 @__VERIFIER_nondet_uchar()
  %conv = zext i8 %call to i32
  store i32 %conv, ptr %x, align 4
  %0 = load i32, ptr %x, align 4
  %call1 = call i32 @toupper(i32 noundef %0) #4
  store i32 %call1, ptr %y, align 4
  %1 = load i32, ptr %x, align 4
  %cmp = icmp sge i32 %1, 97
  br i1 %cmp, label %land.lhs.true, label %if.else8

land.lhs.true:                                    ; preds = %entry
  %2 = load i32, ptr %x, align 4
  %cmp3 = icmp sle i32 %2, 122
  br i1 %cmp3, label %if.then, label %if.else8

if.then:                                          ; preds = %land.lhs.true
  %3 = load i32, ptr %y, align 4
  %add = add nsw i32 %3, 32
  %4 = load i32, ptr %x, align 4
  %cmp5 = icmp eq i32 %add, %4
  br i1 %cmp5, label %if.then7, label %if.else

if.then7:                                         ; preds = %if.then
  br label %if.end

if.else:                                          ; preds = %if.then
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #5
  unreachable

if.end:                                           ; preds = %if.then7
  br label %if.end14

if.else8:                                         ; preds = %land.lhs.true, %entry
  %5 = load i32, ptr %x, align 4
  %6 = load i32, ptr %y, align 4
  %cmp9 = icmp eq i32 %5, %6
  br i1 %cmp9, label %if.then11, label %if.else12

if.then11:                                        ; preds = %if.else8
  br label %if.end13

if.else12:                                        ; preds = %if.else8
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #5
  unreachable

if.end13:                                         ; preds = %if.then11
  br label %if.end14

if.end14:                                         ; preds = %if.end13, %if.end
  %7 = load i32, ptr %retval, align 4
  ret i32 %7
}

declare i8 @__VERIFIER_nondet_uchar() #1

; Function Attrs: nounwind willreturn memory(read)
declare i32 @toupper(i32 noundef) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #3
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Safe
; ModuleID = 'c5/array10_pattern_simplified.c'
source_filename = "c5/array10_pattern_simplified.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@ARR_SIZE = dso_local global i64 0, align 8

define dso_local void @reach_error() #0 {
entry:
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 28, ptr noundef @.str.2) #4
  unreachable
}

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

define dso_local void @assume_abort_if_not(i32 noundef %cond) #0 {
entry:
  %cond.addr = alloca i32, align 4
  store i32 %cond, ptr %cond.addr, align 4
  %0 = load i32, ptr %cond.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  call void @abort() #5
  unreachable

if.end:                                           ; preds = %entry
  ret void
}

; Function Attrs: noreturn
declare void @abort() #2

define dso_local void @__VERIFIER_assert(i32 noundef %cond) #0 {
entry:
  %cond.addr = alloca i32, align 4
  store i32 %cond, ptr %cond.addr, align 4
  %0 = load i32, ptr %cond.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  br label %ERROR

ERROR:                                            ; preds = %if.then
  call void @reach_error()
  call void @abort() #5
  unreachable

if.end:                                           ; preds = %entry
  ret void
}

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %count = alloca i32, align 4
  %sum = alloca i64, align 8
  store i32 0, ptr %retval, align 4
  %call = call i16 @__VERIFIER_nondet_short()
  %conv = sext i16 %call to i64
  store i64 %conv, ptr @ARR_SIZE, align 8
  %0 = load i64, ptr @ARR_SIZE, align 8
  %cmp = icmp sgt i64 %0, 0
  %conv1 = zext i1 %cmp to i32
  call void @assume_abort_if_not(i32 noundef %conv1)
  store i32 0, ptr %x, align 4
  store i32 0, ptr %count, align 4
  store i64 0, ptr %sum, align 8
  store i32 0, ptr %count, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %1 = load i32, ptr %count, align 4
  %conv2 = sext i32 %1 to i64
  %2 = load i64, ptr @ARR_SIZE, align 8
  %cmp3 = icmp slt i64 %conv2, %2
  br i1 %cmp3, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %3 = load i64, ptr %sum, align 8
  %4 = load i32, ptr %x, align 4
  %conv5 = sext i32 %4 to i64
  %add = add nsw i64 %3, %conv5
  store i64 %add, ptr %sum, align 8
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %5 = load i32, ptr %count, align 4
  %inc = add nsw i32 %5, 1
  store i32 %inc, ptr %count, align 4
  br label %for.cond, !llvm.loop !6

for.end:                                          ; preds = %for.cond
  %6 = load i64, ptr %sum, align 8
  %7 = load i64, ptr @ARR_SIZE, align 8
  %sub = sub nsw i64 %7, 1
  %8 = load i64, ptr @ARR_SIZE, align 8
  %add6 = add nsw i64 %8, 1
  %mul = mul nsw i64 %sub, %add6
  %cmp7 = icmp sle i64 %6, %mul
  %conv8 = zext i1 %cmp7 to i32
  call void @__VERIFIER_assert(i32 noundef %conv8)
  ret i32 0
}

declare i16 @__VERIFIER_nondet_short(...) #3
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





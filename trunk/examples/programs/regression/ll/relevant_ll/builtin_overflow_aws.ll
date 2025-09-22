; #Safe
; ModuleID = 'c5/builtin_overflow_aws.c'
source_filename = "c5/builtin_overflow_aws.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i64, align 8
  %b = alloca i64, align 8
  %r = alloca i64, align 8
  store i32 0, ptr %retval, align 4
  %call = call i64 @__VERIFIER_nondet_ulonglong()
  store i64 %call, ptr %a, align 8
  %call1 = call i64 @__VERIFIER_nondet_ulonglong()
  store i64 %call1, ptr %b, align 8
  %0 = load i64, ptr %a, align 8
  %1 = load i64, ptr %b, align 8
  %2 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %0, i64 %1)
  %3 = extractvalue { i64, i1 } %2, 1
  %4 = extractvalue { i64, i1 } %2, 0
  store i64 %4, ptr %r, align 8
  br i1 %3, label %if.else3, label %if.then

if.then:                                          ; preds = %entry
  %5 = load i64, ptr %r, align 8
  %6 = load i64, ptr %a, align 8
  %7 = load i64, ptr %b, align 8
  %add = add i64 %6, %7
  %cmp = icmp eq i64 %5, %add
  br i1 %cmp, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.then
  br label %if.end

if.else:                                          ; preds = %if.then
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end:                                           ; preds = %if.then2
  br label %if.end9

if.else3:                                         ; preds = %entry
  %8 = load i64, ptr %b, align 8
  %cmp4 = icmp ugt i64 %8, 0
  br i1 %cmp4, label %land.lhs.true, label %if.else7

land.lhs.true:                                    ; preds = %if.else3
  %9 = load i64, ptr %a, align 8
  %10 = load i64, ptr %b, align 8
  %sub = sub i64 -1, %10
  %cmp5 = icmp ugt i64 %9, %sub
  br i1 %cmp5, label %if.then6, label %if.else7

if.then6:                                         ; preds = %land.lhs.true
  br label %if.end8

if.else7:                                         ; preds = %land.lhs.true, %if.else3
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 20, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end8:                                          ; preds = %if.then6
  br label %if.end9

if.end9:                                          ; preds = %if.end8, %if.end
  %11 = load i32, ptr %retval, align 4
  ret i32 %11
}

declare i64 @__VERIFIER_nondet_ulonglong(...) #1

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #3
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





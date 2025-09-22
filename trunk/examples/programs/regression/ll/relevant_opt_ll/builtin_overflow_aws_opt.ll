; #Safe
; ModuleID = 'output_folder/builtin_overflow_aws.ll'
source_filename = "c5/builtin_overflow_aws.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i64 @__VERIFIER_nondet_ulonglong()
  %call1 = call i64 @__VERIFIER_nondet_ulonglong()
  %0 = call { i64, i1 } @llvm.uadd.with.overflow.i64(i64 %call, i64 %call1)
  %1 = extractvalue { i64, i1 } %0, 1
  %2 = extractvalue { i64, i1 } %0, 0
  br i1 %1, label %if.else3, label %if.then

if.then:                                          ; preds = %entry
  %add = add i64 %call, %call1
  %cmp = icmp eq i64 %2, %add
  br i1 %cmp, label %if.end9, label %if.else

if.else:                                          ; preds = %if.then
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.else3:                                         ; preds = %entry
  %cmp4 = icmp ugt i64 %call1, 0
  %sub = sub i64 -1, %call1
  %cmp5 = icmp ugt i64 %call, %sub
  %or.cond = select i1 %cmp4, i1 %cmp5, i1 false
  br i1 %or.cond, label %if.end9, label %if.else7

if.else7:                                         ; preds = %if.else3
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 20, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end9:                                          ; preds = %if.else3, %if.then
  ret i32 0
}

declare i64 @__VERIFIER_nondet_ulonglong(...) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.uadd.with.overflow.i64(i64, i64) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





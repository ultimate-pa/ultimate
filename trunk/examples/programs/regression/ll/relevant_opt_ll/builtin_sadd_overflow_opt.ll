; #Safe
; ModuleID = 'output_folder/builtin_sadd_overflow.ll'
source_filename = "c5/builtin_sadd_overflow.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_int()
  %cmp = icmp slt i32 %call, 2
  br i1 %cmp, label %if.end2, label %if.end

if.end:                                           ; preds = %entry
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 2147483647, i32 %call)
  %1 = extractvalue { i32, i1 } %0, 1
  %2 = extractvalue { i32, i1 } %0, 0
  %frombool = zext i1 %1 to i8
  %tobool = trunc i8 %frombool to i1
  br i1 %tobool, label %if.end2, label %if.else

if.else:                                          ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end2:                                          ; preds = %if.end, %entry
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Safe
; ModuleID = 'output_folder/builtin_sadd_overflow2.ll'
source_filename = "c5/builtin_sadd_overflow2.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i16 @__VERIFIER_nondet_short()
  %conv = sext i16 %call to i32
  %call1 = call i16 @__VERIFIER_nondet_short()
  %conv2 = sext i16 %call1 to i32
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %conv, i32 %conv2)
  %1 = extractvalue { i32, i1 } %0, 1
  %2 = extractvalue { i32, i1 } %0, 0
  %frombool = zext i1 %1 to i8
  %tobool = trunc i8 %frombool to i1
  br i1 %tobool, label %if.else, label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  %add = add nsw i32 %conv, %conv2
  %cmp = icmp eq i32 %2, %add
  br i1 %cmp, label %if.end6, label %if.else5

if.else5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end6:                                          ; preds = %if.end
  ret i32 0
}

declare i16 @__VERIFIER_nondet_short(...) #0

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





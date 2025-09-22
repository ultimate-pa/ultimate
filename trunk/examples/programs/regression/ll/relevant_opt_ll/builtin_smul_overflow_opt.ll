; #Safe
; ModuleID = 'output_folder/builtin_smul_overflow.ll'
source_filename = "c5/builtin_smul_overflow.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %0 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 -2147483647, i32 3)
  %1 = extractvalue { i32, i1 } %0, 1
  %2 = extractvalue { i32, i1 } %0, 0
  %cmp = icmp eq i32 %2, -2147483645
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  %3 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 -2147483647, i32 6)
  %4 = extractvalue { i32, i1 } %3, 1
  %5 = extractvalue { i32, i1 } %3, 0
  %cmp1 = icmp eq i32 %5, 6
  br i1 %cmp1, label %if.end4, label %if.else3

if.else3:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end4:                                          ; preds = %if.end
  ret i32 0
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





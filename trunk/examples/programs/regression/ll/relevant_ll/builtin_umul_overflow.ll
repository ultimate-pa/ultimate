; #Safe
; ModuleID = 'c5/builtin_umul_overflow.c'
source_filename = "c5/builtin_umul_overflow.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %r = alloca i32, align 4
  %overflow = alloca i8, align 1
  %0 = call { i32, i1 } @llvm.umul.with.overflow.i32(i32 2147483647, i32 3)
  %1 = extractvalue { i32, i1 } %0, 1
  %2 = extractvalue { i32, i1 } %0, 0
  store i32 %2, ptr %r, align 4
  %frombool = zext i1 %1 to i8
  store i8 %frombool, ptr %overflow, align 1
  %3 = load i8, ptr %overflow, align 1
  %tobool = trunc i8 %3 to i1
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  %4 = load i32, ptr %r, align 4
  %cmp = icmp eq i32 %4, 2147483645
  br i1 %cmp, label %if.then1, label %if.else2

if.then1:                                         ; preds = %if.end
  br label %if.end3

if.else2:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end3:                                          ; preds = %if.then1
  ret i32 0
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.umul.with.overflow.i32(i32, i32) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





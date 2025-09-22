; #Safe
; ModuleID = 'c5/builtin_sadd_overflow2.c'
source_filename = "c5/builtin_sadd_overflow2.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %r = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %overflow = alloca i8, align 1
  %call = call i16 @__VERIFIER_nondet_short()
  %conv = sext i16 %call to i32
  store i32 %conv, ptr %x, align 4
  %call1 = call i16 @__VERIFIER_nondet_short()
  %conv2 = sext i16 %call1 to i32
  store i32 %conv2, ptr %y, align 4
  %0 = load i32, ptr %x, align 4
  %1 = load i32, ptr %y, align 4
  %2 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %0, i32 %1)
  %3 = extractvalue { i32, i1 } %2, 1
  %4 = extractvalue { i32, i1 } %2, 0
  store i32 %4, ptr %r, align 4
  %frombool = zext i1 %3 to i8
  store i8 %frombool, ptr %overflow, align 1
  %5 = load i8, ptr %overflow, align 1
  %tobool = trunc i8 %5 to i1
  br i1 %tobool, label %if.else, label %if.then

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end:                                           ; preds = %if.then
  %6 = load i32, ptr %r, align 4
  %7 = load i32, ptr %x, align 4
  %8 = load i32, ptr %y, align 4
  %add = add nsw i32 %7, %8
  %cmp = icmp eq i32 %6, %add
  br i1 %cmp, label %if.then4, label %if.else5

if.then4:                                         ; preds = %if.end
  br label %if.end6

if.else5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end6:                                          ; preds = %if.then4
  ret i32 0
}

declare i16 @__VERIFIER_nondet_short(...) #1

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #2

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #3
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





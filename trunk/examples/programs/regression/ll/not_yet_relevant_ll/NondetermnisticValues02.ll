; #Safe
; ModuleID = 'c5/NondetermnisticValues02.c'
source_filename = "c5/NondetermnisticValues02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i16, align 2
  %b = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i16 @someMethodThatReturnsASignedShort()
  store i16 %call, ptr %a, align 2
  %0 = load i16, ptr %a, align 2
  %conv = sext i16 %0 to i32
  store i32 %conv, ptr %b, align 4
  %1 = load i32, ptr %b, align 4
  %cmp = icmp sgt i32 %1, 32767
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

declare i16 @someMethodThatReturnsASignedShort(...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





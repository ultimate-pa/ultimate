; #Safe
; ModuleID = './bitwisePointerRead.c'
source_filename = "./bitwisePointerRead.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %r = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %p = alloca ptr, align 8
  store i32 0, ptr %retval, align 4
  store ptr %x, ptr %p, align 8
  %0 = load i32, ptr %y, align 4
  %cmp = icmp slt i32 %0, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %if.end3

if.end:                                           ; preds = %entry
  %1 = load i32, ptr %x, align 4
  %2 = load i32, ptr %y, align 4
  %and = and i32 %1, %2
  store i32 %and, ptr %r, align 4
  %3 = load i32, ptr %r, align 4
  %cmp1 = icmp sge i32 %3, 0
  br i1 %cmp1, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.end
  br label %if.end3

if.else:                                          ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end3:                                          ; preds = %if.then, %if.then2
  %4 = load i32, ptr %retval, align 4
  ret i32 %4
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





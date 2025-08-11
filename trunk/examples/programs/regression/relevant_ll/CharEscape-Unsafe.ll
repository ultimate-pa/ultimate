; ModuleID = 'erw/CharEscape-Unsafe.c'
source_filename = "erw/CharEscape-Unsafe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %c1 = alloca i8, align 1
  %c2 = alloca i8, align 1
  store i32 0, ptr %retval, align 4
  store i8 0, ptr %c1, align 1
  store i8 48, ptr %c2, align 1
  %0 = load i8, ptr %c1, align 1
  %conv = zext i8 %0 to i32
  %1 = load i8, ptr %c2, align 1
  %conv1 = zext i8 %1 to i32
  %cmp = icmp eq i32 %conv, %conv1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





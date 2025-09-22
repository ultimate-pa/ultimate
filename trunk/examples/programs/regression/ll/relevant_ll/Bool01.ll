; #Unsafe
; ModuleID = 'c5/Bool01.c'
source_filename = "c5/Bool01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %x = alloca i8, align 1
  store i8 0, ptr %x, align 1
  %0 = load i8, ptr %x, align 1
  %tobool = trunc i8 %0 to i1
  %conv = zext i1 %tobool to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %1 = load i8, ptr %x, align 1
  %tobool1 = trunc i8 %1 to i1
  store i8 1, ptr %x, align 1
  %2 = load i8, ptr %x, align 1
  %tobool2 = trunc i8 %2 to i1
  %conv3 = zext i1 %tobool2 to i32
  %call4 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv3)
  %3 = load i8, ptr %x, align 1
  %tobool5 = trunc i8 %3 to i1
  store i8 1, ptr %x, align 1
  %4 = load i8, ptr %x, align 1
  %tobool6 = trunc i8 %4 to i1
  %conv7 = zext i1 %tobool6 to i32
  %call8 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv7)
  %5 = load i8, ptr %x, align 1
  %tobool9 = trunc i8 %5 to i1
  %conv10 = zext i1 %tobool9 to i32
  %cmp = icmp eq i32 %conv10, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





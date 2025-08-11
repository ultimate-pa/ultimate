; #Safe
; ModuleID = 'c5/UnicodeCharacters.c'
source_filename = "c5/UnicodeCharacters.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %c16 = alloca i16, align 2
  %c32 = alloca i32, align 4
  store i16 246, ptr %c16, align 2
  %0 = load i16, ptr %c16, align 2
  %conv = zext i16 %0 to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %1 = load i16, ptr %c16, align 2
  %conv1 = zext i16 %1 to i32
  %cmp = icmp ne i32 %conv1, 246
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 21, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  store i32 1114111, ptr %c32, align 4
  %2 = load i32, ptr %c32, align 4
  %cmp3 = icmp ne i32 %2, 1114111
  br i1 %cmp3, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end6:                                          ; preds = %if.end
  %3 = load i32, ptr %c32, align 4
  %call7 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %3)
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





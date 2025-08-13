; #Safe
; ModuleID = 'output_folder/NestedDeclarators.ll'
source_filename = "c5/NestedDeclarators.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@g = dso_local global i32 0, align 4

define dso_local i32 @main() {
entry:
  %0 = load i32, ptr @g, align 4
  %call = call i32 @increase(i32 noundef %0)
  store i32 %call, ptr @g, align 4
  %1 = load i32, ptr @g, align 4
  %sub = sub nsw i32 %1, 1
  %cmp = icmp eq i32 %0, %sub
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

define dso_local i32 @increase(i32 noundef %a) {
entry:
  %inc = add nsw i32 %a, 1
  ret i32 %inc
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





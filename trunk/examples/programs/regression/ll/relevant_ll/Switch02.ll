; #Safe
; ModuleID = 'erw/Switch02.c'
source_filename = "erw/Switch02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %x = alloca i64, align 8
  store i64 4294967296, ptr %x, align 8
  %0 = load i64, ptr %x, align 8
  switch i64 %0, label %sw.default [
    i64 0, label %sw.bb
  ]

sw.bb:                                            ; preds = %entry
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str)
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 19, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

sw.default:                                       ; preds = %entry
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str.3)
  br label %sw.epilog

sw.epilog:                                        ; preds = %sw.default
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





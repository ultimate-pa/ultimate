; #Safe
; ModuleID = 'erw/Enums02-Safe.c'
source_filename = "erw/Enums02-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@var = dso_local global i32 0, align 4

define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  store i32 21, ptr %x, align 4
  %0 = load i32, ptr %x, align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %0)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





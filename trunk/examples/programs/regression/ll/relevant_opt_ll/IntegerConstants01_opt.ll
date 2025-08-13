; #Safe
; ModuleID = 'output_folder/IntegerConstants01.ll'
source_filename = "erw/IntegerConstants01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call2 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call3 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call4 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call5 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  %call6 = call i32 (ptr, ...) @printf(ptr noundef @.str)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





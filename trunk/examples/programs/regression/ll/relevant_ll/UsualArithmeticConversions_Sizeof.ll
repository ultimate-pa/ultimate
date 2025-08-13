; #Safe
; ModuleID = 'erw/UsualArithmeticConversions_Sizeof.c'
source_filename = "erw/UsualArithmeticConversions_Sizeof.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %schar = alloca i8, align 1
  %sshort = alloca i16, align 2
  %sint = alloca i32, align 4
  %uint = alloca i32, align 4
  %slong = alloca i64, align 8
  %slonglong = alloca i64, align 8
  store i32 0, ptr %retval, align 4
  store i8 1, ptr %schar, align 1
  store i16 1, ptr %sshort, align 2
  store i32 1, ptr %sint, align 4
  store i32 1, ptr %uint, align 4
  store i64 1, ptr %slong, align 8
  store i64 1, ptr %slonglong, align 8
  ret i32 0
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Unsafe
; ModuleID = 'output_folder/LineDirective01.ll'
source_filename = "c5/LineDirective01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error() #2
  unreachable

if.else:                                          ; preds = %entry
  call void @__VERIFIER_error() #2
  unreachable
}

declare i32 @__VERIFIER_nondet_int(...) #0

; Function Attrs: noreturn
declare void @__VERIFIER_error(...) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





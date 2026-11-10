; #Safe
; ModuleID = 'output_folder/boolean_bitwise.ll'
source_filename = "./boolean_bitwise.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_int()
  %call1 = call i32 @__VERIFIER_nondet_int()
  %cmp = icmp eq i32 %call, 0
  %conv = zext i1 %cmp to i32
  %cmp2 = icmp eq i32 %call1, 0
  %conv3 = zext i1 %cmp2 to i32
  %and = and i32 %conv, %conv3
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %return, label %if.end

if.end:                                           ; preds = %entry
  %cmp4 = icmp ne i32 %call, 0
  %conv5 = zext i1 %cmp4 to i32
  %cmp6 = icmp ne i32 %call1, 0
  %conv7 = zext i1 %cmp6 to i32
  %or = or i32 %conv5, %conv7
  %tobool8 = icmp ne i32 %or, 0
  br i1 %tobool8, label %return, label %if.end10

if.end10:                                         ; preds = %if.end
  %call11 = call i32 @reach_error()
  br label %return

return:                                           ; preds = %if.end, %entry, %if.end10
  ret i32 0
}

declare i32 @__VERIFIER_nondet_int(...) #0

declare i32 @reach_error(...) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





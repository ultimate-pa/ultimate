; #Safe
; ModuleID = './boolean_bitwise.c'
source_filename = "./boolean_bitwise.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i32 @__VERIFIER_nondet_int()
  store i32 %call, ptr %x, align 4
  %call1 = call i32 @__VERIFIER_nondet_int()
  store i32 %call1, ptr %y, align 4
  %0 = load i32, ptr %x, align 4
  %cmp = icmp eq i32 %0, 0
  %conv = zext i1 %cmp to i32
  %1 = load i32, ptr %y, align 4
  %cmp2 = icmp eq i32 %1, 0
  %conv3 = zext i1 %cmp2 to i32
  %and = and i32 %conv, %conv3
  %tobool = icmp ne i32 %and, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  br label %return

if.end:                                           ; preds = %entry
  %2 = load i32, ptr %x, align 4
  %cmp4 = icmp ne i32 %2, 0
  %conv5 = zext i1 %cmp4 to i32
  %3 = load i32, ptr %y, align 4
  %cmp6 = icmp ne i32 %3, 0
  %conv7 = zext i1 %cmp6 to i32
  %or = or i32 %conv5, %conv7
  %tobool8 = icmp ne i32 %or, 0
  br i1 %tobool8, label %if.then9, label %if.end10

if.then9:                                         ; preds = %if.end
  br label %return

if.end10:                                         ; preds = %if.end
  %call11 = call i32 @reach_error()
  br label %return

return:                                           ; preds = %if.end10, %if.then9, %if.then
  %4 = load i32, ptr %retval, align 4
  ret i32 %4
}

declare i32 @__VERIFIER_nondet_int(...) #1

declare i32 @reach_error(...) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





;#Safe
; ModuleID = 'Bitvector-Safe.c'
source_filename = "Bitvector-Safe.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %call = call i32 (...) @__VERIFIER_nondet_int()
  store i32 %call, ptr %i, align 4
  %0 = load i32, ptr %i, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  store i32 0, ptr %i, align 4
  br label %if.end

if.else:                                          ; preds = %entry
  store i32 0, ptr %i, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %1 = load i32, ptr %i, align 4
  %cmp = icmp ne i32 %1, 0
  br i1 %cmp, label %if.then1, label %if.end2

if.then1:                                         ; preds = %if.end
  br label %if.end2

if.end2:                                          ; preds = %if.then1, %if.end
  %2 = load i32, ptr %retval, align 4
  ret i32 %2
}

declare i32 @__VERIFIER_nondet_int(...) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Ubuntu clang version 19.1.7 (++20250114103332+cd708029e0b2-1~exp1~20250114103446.78)"}





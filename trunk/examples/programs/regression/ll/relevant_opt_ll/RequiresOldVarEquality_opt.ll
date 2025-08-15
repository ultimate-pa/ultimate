; #Safe
; ModuleID = 'output_folder/RequiresOldVarEquality.ll'
source_filename = "c5/RequiresOldVarEquality.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@g = dso_local global i32 0, align 4

define dso_local void @main() {
entry:
  %0 = load i32, ptr @g, align 4
  %inc = add nsw i32 %0, 1
  store i32 %inc, ptr @g, align 4
  br label %while.cond

while.cond:                                       ; preds = %if.end, %entry
  %call = call i8 @__VERIFIER_nondet_char()
  %tobool = icmp ne i8 %call, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %1 = load i32, ptr @g, align 4
  %cmp = icmp slt i32 %1, 2147483647
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %while.body
  %2 = load i32, ptr @g, align 4
  %inc1 = add nsw i32 %2, 1
  store i32 %inc1, ptr @g, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %while.body
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  ret void
}

declare i8 @__VERIFIER_nondet_char(...) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





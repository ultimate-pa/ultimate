; #Safe
; ModuleID = 'output_folder/ShortCircuit-SideEffect-IfStatement-Safe.ll'
source_filename = "c5/ShortCircuit-SideEffect-IfStatement-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %inc = add nsw i32 1, 1
  %cmp = icmp eq i32 1, 0
  br i1 %cmp, label %while.cond, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %inc1 = add nsw i32 1, 1
  br label %while.cond4

while.cond:                                       ; preds = %while.cond, %entry
  %tobool = icmp ne i32 undef, 0
  br i1 %tobool, label %while.cond, label %if.end, !llvm.loop !6

while.cond4:                                      ; preds = %while.cond4, %lor.lhs.false
  %tobool5 = icmp ne i32 undef, 0
  br i1 %tobool5, label %while.cond4, label %if.end, !llvm.loop !8

if.end:                                           ; preds = %while.cond4, %while.cond
  %z.0 = phi i8 [ 1, %while.cond ], [ 0, %while.cond4 ]
  %y.1 = phi i32 [ 1, %while.cond ], [ %inc1, %while.cond4 ]
  %cmp9 = icmp eq i32 %inc, 2
  %cmp10 = icmp eq i32 %y.1, 2
  %or.cond = select i1 %cmp9, i1 %cmp10, i1 false
  %tobool12 = trunc i8 %z.0 to i1
  %conv = zext i1 %tobool12 to i32
  %cmp13 = icmp eq i32 %conv, 0
  %or.cond3 = and i1 %or.cond, %cmp13
  br i1 %or.cond3, label %if.end17, label %if.else16

if.else16:                                        ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 18, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end17:                                         ; preds = %if.end
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0

attributes #0 = { noreturn nounwind "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+fp-armv8,+neon,+outline-atomics,+v8a,-fmv" }
attributes #1 = { noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}

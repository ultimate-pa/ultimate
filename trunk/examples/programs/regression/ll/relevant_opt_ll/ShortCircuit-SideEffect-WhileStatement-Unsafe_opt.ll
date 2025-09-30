; #Unsafe
; ModuleID = 'output_folder/ShortCircuit-SideEffect-WhileStatement-Unsafe.ll'
source_filename = "c5/ShortCircuit-SideEffect-WhileStatement-Unsafe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  br label %while.cond

while.cond:                                       ; preds = %while.end, %entry
  %y.0 = phi i32 [ 1, %entry ], [ %y.1, %while.end ]
  %x.0 = phi i32 [ 1, %entry ], [ %inc, %while.end ]
  %inc = add nsw i32 %x.0, 1
  %cmp = icmp eq i32 %x.0, 0
  %inc1 = add nsw i32 %y.0, 1
  %cmp2 = icmp eq i32 %y.0, 0
  %y.1 = select i1 %cmp, i32 %inc1, i32 %y.0
  %0 = select i1 %cmp, i1 %cmp2, i1 false
  br i1 %0, label %while.cond3, label %while.cond7

while.cond3:                                      ; preds = %while.cond3, %while.cond
  %tobool = icmp ne i32 undef, 0
  br i1 %tobool, label %while.cond3, label %while.end, !llvm.loop !6

while.end:                                        ; preds = %while.cond3
  br label %while.cond, !llvm.loop !8

while.cond7:                                      ; preds = %while.cond7, %while.cond
  %tobool8 = icmp ne i32 undef, 0
  br i1 %tobool8, label %while.cond7, label %while.end11, !llvm.loop !9

while.end11:                                      ; preds = %while.cond7
  %cmp12 = icmp sge i32 %y.1, 2
  br i1 %cmp12, label %if.end, label %if.else

if.else:                                          ; preds = %while.end11
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %while.end11
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
!9 = distinct !{!9, !7}

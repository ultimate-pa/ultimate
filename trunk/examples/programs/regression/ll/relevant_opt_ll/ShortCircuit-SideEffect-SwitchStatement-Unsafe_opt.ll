; #Unsafe
; ModuleID = 'output_folder/ShortCircuit-SideEffect-SwitchStatement-Unsafe.ll'
source_filename = "c5/ShortCircuit-SideEffect-SwitchStatement-Unsafe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %inc = add nsw i32 1, 1
  %cmp = icmp ne i32 1, 0
  %inc1 = add nsw i32 1, 1
  %cmp2 = icmp eq i32 1, 0
  %y.0 = select i1 %cmp, i32 1, i32 %inc1
  %0 = select i1 %cmp, i1 true, i1 %cmp2
  %lor.ext = zext i1 %0 to i32
  switch i32 %lor.ext, label %entry.unreachabledefault [
    i32 0, label %while.cond
    i32 1, label %while.cond4
  ]

while.cond:                                       ; preds = %while.cond, %entry
  %tobool = icmp ne i32 undef, 0
  br i1 %tobool, label %while.cond, label %sw.epilog, !llvm.loop !6

while.cond4:                                      ; preds = %while.cond4, %entry
  %tobool5 = icmp ne i32 undef, 0
  br i1 %tobool5, label %while.cond4, label %sw.epilog, !llvm.loop !8

entry.unreachabledefault:                         ; preds = %entry
  unreachable

sw.epilog:                                        ; preds = %while.cond4, %while.cond
  %cmp14 = icmp eq i32 %y.0, 2
  br i1 %cmp14, label %if.end, label %if.else

if.else:                                          ; preds = %sw.epilog
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 27, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %sw.epilog
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

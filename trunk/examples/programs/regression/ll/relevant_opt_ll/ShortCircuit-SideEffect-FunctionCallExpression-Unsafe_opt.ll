; #Unsafe
; ModuleID = 'output_folder/ShortCircuit-SideEffect-FunctionCallExpression-Unsafe.ll'
source_filename = "c5/ShortCircuit-SideEffect-FunctionCallExpression-Unsafe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i1 @identity(i1 noundef %b) {
entry:
  %frombool = zext i1 %b to i8
  %tobool = trunc i8 %frombool to i1
  ret i1 %tobool
}

define dso_local i32 @main() {
entry:
  %inc = add nsw i32 1, 1
  %cmp = icmp ne i32 1, 0
  %inc1 = add nsw i32 1, 1
  %cmp2 = icmp eq i32 1, 0
  %y.0 = select i1 %cmp, i32 1, i32 %inc1
  %0 = select i1 %cmp, i1 true, i1 %cmp2
  %call = call i1 @identity(i1 noundef %0)
  %frombool = zext i1 %call to i8
  %cmp3 = icmp eq i32 %y.0, 2
  br i1 %cmp3, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
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

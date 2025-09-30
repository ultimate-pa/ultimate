; #Safe
; ModuleID = 'c5/structFlexibleArray02.c'
source_filename = "c5/structFlexibleArray02.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.str = type { i32, [0 x i32] }


define dso_local i32 @main() #0 {
entry:
  %s = alloca ptr, align 8
  %dp = alloca ptr, align 8
  %res = alloca i32, align 4
  %call = call noalias ptr @malloc(i64 noundef 12) #3
  store ptr %call, ptr %s, align 8
  %0 = load ptr, ptr %s, align 8
  %d = getelementptr inbounds %struct.str, ptr %0, i32 0, i32 1
  %arrayidx = getelementptr inbounds [0 x i32], ptr %d, i64 0, i64 0
  store ptr %arrayidx, ptr %dp, align 8
  %1 = load ptr, ptr %dp, align 8
  store i32 42, ptr %1, align 4
  %2 = load ptr, ptr %s, align 8
  %d1 = getelementptr inbounds %struct.str, ptr %2, i32 0, i32 1
  %arrayidx2 = getelementptr inbounds [0 x i32], ptr %d1, i64 0, i64 0
  %3 = load i32, ptr %arrayidx2, align 4
  store i32 %3, ptr %res, align 4
  %4 = load i32, ptr %res, align 4
  %cmp = icmp eq i32 %4, 42
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 20, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





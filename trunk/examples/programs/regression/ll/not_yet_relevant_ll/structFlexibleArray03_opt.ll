; #Safe
; ModuleID = 'output_folder/structFlexibleArray03.ll'
source_filename = "c5/structFlexibleArray03.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.str = type { i32, [0 x i32] }


define dso_local i32 @main() {
entry:
  %call = call noalias ptr @malloc(i64 noundef 12) #3
  %call1 = call noalias ptr @malloc(i64 noundef 6) #3
  %d = getelementptr inbounds %struct.str, ptr %call, i32 0, i32 1
  %arrayidx = getelementptr inbounds [0 x i32], ptr %d, i64 0, i64 0
  store i32 42, ptr %arrayidx, align 4
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %call, ptr align 4 %call1, i64 4, i1 false)
  %d2 = getelementptr inbounds %struct.str, ptr %call, i32 0, i32 1
  %arrayidx3 = getelementptr inbounds [0 x i32], ptr %d2, i64 0, i64 0
  %0 = load i32, ptr %arrayidx3, align 4
  %cmp = icmp eq i32 %0, 42
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #4
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #0

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





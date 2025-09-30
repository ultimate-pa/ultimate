; #Safe
; ModuleID = 'output_folder/CopyStructWithArray.ll'
source_filename = "c5/CopyStructWithArray.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.MYSTRUCT = type { i32, i32, i32, [2 x i32] }

@x = dso_local global %struct.MYSTRUCT zeroinitializer, align 4
@y = dso_local global %struct.MYSTRUCT zeroinitializer, align 4

define dso_local i32 @main() {
entry:
  store i32 12, ptr @x, align 4
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 @y, ptr align 4 @x, i64 20, i1 false)
  %0 = load i32, ptr getelementptr inbounds (%struct.MYSTRUCT, ptr @y, i32 0, i32 3), align 4
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %0)
  %cmp = icmp eq i32 %0, 0
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #0

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





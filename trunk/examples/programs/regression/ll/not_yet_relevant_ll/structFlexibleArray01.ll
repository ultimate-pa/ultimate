; #Safe
; ModuleID = 'c5/structFlexibleArray01.c'
source_filename = "c5/structFlexibleArray01.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.str = type { i32, [0 x i32] }

@__const.main.s = private unnamed_addr constant %struct.str { i32 42, [0 x i32] zeroinitializer }, align 4

define dso_local i32 @main() #0 {
entry:
  %s = alloca %struct.str, align 4
  %res = alloca i32, align 4
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %s, ptr align 4 @__const.main.s, i64 4, i1 false)
  %n = getelementptr inbounds %struct.str, ptr %s, i32 0, i32 0
  %0 = load i32, ptr %n, align 4
  store i32 %0, ptr %res, align 4
  %1 = load i32, ptr %res, align 4
  %cmp = icmp eq i32 %1, 42
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

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





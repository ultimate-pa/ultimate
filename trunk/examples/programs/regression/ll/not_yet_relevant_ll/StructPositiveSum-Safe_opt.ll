; #Safe
; ModuleID = 'output_folder/StructPositiveSum-Safe.ll'
source_filename = "c5/StructPositiveSum-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.pair = type { i32, i32 }

@__const.main.a = private unnamed_addr constant %struct.pair { i32 23, i32 42 }, align 4

define dso_local i32 @main() {
entry:
  %a.sroa.0.0.copyload = load i32, ptr @__const.main.a, align 4
  %a.sroa.6.0.copyload = load i32, ptr getelementptr inbounds (i8, ptr @__const.main.a, i64 4), align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %a.sroa.6.0 = phi i32 [ %a.sroa.6.0.copyload, %entry ], [ %a.sroa.6.1, %while.body ]
  %a.sroa.0.0 = phi i32 [ %a.sroa.0.0.copyload, %entry ], [ %a.sroa.0.1, %while.body ]
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %call1 = call i32 @__VERIFIER_nondet_int()
  %tobool2 = icmp ne i32 %call1, 0
  %inc = add nsw i32 %a.sroa.0.0, 1
  %dec = add nsw i32 %a.sroa.6.0, -1
  %dec4 = add nsw i32 %a.sroa.0.0, -1
  %inc6 = add nsw i32 %a.sroa.6.0, 1
  %a.sroa.6.1 = select i1 %tobool2, i32 %dec, i32 %inc6
  %a.sroa.0.1 = select i1 %tobool2, i32 %inc, i32 %dec4
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %add = add nsw i32 %a.sroa.0.0, %a.sroa.6.0
  %cmp = icmp sge i32 %add, 0
  br i1 %cmp, label %if.end11, label %if.else10

if.else10:                                        ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 27, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end11:                                         ; preds = %while.end
  ret i32 0
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #0

declare i32 @__VERIFIER_nondet_int() #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





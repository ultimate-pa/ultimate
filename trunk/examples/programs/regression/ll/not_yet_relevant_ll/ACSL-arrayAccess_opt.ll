; #Safe
; ModuleID = 'output_folder/ACSL-arrayAccess.ll'

define dso_local i32 @main() {
entry:
  %call = call noalias ptr @malloc(i64 noundef 4) #3
  store i32 42, ptr %call, align 4
  %a.sroa.0.0.copyload = load i32, ptr @__const.main.a, align 4
  %a.sroa.1.0.copyload = load i32, ptr getelementptr inbounds (i8, ptr @__const.main.a, i64 4), align 4
  %arrayidx = getelementptr inbounds i32, ptr %call, i64 0
  %0 = load i32, ptr %arrayidx, align 4
  %cmp = icmp eq i32 %0, 42
  %cmp2 = icmp eq i32 %a.sroa.1.0.copyload, 2
  %or.cond = select i1 %cmp, i1 %cmp2, i1 false
  br i1 %or.cond, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #4
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





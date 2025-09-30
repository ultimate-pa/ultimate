; #Safe
; ModuleID = 'output_folder/ACSL-array_contract.ll'

define dso_local void @init() {
entry:
  %0 = load ptr, ptr @a, align 8
  %arrayidx = getelementptr inbounds i32, ptr %0, i64 0
  store i32 7, ptr %arrayidx, align 4
  ret void
}

define dso_local i32 @main() {
entry:
  %call = call noalias ptr @malloc(i64 noundef 4) #2
  store ptr %call, ptr @a, align 8
  call void @init()
  %0 = load ptr, ptr @a, align 8
  %1 = load i32, ptr %0, align 4
  %cmp = icmp eq i32 %1, 7
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 21, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





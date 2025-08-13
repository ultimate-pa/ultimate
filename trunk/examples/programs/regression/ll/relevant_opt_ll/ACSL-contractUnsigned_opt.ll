; #Safe
; ModuleID = 'output_folder/ACSL-contractUnsigned.ll'

define dso_local i32 @f(i32 noundef %x) {
entry:
  %cmp = icmp ult i32 %x, 3
  %x. = select i1 %cmp, i32 %x, i32 0
  ret i32 %x.
}

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_uint()
  %call1 = call i32 @f(i32 noundef %call)
  %cmp = icmp ult i32 %call1, 3
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %entry
  ret i32 0
}

declare i32 @__VERIFIER_nondet_uint(...) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





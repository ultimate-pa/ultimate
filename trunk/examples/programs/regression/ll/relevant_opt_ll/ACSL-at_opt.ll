; #Safe
; ModuleID = 'output_folder/ACSL-at.ll'

@g = dso_local global i32 0, align 4

define dso_local void @div() {
entry:
  %0 = load i32, ptr @g, align 4
  %div = sdiv i32 %0, 2
  store i32 %div, ptr @g, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %entry
  %call = call i32 @__VERIFIER_nondet_int()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %1 = load i32, ptr @g, align 4
  %div1 = sdiv i32 %1, 2
  store i32 %div1, ptr @g, align 4
  br label %while.cond

while.end:                                        ; preds = %while.cond
  ret void
}

declare i32 @__VERIFIER_nondet_int(...) #0

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_int()
  store i32 %call, ptr @g, align 4
  %0 = load i32, ptr @g, align 4
  %cmp = icmp sgt i32 %0, 0
  br i1 %cmp, label %if.then, label %if.end3

if.then:                                          ; preds = %entry
  call void @div()
  %1 = load i32, ptr @g, align 4
  %cmp1 = icmp slt i32 %1, %call
  br i1 %cmp1, label %if.end3, label %if.else

if.else:                                          ; preds = %if.then
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end3:                                          ; preds = %if.then, %entry
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





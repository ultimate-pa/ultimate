; #Safe
; ModuleID = 'output_folder/ACSL-bitwise.ll'

define dso_local i32 @main() {
entry:
  %and = and i32 42, 0
  %cmp = icmp eq i32 %and, 0
  br i1 %cmp, label %if.end, label %if.else

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  %or = or i32 42, 42
  %cmp1 = icmp eq i32 %or, 42
  br i1 %cmp1, label %if.end4, label %if.else3

if.else3:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end4:                                          ; preds = %if.end
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Safe
; ModuleID = 'erw/ACSL-addressof.c'

define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %p = alloca ptr, align 8
  store ptr %x, ptr %p, align 8
  %0 = load ptr, ptr %p, align 8
  %cmp = icmp eq ptr %0, %x
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
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





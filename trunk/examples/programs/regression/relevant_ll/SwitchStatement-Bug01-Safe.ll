; #Safe
; ModuleID = 'erw/SwitchStatement-Bug01-Safe.c'
source_filename = "erw/SwitchStatement-Bug01-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %a = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 1, ptr %x, align 4
  store i32 5, ptr %a, align 4
  %0 = load i32, ptr %a, align 4
  switch i32 %0, label %sw.epilog [
    i32 0, label %sw.bb
    i32 1, label %sw.bb1
  ]

sw.bb:                                            ; preds = %entry
  store i32 2, ptr %x, align 4
  br label %sw.epilog

sw.bb1:                                           ; preds = %entry
  store i32 23, ptr %x, align 4
  br label %sw.epilog

sw.epilog:                                        ; preds = %entry, %sw.bb1, %sw.bb
  %1 = load i32, ptr %x, align 4
  %cmp = icmp eq i32 %1, 1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %sw.epilog
  br label %if.end

if.else:                                          ; preds = %sw.epilog
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 23, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  %2 = load i32, ptr %retval, align 4
  ret i32 %2
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





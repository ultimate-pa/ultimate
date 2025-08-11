; #Safe
; ModuleID = 'erw/BoogieBoolConversion.c'
source_filename = "erw/BoogieBoolConversion.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i64, align 8
  store i32 0, ptr %retval, align 4
  store i32 2, ptr %a, align 4
  %0 = load i32, ptr %a, align 4
  %cmp = icmp eq i32 %0, 2
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  store i32 1, ptr %b, align 4
  %1 = load i32, ptr %b, align 4
  %cmp1 = icmp eq i32 %1, 1
  br i1 %cmp1, label %if.then2, label %if.else3

if.then2:                                         ; preds = %if.end
  br label %if.end4

if.else3:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end4:                                          ; preds = %if.then2
  store i32 1, ptr %c, align 4
  %2 = load i32, ptr %c, align 4
  %cmp5 = icmp eq i32 %2, 1
  br i1 %cmp5, label %if.then6, label %if.else7

if.then6:                                         ; preds = %if.end4
  br label %if.end8

if.else7:                                         ; preds = %if.end4
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end8:                                          ; preds = %if.then6
  store i64 1, ptr %d, align 8
  %3 = load i64, ptr %d, align 8
  %cmp9 = icmp eq i64 %3, 1
  br i1 %cmp9, label %if.then10, label %if.else11

if.then10:                                        ; preds = %if.end8
  br label %if.end12

if.else11:                                        ; preds = %if.end8
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.1, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end12:                                         ; preds = %if.then10
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





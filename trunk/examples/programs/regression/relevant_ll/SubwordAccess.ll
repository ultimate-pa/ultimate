; #Unsafe
; ModuleID = 'c5/SubwordAccess.c'
source_filename = "c5/SubwordAccess.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %ptr = alloca ptr, align 8
  store i32 0, ptr %retval, align 4
  store i32 0, ptr %x, align 4
  store ptr %x, ptr %ptr, align 8
  %0 = load ptr, ptr %ptr, align 8
  %arrayidx = getelementptr inbounds i8, ptr %0, i64 1
  store i8 1, ptr %arrayidx, align 1
  %1 = load i32, ptr %x, align 4
  %cmp = icmp eq i32 %1, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str)
  br label %if.end

if.else:                                          ; preds = %entry
  %2 = load i32, ptr %x, align 4
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str.1, i32 noundef %2)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %3 = load i32, ptr %x, align 4
  %cmp2 = icmp eq i32 %3, 0
  br i1 %cmp2, label %if.then3, label %if.else4

if.then3:                                         ; preds = %if.end
  br label %if.end5

if.else4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.3, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end5:                                          ; preds = %if.then3
  %4 = load i32, ptr %retval, align 4
  ret i32 %4
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Unsafe
; ModuleID = 'c5/VariableDeclarationInLoops.c'
source_filename = "c5/VariableDeclarationInLoops.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %y = alloca i32, align 4
  %x = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 5, ptr %x, align 4
  br label %while.cond

while.cond:                                       ; preds = %if.end, %entry
  %0 = load i32, ptr %x, align 4
  %cmp = icmp sgt i32 %0, 0
  br i1 %cmp, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %1 = load i32, ptr %z, align 4
  store i32 %1, ptr %y, align 4
  %2 = load i32, ptr %y, align 4
  %cmp1 = icmp ne i32 %2, 0
  br i1 %cmp1, label %if.then, label %if.else

if.then:                                          ; preds = %while.body
  br label %if.end

if.else:                                          ; preds = %while.body
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %call = call i32 @test()
  store i32 %call, ptr %x, align 4
  %3 = load i32, ptr %retval, align 4
  ret i32 %3
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

define dso_local i32 @test() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  br label %MY_LABEL

MY_LABEL:                                         ; preds = %if.then, %entry
  %0 = load i32, ptr %x, align 4
  %cmp = icmp ne i32 %0, 0
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %MY_LABEL
  br label %MY_LABEL

if.end:                                           ; preds = %MY_LABEL
  %1 = load i32, ptr %x, align 4
  %cmp1 = icmp eq i32 %1, 0
  br i1 %cmp1, label %if.then2, label %if.else

if.then2:                                         ; preds = %if.end
  br label %if.end3

if.else:                                          ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.test) #2
  unreachable

if.end3:                                          ; preds = %if.then2
  %2 = load i32, ptr %retval, align 4
  ret i32 %2
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





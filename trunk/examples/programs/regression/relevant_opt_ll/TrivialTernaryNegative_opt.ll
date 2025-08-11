; #Safe
; ModuleID = 'output_folder/TrivialTernaryNegative.ll'
source_filename = "c5/TrivialTernaryNegative.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@var1 = dso_local global i8 0, align 1
@var2 = dso_local global i8 0, align 1

define dso_local void @step() {
entry:
  %0 = load i8, ptr @var2, align 1
  %tobool = icmp ne i8 %0, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i8 1, ptr @var1, align 1
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

define dso_local i32 @property() {
entry:
  %0 = load i8, ptr @var2, align 1
  %conv = zext i8 %0 to i32
  %tobool = icmp ne i32 %conv, 0
  %1 = load i8, ptr @var1, align 1
  %conv1 = zext i8 %1 to i32
  %cmp = icmp eq i32 %conv1, 1
  %conv2 = zext i1 %cmp to i32
  %cond = select i1 %tobool, i32 %conv2, i32 1
  ret i32 %cond
}

define dso_local i32 @main() {
entry:
  br label %while.body

while.body:                                       ; preds = %if.end, %entry
  call void @step()
  %call = call i32 @property()
  %tobool = icmp ne i32 %call, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %while.body
  call void @__VERIFIER_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %while.body
  br label %while.body
}

declare void @__VERIFIER_error(...) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





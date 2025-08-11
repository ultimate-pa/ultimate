; #Safe
; ModuleID = 'c5/NutzTransformation04.c'
source_filename = "c5/NutzTransformation04.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i16, align 2
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %d = alloca i32, align 4
  %e = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i16 0, ptr %a, align 2
  %0 = load i16, ptr %a, align 2
  %conv = zext i16 %0 to i32
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %conv)
  %1 = load i16, ptr %a, align 2
  %tobool = icmp ne i16 %1, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  store i32 %lnot.ext, ptr %b, align 4
  %2 = load i32, ptr %b, align 4
  %cmp = icmp eq i32 %2, 1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str.1, ptr noundef @.str.2, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  %3 = load i16, ptr %a, align 2
  %conv2 = zext i16 %3 to i32
  %tobool3 = icmp ne i32 %conv2, 0
  br i1 %tobool3, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %if.end
  br label %land.end

land.end:                                         ; preds = %land.rhs, %if.end
  %4 = phi i1 [ false, %if.end ], [ true, %land.rhs ]
  %land.ext = zext i1 %4 to i32
  store i32 %land.ext, ptr %c, align 4
  %5 = load i32, ptr %c, align 4
  %cmp4 = icmp eq i32 %5, 0
  br i1 %cmp4, label %if.then6, label %if.else7

if.then6:                                         ; preds = %land.end
  br label %if.end8

if.else7:                                         ; preds = %land.end
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.2, i32 noundef 24, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end8:                                          ; preds = %if.then6
  %6 = load i16, ptr %a, align 2
  %conv9 = zext i16 %6 to i32
  %tobool10 = icmp ne i32 %conv9, 0
  br i1 %tobool10, label %lor.end, label %lor.rhs

lor.rhs:                                          ; preds = %if.end8
  br label %lor.end

lor.end:                                          ; preds = %lor.rhs, %if.end8
  %7 = phi i1 [ true, %if.end8 ], [ false, %lor.rhs ]
  %lor.ext = zext i1 %7 to i32
  store i32 %lor.ext, ptr %d, align 4
  %8 = load i32, ptr %d, align 4
  %cmp11 = icmp eq i32 %8, 0
  br i1 %cmp11, label %if.then13, label %if.else14

if.then13:                                        ; preds = %lor.end
  br label %if.end15

if.else14:                                        ; preds = %lor.end
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.2, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end15:                                         ; preds = %if.then13
  %9 = load i16, ptr %a, align 2
  %conv16 = zext i16 %9 to i32
  %tobool17 = icmp ne i32 %conv16, 0
  %10 = zext i1 %tobool17 to i64
  %cond = select i1 %tobool17, i32 5, i32 17
  store i32 %cond, ptr %e, align 4
  %11 = load i32, ptr %e, align 4
  %cmp18 = icmp eq i32 %11, 17
  br i1 %cmp18, label %if.then20, label %if.else21

if.then20:                                        ; preds = %if.end15
  br label %if.end22

if.else21:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.2, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end22:                                         ; preds = %if.then20
  %12 = load i16, ptr %a, align 2
  %tobool23 = icmp ne i16 %12, 0
  br i1 %tobool23, label %if.then24, label %if.end25

if.then24:                                        ; preds = %if.end22
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 30, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end25:                                         ; preds = %if.end22
  br label %while.cond

while.cond:                                       ; preds = %if.end25
  %13 = load i16, ptr %a, align 2
  %tobool26 = icmp ne i16 %13, 0
  br i1 %tobool26, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  call void @__assert_fail(ptr noundef @.str.6, ptr noundef @.str.2, i32 noundef 33, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

while.end:                                        ; preds = %while.cond
  store i32 0, ptr %i, align 4
  br label %do.body

do.body:                                          ; preds = %do.cond, %while.end
  %14 = load i32, ptr %i, align 4
  %inc = add nsw i32 %14, 1
  store i32 %inc, ptr %i, align 4
  br label %do.cond

do.cond:                                          ; preds = %do.body
  %15 = load i16, ptr %a, align 2
  %tobool27 = icmp ne i16 %15, 0
  br i1 %tobool27, label %do.body, label %do.end, !llvm.loop !6

do.end:                                           ; preds = %do.cond
  %16 = load i32, ptr %i, align 4
  %cmp28 = icmp eq i32 %16, 1
  br i1 %cmp28, label %if.then30, label %if.else31

if.then30:                                        ; preds = %do.end
  br label %if.end32

if.else31:                                        ; preds = %do.end
  call void @__assert_fail(ptr noundef @.str.7, ptr noundef @.str.2, i32 noundef 44, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end32:                                         ; preds = %if.then30
  ret i32 0
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
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





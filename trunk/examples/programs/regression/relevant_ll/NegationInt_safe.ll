; #Safe
; ModuleID = 'c5/NegationInt_safe.c'
source_filename = "c5/NegationInt_safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  %negX = alloca i32, align 4
  %negY = alloca i32, align 4
  %negZ = alloca i32, align 4
  store i32 0, ptr %x, align 4
  store i32 1, ptr %y, align 4
  store i32 2, ptr %z, align 4
  %0 = load i32, ptr %x, align 4
  %tobool = icmp ne i32 %0, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  store i32 %lnot.ext, ptr %negX, align 4
  %1 = load i32, ptr %y, align 4
  %tobool1 = icmp ne i32 %1, 0
  %lnot2 = xor i1 %tobool1, true
  %lnot.ext3 = zext i1 %lnot2 to i32
  store i32 %lnot.ext3, ptr %negY, align 4
  %2 = load i32, ptr %z, align 4
  %tobool4 = icmp ne i32 %2, 0
  %lnot5 = xor i1 %tobool4, true
  %lnot.ext6 = zext i1 %lnot5 to i32
  store i32 %lnot.ext6, ptr %negZ, align 4
  %3 = load i32, ptr %negX, align 4
  %cmp = icmp eq i32 %3, 1
  br i1 %cmp, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %entry
  %4 = load i32, ptr %negY, align 4
  %cmp7 = icmp eq i32 %4, 0
  br i1 %cmp7, label %land.lhs.true8, label %if.else

land.lhs.true8:                                   ; preds = %land.lhs.true
  %5 = load i32, ptr %negZ, align 4
  %cmp9 = icmp eq i32 %5, 0
  br i1 %cmp9, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true8
  br label %if.end

if.else:                                          ; preds = %land.lhs.true8, %land.lhs.true, %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #2
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





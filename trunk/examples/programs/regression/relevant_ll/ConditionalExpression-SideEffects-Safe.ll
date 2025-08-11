; #Safe
; ModuleID = 'c5/ConditionalExpression-SideEffects-Safe.c'
source_filename = "c5/ConditionalExpression-SideEffects-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @foo(i32 noundef %a, i32 noundef %b, i32 noundef %c) #0 {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %c.addr = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  %n = alloca i32, align 4
  store i32 %a, ptr %a.addr, align 4
  store i32 %b, ptr %b.addr, align 4
  store i32 %c, ptr %c.addr, align 4
  %0 = load i32, ptr %a.addr, align 4
  store i32 %0, ptr %x, align 4
  %1 = load i32, ptr %b.addr, align 4
  store i32 %1, ptr %y, align 4
  %2 = load i32, ptr %c.addr, align 4
  store i32 %2, ptr %z, align 4
  %3 = load i32, ptr %x, align 4
  %inc = add nsw i32 %3, 1
  store i32 %inc, ptr %x, align 4
  %cmp = icmp eq i32 %3, 0
  br i1 %cmp, label %cond.true, label %cond.false

cond.true:                                        ; preds = %entry
  %4 = load i32, ptr %y, align 4
  %inc1 = add nsw i32 %4, 1
  store i32 %inc1, ptr %y, align 4
  br label %cond.end

cond.false:                                       ; preds = %entry
  %5 = load i32, ptr %z, align 4
  %inc2 = add nsw i32 %5, 1
  store i32 %inc2, ptr %z, align 4
  br label %cond.end

cond.end:                                         ; preds = %cond.false, %cond.true
  %cond = phi i32 [ %4, %cond.true ], [ %5, %cond.false ]
  store i32 %cond, ptr %n, align 4
  %6 = load i32, ptr %x, align 4
  %7 = load i32, ptr %a.addr, align 4
  %add = add nsw i32 %7, 1
  %cmp3 = icmp eq i32 %6, %add
  br i1 %cmp3, label %if.then, label %if.else

if.then:                                          ; preds = %cond.end
  br label %if.end

if.else:                                          ; preds = %cond.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 12, ptr noundef @__PRETTY_FUNCTION__.foo) #2
  unreachable

if.end:                                           ; preds = %if.then
  %8 = load i32, ptr %a.addr, align 4
  %cmp4 = icmp eq i32 %8, 0
  br i1 %cmp4, label %cond.true5, label %cond.false7

cond.true5:                                       ; preds = %if.end
  %9 = load i32, ptr %n, align 4
  %10 = load i32, ptr %b.addr, align 4
  %cmp6 = icmp eq i32 %9, %10
  br i1 %cmp6, label %if.then8, label %if.else9

cond.false7:                                      ; preds = %if.end
  br i1 true, label %if.then8, label %if.else9

if.then8:                                         ; preds = %cond.false7, %cond.true5
  br label %if.end10

if.else9:                                         ; preds = %cond.false7, %cond.true5
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.foo) #2
  unreachable

if.end10:                                         ; preds = %if.then8
  %11 = load i32, ptr %a.addr, align 4
  %cmp11 = icmp eq i32 %11, 0
  br i1 %cmp11, label %cond.true12, label %cond.false15

cond.true12:                                      ; preds = %if.end10
  %12 = load i32, ptr %y, align 4
  %13 = load i32, ptr %b.addr, align 4
  %add13 = add nsw i32 %13, 1
  %cmp14 = icmp eq i32 %12, %add13
  br i1 %cmp14, label %if.then16, label %if.else17

cond.false15:                                     ; preds = %if.end10
  br i1 true, label %if.then16, label %if.else17

if.then16:                                        ; preds = %cond.false15, %cond.true12
  br label %if.end18

if.else17:                                        ; preds = %cond.false15, %cond.true12
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.foo) #2
  unreachable

if.end18:                                         ; preds = %if.then16
  %14 = load i32, ptr %a.addr, align 4
  %cmp19 = icmp ne i32 %14, 0
  br i1 %cmp19, label %cond.true20, label %cond.false22

cond.true20:                                      ; preds = %if.end18
  %15 = load i32, ptr %n, align 4
  %16 = load i32, ptr %c.addr, align 4
  %cmp21 = icmp eq i32 %15, %16
  br i1 %cmp21, label %if.then23, label %if.else24

cond.false22:                                     ; preds = %if.end18
  br i1 true, label %if.then23, label %if.else24

if.then23:                                        ; preds = %cond.false22, %cond.true20
  br label %if.end25

if.else24:                                        ; preds = %cond.false22, %cond.true20
  call void @__assert_fail(ptr noundef @.str.4, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.foo) #2
  unreachable

if.end25:                                         ; preds = %if.then23
  %17 = load i32, ptr %a.addr, align 4
  %cmp26 = icmp ne i32 %17, 0
  br i1 %cmp26, label %cond.true27, label %cond.false30

cond.true27:                                      ; preds = %if.end25
  %18 = load i32, ptr %z, align 4
  %19 = load i32, ptr %c.addr, align 4
  %add28 = add nsw i32 %19, 1
  %cmp29 = icmp eq i32 %18, %add28
  br i1 %cmp29, label %if.then31, label %if.else32

cond.false30:                                     ; preds = %if.end25
  br i1 true, label %if.then31, label %if.else32

if.then31:                                        ; preds = %cond.false30, %cond.true27
  br label %if.end33

if.else32:                                        ; preds = %cond.false30, %cond.true27
  call void @__assert_fail(ptr noundef @.str.5, ptr noundef @.str.1, i32 noundef 16, ptr noundef @__PRETTY_FUNCTION__.foo) #2
  unreachable

if.end33:                                         ; preds = %if.then31
  %20 = load i32, ptr %n, align 4
  ret i32 %20
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %res = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  %0 = load i32, ptr %a, align 4
  %1 = load i32, ptr %b, align 4
  %2 = load i32, ptr %c, align 4
  %call = call i32 @foo(i32 noundef %0, i32 noundef %1, i32 noundef %2)
  store i32 %call, ptr %res, align 4
  ret i32 0
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





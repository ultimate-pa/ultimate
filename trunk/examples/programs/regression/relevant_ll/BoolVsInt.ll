; #Safe
; ModuleID = 'c5/BoolVsInt.c'
source_filename = "c5/BoolVsInt.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 1, ptr %i, align 4
  %0 = load i32, ptr %i, align 4
  %tobool = icmp ne i32 %0, 0
  %lnot = xor i1 %tobool, true
  %lnot.ext = zext i1 %lnot to i32
  store i32 %lnot.ext, ptr %i, align 4
  %1 = load i32, ptr %i, align 4
  %cmp = icmp eq i32 %1, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 11, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  %2 = load i32, ptr %i, align 4
  %tobool1 = icmp ne i32 %2, 0
  %lnot2 = xor i1 %tobool1, true
  %lnot.ext3 = zext i1 %lnot2 to i32
  store i32 %lnot.ext3, ptr %i, align 4
  %3 = load i32, ptr %i, align 4
  %cmp4 = icmp ne i32 %3, 0
  br i1 %cmp4, label %if.then5, label %if.else6

if.then5:                                         ; preds = %if.end
  br label %if.end7

if.else6:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 13, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end7:                                          ; preds = %if.then5
  store i32 1, ptr %i, align 4
  %4 = load i32, ptr %i, align 4
  %cmp8 = icmp ne i32 %4, 0
  br i1 %cmp8, label %if.then9, label %if.else10

if.then9:                                         ; preds = %if.end7
  br label %if.end11

if.else10:                                        ; preds = %if.end7
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end11:                                         ; preds = %if.then9
  store i32 1, ptr %i, align 4
  %5 = load i32, ptr %i, align 4
  %cmp12 = icmp ne i32 %5, 0
  br i1 %cmp12, label %if.then13, label %if.else14

if.then13:                                        ; preds = %if.end11
  br label %if.end15

if.else14:                                        ; preds = %if.end11
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 22, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end15:                                         ; preds = %if.then13
  store i32 0, ptr %i, align 4
  %6 = load i32, ptr %i, align 4
  %cmp16 = icmp eq i32 %6, 0
  br i1 %cmp16, label %if.then17, label %if.else18

if.then17:                                        ; preds = %if.end15
  br label %if.end19

if.else18:                                        ; preds = %if.end15
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end19:                                         ; preds = %if.then17
  store i32 1, ptr %i, align 4
  %7 = load i32, ptr %i, align 4
  %cmp20 = icmp ne i32 %7, 0
  br i1 %cmp20, label %if.then21, label %if.else22

if.then21:                                        ; preds = %if.end19
  br label %if.end23

if.else22:                                        ; preds = %if.end19
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 28, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end23:                                         ; preds = %if.then21
  store i32 0, ptr %i, align 4
  %8 = load i32, ptr %i, align 4
  %cmp24 = icmp eq i32 %8, 0
  br i1 %cmp24, label %if.then25, label %if.else26

if.then25:                                        ; preds = %if.end23
  br label %if.end27

if.else26:                                        ; preds = %if.end23
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 31, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end27:                                         ; preds = %if.then25
  store i32 1, ptr %i, align 4
  %9 = load i32, ptr %i, align 4
  %cmp28 = icmp ne i32 %9, 0
  br i1 %cmp28, label %if.then29, label %if.else30

if.then29:                                        ; preds = %if.end27
  br label %if.end31

if.else30:                                        ; preds = %if.end27
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.1, i32 noundef 34, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end31:                                         ; preds = %if.then29
  store i32 0, ptr %i, align 4
  %10 = load i32, ptr %i, align 4
  %cmp32 = icmp eq i32 %10, 0
  br i1 %cmp32, label %if.then33, label %if.else34

if.then33:                                        ; preds = %if.end31
  br label %if.end35

if.else34:                                        ; preds = %if.end31
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 37, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end35:                                         ; preds = %if.then33
  store i32 0, ptr %i, align 4
  store i32 0, ptr %i, align 4
  %11 = load i32, ptr %i, align 4
  %cmp36 = icmp eq i32 %11, 0
  br i1 %cmp36, label %if.then37, label %if.else38

if.then37:                                        ; preds = %if.end35
  br label %if.end39

if.else38:                                        ; preds = %if.end35
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 45, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end39:                                         ; preds = %if.then37
  store i32 1, ptr %i, align 4
  %12 = load i32, ptr %i, align 4
  %cmp40 = icmp eq i32 %12, 1
  br i1 %cmp40, label %if.then41, label %if.else42

if.then41:                                        ; preds = %if.end39
  br label %if.end43

if.else42:                                        ; preds = %if.end39
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 47, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end43:                                         ; preds = %if.then41
  store i32 0, ptr %i, align 4
  %13 = load i32, ptr %i, align 4
  %tobool44 = icmp ne i32 %13, 0
  br i1 %tobool44, label %if.then45, label %if.end46

if.then45:                                        ; preds = %if.end43
  store i32 1, ptr %i, align 4
  br label %if.end46

if.end46:                                         ; preds = %if.then45, %if.end43
  %14 = load i32, ptr %i, align 4
  %cmp47 = icmp eq i32 %14, 0
  br i1 %cmp47, label %if.then48, label %if.else49

if.then48:                                        ; preds = %if.end46
  br label %if.end50

if.else49:                                        ; preds = %if.end46
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 57, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end50:                                         ; preds = %if.then48
  store i32 0, ptr %i, align 4
  %15 = load i32, ptr %i, align 4
  %tobool51 = icmp ne i32 %15, 0
  br i1 %tobool51, label %if.end53, label %if.then52

if.then52:                                        ; preds = %if.end50
  store i32 1, ptr %i, align 4
  br label %if.end53

if.end53:                                         ; preds = %if.then52, %if.end50
  %16 = load i32, ptr %i, align 4
  %cmp54 = icmp eq i32 %16, 1
  br i1 %cmp54, label %if.then55, label %if.else56

if.then55:                                        ; preds = %if.end53
  br label %if.end57

if.else56:                                        ; preds = %if.end53
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 63, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end57:                                         ; preds = %if.then55
  store i32 0, ptr %i, align 4
  store i32 1, ptr %i, align 4
  %17 = load i32, ptr %i, align 4
  %cmp58 = icmp eq i32 %17, 1
  br i1 %cmp58, label %if.then59, label %if.else60

if.then59:                                        ; preds = %if.end57
  br label %if.end61

if.else60:                                        ; preds = %if.end57
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 69, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end61:                                         ; preds = %if.then59
  store i32 0, ptr %i, align 4
  %18 = load i32, ptr %i, align 4
  %cmp62 = icmp eq i32 %18, 0
  br i1 %cmp62, label %land.lhs.true, label %if.end65

land.lhs.true:                                    ; preds = %if.end61
  %19 = load i32, ptr %i, align 4
  %tobool63 = icmp ne i32 %19, 0
  br i1 %tobool63, label %if.then64, label %if.end65

if.then64:                                        ; preds = %land.lhs.true
  store i32 1, ptr %i, align 4
  br label %if.end65

if.end65:                                         ; preds = %if.then64, %land.lhs.true, %if.end61
  %20 = load i32, ptr %i, align 4
  %cmp66 = icmp eq i32 %20, 0
  br i1 %cmp66, label %if.then67, label %if.else68

if.then67:                                        ; preds = %if.end65
  br label %if.end69

if.else68:                                        ; preds = %if.end65
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 75, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end69:                                         ; preds = %if.then67
  store i32 0, ptr %i, align 4
  %21 = load i32, ptr %i, align 4
  %add = add nsw i32 %21, 1
  %tobool70 = icmp ne i32 %add, 0
  br i1 %tobool70, label %if.then71, label %if.end72

if.then71:                                        ; preds = %if.end69
  store i32 1, ptr %i, align 4
  br label %if.end72

if.end72:                                         ; preds = %if.then71, %if.end69
  %22 = load i32, ptr %i, align 4
  %cmp73 = icmp eq i32 %22, 1
  br i1 %cmp73, label %if.then74, label %if.else75

if.then74:                                        ; preds = %if.end72
  br label %if.end76

if.else75:                                        ; preds = %if.end72
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 81, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end76:                                         ; preds = %if.then74
  store i32 2, ptr %i, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.body, %if.end76
  %23 = load i32, ptr %i, align 4
  %tobool77 = icmp ne i32 %23, 0
  br i1 %tobool77, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %24 = load i32, ptr %i, align 4
  %sub = sub nsw i32 %24, 1
  store i32 %sub, ptr %i, align 4
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %25 = load i32, ptr %i, align 4
  %cmp78 = icmp eq i32 %25, 0
  br i1 %cmp78, label %if.then79, label %if.else80

if.then79:                                        ; preds = %while.end
  br label %if.end81

if.else80:                                        ; preds = %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 91, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end81:                                         ; preds = %if.then79
  store i32 2, ptr %i, align 4
  br label %while.body83

while.body83:                                     ; preds = %if.end81
  %26 = load i32, ptr %i, align 4
  %sub84 = sub nsw i32 %26, 1
  store i32 %sub84, ptr %i, align 4
  br label %while.end85

while.end85:                                      ; preds = %while.body83
  %27 = load i32, ptr %i, align 4
  %cmp86 = icmp eq i32 %27, 1
  br i1 %cmp86, label %if.then87, label %if.else88

if.then87:                                        ; preds = %while.end85
  br label %if.end89

if.else88:                                        ; preds = %while.end85
  call void @__assert_fail(ptr noundef @.str.3, ptr noundef @.str.1, i32 noundef 98, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end89:                                         ; preds = %if.then87
  store i32 2, ptr %i, align 4
  br label %while.cond90

while.cond90:                                     ; preds = %while.body92, %if.end89
  %28 = load i32, ptr %i, align 4
  %tobool91 = icmp ne i32 %28, 0
  br i1 %tobool91, label %while.body92, label %while.end94

while.body92:                                     ; preds = %while.cond90
  %29 = load i32, ptr %i, align 4
  %sub93 = sub nsw i32 %29, 1
  store i32 %sub93, ptr %i, align 4
  br label %while.cond90, !llvm.loop !8

while.end94:                                      ; preds = %while.cond90
  %30 = load i32, ptr %i, align 4
  %cmp95 = icmp eq i32 %30, 0
  br i1 %cmp95, label %if.then96, label %if.else97

if.then96:                                        ; preds = %while.end94
  br label %if.end98

if.else97:                                        ; preds = %while.end94
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 104, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end98:                                         ; preds = %if.then96
  store i32 2, ptr %i, align 4
  br label %do.body

do.body:                                          ; preds = %do.cond, %if.end98
  %31 = load i32, ptr %i, align 4
  %sub99 = sub nsw i32 %31, 1
  store i32 %sub99, ptr %i, align 4
  br label %do.cond

do.cond:                                          ; preds = %do.body
  %32 = load i32, ptr %i, align 4
  %tobool100 = icmp ne i32 %32, 0
  br i1 %tobool100, label %do.body, label %do.end, !llvm.loop !9

do.end:                                           ; preds = %do.cond
  %33 = load i32, ptr %i, align 4
  %cmp101 = icmp eq i32 %33, 0
  br i1 %cmp101, label %if.then102, label %if.else103

if.then102:                                       ; preds = %do.end
  br label %if.end104

if.else103:                                       ; preds = %do.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 110, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end104:                                        ; preds = %if.then102
  %34 = load i32, ptr %i, align 4
  ret i32 %34
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}





; #Safe
; ModuleID = 'output_folder/CharacterConstantsAndEscapeSequences.ll'
source_filename = "c5/CharacterConstantsAndEscapeSequences.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %conv = zext i8 39 to i32
  %cmp = icmp ne i32 %conv, 39
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 21, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end:                                           ; preds = %entry
  %conv2 = zext i8 34 to i32
  %cmp3 = icmp ne i32 %conv2, 34
  br i1 %cmp3, label %if.then5, label %if.end6

if.then5:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 25, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end6:                                          ; preds = %if.end
  %conv7 = zext i8 63 to i32
  %cmp8 = icmp ne i32 %conv7, 63
  br i1 %cmp8, label %if.then10, label %if.end11

if.then10:                                        ; preds = %if.end6
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 29, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end11:                                         ; preds = %if.end6
  %conv12 = zext i8 92 to i32
  %cmp13 = icmp ne i32 %conv12, 92
  br i1 %cmp13, label %if.then15, label %if.end16

if.then15:                                        ; preds = %if.end11
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 33, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end16:                                         ; preds = %if.end11
  %conv17 = zext i8 7 to i32
  %cmp18 = icmp ne i32 %conv17, 7
  br i1 %cmp18, label %if.then20, label %if.end21

if.then20:                                        ; preds = %if.end16
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 42, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end21:                                         ; preds = %if.end16
  %conv22 = zext i8 8 to i32
  %cmp23 = icmp ne i32 %conv22, 8
  br i1 %cmp23, label %if.then25, label %if.end26

if.then25:                                        ; preds = %if.end21
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 46, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end26:                                         ; preds = %if.end21
  %conv27 = zext i8 12 to i32
  %cmp28 = icmp ne i32 %conv27, 12
  br i1 %cmp28, label %if.then30, label %if.end31

if.then30:                                        ; preds = %if.end26
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 50, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end31:                                         ; preds = %if.end26
  %conv32 = zext i8 10 to i32
  %cmp33 = icmp ne i32 %conv32, 10
  br i1 %cmp33, label %if.then35, label %if.end36

if.then35:                                        ; preds = %if.end31
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 54, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end36:                                         ; preds = %if.end31
  %conv37 = zext i8 13 to i32
  %cmp38 = icmp ne i32 %conv37, 13
  br i1 %cmp38, label %if.then40, label %if.end41

if.then40:                                        ; preds = %if.end36
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 58, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end41:                                         ; preds = %if.end36
  %conv42 = zext i8 9 to i32
  %cmp43 = icmp ne i32 %conv42, 9
  br i1 %cmp43, label %if.then45, label %if.end46

if.then45:                                        ; preds = %if.end41
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 62, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end46:                                         ; preds = %if.end41
  %conv47 = zext i8 11 to i32
  %cmp48 = icmp ne i32 %conv47, 11
  br i1 %cmp48, label %if.then50, label %if.end51

if.then50:                                        ; preds = %if.end46
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 66, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end51:                                         ; preds = %if.end46
  %conv52 = zext i8 24 to i32
  %cmp53 = icmp ne i32 %conv52, 24
  br i1 %cmp53, label %if.then55, label %if.end56

if.then55:                                        ; preds = %if.end51
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 74, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end56:                                         ; preds = %if.end51
  %conv57 = zext i8 -1 to i32
  %cmp58 = icmp ne i32 %conv57, 255
  br i1 %cmp58, label %if.then60, label %if.end61

if.then60:                                        ; preds = %if.end56
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 78, ptr noundef @__PRETTY_FUNCTION__.main) #1
  unreachable

if.end61:                                         ; preds = %if.end56
  ret i32 0
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





; #Unsafe
; ModuleID = 'output_folder/bitwiseOrUnsigned.ll'
source_filename = "c5/bitwiseOrUnsigned.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %call = call i8 @__VERIFIER_nondet_uchar()
  %conv = zext i8 %call to i32
  %sub = sub nsw i32 %conv, 48
  %shr = ashr i32 %sub, 31
  %shr1 = ashr i32 %shr, 31
  %conv2 = zext i8 %call to i32
  %sub3 = sub nsw i32 %conv2, 48
  %shr4 = ashr i32 %sub3, 31
  %shr5 = ashr i32 %shr4, 31
  %add = add nsw i32 %shr1, %shr5
  %conv6 = zext i8 %call to i32
  %sub7 = sub nsw i32 %conv6, 48
  %shr8 = ashr i32 %sub7, 31
  %conv9 = zext i8 %call to i32
  %sub10 = sub nsw i32 %conv9, 48
  %shr11 = ashr i32 %sub10, 31
  %add12 = add nsw i32 %shr8, %shr11
  %conv13 = zext i8 %call to i32
  %sub14 = sub nsw i32 %conv13, 48
  %conv15 = zext i8 %call to i32
  %sub16 = sub nsw i32 %conv15, 48
  %add17 = add nsw i32 %sub14, %sub16
  %shr18 = ashr i32 %add17, 31
  %or = or i32 %add12, %shr18
  %shr19 = ashr i32 %or, 31
  %or20 = or i32 %add, %shr19
  %cmp = icmp eq i32 %or20, 0
  br i1 %cmp, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret i32 0
}

declare i8 @__VERIFIER_nondet_uchar() #0

declare void @__VERIFIER_error() #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





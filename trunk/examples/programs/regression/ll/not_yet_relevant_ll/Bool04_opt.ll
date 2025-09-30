; #Safe
; ModuleID = 'output_folder/Bool04.ll'
source_filename = "./Bool04.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

define dso_local i32 @main() {
entry:
  %call = call i32 @__VERIFIER_nondet_bool()
  %tobool = icmp ne i32 %call, 0
  %frombool = zext i1 %tobool to i8
  %call1 = call i32 @__VERIFIER_nondet_bool()
  %tobool2 = icmp ne i32 %call1, 0
  %frombool3 = zext i1 %tobool2 to i8
  %tobool4 = trunc i8 %frombool to i1
  %conv = zext i1 %tobool4 to i32
  %tobool5 = trunc i8 %frombool3 to i1
  %conv6 = zext i1 %tobool5 to i32
  %add = add nsw i32 %conv, %conv6
  %cmp = icmp sgt i32 %add, 2
  br i1 %cmp, label %if.then, label %lor.lhs.false

lor.lhs.false:                                    ; preds = %entry
  %tobool8 = trunc i8 %frombool to i1
  %conv9 = zext i1 %tobool8 to i32
  %tobool10 = trunc i8 %frombool3 to i1
  %conv11 = zext i1 %tobool10 to i32
  %add12 = add nsw i32 %conv9, %conv11
  %cmp13 = icmp slt i32 %add12, 0
  br i1 %cmp13, label %if.then, label %if.end

if.then:                                          ; preds = %lor.lhs.false, %entry
  %call15 = call i32 @reach_error()
  br label %if.end

if.end:                                           ; preds = %if.then, %lor.lhs.false
  ret i32 0
}

declare i32 @__VERIFIER_nondet_bool(...) #0

declare i32 @reach_error(...) #0
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





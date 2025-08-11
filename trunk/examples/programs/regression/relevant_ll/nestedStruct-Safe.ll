; ModuleID = 'c5/nestedStruct-Safe.c'
source_filename = "c5/nestedStruct-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.Outer = type { i32, %struct.Inner }
%struct.Inner = type { i32 }

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %outer = alloca %struct.Outer, align 4
  store i32 0, ptr %retval, align 4
  %x = getelementptr inbounds %struct.Outer, ptr %outer, i32 0, i32 1
  %b = getelementptr inbounds %struct.Inner, ptr %x, i32 0, i32 0
  %0 = load i32, ptr %b, align 4
  %cmp = icmp eq i32 %0, 4
  br i1 %cmp, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  store i32 1, ptr %retval, align 4
  br label %return

if.end:                                           ; preds = %entry
  store i32 0, ptr %retval, align 4
  br label %return

return:                                           ; preds = %if.end, %if.then
  %1 = load i32, ptr %retval, align 4
  ret i32 %1
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





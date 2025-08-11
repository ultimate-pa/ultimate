; ModuleID = 'erw/incompleteStruct-Safe.c'
source_filename = "erw/incompleteStruct-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.fraction = type { i32, i32 }


define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %f = alloca %struct.fraction, align 4
  store i32 0, ptr %retval, align 4
  %num = getelementptr inbounds %struct.fraction, ptr %f, i32 0, i32 0
  store i32 5, ptr %num, align 4
  %denom = getelementptr inbounds %struct.fraction, ptr %f, i32 0, i32 1
  store i32 5, ptr %denom, align 4
  %num1 = getelementptr inbounds %struct.fraction, ptr %f, i32 0, i32 0
  %0 = load i32, ptr %num1, align 4
  %denom2 = getelementptr inbounds %struct.fraction, ptr %f, i32 0, i32 1
  %1 = load i32, ptr %denom2, align 4
  %cmp = icmp eq i32 %0, %1
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 20, ptr noundef @__PRETTY_FUNCTION__.main) #2
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





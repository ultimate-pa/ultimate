; #Safe
; ModuleID = 'c5/ShortCircuit-SideEffect-DoStatement-Safe.c'
source_filename = "c5/ShortCircuit-SideEffect-DoStatement-Safe.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@.str = private unnamed_addr constant [17 x i8] c"x >= 1 && y >= 1\00", align 1
@.str.1 = private unnamed_addr constant [46 x i8] c"c5/ShortCircuit-SideEffect-DoStatement-Safe.c\00", align 1
@__PRETTY_FUNCTION__.main = private unnamed_addr constant [11 x i8] c"int main()\00", align 1

define dso_local i32 @main() #0 {
entry:
  %retval = alloca i32, align 4
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 0, ptr %retval, align 4
  store i32 1, ptr %x, align 4
  store i32 1, ptr %y, align 4
  br label %do.body

do.body:                                          ; preds = %land.end, %entry
  br label %while.cond

while.cond:                                       ; preds = %while.body, %do.body
  %0 = load i32, ptr %a, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %while.body, label %while.end

while.body:                                       ; preds = %while.cond
  %1 = load i32, ptr %b, align 4
  store i32 %1, ptr %a, align 4
  br label %while.cond, !llvm.loop !6

while.end:                                        ; preds = %while.cond
  %2 = load i32, ptr %x, align 4
  %cmp = icmp sge i32 %2, 1
  br i1 %cmp, label %land.lhs.true, label %if.else

land.lhs.true:                                    ; preds = %while.end
  %3 = load i32, ptr %y, align 4
  %cmp1 = icmp sge i32 %3, 1
  br i1 %cmp1, label %if.then, label %if.else

if.then:                                          ; preds = %land.lhs.true
  br label %if.end

if.else:                                          ; preds = %land.lhs.true, %while.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 14, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end:                                           ; preds = %if.then
  br label %do.cond

do.cond:                                          ; preds = %if.end
  %4 = load i32, ptr %x, align 4
  %inc = add nsw i32 %4, 1
  store i32 %inc, ptr %x, align 4
  %cmp2 = icmp ne i32 %4, 0
  br i1 %cmp2, label %land.rhs, label %land.end

land.rhs:                                         ; preds = %do.cond
  %5 = load i32, ptr %y, align 4
  %inc3 = add nsw i32 %5, 1
  store i32 %inc3, ptr %y, align 4
  %cmp4 = icmp ne i32 %5, 0
  br label %land.end

land.end:                                         ; preds = %land.rhs, %do.cond
  %6 = phi i1 [ false, %do.cond ], [ %cmp4, %land.rhs ]
  br i1 %6, label %do.body, label %do.end, !llvm.loop !8

do.end:                                           ; preds = %land.end
  %7 = load i32, ptr %retval, align 4
  ret i32 %7
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

attributes #1 = { noreturn nounwind "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+fp-armv8,+neon,+outline-atomics,+v8a,-fmv" }
attributes #2 = { noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}

; #Safe
; ModuleID = 'output_folder/varargs.ll'
source_filename = "c5/varargs.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.__va_list = type { ptr, ptr, ptr, i32, i32 }


define dso_local void @positive(i32 noundef %count, ...) {
entry:
  %valist = alloca %struct.__va_list, align 8
  call void @llvm.va_start(ptr %valist)
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %cmp = icmp slt i32 %i.0, %count
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %gr_offs_p = getelementptr inbounds %struct.__va_list, ptr %valist, i32 0, i32 3
  %gr_offs = load i32, ptr %gr_offs_p, align 8
  %0 = icmp sge i32 %gr_offs, 0
  br i1 %0, label %vaarg.on_stack, label %vaarg.maybe_reg

vaarg.maybe_reg:                                  ; preds = %for.body
  %new_reg_offs = add i32 %gr_offs, 8
  store i32 %new_reg_offs, ptr %gr_offs_p, align 8
  %inreg = icmp sle i32 %new_reg_offs, 0
  br i1 %inreg, label %vaarg.in_reg, label %vaarg.on_stack

vaarg.in_reg:                                     ; preds = %vaarg.maybe_reg
  %reg_top_p = getelementptr inbounds %struct.__va_list, ptr %valist, i32 0, i32 1
  %reg_top = load ptr, ptr %reg_top_p, align 8
  %1 = getelementptr inbounds i8, ptr %reg_top, i32 %gr_offs
  br label %vaarg.end

vaarg.on_stack:                                   ; preds = %vaarg.maybe_reg, %for.body
  %stack_p = getelementptr inbounds %struct.__va_list, ptr %valist, i32 0, i32 0
  %stack = load ptr, ptr %stack_p, align 8
  %new_stack = getelementptr inbounds i8, ptr %stack, i64 8
  store ptr %new_stack, ptr %stack_p, align 8
  br label %vaarg.end

vaarg.end:                                        ; preds = %vaarg.on_stack, %vaarg.in_reg
  %vaargs.addr = phi ptr [ %1, %vaarg.in_reg ], [ %stack, %vaarg.on_stack ]
  %2 = load i32, ptr %vaargs.addr, align 8
  %cmp1 = icmp sgt i32 %2, 0
  br i1 %cmp1, label %for.inc, label %if.else

if.else:                                          ; preds = %vaarg.end
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 15, ptr noundef @__PRETTY_FUNCTION__.positive) #2
  unreachable

for.inc:                                          ; preds = %vaarg.end
  %inc = add nsw i32 %i.0, 1
  br label %for.cond, !llvm.loop !6

for.end:                                          ; preds = %for.cond
  call void @llvm.va_end(ptr %valist)
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn
declare void @llvm.va_start(ptr) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: nocallback nofree nosync nounwind willreturn
declare void @llvm.va_end(ptr) #0

define dso_local i32 @main() {
entry:
  call void (i32, ...) @positive(i32 noundef 2, i32 noundef 97, i32 noundef 42)
  ret i32 0
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}





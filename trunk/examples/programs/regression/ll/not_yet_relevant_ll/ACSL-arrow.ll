; #Safe
; ModuleID = 'c5/ACSL-arrow.c'

%struct.str = type { i32 }

define dso_local i32 @main() #0 {
entry:
  %s = alloca %struct.str, align 4
  %p = alloca ptr, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 4 %s, ptr align 4 @__const.main.s, i64 4, i1 false)
  store ptr %s, ptr %p, align 8
  %0 = load ptr, ptr %p, align 8
  %x = getelementptr inbounds %struct.str, ptr %0, i32 0, i32 0
  %1 = load i32, ptr %x, align 4
  %cmp = icmp eq i32 %1, 5
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  br label %if.end

if.else:                                          ; preds = %entry
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 17, ptr noundef @__PRETTY_FUNCTION__.main) #3
  unreachable

if.end:                                           ; preds = %if.then
  ret i32 0
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





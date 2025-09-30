; #Safe
; ModuleID = 'output_folder/SdHtcFail.ll'
source_filename = "./SdHtcFail.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.ldv_list_head = type { i32, i32 }

@global_list_13 = dso_local global %struct.ldv_list_head zeroinitializer, align 4

define dso_local ptr @ldv_malloc(i32 noundef %size) {
entry:
  %conv = sext i32 %size to i64
  %call = call ptr @malloc(i64 noundef %conv) #1
  ret ptr %call
}

; Function Attrs: allocsize(0)
declare ptr @malloc(i64 noundef) #0

define dso_local void @ldv_list_del(i32 noundef %entry1) {
entry:
  ret void
}

define dso_local void @alloc_13() {
entry:
  %call = call ptr @ldv_malloc(i32 noundef 0)
  ret void
}

define dso_local void @free_unsafe_13() {
entry:
  %0 = load i32, ptr @global_list_13, align 4
  call void @ldv_list_del(i32 noundef 0)
  ret void
}

define dso_local void @entry_point() {
entry:
  call void @alloc_13()
  call void @free_unsafe_13()
  ret void
}

define dso_local void @main() {
entry:
  call void @entry_point()
  ret void
}
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





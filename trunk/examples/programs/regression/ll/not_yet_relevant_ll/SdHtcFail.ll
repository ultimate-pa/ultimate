; #Safe
; ModuleID = './SdHtcFail.c'
source_filename = "./SdHtcFail.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.ldv_list_head = type { i32, i32 }

@global_list_13 = dso_local global %struct.ldv_list_head zeroinitializer, align 4

define dso_local ptr @ldv_malloc(i32 noundef %size) #0 {
entry:
  %size.addr = alloca i32, align 4
  store i32 %size, ptr %size.addr, align 4
  %0 = load i32, ptr %size.addr, align 4
  %conv = sext i32 %0 to i64
  %call = call ptr @malloc(i64 noundef %conv) #2
  ret ptr %call
}

; Function Attrs: allocsize(0)
declare ptr @malloc(i64 noundef) #1

define dso_local void @ldv_list_del(i32 noundef %entry1) #0 {
entry:
  %entry.addr = alloca i32, align 4
  store i32 %entry1, ptr %entry.addr, align 4
  ret void
}

define dso_local void @alloc_13() #0 {
entry:
  %call = call ptr @ldv_malloc(i32 noundef 0)
  ret void
}

define dso_local void @free_unsafe_13() #0 {
entry:
  %__mptr = alloca i32, align 4
  %0 = load i32, ptr @global_list_13, align 4
  store i32 %0, ptr %__mptr, align 4
  call void @ldv_list_del(i32 noundef 0)
  ret void
}

define dso_local void @entry_point() #0 {
entry:
  call void @alloc_13()
  call void @free_unsafe_13()
  ret void
}

define dso_local void @main() #0 {
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





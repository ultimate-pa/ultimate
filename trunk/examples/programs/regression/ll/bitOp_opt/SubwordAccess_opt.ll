; #Unsafe
; ModuleID = 'output_folder/SubwordAccess.ll'
source_filename = "c5/SubwordAccess.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"


define dso_local i32 @main() {
entry:
  %x.sroa.5.0.insert.ext = zext i16 0 to i32
  %x.sroa.5.0.insert.shift = shl i32 %x.sroa.5.0.insert.ext, 16
  %x.sroa.5.0.insert.mask = and i32 undef, 65535
  %x.sroa.5.0.insert.insert = or i32 %x.sroa.5.0.insert.mask, %x.sroa.5.0.insert.shift
  %x.sroa.4.0.insert.ext = zext i8 1 to i32
  %x.sroa.4.0.insert.shift = shl i32 %x.sroa.4.0.insert.ext, 8
  %x.sroa.4.0.insert.mask = and i32 %x.sroa.5.0.insert.insert, -65281
  %x.sroa.4.0.insert.insert = or i32 %x.sroa.4.0.insert.mask, %x.sroa.4.0.insert.shift
  %x.sroa.0.0.insert.ext = zext i8 0 to i32
  %x.sroa.0.0.insert.mask = and i32 %x.sroa.4.0.insert.insert, -256
  %x.sroa.0.0.insert.insert = or i32 %x.sroa.0.0.insert.mask, %x.sroa.0.0.insert.ext
  %cmp = icmp eq i32 %x.sroa.0.0.insert.insert, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %call = call i32 (ptr, ...) @printf(ptr noundef @.str)
  br label %if.end

if.else:                                          ; preds = %entry
  %x.sroa.5.0.insert.ext20 = zext i16 0 to i32
  %x.sroa.5.0.insert.shift21 = shl i32 %x.sroa.5.0.insert.ext20, 16
  %x.sroa.5.0.insert.mask22 = and i32 undef, 65535
  %x.sroa.5.0.insert.insert23 = or i32 %x.sroa.5.0.insert.mask22, %x.sroa.5.0.insert.shift21
  %x.sroa.4.0.insert.ext10 = zext i8 1 to i32
  %x.sroa.4.0.insert.shift11 = shl i32 %x.sroa.4.0.insert.ext10, 8
  %x.sroa.4.0.insert.mask12 = and i32 %x.sroa.5.0.insert.insert23, -65281
  %x.sroa.4.0.insert.insert13 = or i32 %x.sroa.4.0.insert.mask12, %x.sroa.4.0.insert.shift11
  %x.sroa.0.0.insert.ext2 = zext i8 0 to i32
  %x.sroa.0.0.insert.mask3 = and i32 %x.sroa.4.0.insert.insert13, -256
  %x.sroa.0.0.insert.insert4 = or i32 %x.sroa.0.0.insert.mask3, %x.sroa.0.0.insert.ext2
  %call1 = call i32 (ptr, ...) @printf(ptr noundef @.str.1, i32 noundef %x.sroa.0.0.insert.insert4)
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %x.sroa.5.0.insert.ext25 = zext i16 0 to i32
  %x.sroa.5.0.insert.shift26 = shl i32 %x.sroa.5.0.insert.ext25, 16
  %x.sroa.5.0.insert.mask27 = and i32 undef, 65535
  %x.sroa.5.0.insert.insert28 = or i32 %x.sroa.5.0.insert.mask27, %x.sroa.5.0.insert.shift26
  %x.sroa.4.0.insert.ext15 = zext i8 1 to i32
  %x.sroa.4.0.insert.shift16 = shl i32 %x.sroa.4.0.insert.ext15, 8
  %x.sroa.4.0.insert.mask17 = and i32 %x.sroa.5.0.insert.insert28, -65281
  %x.sroa.4.0.insert.insert18 = or i32 %x.sroa.4.0.insert.mask17, %x.sroa.4.0.insert.shift16
  %x.sroa.0.0.insert.ext6 = zext i8 0 to i32
  %x.sroa.0.0.insert.mask7 = and i32 %x.sroa.4.0.insert.insert18, -256
  %x.sroa.0.0.insert.insert8 = or i32 %x.sroa.0.0.insert.mask7, %x.sroa.0.0.insert.ext6
  %cmp2 = icmp eq i32 %x.sroa.0.0.insert.insert8, 0
  br i1 %cmp2, label %if.end5, label %if.else4

if.else4:                                         ; preds = %if.end
  call void @__assert_fail(ptr noundef @.str.2, ptr noundef @.str.3, i32 noundef 26, ptr noundef @__PRETTY_FUNCTION__.main) #2
  unreachable

if.end5:                                          ; preds = %if.end
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #0

; Function Attrs: noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





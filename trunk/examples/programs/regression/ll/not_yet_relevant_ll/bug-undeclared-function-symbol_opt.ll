; #Safe
; ModuleID = 'output_folder/bug-undeclared-function-symbol.ll'
source_filename = "c5/bug-undeclared-function-symbol.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.net_device = type { ptr }
%struct.net_device_ops = type { ptr }

@tlan_have_eisa = dso_local global i32 0, align 4
@ldv_spin__xmit_lock_of_netdev_queue = dso_local global i32 1, align 4
@ldv_spin_addr_list_lock_of_net_device = dso_local global i32 1, align 4

define dso_local void @outb_p(i32 noundef %value, i32 noundef %port) {
entry:
  ret void
}

define dso_local void @tlan_stop(ptr noundef %dev) {
entry:
  call void @tlan_reset_adapter(ptr noundef %dev)
  ret void
}

define dso_local void @tlan_eisa_cleanup() {
entry:
  br label %ldv_43677

ldv_43677:                                        ; preds = %if.then, %entry
  %0 = load i32, ptr @tlan_have_eisa, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.then, label %if.end

if.then:                                          ; preds = %ldv_43677
  call void @ldv_unregister_netdev_74(ptr noundef undef)
  br label %ldv_43677

if.end:                                           ; preds = %ldv_43677
  ret void
}

define dso_local void @tlan_exit() {
entry:
  call void @tlan_eisa_cleanup()
  ret void
}

define dso_local i32 @tlan_close(i32 noundef %dev) {
entry:
  call void @tlan_stop(ptr noundef null)
  ret i32 0
}

define dso_local void @tlan_reset_adapter(ptr noundef %dev) {
entry:
  call void @outb_p(i32 noundef 0, i32 noundef 0)
  ret void
}

define dso_local void @ldv_EMGentry_exit_tlan_exit_14_2(ptr noundef %arg0) {
entry:
  call void @tlan_exit()
  ret void
}

define dso_local void @ldv_entry_EMGentry_14(i32 noundef %arg0) {
entry:
  call void @ldv_assume()
  call void @ldv_EMGentry_exit_tlan_exit_14_2(ptr noundef null)
  call void @ldv_check_final_state()
  call void @ldv_stop()
  ret void
}

declare void @ldv_assume(...) #0

declare void @ldv_stop(...) #0

define dso_local void @main() {
entry:
  call void @ldv_entry_EMGentry_14(i32 noundef 0)
  ret void
}

define dso_local void @ldv_unregister_netdev(i32 noundef %arg0, i32 noundef %arg1) {
entry:
  %netdev_ops = getelementptr inbounds %struct.net_device, ptr undef, i32 0, i32 0
  %0 = load ptr, ptr %netdev_ops, align 8
  %ndo_stop = getelementptr inbounds %struct.net_device_ops, ptr %0, i32 0, i32 0
  %1 = load ptr, ptr %ndo_stop, align 8
  call void @ldv_unregister_netdev_stop_11_2(ptr noundef %1, ptr noundef undef)
  ret void
}

define dso_local void @ldv_unregister_netdev_stop_11_2(ptr noundef %arg0, ptr noundef %arg1) {
entry:
  %call = call i32 @tlan_close(i32 noundef 0)
  ret void
}

define dso_local void @ldv_unregister_netdev_74(ptr noundef %ldv_func_arg1) {
entry:
  call void @ldv_unregister_netdev(i32 noundef 0, i32 noundef 0)
  ret void
}

define dso_local void @ldv_check_final_state() {
entry:
  %0 = load i32, ptr @ldv_spin__xmit_lock_of_netdev_queue, align 4
  %cmp = icmp eq i32 %0, 1
  %conv = zext i1 %cmp to i32
  call void @ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(i32 noundef %conv)
  %1 = load i32, ptr @ldv_spin_addr_list_lock_of_net_device, align 4
  %cmp1 = icmp eq i32 %1, 1
  %conv2 = zext i1 %cmp1 to i32
  call void @ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(i32 noundef %conv2)
  ret void
}

define dso_local void @ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(i32 noundef %expr) {
entry:
  %tobool = icmp ne i32 %expr, 0
  br i1 %tobool, label %if.end, label %if.then

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error() #2
  unreachable

if.end:                                           ; preds = %entry
  ret void
}

; Function Attrs: noreturn
declare void @__VERIFIER_error(...) #1
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





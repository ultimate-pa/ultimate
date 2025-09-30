; #Safe
; ModuleID = 'c5/bug-undeclared-function-symbol.c'
source_filename = "c5/bug-undeclared-function-symbol.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

%struct.net_device = type { ptr }
%struct.net_device_ops = type { ptr }

@tlan_have_eisa = dso_local global i32 0, align 4
@ldv_spin__xmit_lock_of_netdev_queue = dso_local global i32 1, align 4
@ldv_spin_addr_list_lock_of_net_device = dso_local global i32 1, align 4

define dso_local void @outb_p(i32 noundef %value, i32 noundef %port) #0 {
entry:
  %value.addr = alloca i32, align 4
  %port.addr = alloca i32, align 4
  store i32 %value, ptr %value.addr, align 4
  store i32 %port, ptr %port.addr, align 4
  ret void
}

define dso_local void @tlan_stop(ptr noundef %dev) #0 {
entry:
  %dev.addr = alloca ptr, align 8
  store ptr %dev, ptr %dev.addr, align 8
  %0 = load ptr, ptr %dev.addr, align 8
  call void @tlan_reset_adapter(ptr noundef %0)
  ret void
}

define dso_local void @tlan_eisa_cleanup() #0 {
entry:
  %dev = alloca ptr, align 8
  br label %ldv_43677

ldv_43676:                                        ; preds = %if.then
  %0 = load ptr, ptr %dev, align 8
  call void @ldv_unregister_netdev_74(ptr noundef %0)
  br label %ldv_43677

ldv_43677:                                        ; preds = %ldv_43676, %entry
  %1 = load i32, ptr @tlan_have_eisa, align 4
  %tobool = icmp ne i32 %1, 0
  br i1 %tobool, label %if.then, label %if.else

if.then:                                          ; preds = %ldv_43677
  br label %ldv_43676

if.else:                                          ; preds = %ldv_43677
  br label %if.end

if.end:                                           ; preds = %if.else
  ret void
}

define dso_local void @tlan_exit() #0 {
entry:
  call void @tlan_eisa_cleanup()
  ret void
}

define dso_local i32 @tlan_close(i32 noundef %dev) #0 {
entry:
  %dev.addr = alloca i32, align 4
  store i32 %dev, ptr %dev.addr, align 4
  call void @tlan_stop(ptr noundef null)
  ret i32 0
}

define dso_local void @tlan_reset_adapter(ptr noundef %dev) #0 {
entry:
  %dev.addr = alloca ptr, align 8
  store ptr %dev, ptr %dev.addr, align 8
  call void @outb_p(i32 noundef 0, i32 noundef 0)
  ret void
}

define dso_local void @ldv_EMGentry_exit_tlan_exit_14_2(ptr noundef %arg0) #0 {
entry:
  %arg0.addr = alloca ptr, align 8
  store ptr %arg0, ptr %arg0.addr, align 8
  call void @tlan_exit()
  ret void
}

define dso_local void @ldv_entry_EMGentry_14(i32 noundef %arg0) #0 {
entry:
  %arg0.addr = alloca i32, align 4
  store i32 %arg0, ptr %arg0.addr, align 4
  call void @ldv_assume()
  call void @ldv_EMGentry_exit_tlan_exit_14_2(ptr noundef null)
  call void @ldv_check_final_state()
  call void @ldv_stop()
  ret void
}

declare void @ldv_assume(...) #1

declare void @ldv_stop(...) #1

define dso_local void @main() #0 {
entry:
  call void @ldv_entry_EMGentry_14(i32 noundef 0)
  ret void
}

define dso_local void @ldv_unregister_netdev(i32 noundef %arg0, i32 noundef %arg1) #0 {
entry:
  %arg0.addr = alloca i32, align 4
  %arg1.addr = alloca i32, align 4
  %ldv_11_netdev_net_device = alloca ptr, align 8
  store i32 %arg0, ptr %arg0.addr, align 4
  store i32 %arg1, ptr %arg1.addr, align 4
  %0 = load ptr, ptr %ldv_11_netdev_net_device, align 8
  %netdev_ops = getelementptr inbounds %struct.net_device, ptr %0, i32 0, i32 0
  %1 = load ptr, ptr %netdev_ops, align 8
  %ndo_stop = getelementptr inbounds %struct.net_device_ops, ptr %1, i32 0, i32 0
  %2 = load ptr, ptr %ndo_stop, align 8
  %3 = load ptr, ptr %ldv_11_netdev_net_device, align 8
  call void @ldv_unregister_netdev_stop_11_2(ptr noundef %2, ptr noundef %3)
  ret void
}

define dso_local void @ldv_unregister_netdev_stop_11_2(ptr noundef %arg0, ptr noundef %arg1) #0 {
entry:
  %arg0.addr = alloca ptr, align 8
  %arg1.addr = alloca ptr, align 8
  store ptr %arg0, ptr %arg0.addr, align 8
  store ptr %arg1, ptr %arg1.addr, align 8
  %call = call i32 @tlan_close(i32 noundef 0)
  ret void
}

define dso_local void @ldv_unregister_netdev_74(ptr noundef %ldv_func_arg1) #0 {
entry:
  %ldv_func_arg1.addr = alloca ptr, align 8
  store ptr %ldv_func_arg1, ptr %ldv_func_arg1.addr, align 8
  call void @ldv_unregister_netdev(i32 noundef 0, i32 noundef 0)
  ret void
}

define dso_local void @ldv_check_final_state() #0 {
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

define dso_local void @ldv_assert_linux_kernel_locking_spinlock__one_thread_locked_at_exit(i32 noundef %expr) #0 {
entry:
  %expr.addr = alloca i32, align 4
  store i32 %expr, ptr %expr.addr, align 4
  %0 = load i32, ptr %expr.addr, align 4
  %tobool = icmp ne i32 %0, 0
  br i1 %tobool, label %if.else, label %if.then

if.then:                                          ; preds = %entry
  call void @__VERIFIER_error() #3
  unreachable

if.else:                                          ; preds = %entry
  br label %if.end

if.end:                                           ; preds = %if.else
  ret void
}

; Function Attrs: noreturn
declare void @__VERIFIER_error(...) #2
!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}





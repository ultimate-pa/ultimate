extern void __VERIFIER_error() __attribute__ ((__noreturn__));

typedef signed char __s8;
typedef unsigned char __u8;
typedef short __s16;
typedef unsigned short __u16;
typedef int __s32;
typedef unsigned int __u32;
typedef long long __s64;
typedef unsigned long long __u64;
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef long long s64;
typedef unsigned long long u64;
typedef unsigned short umode_t;
typedef unsigned int __kernel_mode_t;
typedef int __kernel_pid_t;
typedef unsigned int __kernel_uid_t;
typedef unsigned int __kernel_gid_t;
typedef unsigned long __kernel_size_t;
typedef long __kernel_ssize_t;
typedef long __kernel_time_t;
typedef long __kernel_clock_t;
typedef int __kernel_timer_t;
typedef int __kernel_clockid_t;
typedef long long __kernel_loff_t;
typedef __kernel_uid_t __kernel_uid32_t;
typedef __kernel_gid_t __kernel_gid32_t;
typedef __u32 __kernel_dev_t;
typedef __kernel_dev_t dev_t;
typedef __kernel_mode_t mode_t;
typedef __kernel_pid_t pid_t;
typedef __kernel_clockid_t clockid_t;
typedef _Bool bool;
typedef __kernel_uid32_t uid_t;
typedef __kernel_gid32_t gid_t;
typedef __kernel_loff_t loff_t;
typedef __kernel_size_t size_t;
typedef __kernel_ssize_t ssize_t;
typedef __kernel_time_t time_t;
typedef __s32 int32_t;
typedef __u8 uint8_t;
typedef __u32 uint32_t;
typedef unsigned long sector_t;
typedef unsigned long blkcnt_t;
typedef u64 dma_addr_t;
typedef __u16 __le16;
typedef __u16 __be16;
typedef __u32 __be32;
typedef unsigned int gfp_t;
typedef unsigned int fmode_t;
struct __anonstruct_atomic_t_7 {
   int counter ;
};
typedef struct __anonstruct_atomic_t_7 atomic_t;
struct __anonstruct_atomic64_t_8 {
   long counter ;
};
typedef struct __anonstruct_atomic64_t_8 atomic64_t;
struct list_head {
   struct list_head *next ;
   struct list_head *prev ;
};
struct hlist_node;
struct hlist_node;
struct hlist_head {
   struct hlist_node *first ;
};
struct hlist_node {
   struct hlist_node *next ;
   struct hlist_node **pprev ;
};
struct module;
struct module;
struct module;
typedef void (*ctor_fn_t)(void);
struct bug_entry {
   int bug_addr_disp ;
   int file_disp ;
   unsigned short line ;
   unsigned short flags ;
};
struct completion;
struct completion;
struct completion;
struct pt_regs;
struct pt_regs;
struct pt_regs;
struct pid;
struct pid;
struct pid;
struct timespec;
struct timespec;
struct timespec;
struct page;
struct page;
struct page;
struct task_struct;
struct task_struct;
struct task_struct;
struct task_struct;
struct mm_struct;
struct mm_struct;
struct mm_struct;
struct pt_regs {
   unsigned long r15 ;
   unsigned long r14 ;
   unsigned long r13 ;
   unsigned long r12 ;
   unsigned long bp ;
   unsigned long bx ;
   unsigned long r11 ;
   unsigned long r10 ;
   unsigned long r9 ;
   unsigned long r8 ;
   unsigned long ax ;
   unsigned long cx ;
   unsigned long dx ;
   unsigned long si ;
   unsigned long di ;
   unsigned long orig_ax ;
   unsigned long ip ;
   unsigned long cs ;
   unsigned long flags ;
   unsigned long sp ;
   unsigned long ss ;
};
struct task_struct;
struct kernel_vm86_regs {
   struct pt_regs pt ;
   unsigned short es ;
   unsigned short __esh ;
   unsigned short ds ;
   unsigned short __dsh ;
   unsigned short fs ;
   unsigned short __fsh ;
   unsigned short gs ;
   unsigned short __gsh ;
};
union __anonunion____missing_field_name_14 {
   struct pt_regs *regs ;
   struct kernel_vm86_regs *vm86 ;
};
struct math_emu_info {
   long ___orig_eip ;
   union __anonunion____missing_field_name_14 __annonCompField5 ;
};
struct task_struct;
typedef unsigned long pgdval_t;
typedef unsigned long pgprotval_t;
struct pgprot {
   pgprotval_t pgprot ;
};
typedef struct pgprot pgprot_t;
struct __anonstruct_pgd_t_17 {
   pgdval_t pgd ;
};
typedef struct __anonstruct_pgd_t_17 pgd_t;
typedef struct page *pgtable_t;
struct file;
struct file;
struct file;
struct seq_file;
struct seq_file;
struct seq_file;
struct __anonstruct____missing_field_name_22 {
   unsigned int a ;
   unsigned int b ;
};
struct __anonstruct____missing_field_name_23 {
   u16 limit0 ;
   u16 base0 ;
   unsigned int base1 : 8 ;
   unsigned int type : 4 ;
   unsigned int s : 1 ;
   unsigned int dpl : 2 ;
   unsigned int p : 1 ;
   unsigned int limit : 4 ;
   unsigned int avl : 1 ;
   unsigned int l : 1 ;
   unsigned int d : 1 ;
   unsigned int g : 1 ;
   unsigned int base2 : 8 ;
};
union __anonunion____missing_field_name_21 {
   struct __anonstruct____missing_field_name_22 __annonCompField7 ;
   struct __anonstruct____missing_field_name_23 __annonCompField8 ;
};
struct desc_struct {
   union __anonunion____missing_field_name_21 __annonCompField9 ;
} __attribute__((__packed__)) ;
struct page;
struct thread_struct;
struct thread_struct;
struct thread_struct;
struct mm_struct;
struct desc_struct;
struct task_struct;
struct cpumask;
struct cpumask;
struct cpumask;
struct arch_spinlock;
struct arch_spinlock;
struct arch_spinlock;
struct cpumask {
   unsigned long bits[((4096UL + 8UL * sizeof(long )) - 1UL) / (8UL * sizeof(long ))] ;
};
typedef struct cpumask cpumask_t;
typedef struct cpumask *cpumask_var_t;
struct task_struct;
struct pt_regs;
struct i387_fsave_struct {
   u32 cwd ;
   u32 swd ;
   u32 twd ;
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
   u32 st_space[20] ;
   u32 status ;
};
struct __anonstruct____missing_field_name_31 {
   u64 rip ;
   u64 rdp ;
};
struct __anonstruct____missing_field_name_32 {
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
};
union __anonunion____missing_field_name_30 {
   struct __anonstruct____missing_field_name_31 __annonCompField12 ;
   struct __anonstruct____missing_field_name_32 __annonCompField13 ;
};
union __anonunion____missing_field_name_33 {
   u32 padding1[12] ;
   u32 sw_reserved[12] ;
};
struct i387_fxsave_struct {
   u16 cwd ;
   u16 swd ;
   u16 twd ;
   u16 fop ;
   union __anonunion____missing_field_name_30 __annonCompField14 ;
   u32 mxcsr ;
   u32 mxcsr_mask ;
   u32 st_space[32] ;
   u32 xmm_space[64] ;
   u32 padding[12] ;
   union __anonunion____missing_field_name_33 __annonCompField15 ;
} __attribute__((__aligned__(16))) ;
struct i387_soft_struct {
   u32 cwd ;
   u32 swd ;
   u32 twd ;
   u32 fip ;
   u32 fcs ;
   u32 foo ;
   u32 fos ;
   u32 st_space[20] ;
   u8 ftop ;
   u8 changed ;
   u8 lookahead ;
   u8 no_update ;
   u8 rm ;
   u8 alimit ;
   struct math_emu_info *info ;
   u32 entry_eip ;
};
struct ymmh_struct {
   u32 ymmh_space[64] ;
};
struct xsave_hdr_struct {
   u64 xstate_bv ;
   u64 reserved1[2] ;
   u64 reserved2[5] ;
} __attribute__((__packed__)) ;
struct xsave_struct {
   struct i387_fxsave_struct i387 ;
   struct xsave_hdr_struct xsave_hdr ;
   struct ymmh_struct ymmh ;
} __attribute__((__packed__, __aligned__(64))) ;
union thread_xstate {
   struct i387_fsave_struct fsave ;
   struct i387_fxsave_struct fxsave ;
   struct i387_soft_struct soft ;
   struct xsave_struct xsave ;
};
struct fpu {
   union thread_xstate *state ;
};
struct kmem_cache;
struct kmem_cache;
struct perf_event;
struct perf_event;
struct perf_event;
struct thread_struct {
   struct desc_struct tls_array[3] ;
   unsigned long sp0 ;
   unsigned long sp ;
   unsigned long usersp ;
   unsigned short es ;
   unsigned short ds ;
   unsigned short fsindex ;
   unsigned short gsindex ;
   unsigned long fs ;
   unsigned long gs ;
   struct perf_event *ptrace_bps[4] ;
   unsigned long debugreg6 ;
   unsigned long ptrace_dr7 ;
   unsigned long cr2 ;
   unsigned long trap_no ;
   unsigned long error_code ;
   struct fpu fpu ;
   unsigned long *io_bitmap_ptr ;
   unsigned long iopl ;
   unsigned int io_bitmap_max ;
};
typedef atomic64_t atomic_long_t;
struct arch_spinlock {
   unsigned int slock ;
};
typedef struct arch_spinlock arch_spinlock_t;
struct __anonstruct_arch_rwlock_t_36 {
   unsigned int lock ;
};
typedef struct __anonstruct_arch_rwlock_t_36 arch_rwlock_t;
struct task_struct;
struct lockdep_map;
struct lockdep_map;
struct lockdep_map;
struct task_struct;
struct task_struct;
struct task_struct;
struct pt_regs;
struct task_struct;
struct stack_trace {
   unsigned int nr_entries ;
   unsigned int max_entries ;
   unsigned long *entries ;
   int skip ;
};
struct lockdep_subclass_key {
   char __one_byte ;
} __attribute__((__packed__)) ;
struct lock_class_key {
   struct lockdep_subclass_key subkeys[8UL] ;
};
struct lock_class {
   struct list_head hash_entry ;
   struct list_head lock_entry ;
   struct lockdep_subclass_key *key ;
   unsigned int subclass ;
   unsigned int dep_gen_id ;
   unsigned long usage_mask ;
   struct stack_trace usage_traces[13] ;
   struct list_head locks_after ;
   struct list_head locks_before ;
   unsigned int version ;
   unsigned long ops ;
   char const *name ;
   int name_version ;
   unsigned long contention_point[4] ;
   unsigned long contending_point[4] ;
};
struct lockdep_map {
   struct lock_class_key *key ;
   struct lock_class *class_cache[2] ;
   char const *name ;
   int cpu ;
   unsigned long ip ;
};
struct held_lock {
   u64 prev_chain_key ;
   unsigned long acquire_ip ;
   struct lockdep_map *instance ;
   struct lockdep_map *nest_lock ;
   u64 waittime_stamp ;
   u64 holdtime_stamp ;
   unsigned int class_idx : 13 ;
   unsigned int irq_context : 2 ;
   unsigned int trylock : 1 ;
   unsigned int read : 2 ;
   unsigned int check : 2 ;
   unsigned int hardirqs_off : 1 ;
   unsigned int references : 11 ;
};
struct raw_spinlock {
   arch_spinlock_t raw_lock ;
   unsigned int magic ;
   unsigned int owner_cpu ;
   void *owner ;
   struct lockdep_map dep_map ;
};
typedef struct raw_spinlock raw_spinlock_t;
struct __anonstruct____missing_field_name_38 {
   u8 __padding[(unsigned int )(& ((struct raw_spinlock *)0)->dep_map)] ;
   struct lockdep_map dep_map ;
};
union __anonunion____missing_field_name_37 {
   struct raw_spinlock rlock ;
   struct __anonstruct____missing_field_name_38 __annonCompField17 ;
};
struct spinlock {
   union __anonunion____missing_field_name_37 __annonCompField18 ;
};
typedef struct spinlock spinlock_t;
struct __anonstruct_rwlock_t_39 {
   arch_rwlock_t raw_lock ;
   unsigned int magic ;
   unsigned int owner_cpu ;
   void *owner ;
   struct lockdep_map dep_map ;
};
typedef struct __anonstruct_rwlock_t_39 rwlock_t;
struct __wait_queue;
struct __wait_queue;
typedef struct __wait_queue wait_queue_t;
struct __wait_queue {
   unsigned int flags ;
   void *private ;
   int (*func)(wait_queue_t *wait , unsigned int mode , int flags , void *key ) ;
   struct list_head task_list ;
};
struct __wait_queue_head {
   spinlock_t lock ;
   struct list_head task_list ;
};
typedef struct __wait_queue_head wait_queue_head_t;
struct task_struct;
struct seqcount {
   unsigned int sequence ;
};
typedef struct seqcount seqcount_t;
struct __anonstruct_nodemask_t_41 {
   unsigned long bits[(((unsigned long )(1 << 10) + 8UL * sizeof(long )) - 1UL) / (8UL * sizeof(long ))] ;
};
typedef struct __anonstruct_nodemask_t_41 nodemask_t;
struct page;
struct mutex {
   atomic_t count ;
   spinlock_t wait_lock ;
   struct list_head wait_list ;
   struct task_struct *owner ;
   char const *name ;
   void *magic ;
   struct lockdep_map dep_map ;
};
struct mutex_waiter {
   struct list_head list ;
   struct task_struct *task ;
   void *magic ;
};
struct rw_semaphore;
struct rw_semaphore;
struct rw_semaphore;
struct rw_semaphore {
   long count ;
   spinlock_t wait_lock ;
   struct list_head wait_list ;
   struct lockdep_map dep_map ;
};
struct page;
struct device;
struct device;
struct device;
struct device;
struct timespec {
   __kernel_time_t tv_sec ;
   long tv_nsec ;
};
union ktime {
   s64 tv64 ;
};
typedef union ktime ktime_t;
struct tvec_base;
struct tvec_base;
struct tvec_base;
struct timer_list {
   struct list_head entry ;
   unsigned long expires ;
   struct tvec_base *base ;
   void (*function)(unsigned long ) ;
   unsigned long data ;
   int slack ;
   int start_pid ;
   void *start_site ;
   char start_comm[16] ;
   struct lockdep_map lockdep_map ;
};
struct hrtimer;
struct hrtimer;
struct hrtimer;
enum hrtimer_restart;
enum hrtimer_restart;
struct work_struct;
struct work_struct;
struct work_struct;
struct work_struct {
   atomic_long_t data ;
   struct list_head entry ;
   void (*func)(struct work_struct *work ) ;
   struct lockdep_map lockdep_map ;
};
struct delayed_work {
   struct work_struct work ;
   struct timer_list timer ;
};
struct completion {
   unsigned int done ;
   wait_queue_head_t wait ;
};
struct device;
struct pm_message {
   int event ;
};
typedef struct pm_message pm_message_t;
struct dev_pm_ops {
   int (*prepare)(struct device *dev ) ;
   void (*complete)(struct device *dev ) ;
   int (*suspend)(struct device *dev ) ;
   int (*resume)(struct device *dev ) ;
   int (*freeze)(struct device *dev ) ;
   int (*thaw)(struct device *dev ) ;
   int (*poweroff)(struct device *dev ) ;
   int (*restore)(struct device *dev ) ;
   int (*suspend_noirq)(struct device *dev ) ;
   int (*resume_noirq)(struct device *dev ) ;
   int (*freeze_noirq)(struct device *dev ) ;
   int (*thaw_noirq)(struct device *dev ) ;
   int (*poweroff_noirq)(struct device *dev ) ;
   int (*restore_noirq)(struct device *dev ) ;
   int (*runtime_suspend)(struct device *dev ) ;
   int (*runtime_resume)(struct device *dev ) ;
   int (*runtime_idle)(struct device *dev ) ;
};
enum rpm_status {
    RPM_ACTIVE = 0,
    RPM_RESUMING = 1,
    RPM_SUSPENDED = 2,
    RPM_SUSPENDING = 3
} ;
enum rpm_request {
    RPM_REQ_NONE = 0,
    RPM_REQ_IDLE = 1,
    RPM_REQ_SUSPEND = 2,
    RPM_REQ_AUTOSUSPEND = 3,
    RPM_REQ_RESUME = 4
} ;
struct wakeup_source;
struct wakeup_source;
struct wakeup_source;
struct dev_pm_info {
   pm_message_t power_state ;
   unsigned int can_wakeup : 1 ;
   unsigned int async_suspend : 1 ;
   bool is_prepared : 1 ;
   bool is_suspended : 1 ;
   spinlock_t lock ;
   struct list_head entry ;
   struct completion completion ;
   struct wakeup_source *wakeup ;
   struct timer_list suspend_timer ;
   unsigned long timer_expires ;
   struct work_struct work ;
   wait_queue_head_t wait_queue ;
   atomic_t usage_count ;
   atomic_t child_count ;
   unsigned int disable_depth : 3 ;
   unsigned int ignore_children : 1 ;
   unsigned int idle_notification : 1 ;
   unsigned int request_pending : 1 ;
   unsigned int deferred_resume : 1 ;
   unsigned int run_wake : 1 ;
   unsigned int runtime_auto : 1 ;
   unsigned int no_callbacks : 1 ;
   unsigned int irq_safe : 1 ;
   unsigned int use_autosuspend : 1 ;
   unsigned int timer_autosuspends : 1 ;
   enum rpm_request request ;
   enum rpm_status runtime_status ;
   int runtime_error ;
   int autosuspend_delay ;
   unsigned long last_busy ;
   unsigned long active_jiffies ;
   unsigned long suspended_jiffies ;
   unsigned long accounting_timestamp ;
   void *subsys_data ;
};
struct dev_power_domain {
   struct dev_pm_ops ops ;
};
struct __anonstruct_mm_context_t_111 {
   void *ldt ;
   int size ;
   unsigned short ia32_compat ;
   struct mutex lock ;
   void *vdso ;
};
typedef struct __anonstruct_mm_context_t_111 mm_context_t;
struct vm_area_struct;
struct vm_area_struct;
struct vm_area_struct;
struct page;
struct vm_area_struct;
struct sock;
struct sock;
struct sock;
struct kobject;
struct kobject;
struct kobject;
enum kobj_ns_type {
    KOBJ_NS_TYPE_NONE = 0,
    KOBJ_NS_TYPE_NET = 1,
    KOBJ_NS_TYPES = 2
} ;
struct kobj_ns_type_operations {
   enum kobj_ns_type type ;
   void *(*grab_current_ns)(void) ;
   void const *(*netlink_ns)(struct sock *sk ) ;
   void const *(*initial_ns)(void) ;
   void (*drop_ns)(void * ) ;
};
struct kobject;
struct module;
enum kobj_ns_type;
struct attribute {
   char const *name ;
   mode_t mode ;
   struct lock_class_key *key ;
   struct lock_class_key skey ;
};
struct attribute_group {
   char const *name ;
   mode_t (*is_visible)(struct kobject * , struct attribute * , int ) ;
   struct attribute **attrs ;
};
struct file;
struct vm_area_struct;
struct bin_attribute {
   struct attribute attr ;
   size_t size ;
   void *private ;
   ssize_t (*read)(struct file * , struct kobject * , struct bin_attribute * , char * ,
                   loff_t , size_t ) ;
   ssize_t (*write)(struct file * , struct kobject * , struct bin_attribute * , char * ,
                    loff_t , size_t ) ;
   int (*mmap)(struct file * , struct kobject * , struct bin_attribute *attr , struct vm_area_struct *vma ) ;
};
struct sysfs_ops {
   ssize_t (*show)(struct kobject * , struct attribute * , char * ) ;
   ssize_t (*store)(struct kobject * , struct attribute * , char const * , size_t ) ;
};
struct sysfs_dirent;
struct sysfs_dirent;
struct sysfs_dirent;
struct kref {
   atomic_t refcount ;
};
struct kset;
struct kset;
struct kobj_type;
struct kobj_type;
struct kobject {
   char const *name ;
   struct list_head entry ;
   struct kobject *parent ;
   struct kset *kset ;
   struct kobj_type *ktype ;
   struct sysfs_dirent *sd ;
   struct kref kref ;
   unsigned int state_initialized : 1 ;
   unsigned int state_in_sysfs : 1 ;
   unsigned int state_add_uevent_sent : 1 ;
   unsigned int state_remove_uevent_sent : 1 ;
   unsigned int uevent_suppress : 1 ;
};
struct kobj_type {
   void (*release)(struct kobject *kobj ) ;
   struct sysfs_ops const *sysfs_ops ;
   struct attribute **default_attrs ;
   struct kobj_ns_type_operations const *(*child_ns_type)(struct kobject *kobj ) ;
   void const *(*namespace)(struct kobject *kobj ) ;
};
struct kobj_uevent_env {
   char *envp[32] ;
   int envp_idx ;
   char buf[2048] ;
   int buflen ;
};
struct kset_uevent_ops {
   int (* const filter)(struct kset *kset , struct kobject *kobj ) ;
   char const *(* const name)(struct kset *kset , struct kobject *kobj ) ;
   int (* const uevent)(struct kset *kset , struct kobject *kobj , struct kobj_uevent_env *env ) ;
};
struct sock;
struct kset {
   struct list_head list ;
   spinlock_t list_lock ;
   struct kobject kobj ;
   struct kset_uevent_ops const *uevent_ops ;
};
struct kmem_cache_cpu {
   void **freelist ;
   unsigned long tid ;
   struct page *page ;
   int node ;
   unsigned int stat[19] ;
};
struct kmem_cache_node {
   spinlock_t list_lock ;
   unsigned long nr_partial ;
   struct list_head partial ;
   atomic_long_t nr_slabs ;
   atomic_long_t total_objects ;
   struct list_head full ;
};
struct kmem_cache_order_objects {
   unsigned long x ;
};
struct kmem_cache {
   struct kmem_cache_cpu *cpu_slab ;
   unsigned long flags ;
   unsigned long min_partial ;
   int size ;
   int objsize ;
   int offset ;
   struct kmem_cache_order_objects oo ;
   struct kmem_cache_order_objects max ;
   struct kmem_cache_order_objects min ;
   gfp_t allocflags ;
   int refcount ;
   void (*ctor)(void * ) ;
   int inuse ;
   int align ;
   int reserved ;
   char const *name ;
   struct list_head list ;
   struct kobject kobj ;
   int remote_node_defrag_ratio ;
   struct kmem_cache_node *node[1 << 10] ;
};
struct page;
struct block_device;
struct block_device;
struct block_device;
struct rcu_head {
   struct rcu_head *next ;
   void (*func)(struct rcu_head *head ) ;
};
struct hlist_bl_node;
struct hlist_bl_node;
struct hlist_bl_head {
   struct hlist_bl_node *first ;
};
struct hlist_bl_node {
   struct hlist_bl_node *next ;
   struct hlist_bl_node **pprev ;
};
struct nameidata;
struct nameidata;
struct nameidata;
struct path;
struct path;
struct path;
struct vfsmount;
struct vfsmount;
struct vfsmount;
struct qstr {
   unsigned int hash ;
   unsigned int len ;
   unsigned char const *name ;
};
struct inode;
struct inode;
struct dentry_operations;
struct dentry_operations;
struct super_block;
struct super_block;
union __anonunion_d_u_135 {
   struct list_head d_child ;
   struct rcu_head d_rcu ;
};
struct dentry {
   unsigned int d_flags ;
   seqcount_t d_seq ;
   struct hlist_bl_node d_hash ;
   struct dentry *d_parent ;
   struct qstr d_name ;
   struct inode *d_inode ;
   unsigned char d_iname[32] ;
   unsigned int d_count ;
   spinlock_t d_lock ;
   struct dentry_operations const *d_op ;
   struct super_block *d_sb ;
   unsigned long d_time ;
   void *d_fsdata ;
   struct list_head d_lru ;
   union __anonunion_d_u_135 d_u ;
   struct list_head d_subdirs ;
   struct list_head d_alias ;
};
struct dentry_operations {
   int (*d_revalidate)(struct dentry * , struct nameidata * ) ;
   int (*d_hash)(struct dentry const * , struct inode const * , struct qstr * ) ;
   int (*d_compare)(struct dentry const * , struct inode const * , struct dentry const * ,
                    struct inode const * , unsigned int , char const * , struct qstr const * ) ;
   int (*d_delete)(struct dentry const * ) ;
   void (*d_release)(struct dentry * ) ;
   void (*d_iput)(struct dentry * , struct inode * ) ;
   char *(*d_dname)(struct dentry * , char * , int ) ;
   struct vfsmount *(*d_automount)(struct path * ) ;
   int (*d_manage)(struct dentry * , bool ) ;
} __attribute__((__aligned__((1) << (6) ))) ;
struct dentry;
struct vfsmount;
struct path {
   struct vfsmount *mnt ;
   struct dentry *dentry ;
};
struct kstat {
   u64 ino ;
   dev_t dev ;
   umode_t mode ;
   unsigned int nlink ;
   uid_t uid ;
   gid_t gid ;
   dev_t rdev ;
   loff_t size ;
   struct timespec atime ;
   struct timespec mtime ;
   struct timespec ctime ;
   unsigned long blksize ;
   unsigned long long blocks ;
};
struct radix_tree_node;
struct radix_tree_node;
struct radix_tree_root {
   unsigned int height ;
   gfp_t gfp_mask ;
   struct radix_tree_node *rnode ;
};
struct prio_tree_node;
struct prio_tree_node;
struct raw_prio_tree_node {
   struct prio_tree_node *left ;
   struct prio_tree_node *right ;
   struct prio_tree_node *parent ;
};
struct prio_tree_node {
   struct prio_tree_node *left ;
   struct prio_tree_node *right ;
   struct prio_tree_node *parent ;
   unsigned long start ;
   unsigned long last ;
};
struct prio_tree_root {
   struct prio_tree_node *prio_tree_node ;
   unsigned short index_bits ;
   unsigned short raw ;
};
enum pid_type {
    PIDTYPE_PID = 0,
    PIDTYPE_PGID = 1,
    PIDTYPE_SID = 2,
    PIDTYPE_MAX = 3
} ;
struct pid_namespace;
struct pid_namespace;
struct upid {
   int nr ;
   struct pid_namespace *ns ;
   struct hlist_node pid_chain ;
};
struct pid {
   atomic_t count ;
   unsigned int level ;
   struct hlist_head tasks[3] ;
   struct rcu_head rcu ;
   struct upid numbers[1] ;
};
struct pid_link {
   struct hlist_node node ;
   struct pid *pid ;
};
struct pid_namespace;
struct task_struct;
struct kernel_cap_struct {
   __u32 cap[2] ;
};
typedef struct kernel_cap_struct kernel_cap_t;
struct dentry;
struct user_namespace;
struct user_namespace;
struct user_namespace;
struct fiemap_extent {
   __u64 fe_logical ;
   __u64 fe_physical ;
   __u64 fe_length ;
   __u64 fe_reserved64[2] ;
   __u32 fe_flags ;
   __u32 fe_reserved[3] ;
};
struct export_operations;
struct export_operations;
struct export_operations;
struct iovec;
struct iovec;
struct iovec;
struct nameidata;
struct kiocb;
struct kiocb;
struct kiocb;
struct kobject;
struct pipe_inode_info;
struct pipe_inode_info;
struct pipe_inode_info;
struct poll_table_struct;
struct poll_table_struct;
struct poll_table_struct;
struct kstatfs;
struct kstatfs;
struct kstatfs;
struct vm_area_struct;
struct vfsmount;
struct cred;
struct cred;
struct cred;
struct iattr {
   unsigned int ia_valid ;
   umode_t ia_mode ;
   uid_t ia_uid ;
   gid_t ia_gid ;
   loff_t ia_size ;
   struct timespec ia_atime ;
   struct timespec ia_mtime ;
   struct timespec ia_ctime ;
   struct file *ia_file ;
};
struct if_dqinfo {
   __u64 dqi_bgrace ;
   __u64 dqi_igrace ;
   __u32 dqi_flags ;
   __u32 dqi_valid ;
};
struct fs_disk_quota {
   __s8 d_version ;
   __s8 d_flags ;
   __u16 d_fieldmask ;
   __u32 d_id ;
   __u64 d_blk_hardlimit ;
   __u64 d_blk_softlimit ;
   __u64 d_ino_hardlimit ;
   __u64 d_ino_softlimit ;
   __u64 d_bcount ;
   __u64 d_icount ;
   __s32 d_itimer ;
   __s32 d_btimer ;
   __u16 d_iwarns ;
   __u16 d_bwarns ;
   __s32 d_padding2 ;
   __u64 d_rtb_hardlimit ;
   __u64 d_rtb_softlimit ;
   __u64 d_rtbcount ;
   __s32 d_rtbtimer ;
   __u16 d_rtbwarns ;
   __s16 d_padding3 ;
   char d_padding4[8] ;
};
struct fs_qfilestat {
   __u64 qfs_ino ;
   __u64 qfs_nblks ;
   __u32 qfs_nextents ;
};
typedef struct fs_qfilestat fs_qfilestat_t;
struct fs_quota_stat {
   __s8 qs_version ;
   __u16 qs_flags ;
   __s8 qs_pad ;
   fs_qfilestat_t qs_uquota ;
   fs_qfilestat_t qs_gquota ;
   __u32 qs_incoredqs ;
   __s32 qs_btimelimit ;
   __s32 qs_itimelimit ;
   __s32 qs_rtbtimelimit ;
   __u16 qs_bwarnlimit ;
   __u16 qs_iwarnlimit ;
};
struct dquot;
struct dquot;
struct dquot;
typedef __kernel_uid32_t qid_t;
typedef long long qsize_t;
struct mem_dqblk {
   qsize_t dqb_bhardlimit ;
   qsize_t dqb_bsoftlimit ;
   qsize_t dqb_curspace ;
   qsize_t dqb_rsvspace ;
   qsize_t dqb_ihardlimit ;
   qsize_t dqb_isoftlimit ;
   qsize_t dqb_curinodes ;
   time_t dqb_btime ;
   time_t dqb_itime ;
};
struct quota_format_type;
struct quota_format_type;
struct quota_format_type;
struct mem_dqinfo {
   struct quota_format_type *dqi_format ;
   int dqi_fmt_id ;
   struct list_head dqi_dirty_list ;
   unsigned long dqi_flags ;
   unsigned int dqi_bgrace ;
   unsigned int dqi_igrace ;
   qsize_t dqi_maxblimit ;
   qsize_t dqi_maxilimit ;
   void *dqi_priv ;
};
struct super_block;
struct dquot {
   struct hlist_node dq_hash ;
   struct list_head dq_inuse ;
   struct list_head dq_free ;
   struct list_head dq_dirty ;
   struct mutex dq_lock ;
   atomic_t dq_count ;
   wait_queue_head_t dq_wait_unused ;
   struct super_block *dq_sb ;
   unsigned int dq_id ;
   loff_t dq_off ;
   unsigned long dq_flags ;
   short dq_type ;
   struct mem_dqblk dq_dqb ;
};
struct quota_format_ops {
   int (*check_quota_file)(struct super_block *sb , int type ) ;
   int (*read_file_info)(struct super_block *sb , int type ) ;
   int (*write_file_info)(struct super_block *sb , int type ) ;
   int (*free_file_info)(struct super_block *sb , int type ) ;
   int (*read_dqblk)(struct dquot *dquot ) ;
   int (*commit_dqblk)(struct dquot *dquot ) ;
   int (*release_dqblk)(struct dquot *dquot ) ;
};
struct dquot_operations {
   int (*write_dquot)(struct dquot * ) ;
   struct dquot *(*alloc_dquot)(struct super_block * , int ) ;
   void (*destroy_dquot)(struct dquot * ) ;
   int (*acquire_dquot)(struct dquot * ) ;
   int (*release_dquot)(struct dquot * ) ;
   int (*mark_dirty)(struct dquot * ) ;
   int (*write_info)(struct super_block * , int ) ;
   qsize_t *(*get_reserved_space)(struct inode * ) ;
};
struct path;
struct quotactl_ops {
   int (*quota_on)(struct super_block * , int , int , struct path * ) ;
   int (*quota_on_meta)(struct super_block * , int , int ) ;
   int (*quota_off)(struct super_block * , int ) ;
   int (*quota_sync)(struct super_block * , int , int ) ;
   int (*get_info)(struct super_block * , int , struct if_dqinfo * ) ;
   int (*set_info)(struct super_block * , int , struct if_dqinfo * ) ;
   int (*get_dqblk)(struct super_block * , int , qid_t , struct fs_disk_quota * ) ;
   int (*set_dqblk)(struct super_block * , int , qid_t , struct fs_disk_quota * ) ;
   int (*get_xstate)(struct super_block * , struct fs_quota_stat * ) ;
   int (*set_xstate)(struct super_block * , unsigned int , int ) ;
};
struct quota_format_type {
   int qf_fmt_id ;
   struct quota_format_ops const *qf_ops ;
   struct module *qf_owner ;
   struct quota_format_type *qf_next ;
};
struct quota_info {
   unsigned int flags ;
   struct mutex dqio_mutex ;
   struct mutex dqonoff_mutex ;
   struct rw_semaphore dqptr_sem ;
   struct inode *files[2] ;
   struct mem_dqinfo info[2] ;
   struct quota_format_ops const *ops[2] ;
};
struct page;
struct address_space;
struct address_space;
struct address_space;
struct writeback_control;
struct writeback_control;
struct writeback_control;
union __anonunion_arg_143 {
   char *buf ;
   void *data ;
};
struct __anonstruct_read_descriptor_t_142 {
   size_t written ;
   size_t count ;
   union __anonunion_arg_143 arg ;
   int error ;
};
typedef struct __anonstruct_read_descriptor_t_142 read_descriptor_t;
struct address_space_operations {
   int (*writepage)(struct page *page , struct writeback_control *wbc ) ;
   int (*readpage)(struct file * , struct page * ) ;
   int (*writepages)(struct address_space * , struct writeback_control * ) ;
   int (*set_page_dirty)(struct page *page ) ;
   int (*readpages)(struct file *filp , struct address_space *mapping , struct list_head *pages ,
                    unsigned int nr_pages ) ;
   int (*write_begin)(struct file * , struct address_space *mapping , loff_t pos ,
                      unsigned int len , unsigned int flags , struct page **pagep ,
                      void **fsdata ) ;
   int (*write_end)(struct file * , struct address_space *mapping , loff_t pos , unsigned int len ,
                    unsigned int copied , struct page *page , void *fsdata ) ;
   sector_t (*bmap)(struct address_space * , sector_t ) ;
   void (*invalidatepage)(struct page * , unsigned long ) ;
   int (*releasepage)(struct page * , gfp_t ) ;
   void (*freepage)(struct page * ) ;
   ssize_t (*direct_IO)(int , struct kiocb * , struct iovec const *iov , loff_t offset ,
                        unsigned long nr_segs ) ;
   int (*get_xip_mem)(struct address_space * , unsigned long , int , void ** , unsigned long * ) ;
   int (*migratepage)(struct address_space * , struct page * , struct page * ) ;
   int (*launder_page)(struct page * ) ;
   int (*is_partially_uptodate)(struct page * , read_descriptor_t * , unsigned long ) ;
   int (*error_remove_page)(struct address_space * , struct page * ) ;
};
struct backing_dev_info;
struct backing_dev_info;
struct backing_dev_info;
struct address_space {
   struct inode *host ;
   struct radix_tree_root page_tree ;
   spinlock_t tree_lock ;
   unsigned int i_mmap_writable ;
   struct prio_tree_root i_mmap ;
   struct list_head i_mmap_nonlinear ;
   struct mutex i_mmap_mutex ;
   unsigned long nrpages ;
   unsigned long writeback_index ;
   struct address_space_operations const *a_ops ;
   unsigned long flags ;
   struct backing_dev_info *backing_dev_info ;
   spinlock_t private_lock ;
   struct list_head private_list ;
   struct address_space *assoc_mapping ;
} __attribute__((__aligned__(sizeof(long )))) ;
struct hd_struct;
struct hd_struct;
struct gendisk;
struct gendisk;
struct block_device {
   dev_t bd_dev ;
   int bd_openers ;
   struct inode *bd_inode ;
   struct super_block *bd_super ;
   struct mutex bd_mutex ;
   struct list_head bd_inodes ;
   void *bd_claiming ;
   void *bd_holder ;
   int bd_holders ;
   bool bd_write_holder ;
   struct list_head bd_holder_disks ;
   struct block_device *bd_contains ;
   unsigned int bd_block_size ;
   struct hd_struct *bd_part ;
   unsigned int bd_part_count ;
   int bd_invalidated ;
   struct gendisk *bd_disk ;
   struct list_head bd_list ;
   unsigned long bd_private ;
   int bd_fsfreeze_count ;
   struct mutex bd_fsfreeze_mutex ;
};
struct posix_acl;
struct posix_acl;
struct posix_acl;
struct inode_operations;
struct inode_operations;
union __anonunion____missing_field_name_144 {
   struct list_head i_dentry ;
   struct rcu_head i_rcu ;
};
struct file_operations;
struct file_operations;
struct file_lock;
struct file_lock;
struct cdev;
struct cdev;
union __anonunion____missing_field_name_145 {
   struct pipe_inode_info *i_pipe ;
   struct block_device *i_bdev ;
   struct cdev *i_cdev ;
};
struct inode {
   umode_t i_mode ;
   uid_t i_uid ;
   gid_t i_gid ;
   struct inode_operations const *i_op ;
   struct super_block *i_sb ;
   spinlock_t i_lock ;
   unsigned int i_flags ;
   unsigned long i_state ;
   void *i_security ;
   struct mutex i_mutex ;
   unsigned long dirtied_when ;
   struct hlist_node i_hash ;
   struct list_head i_wb_list ;
   struct list_head i_lru ;
   struct list_head i_sb_list ;
   union __anonunion____missing_field_name_144 __annonCompField29 ;
   unsigned long i_ino ;
   atomic_t i_count ;
   unsigned int i_nlink ;
   dev_t i_rdev ;
   unsigned int i_blkbits ;
   u64 i_version ;
   loff_t i_size ;
   struct timespec i_atime ;
   struct timespec i_mtime ;
   struct timespec i_ctime ;
   blkcnt_t i_blocks ;
   unsigned short i_bytes ;
   struct rw_semaphore i_alloc_sem ;
   struct file_operations const *i_fop ;
   struct file_lock *i_flock ;
   struct address_space *i_mapping ;
   struct address_space i_data ;
   struct dquot *i_dquot[2] ;
   struct list_head i_devices ;
   union __anonunion____missing_field_name_145 __annonCompField30 ;
   __u32 i_generation ;
   __u32 i_fsnotify_mask ;
   struct hlist_head i_fsnotify_marks ;
   atomic_t i_readcount ;
   atomic_t i_writecount ;
   struct posix_acl *i_acl ;
   struct posix_acl *i_default_acl ;
   void *i_private ;
};
struct fown_struct {
   rwlock_t lock ;
   struct pid *pid ;
   enum pid_type pid_type ;
   uid_t uid ;
   uid_t euid ;
   int signum ;
};
struct file_ra_state {
   unsigned long start ;
   unsigned int size ;
   unsigned int async_size ;
   unsigned int ra_pages ;
   unsigned int mmap_miss ;
   loff_t prev_pos ;
};
union __anonunion_f_u_146 {
   struct list_head fu_list ;
   struct rcu_head fu_rcuhead ;
};
struct file {
   union __anonunion_f_u_146 f_u ;
   struct path f_path ;
   struct file_operations const *f_op ;
   spinlock_t f_lock ;
   int f_sb_list_cpu ;
   atomic_long_t f_count ;
   unsigned int f_flags ;
   fmode_t f_mode ;
   loff_t f_pos ;
   struct fown_struct f_owner ;
   struct cred const *f_cred ;
   struct file_ra_state f_ra ;
   u64 f_version ;
   void *f_security ;
   void *private_data ;
   struct list_head f_ep_links ;
   struct address_space *f_mapping ;
   unsigned long f_mnt_write_state ;
};
struct files_struct;
struct files_struct;
typedef struct files_struct *fl_owner_t;
struct file_lock_operations {
   void (*fl_copy_lock)(struct file_lock * , struct file_lock * ) ;
   void (*fl_release_private)(struct file_lock * ) ;
};
struct lock_manager_operations {
   int (*fl_compare_owner)(struct file_lock * , struct file_lock * ) ;
   void (*fl_notify)(struct file_lock * ) ;
   int (*fl_grant)(struct file_lock * , struct file_lock * , int ) ;
   void (*fl_release_private)(struct file_lock * ) ;
   void (*fl_break)(struct file_lock * ) ;
   int (*fl_change)(struct file_lock ** , int ) ;
};
struct nlm_lockowner;
struct nlm_lockowner;
struct nlm_lockowner;
struct nfs_lock_info {
   u32 state ;
   struct nlm_lockowner *owner ;
   struct list_head list ;
};
struct nfs4_lock_state;
struct nfs4_lock_state;
struct nfs4_lock_state;
struct nfs4_lock_info {
   struct nfs4_lock_state *owner ;
};
struct fasync_struct;
struct fasync_struct;
struct __anonstruct_afs_148 {
   struct list_head link ;
   int state ;
};
union __anonunion_fl_u_147 {
   struct nfs_lock_info nfs_fl ;
   struct nfs4_lock_info nfs4_fl ;
   struct __anonstruct_afs_148 afs ;
};
struct file_lock {
   struct file_lock *fl_next ;
   struct list_head fl_link ;
   struct list_head fl_block ;
   fl_owner_t fl_owner ;
   unsigned char fl_flags ;
   unsigned char fl_type ;
   unsigned int fl_pid ;
   struct pid *fl_nspid ;
   wait_queue_head_t fl_wait ;
   struct file *fl_file ;
   loff_t fl_start ;
   loff_t fl_end ;
   struct fasync_struct *fl_fasync ;
   unsigned long fl_break_time ;
   struct file_lock_operations const *fl_ops ;
   struct lock_manager_operations const *fl_lmops ;
   union __anonunion_fl_u_147 fl_u ;
};
struct fasync_struct {
   spinlock_t fa_lock ;
   int magic ;
   int fa_fd ;
   struct fasync_struct *fa_next ;
   struct file *fa_file ;
   struct rcu_head fa_rcu ;
};
struct file_system_type;
struct file_system_type;
struct super_operations;
struct super_operations;
struct xattr_handler;
struct xattr_handler;
struct mtd_info;
struct mtd_info;
struct super_block {
   struct list_head s_list ;
   dev_t s_dev ;
   unsigned char s_dirt ;
   unsigned char s_blocksize_bits ;
   unsigned long s_blocksize ;
   loff_t s_maxbytes ;
   struct file_system_type *s_type ;
   struct super_operations const *s_op ;
   struct dquot_operations const *dq_op ;
   struct quotactl_ops const *s_qcop ;
   struct export_operations const *s_export_op ;
   unsigned long s_flags ;
   unsigned long s_magic ;
   struct dentry *s_root ;
   struct rw_semaphore s_umount ;
   struct mutex s_lock ;
   int s_count ;
   atomic_t s_active ;
   void *s_security ;
   struct xattr_handler const **s_xattr ;
   struct list_head s_inodes ;
   struct hlist_bl_head s_anon ;
   struct list_head *s_files ;
   struct list_head s_dentry_lru ;
   int s_nr_dentry_unused ;
   struct block_device *s_bdev ;
   struct backing_dev_info *s_bdi ;
   struct mtd_info *s_mtd ;
   struct list_head s_instances ;
   struct quota_info s_dquot ;
   int s_frozen ;
   wait_queue_head_t s_wait_unfrozen ;
   char s_id[32] ;
   u8 s_uuid[16] ;
   void *s_fs_info ;
   fmode_t s_mode ;
   u32 s_time_gran ;
   struct mutex s_vfs_rename_mutex ;
   char *s_subtype ;
   char *s_options ;
   struct dentry_operations const *s_d_op ;
   int cleancache_poolid ;
};
struct fiemap_extent_info {
   unsigned int fi_flags ;
   unsigned int fi_extents_mapped ;
   unsigned int fi_extents_max ;
   struct fiemap_extent *fi_extents_start ;
};
struct file_operations {
   struct module *owner ;
   loff_t (*llseek)(struct file * , loff_t , int ) ;
   ssize_t (*read)(struct file * , char * , size_t , loff_t * ) ;
   ssize_t (*write)(struct file * , char const * , size_t , loff_t * ) ;
   ssize_t (*aio_read)(struct kiocb * , struct iovec const * , unsigned long ,
                       loff_t ) ;
   ssize_t (*aio_write)(struct kiocb * , struct iovec const * , unsigned long ,
                        loff_t ) ;
   int (*readdir)(struct file * , void * , int (*)(void * , char const * , int ,
                                                   loff_t , u64 , unsigned int ) ) ;
   unsigned int (*poll)(struct file * , struct poll_table_struct * ) ;
   long (*unlocked_ioctl)(struct file * , unsigned int , unsigned long ) ;
   long (*compat_ioctl)(struct file * , unsigned int , unsigned long ) ;
   int (*mmap)(struct file * , struct vm_area_struct * ) ;
   int (*open)(struct inode * , struct file * ) ;
   int (*flush)(struct file * , fl_owner_t id ) ;
   int (*release)(struct inode * , struct file * ) ;
   int (*fsync)(struct file * , int datasync ) ;
   int (*aio_fsync)(struct kiocb * , int datasync ) ;
   int (*fasync)(int , struct file * , int ) ;
   int (*lock)(struct file * , int , struct file_lock * ) ;
   ssize_t (*sendpage)(struct file * , struct page * , int , size_t , loff_t * ,
                       int ) ;
   unsigned long (*get_unmapped_area)(struct file * , unsigned long , unsigned long ,
                                      unsigned long , unsigned long ) ;
   int (*check_flags)(int ) ;
   int (*flock)(struct file * , int , struct file_lock * ) ;
   ssize_t (*splice_write)(struct pipe_inode_info * , struct file * , loff_t * , size_t ,
                           unsigned int ) ;
   ssize_t (*splice_read)(struct file * , loff_t * , struct pipe_inode_info * , size_t ,
                          unsigned int ) ;
   int (*setlease)(struct file * , long , struct file_lock ** ) ;
   long (*fallocate)(struct file *file , int mode , loff_t offset , loff_t len ) ;
};
struct inode_operations {
   struct dentry *(*lookup)(struct inode * , struct dentry * , struct nameidata * ) ;
   void *(*follow_link)(struct dentry * , struct nameidata * ) ;
   int (*permission)(struct inode * , int , unsigned int ) ;
   int (*check_acl)(struct inode * , int , unsigned int ) ;
   int (*readlink)(struct dentry * , char * , int ) ;
   void (*put_link)(struct dentry * , struct nameidata * , void * ) ;
   int (*create)(struct inode * , struct dentry * , int , struct nameidata * ) ;
   int (*link)(struct dentry * , struct inode * , struct dentry * ) ;
   int (*unlink)(struct inode * , struct dentry * ) ;
   int (*symlink)(struct inode * , struct dentry * , char const * ) ;
   int (*mkdir)(struct inode * , struct dentry * , int ) ;
   int (*rmdir)(struct inode * , struct dentry * ) ;
   int (*mknod)(struct inode * , struct dentry * , int , dev_t ) ;
   int (*rename)(struct inode * , struct dentry * , struct inode * , struct dentry * ) ;
   void (*truncate)(struct inode * ) ;
   int (*setattr)(struct dentry * , struct iattr * ) ;
   int (*getattr)(struct vfsmount *mnt , struct dentry * , struct kstat * ) ;
   int (*setxattr)(struct dentry * , char const * , void const * , size_t , int ) ;
   ssize_t (*getxattr)(struct dentry * , char const * , void * , size_t ) ;
   ssize_t (*listxattr)(struct dentry * , char * , size_t ) ;
   int (*removexattr)(struct dentry * , char const * ) ;
   void (*truncate_range)(struct inode * , loff_t , loff_t ) ;
   int (*fiemap)(struct inode * , struct fiemap_extent_info * , u64 start , u64 len ) ;
} __attribute__((__aligned__((1) << (6) ))) ;
struct seq_file;
struct super_operations {
   struct inode *(*alloc_inode)(struct super_block *sb ) ;
   void (*destroy_inode)(struct inode * ) ;
   void (*dirty_inode)(struct inode * , int flags ) ;
   int (*write_inode)(struct inode * , struct writeback_control *wbc ) ;
   int (*drop_inode)(struct inode * ) ;
   void (*evict_inode)(struct inode * ) ;
   void (*put_super)(struct super_block * ) ;
   void (*write_super)(struct super_block * ) ;
   int (*sync_fs)(struct super_block *sb , int wait ) ;
   int (*freeze_fs)(struct super_block * ) ;
   int (*unfreeze_fs)(struct super_block * ) ;
   int (*statfs)(struct dentry * , struct kstatfs * ) ;
   int (*remount_fs)(struct super_block * , int * , char * ) ;
   void (*umount_begin)(struct super_block * ) ;
   int (*show_options)(struct seq_file * , struct vfsmount * ) ;
   int (*show_devname)(struct seq_file * , struct vfsmount * ) ;
   int (*show_path)(struct seq_file * , struct vfsmount * ) ;
   int (*show_stats)(struct seq_file * , struct vfsmount * ) ;
   ssize_t (*quota_read)(struct super_block * , int , char * , size_t , loff_t ) ;
   ssize_t (*quota_write)(struct super_block * , int , char const * , size_t ,
                          loff_t ) ;
   int (*bdev_try_to_free_page)(struct super_block * , struct page * , gfp_t ) ;
};
struct file_system_type {
   char const *name ;
   int fs_flags ;
   struct dentry *(*mount)(struct file_system_type * , int , char const * , void * ) ;
   void (*kill_sb)(struct super_block * ) ;
   struct module *owner ;
   struct file_system_type *next ;
   struct list_head fs_supers ;
   struct lock_class_key s_lock_key ;
   struct lock_class_key s_umount_key ;
   struct lock_class_key s_vfs_rename_key ;
   struct lock_class_key i_lock_key ;
   struct lock_class_key i_mutex_key ;
   struct lock_class_key i_mutex_dir_key ;
   struct lock_class_key i_alloc_sem_key ;
};
typedef unsigned char cc_t;
typedef unsigned int speed_t;
typedef unsigned int tcflag_t;
struct ktermios {
   tcflag_t c_iflag ;
   tcflag_t c_oflag ;
   tcflag_t c_cflag ;
   tcflag_t c_lflag ;
   cc_t c_line ;
   cc_t c_cc[19] ;
   speed_t c_ispeed ;
   speed_t c_ospeed ;
};
struct winsize {
   unsigned short ws_row ;
   unsigned short ws_col ;
   unsigned short ws_xpixel ;
   unsigned short ws_ypixel ;
};
struct exception_table_entry {
   unsigned long insn ;
   unsigned long fixup ;
};
struct termiox {
   __u16 x_hflag ;
   __u16 x_cflag ;
   __u16 x_rflag[5] ;
   __u16 x_sflag ;
};
struct file_operations;
struct inode;
struct module;
struct cdev {
   struct kobject kobj ;
   struct module *owner ;
   struct file_operations const *ops ;
   struct list_head list ;
   dev_t dev ;
   unsigned int count ;
};
struct tty_struct;
struct tty_struct;
struct tty_struct;
struct tty_driver;
struct tty_driver;
struct tty_driver;
struct serial_icounter_struct;
struct serial_icounter_struct;
struct serial_icounter_struct;
struct tty_operations {
   struct tty_struct *(*lookup)(struct tty_driver *driver , struct inode *inode ,
                                int idx ) ;
   int (*install)(struct tty_driver *driver , struct tty_struct *tty ) ;
   void (*remove)(struct tty_driver *driver , struct tty_struct *tty ) ;
   int (*open)(struct tty_struct *tty , struct file *filp ) ;
   void (*close)(struct tty_struct *tty , struct file *filp ) ;
   void (*shutdown)(struct tty_struct *tty ) ;
   void (*cleanup)(struct tty_struct *tty ) ;
   int (*write)(struct tty_struct *tty , unsigned char const *buf , int count ) ;
   int (*put_char)(struct tty_struct *tty , unsigned char ch ) ;
   void (*flush_chars)(struct tty_struct *tty ) ;
   int (*write_room)(struct tty_struct *tty ) ;
   int (*chars_in_buffer)(struct tty_struct *tty ) ;
   int (*ioctl)(struct tty_struct *tty , unsigned int cmd , unsigned long arg ) ;
   long (*compat_ioctl)(struct tty_struct *tty , unsigned int cmd , unsigned long arg ) ;
   void (*set_termios)(struct tty_struct *tty , struct ktermios *old ) ;
   void (*throttle)(struct tty_struct *tty ) ;
   void (*unthrottle)(struct tty_struct *tty ) ;
   void (*stop)(struct tty_struct *tty ) ;
   void (*start)(struct tty_struct *tty ) ;
   void (*hangup)(struct tty_struct *tty ) ;
   int (*break_ctl)(struct tty_struct *tty , int state ) ;
   void (*flush_buffer)(struct tty_struct *tty ) ;
   void (*set_ldisc)(struct tty_struct *tty ) ;
   void (*wait_until_sent)(struct tty_struct *tty , int timeout ) ;
   void (*send_xchar)(struct tty_struct *tty , char ch ) ;
   int (*tiocmget)(struct tty_struct *tty ) ;
   int (*tiocmset)(struct tty_struct *tty , unsigned int set , unsigned int clear ) ;
   int (*resize)(struct tty_struct *tty , struct winsize *ws ) ;
   int (*set_termiox)(struct tty_struct *tty , struct termiox *tnew ) ;
   int (*get_icount)(struct tty_struct *tty , struct serial_icounter_struct *icount ) ;
   int (*poll_init)(struct tty_driver *driver , int line , char *options ) ;
   int (*poll_get_char)(struct tty_driver *driver , int line ) ;
   void (*poll_put_char)(struct tty_driver *driver , int line , char ch ) ;
   struct file_operations const *proc_fops ;
};
struct proc_dir_entry;
struct proc_dir_entry;
struct tty_driver {
   int magic ;
   struct kref kref ;
   struct cdev cdev ;
   struct module *owner ;
   char const *driver_name ;
   char const *name ;
   int name_base ;
   int major ;
   int minor_start ;
   int minor_num ;
   int num ;
   short type ;
   short subtype ;
   struct ktermios init_termios ;
   int flags ;
   struct proc_dir_entry *proc_entry ;
   struct tty_driver *other ;
   struct tty_struct **ttys ;
   struct ktermios **termios ;
   struct ktermios **termios_locked ;
   void *driver_state ;
   struct tty_operations const *ops ;
   struct list_head tty_drivers ;
};
struct klist_node;
struct klist_node;
struct klist_node;
struct klist_node {
   void *n_klist ;
   struct list_head n_node ;
   struct kref n_ref ;
};
struct completion;
struct nsproxy;
struct nsproxy;
struct nsproxy;
struct cred;
struct file;
struct task_struct;
struct file;
typedef __u64 Elf64_Addr;
typedef __u16 Elf64_Half;
typedef __u32 Elf64_Word;
typedef __u64 Elf64_Xword;
struct elf64_sym {
   Elf64_Word st_name ;
   unsigned char st_info ;
   unsigned char st_other ;
   Elf64_Half st_shndx ;
   Elf64_Addr st_value ;
   Elf64_Xword st_size ;
};
typedef struct elf64_sym Elf64_Sym;
struct kernel_param;
struct kernel_param;
struct kernel_param;
struct kernel_param_ops {
   int (*set)(char const *val , struct kernel_param const *kp ) ;
   int (*get)(char *buffer , struct kernel_param const *kp ) ;
   void (*free)(void *arg ) ;
};
struct kparam_string;
struct kparam_string;
struct kparam_array;
struct kparam_array;
union __anonunion____missing_field_name_211 {
   void *arg ;
   struct kparam_string const *str ;
   struct kparam_array const *arr ;
};
struct kernel_param {
   char const *name ;
   struct kernel_param_ops const *ops ;
   u16 perm ;
   u16 flags ;
   union __anonunion____missing_field_name_211 __annonCompField33 ;
};
struct kparam_string {
   unsigned int maxlen ;
   char *string ;
};
struct kparam_array {
   unsigned int max ;
   unsigned int elemsize ;
   unsigned int *num ;
   struct kernel_param_ops const *ops ;
   void *elem ;
};
struct module;
struct module;
struct jump_label_key {
   atomic_t enabled ;
};
struct module;
struct tracepoint;
struct tracepoint;
struct tracepoint;
struct tracepoint_func {
   void *func ;
   void *data ;
};
struct tracepoint {
   char const *name ;
   struct jump_label_key key ;
   void (*regfunc)(void) ;
   void (*unregfunc)(void) ;
   struct tracepoint_func *funcs ;
};
struct mod_arch_specific {

};
struct module;
struct kernel_symbol {
   unsigned long value ;
   char const *name ;
};
struct module;
struct module_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct module_attribute * , struct module * , char * ) ;
   ssize_t (*store)(struct module_attribute * , struct module * , char const * ,
                    size_t count ) ;
   void (*setup)(struct module * , char const * ) ;
   int (*test)(struct module * ) ;
   void (*free)(struct module * ) ;
};
struct module_param_attrs;
struct module_param_attrs;
struct module_kobject {
   struct kobject kobj ;
   struct module *mod ;
   struct kobject *drivers_dir ;
   struct module_param_attrs *mp ;
};
struct exception_table_entry;
enum module_state {
    MODULE_STATE_LIVE = 0,
    MODULE_STATE_COMING = 1,
    MODULE_STATE_GOING = 2
} ;
struct module_sect_attrs;
struct module_sect_attrs;
struct module_notes_attrs;
struct module_notes_attrs;
struct ftrace_event_call;
struct ftrace_event_call;
struct module_ref {
   unsigned int incs ;
   unsigned int decs ;
};
struct module {
   enum module_state state ;
   struct list_head list ;
   char name[64UL - sizeof(unsigned long )] ;
   struct module_kobject mkobj ;
   struct module_attribute *modinfo_attrs ;
   char const *version ;
   char const *srcversion ;
   struct kobject *holders_dir ;
   struct kernel_symbol const *syms ;
   unsigned long const *crcs ;
   unsigned int num_syms ;
   struct kernel_param *kp ;
   unsigned int num_kp ;
   unsigned int num_gpl_syms ;
   struct kernel_symbol const *gpl_syms ;
   unsigned long const *gpl_crcs ;
   struct kernel_symbol const *unused_syms ;
   unsigned long const *unused_crcs ;
   unsigned int num_unused_syms ;
   unsigned int num_unused_gpl_syms ;
   struct kernel_symbol const *unused_gpl_syms ;
   unsigned long const *unused_gpl_crcs ;
   struct kernel_symbol const *gpl_future_syms ;
   unsigned long const *gpl_future_crcs ;
   unsigned int num_gpl_future_syms ;
   unsigned int num_exentries ;
   struct exception_table_entry *extable ;
   int (*init)(void) ;
   void *module_init ;
   void *module_core ;
   unsigned int init_size ;
   unsigned int core_size ;
   unsigned int init_text_size ;
   unsigned int core_text_size ;
   unsigned int init_ro_size ;
   unsigned int core_ro_size ;
   struct mod_arch_specific arch ;
   unsigned int taints ;
   unsigned int num_bugs ;
   struct list_head bug_list ;
   struct bug_entry *bug_table ;
   Elf64_Sym *symtab ;
   Elf64_Sym *core_symtab ;
   unsigned int num_symtab ;
   unsigned int core_num_syms ;
   char *strtab ;
   char *core_strtab ;
   struct module_sect_attrs *sect_attrs ;
   struct module_notes_attrs *notes_attrs ;
   char *args ;
   void *percpu ;
   unsigned int percpu_size ;
   unsigned int num_tracepoints ;
   struct tracepoint * const *tracepoints_ptrs ;
   unsigned int num_trace_bprintk_fmt ;
   char const **trace_bprintk_fmt_start ;
   struct ftrace_event_call **trace_events ;
   unsigned int num_trace_events ;
   unsigned int num_ftrace_callsites ;
   unsigned long *ftrace_callsites ;
   struct list_head source_list ;
   struct list_head target_list ;
   struct task_struct *waiter ;
   void (*exit)(void) ;
   struct module_ref *refptr ;
   ctor_fn_t *ctors ;
   unsigned int num_ctors ;
};
struct dma_map_ops;
struct dma_map_ops;
struct dev_archdata {
   void *acpi_handle ;
   struct dma_map_ops *dma_ops ;
   void *iommu ;
};
struct device;
struct device_private;
struct device_private;
struct device_private {
  void *driver_data;
  struct device *device;
};
struct device_driver;
struct device_driver;
struct device_driver;
struct driver_private;
struct driver_private;
struct driver_private;
struct class;
struct class;
struct class;
struct subsys_private;
struct subsys_private;
struct subsys_private;
struct bus_type;
struct bus_type;
struct bus_type;
struct device_node;
struct device_node;
struct device_node;
struct bus_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct bus_type *bus , char *buf ) ;
   ssize_t (*store)(struct bus_type *bus , char const *buf , size_t count ) ;
};
struct device_attribute;
struct device_attribute;
struct driver_attribute;
struct driver_attribute;
struct bus_type {
   char const *name ;
   struct bus_attribute *bus_attrs ;
   struct device_attribute *dev_attrs ;
   struct driver_attribute *drv_attrs ;
   int (*match)(struct device *dev , struct device_driver *drv ) ;
   int (*uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   int (*probe)(struct device *dev ) ;
   int (*remove)(struct device *dev ) ;
   void (*shutdown)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
   struct subsys_private *p ;
};
struct of_device_id;
struct of_device_id;
struct device_driver {
   char const *name ;
   struct bus_type *bus ;
   struct module *owner ;
   char const *mod_name ;
   bool suppress_bind_attrs ;
   struct of_device_id const *of_match_table ;
   int (*probe)(struct device *dev ) ;
   int (*remove)(struct device *dev ) ;
   void (*shutdown)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct attribute_group const **groups ;
   struct dev_pm_ops const *pm ;
   struct driver_private *p ;
};
struct driver_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct device_driver *driver , char *buf ) ;
   ssize_t (*store)(struct device_driver *driver , char const *buf , size_t count ) ;
};
struct class_attribute;
struct class_attribute;
struct class {
   char const *name ;
   struct module *owner ;
   struct class_attribute *class_attrs ;
   struct device_attribute *dev_attrs ;
   struct bin_attribute *dev_bin_attrs ;
   struct kobject *dev_kobj ;
   int (*dev_uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   char *(*devnode)(struct device *dev , mode_t *mode ) ;
   void (*class_release)(struct class *class ) ;
   void (*dev_release)(struct device *dev ) ;
   int (*suspend)(struct device *dev , pm_message_t state ) ;
   int (*resume)(struct device *dev ) ;
   struct kobj_ns_type_operations const *ns_type ;
   void const *(*namespace)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
   struct subsys_private *p ;
};
struct device_type;
struct device_type;
struct class_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct class *class , struct class_attribute *attr , char *buf ) ;
   ssize_t (*store)(struct class *class , struct class_attribute *attr , char const *buf ,
                    size_t count ) ;
};
struct device_type {
   char const *name ;
   struct attribute_group const **groups ;
   int (*uevent)(struct device *dev , struct kobj_uevent_env *env ) ;
   char *(*devnode)(struct device *dev , mode_t *mode ) ;
   void (*release)(struct device *dev ) ;
   struct dev_pm_ops const *pm ;
};
struct device_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct device *dev , struct device_attribute *attr , char *buf ) ;
   ssize_t (*store)(struct device *dev , struct device_attribute *attr , char const *buf ,
                    size_t count ) ;
};
struct device_dma_parameters {
   unsigned int max_segment_size ;
   unsigned long segment_boundary_mask ;
};
struct dma_coherent_mem;
struct dma_coherent_mem;
struct device {
   struct device *parent ;
   struct device_private *p ;
   struct kobject kobj ;
   char const *init_name ;
   struct device_type const *type ;
   struct mutex mutex ;
   struct bus_type *bus ;
   struct device_driver *driver ;
   void *platform_data ;
   struct dev_pm_info power ;
   struct dev_power_domain *pwr_domain ;
   int numa_node ;
   u64 *dma_mask ;
   u64 coherent_dma_mask ;
   struct device_dma_parameters *dma_parms ;
   struct list_head dma_pools ;
   struct dma_coherent_mem *dma_mem ;
   struct dev_archdata archdata ;
   struct device_node *of_node ;
   dev_t devt ;
   spinlock_t devres_lock ;
   struct list_head devres_head ;
   struct klist_node knode_class ;
   struct class *class ;
   struct attribute_group const **groups ;
   void (*release)(struct device *dev ) ;
};
struct wakeup_source {
   char *name ;
   struct list_head entry ;
   spinlock_t lock ;
   struct timer_list timer ;
   unsigned long timer_expires ;
   ktime_t total_time ;
   ktime_t max_time ;
   ktime_t last_time ;
   unsigned long event_count ;
   unsigned long active_count ;
   unsigned long relax_count ;
   unsigned long hit_count ;
   unsigned int active : 1 ;
};
struct pps_event_time {
   struct timespec ts_real ;
};
struct tty_ldisc_ops {
   int magic ;
   char *name ;
   int num ;
   int flags ;
   int (*open)(struct tty_struct * ) ;
   void (*close)(struct tty_struct * ) ;
   void (*flush_buffer)(struct tty_struct *tty ) ;
   ssize_t (*chars_in_buffer)(struct tty_struct *tty ) ;
   ssize_t (*read)(struct tty_struct *tty , struct file *file , unsigned char *buf ,
                   size_t nr ) ;
   ssize_t (*write)(struct tty_struct *tty , struct file *file , unsigned char const *buf ,
                    size_t nr ) ;
   int (*ioctl)(struct tty_struct *tty , struct file *file , unsigned int cmd , unsigned long arg ) ;
   long (*compat_ioctl)(struct tty_struct *tty , struct file *file , unsigned int cmd ,
                        unsigned long arg ) ;
   void (*set_termios)(struct tty_struct *tty , struct ktermios *old ) ;
   unsigned int (*poll)(struct tty_struct * , struct file * , struct poll_table_struct * ) ;
   int (*hangup)(struct tty_struct *tty ) ;
   void (*receive_buf)(struct tty_struct * , unsigned char const *cp , char *fp ,
                       int count ) ;
   void (*write_wakeup)(struct tty_struct * ) ;
   void (*dcd_change)(struct tty_struct * , unsigned int , struct pps_event_time * ) ;
   struct module *owner ;
   int refcount ;
};
struct tty_ldisc {
   struct tty_ldisc_ops *ops ;
   atomic_t users ;
};
struct tty_buffer {
   struct tty_buffer *next ;
   char *char_buf_ptr ;
   unsigned char *flag_buf_ptr ;
   int used ;
   int size ;
   int commit ;
   int read ;
   unsigned long data[0] ;
};
struct tty_bufhead {
   struct work_struct work ;
   spinlock_t lock ;
   struct tty_buffer *head ;
   struct tty_buffer *tail ;
   struct tty_buffer *free ;
   int memory_used ;
};
struct device;
struct signal_struct;
struct signal_struct;
struct signal_struct;
struct tty_port;
struct tty_port;
struct tty_port;
struct tty_port_operations {
   int (*carrier_raised)(struct tty_port *port ) ;
   void (*dtr_rts)(struct tty_port *port , int raise ) ;
   void (*shutdown)(struct tty_port *port ) ;
   void (*drop)(struct tty_port *port ) ;
   int (*activate)(struct tty_port *port , struct tty_struct *tty ) ;
   void (*destruct)(struct tty_port *port ) ;
};
struct tty_port {
   struct tty_struct *tty ;
   struct tty_port_operations const *ops ;
   spinlock_t lock ;
   int blocked_open ;
   int count ;
   wait_queue_head_t open_wait ;
   wait_queue_head_t close_wait ;
   wait_queue_head_t delta_msr_wait ;
   unsigned long flags ;
   unsigned char console : 1 ;
   struct mutex mutex ;
   struct mutex buf_mutex ;
   unsigned char *xmit_buf ;
   unsigned int close_delay ;
   unsigned int closing_wait ;
   int drain_delay ;
   struct kref kref ;
};
struct tty_operations;
struct tty_struct {
   int magic ;
   struct kref kref ;
   struct device *dev ;
   struct tty_driver *driver ;
   struct tty_operations const *ops ;
   int index ;
   struct mutex ldisc_mutex ;
   struct tty_ldisc *ldisc ;
   struct mutex termios_mutex ;
   spinlock_t ctrl_lock ;
   struct ktermios *termios ;
   struct ktermios *termios_locked ;
   struct termiox *termiox ;
   char name[64] ;
   struct pid *pgrp ;
   struct pid *session ;
   unsigned long flags ;
   int count ;
   struct winsize winsize ;
   unsigned char stopped : 1 ;
   unsigned char hw_stopped : 1 ;
   unsigned char flow_stopped : 1 ;
   unsigned char packet : 1 ;
   unsigned char low_latency : 1 ;
   unsigned char warned : 1 ;
   unsigned char ctrl_status ;
   unsigned int receive_room ;
   struct tty_struct *link ;
   struct fasync_struct *fasync ;
   struct tty_bufhead buf ;
   int alt_speed ;
   wait_queue_head_t write_wait ;
   wait_queue_head_t read_wait ;
   struct work_struct hangup_work ;
   void *disc_data ;
   void *driver_data ;
   struct list_head tty_files ;
   unsigned int column ;
   unsigned char lnext : 1 ;
   unsigned char erasing : 1 ;
   unsigned char raw : 1 ;
   unsigned char real_raw : 1 ;
   unsigned char icanon : 1 ;
   unsigned char closing : 1 ;
   unsigned char echo_overrun : 1 ;
   unsigned short minimum_to_wake ;
   unsigned long overrun_time ;
   int num_overrun ;
   unsigned long process_char_map[256UL / (8UL * sizeof(unsigned long ))] ;
   char *read_buf ;
   int read_head ;
   int read_tail ;
   int read_cnt ;
   unsigned long read_flags[4096UL / (8UL * sizeof(unsigned long ))] ;
   unsigned char *echo_buf ;
   unsigned int echo_pos ;
   unsigned int echo_cnt ;
   int canon_data ;
   unsigned long canon_head ;
   unsigned int canon_column ;
   struct mutex atomic_read_lock ;
   struct mutex atomic_write_lock ;
   struct mutex output_lock ;
   struct mutex echo_lock ;
   unsigned char *write_buf ;
   int write_cnt ;
   spinlock_t read_lock ;
   struct work_struct SAK_work ;
   struct tty_port *port ;
};
typedef unsigned long kernel_ulong_t;
struct usb_device_id {
   __u16 match_flags ;
   __u16 idVendor ;
   __u16 idProduct ;
   __u16 bcdDevice_lo ;
   __u16 bcdDevice_hi ;
   __u8 bDeviceClass ;
   __u8 bDeviceSubClass ;
   __u8 bDeviceProtocol ;
   __u8 bInterfaceClass ;
   __u8 bInterfaceSubClass ;
   __u8 bInterfaceProtocol ;
   kernel_ulong_t driver_info ;
};
struct of_device_id {
   char name[32] ;
   char type[32] ;
   char compatible[128] ;
   void *data ;
};
struct usb_device_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __le16 bcdUSB ;
   __u8 bDeviceClass ;
   __u8 bDeviceSubClass ;
   __u8 bDeviceProtocol ;
   __u8 bMaxPacketSize0 ;
   __le16 idVendor ;
   __le16 idProduct ;
   __le16 bcdDevice ;
   __u8 iManufacturer ;
   __u8 iProduct ;
   __u8 iSerialNumber ;
   __u8 bNumConfigurations ;
} __attribute__((__packed__)) ;
struct usb_config_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __le16 wTotalLength ;
   __u8 bNumInterfaces ;
   __u8 bConfigurationValue ;
   __u8 iConfiguration ;
   __u8 bmAttributes ;
   __u8 bMaxPower ;
} __attribute__((__packed__)) ;
struct usb_interface_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bInterfaceNumber ;
   __u8 bAlternateSetting ;
   __u8 bNumEndpoints ;
   __u8 bInterfaceClass ;
   __u8 bInterfaceSubClass ;
   __u8 bInterfaceProtocol ;
   __u8 iInterface ;
} __attribute__((__packed__)) ;
struct usb_endpoint_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bEndpointAddress ;
   __u8 bmAttributes ;
   __le16 wMaxPacketSize ;
   __u8 bInterval ;
   __u8 bRefresh ;
   __u8 bSynchAddress ;
} __attribute__((__packed__)) ;
struct usb_ss_ep_comp_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bMaxBurst ;
   __u8 bmAttributes ;
   __le16 wBytesPerInterval ;
} __attribute__((__packed__)) ;
struct usb_interface_assoc_descriptor {
   __u8 bLength ;
   __u8 bDescriptorType ;
   __u8 bFirstInterface ;
   __u8 bInterfaceCount ;
   __u8 bFunctionClass ;
   __u8 bFunctionSubClass ;
   __u8 bFunctionProtocol ;
   __u8 iFunction ;
} __attribute__((__packed__)) ;
enum usb_device_speed {
    USB_SPEED_UNKNOWN = 0,
    USB_SPEED_LOW = 1,
    USB_SPEED_FULL = 2,
    USB_SPEED_HIGH = 3,
    USB_SPEED_WIRELESS = 4,
    USB_SPEED_SUPER = 5
} ;
enum usb_device_state {
    USB_STATE_NOTATTACHED = 0,
    USB_STATE_ATTACHED = 1,
    USB_STATE_POWERED = 2,
    USB_STATE_RECONNECTING = 3,
    USB_STATE_UNAUTHENTICATED = 4,
    USB_STATE_DEFAULT = 5,
    USB_STATE_ADDRESS = 6,
    USB_STATE_CONFIGURED = 7,
    USB_STATE_SUSPENDED = 8
} ;
enum irqreturn {
    IRQ_NONE = 0,
    IRQ_HANDLED = 1,
    IRQ_WAKE_THREAD = 2
} ;
typedef enum irqreturn irqreturn_t;
struct seq_file;
struct proc_dir_entry;
struct irqaction;
struct irqaction;
struct proc_dir_entry;
struct pt_regs;
struct task_struct;
struct mm_struct;
struct pt_regs;
struct irqaction;
struct task_struct;
struct rb_node {
   unsigned long rb_parent_color ;
   struct rb_node *rb_right ;
   struct rb_node *rb_left ;
} __attribute__((__aligned__(sizeof(long )))) ;
struct rb_root {
   struct rb_node *rb_node ;
};
struct timerqueue_node {
   struct rb_node node ;
   ktime_t expires ;
};
struct timerqueue_head {
   struct rb_root head ;
   struct timerqueue_node *next ;
};
struct hrtimer_clock_base;
struct hrtimer_clock_base;
struct hrtimer_clock_base;
struct hrtimer_cpu_base;
struct hrtimer_cpu_base;
struct hrtimer_cpu_base;
enum hrtimer_restart {
    HRTIMER_NORESTART = 0,
    HRTIMER_RESTART = 1
} ;
struct hrtimer {
   struct timerqueue_node node ;
   ktime_t _softexpires ;
   enum hrtimer_restart (*function)(struct hrtimer * ) ;
   struct hrtimer_clock_base *base ;
   unsigned long state ;
   int start_pid ;
   void *start_site ;
   char start_comm[16] ;
};
struct hrtimer_clock_base {
   struct hrtimer_cpu_base *cpu_base ;
   int index ;
   clockid_t clockid ;
   struct timerqueue_head active ;
   ktime_t resolution ;
   ktime_t (*get_time)(void) ;
   ktime_t softirq_time ;
   ktime_t offset ;
};
struct hrtimer_cpu_base {
   raw_spinlock_t lock ;
   unsigned long active_bases ;
   ktime_t expires_next ;
   int hres_active ;
   int hang_detected ;
   unsigned long nr_events ;
   unsigned long nr_retries ;
   unsigned long nr_hangs ;
   ktime_t max_hang_time ;
   struct hrtimer_clock_base clock_base[3] ;
};
struct irqaction;
struct irqaction {
   irqreturn_t (*handler)(int , void * ) ;
   unsigned long flags ;
   void *dev_id ;
   struct irqaction *next ;
   int irq ;
   irqreturn_t (*thread_fn)(int , void * ) ;
   struct task_struct *thread ;
   unsigned long thread_flags ;
   unsigned long thread_mask ;
   char const *name ;
   struct proc_dir_entry *dir ;
} __attribute__((__aligned__((1) << (12) ))) ;
struct device;
struct seq_file;
struct address_space;
struct __anonstruct____missing_field_name_223 {
   u16 inuse ;
   u16 objects ;
};
union __anonunion____missing_field_name_222 {
   atomic_t _mapcount ;
   struct __anonstruct____missing_field_name_223 __annonCompField34 ;
};
struct __anonstruct____missing_field_name_225 {
   unsigned long private ;
   struct address_space *mapping ;
};
union __anonunion____missing_field_name_224 {
   struct __anonstruct____missing_field_name_225 __annonCompField36 ;
   struct kmem_cache *slab ;
   struct page *first_page ;
};
union __anonunion____missing_field_name_226 {
   unsigned long index ;
   void *freelist ;
};
struct page {
   unsigned long flags ;
   atomic_t _count ;
   union __anonunion____missing_field_name_222 __annonCompField35 ;
   union __anonunion____missing_field_name_224 __annonCompField37 ;
   union __anonunion____missing_field_name_226 __annonCompField38 ;
   struct list_head lru ;
};
struct __anonstruct_vm_set_228 {
   struct list_head list ;
   void *parent ;
   struct vm_area_struct *head ;
};
union __anonunion_shared_227 {
   struct __anonstruct_vm_set_228 vm_set ;
   struct raw_prio_tree_node prio_tree_node ;
};
struct anon_vma;
struct anon_vma;
struct vm_operations_struct;
struct vm_operations_struct;
struct mempolicy;
struct mempolicy;
struct vm_area_struct {
   struct mm_struct *vm_mm ;
   unsigned long vm_start ;
   unsigned long vm_end ;
   struct vm_area_struct *vm_next ;
   struct vm_area_struct *vm_prev ;
   pgprot_t vm_page_prot ;
   unsigned long vm_flags ;
   struct rb_node vm_rb ;
   union __anonunion_shared_227 shared ;
   struct list_head anon_vma_chain ;
   struct anon_vma *anon_vma ;
   struct vm_operations_struct const *vm_ops ;
   unsigned long vm_pgoff ;
   struct file *vm_file ;
   void *vm_private_data ;
   struct mempolicy *vm_policy ;
};
struct core_thread {
   struct task_struct *task ;
   struct core_thread *next ;
};
struct core_state {
   atomic_t nr_threads ;
   struct core_thread dumper ;
   struct completion startup ;
};
struct mm_rss_stat {
   atomic_long_t count[3] ;
};
struct linux_binfmt;
struct linux_binfmt;
struct mmu_notifier_mm;
struct mmu_notifier_mm;
struct mm_struct {
   struct vm_area_struct *mmap ;
   struct rb_root mm_rb ;
   struct vm_area_struct *mmap_cache ;
   unsigned long (*get_unmapped_area)(struct file *filp , unsigned long addr , unsigned long len ,
                                      unsigned long pgoff , unsigned long flags ) ;
   void (*unmap_area)(struct mm_struct *mm , unsigned long addr ) ;
   unsigned long mmap_base ;
   unsigned long task_size ;
   unsigned long cached_hole_size ;
   unsigned long free_area_cache ;
   pgd_t *pgd ;
   atomic_t mm_users ;
   atomic_t mm_count ;
   int map_count ;
   spinlock_t page_table_lock ;
   struct rw_semaphore mmap_sem ;
   struct list_head mmlist ;
   unsigned long hiwater_rss ;
   unsigned long hiwater_vm ;
   unsigned long total_vm ;
   unsigned long locked_vm ;
   unsigned long shared_vm ;
   unsigned long exec_vm ;
   unsigned long stack_vm ;
   unsigned long reserved_vm ;
   unsigned long def_flags ;
   unsigned long nr_ptes ;
   unsigned long start_code ;
   unsigned long end_code ;
   unsigned long start_data ;
   unsigned long end_data ;
   unsigned long start_brk ;
   unsigned long brk ;
   unsigned long start_stack ;
   unsigned long arg_start ;
   unsigned long arg_end ;
   unsigned long env_start ;
   unsigned long env_end ;
   unsigned long saved_auxv[44] ;
   struct mm_rss_stat rss_stat ;
   struct linux_binfmt *binfmt ;
   cpumask_var_t cpu_vm_mask_var ;
   mm_context_t context ;
   unsigned int faultstamp ;
   unsigned int token_priority ;
   unsigned int last_interval ;
   atomic_t oom_disable_count ;
   unsigned long flags ;
   struct core_state *core_state ;
   spinlock_t ioctx_lock ;
   struct hlist_head ioctx_list ;
   struct task_struct *owner ;
   struct file *exe_file ;
   unsigned long num_exe_file_vmas ;
   struct mmu_notifier_mm *mmu_notifier_mm ;
   pgtable_t pmd_huge_pte ;
   struct cpumask cpumask_allocation ;
};
typedef unsigned long cputime_t;
struct task_struct;
struct sem_undo_list;
struct sem_undo_list;
struct sem_undo_list {
   atomic_t refcnt ;
   spinlock_t lock ;
   struct list_head list_proc ;
};
struct sysv_sem {
   struct sem_undo_list *undo_list ;
};
struct siginfo;
struct siginfo;
struct siginfo;
struct __anonstruct_sigset_t_230 {
   unsigned long sig[1] ;
};
typedef struct __anonstruct_sigset_t_230 sigset_t;
typedef void __signalfn_t(int );
typedef __signalfn_t *__sighandler_t;
typedef void __restorefn_t(void);
typedef __restorefn_t *__sigrestore_t;
struct sigaction {
   __sighandler_t sa_handler ;
   unsigned long sa_flags ;
   __sigrestore_t sa_restorer ;
   sigset_t sa_mask ;
};
struct k_sigaction {
   struct sigaction sa ;
};
union sigval {
   int sival_int ;
   void *sival_ptr ;
};
typedef union sigval sigval_t;
struct __anonstruct__kill_232 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
};
struct __anonstruct__timer_233 {
   __kernel_timer_t _tid ;
   int _overrun ;
   char _pad[sizeof(__kernel_uid32_t ) - sizeof(int )] ;
   sigval_t _sigval ;
   int _sys_private ;
};
struct __anonstruct__rt_234 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
   sigval_t _sigval ;
};
struct __anonstruct__sigchld_235 {
   __kernel_pid_t _pid ;
   __kernel_uid32_t _uid ;
   int _status ;
   __kernel_clock_t _utime ;
   __kernel_clock_t _stime ;
};
struct __anonstruct__sigfault_236 {
   void *_addr ;
   short _addr_lsb ;
};
struct __anonstruct__sigpoll_237 {
   long _band ;
   int _fd ;
};
union __anonunion__sifields_231 {
   int _pad[(128UL - 4UL * sizeof(int )) / sizeof(int )] ;
   struct __anonstruct__kill_232 _kill ;
   struct __anonstruct__timer_233 _timer ;
   struct __anonstruct__rt_234 _rt ;
   struct __anonstruct__sigchld_235 _sigchld ;
   struct __anonstruct__sigfault_236 _sigfault ;
   struct __anonstruct__sigpoll_237 _sigpoll ;
};
struct siginfo {
   int si_signo ;
   int si_errno ;
   int si_code ;
   union __anonunion__sifields_231 _sifields ;
};
typedef struct siginfo siginfo_t;
struct siginfo;
struct task_struct;
struct user_struct;
struct user_struct;
struct sigpending {
   struct list_head list ;
   sigset_t signal ;
};
struct timespec;
struct pt_regs;
struct prop_local_single {
   unsigned long events ;
   unsigned long period ;
   int shift ;
   spinlock_t lock ;
};
struct __anonstruct_seccomp_t_240 {
   int mode ;
};
typedef struct __anonstruct_seccomp_t_240 seccomp_t;
struct plist_head {
   struct list_head node_list ;
   raw_spinlock_t *rawlock ;
   spinlock_t *spinlock ;
};
struct plist_node {
   int prio ;
   struct list_head prio_list ;
   struct list_head node_list ;
};
struct rt_mutex_waiter;
struct rt_mutex_waiter;
struct rt_mutex_waiter;
struct rlimit {
   unsigned long rlim_cur ;
   unsigned long rlim_max ;
};
struct task_struct;
struct task_io_accounting {
   u64 rchar ;
   u64 wchar ;
   u64 syscr ;
   u64 syscw ;
   u64 read_bytes ;
   u64 write_bytes ;
   u64 cancelled_write_bytes ;
};
struct latency_record {
   unsigned long backtrace[12] ;
   unsigned int count ;
   unsigned long time ;
   unsigned long max ;
};
struct task_struct;
typedef int32_t key_serial_t;
typedef uint32_t key_perm_t;
struct key;
struct key;
struct key;
struct seq_file;
struct user_struct;
struct signal_struct;
struct cred;
struct key_type;
struct key_type;
struct key_type;
struct keyring_list;
struct keyring_list;
struct keyring_list;
struct key_user;
struct key_user;
union __anonunion____missing_field_name_241 {
   time_t expiry ;
   time_t revoked_at ;
};
union __anonunion_type_data_242 {
   struct list_head link ;
   unsigned long x[2] ;
   void *p[2] ;
   int reject_error ;
};
union __anonunion_payload_243 {
   unsigned long value ;
   void *rcudata ;
   void *data ;
   struct keyring_list *subscriptions ;
};
struct key {
   atomic_t usage ;
   key_serial_t serial ;
   struct rb_node serial_node ;
   struct key_type *type ;
   struct rw_semaphore sem ;
   struct key_user *user ;
   void *security ;
   union __anonunion____missing_field_name_241 __annonCompField39 ;
   uid_t uid ;
   gid_t gid ;
   key_perm_t perm ;
   unsigned short quotalen ;
   unsigned short datalen ;
   unsigned long flags ;
   char *description ;
   union __anonunion_type_data_242 type_data ;
   union __anonunion_payload_243 payload ;
};
struct audit_context;
struct audit_context;
struct audit_context;
struct user_struct;
struct cred;
struct inode;
struct group_info {
   atomic_t usage ;
   int ngroups ;
   int nblocks ;
   gid_t small_block[32] ;
   gid_t *blocks[0] ;
};
struct thread_group_cred {
   atomic_t usage ;
   pid_t tgid ;
   spinlock_t lock ;
   struct key *session_keyring ;
   struct key *process_keyring ;
   struct rcu_head rcu ;
};
struct cred {
   atomic_t usage ;
   atomic_t subscribers ;
   void *put_addr ;
   unsigned int magic ;
   uid_t uid ;
   gid_t gid ;
   uid_t suid ;
   gid_t sgid ;
   uid_t euid ;
   gid_t egid ;
   uid_t fsuid ;
   gid_t fsgid ;
   unsigned int securebits ;
   kernel_cap_t cap_inheritable ;
   kernel_cap_t cap_permitted ;
   kernel_cap_t cap_effective ;
   kernel_cap_t cap_bset ;
   unsigned char jit_keyring ;
   struct key *thread_keyring ;
   struct key *request_key_auth ;
   struct thread_group_cred *tgcred ;
   void *security ;
   struct user_struct *user ;
   struct user_namespace *user_ns ;
   struct group_info *group_info ;
   struct rcu_head rcu ;
};
struct futex_pi_state;
struct futex_pi_state;
struct futex_pi_state;
struct robust_list_head;
struct robust_list_head;
struct robust_list_head;
struct bio_list;
struct bio_list;
struct bio_list;
struct fs_struct;
struct fs_struct;
struct fs_struct;
struct perf_event_context;
struct perf_event_context;
struct perf_event_context;
struct blk_plug;
struct blk_plug;
struct blk_plug;
struct seq_file;
struct cfs_rq;
struct cfs_rq;
struct cfs_rq;
struct task_struct;
struct nsproxy;
struct user_namespace;
struct io_event {
   __u64 data ;
   __u64 obj ;
   __s64 res ;
   __s64 res2 ;
};
struct iovec {
   void *iov_base ;
   __kernel_size_t iov_len ;
};
struct kioctx;
struct kioctx;
struct kioctx;
union __anonunion_ki_obj_245 {
   void *user ;
   struct task_struct *tsk ;
};
struct eventfd_ctx;
struct eventfd_ctx;
struct kiocb {
   struct list_head ki_run_list ;
   unsigned long ki_flags ;
   int ki_users ;
   unsigned int ki_key ;
   struct file *ki_filp ;
   struct kioctx *ki_ctx ;
   int (*ki_cancel)(struct kiocb * , struct io_event * ) ;
   ssize_t (*ki_retry)(struct kiocb * ) ;
   void (*ki_dtor)(struct kiocb * ) ;
   union __anonunion_ki_obj_245 ki_obj ;
   __u64 ki_user_data ;
   loff_t ki_pos ;
   void *private ;
   unsigned short ki_opcode ;
   size_t ki_nbytes ;
   char *ki_buf ;
   size_t ki_left ;
   struct iovec ki_inline_vec ;
   struct iovec *ki_iovec ;
   unsigned long ki_nr_segs ;
   unsigned long ki_cur_seg ;
   struct list_head ki_list ;
   struct eventfd_ctx *ki_eventfd ;
};
struct aio_ring_info {
   unsigned long mmap_base ;
   unsigned long mmap_size ;
   struct page **ring_pages ;
   spinlock_t ring_lock ;
   long nr_pages ;
   unsigned int nr ;
   unsigned int tail ;
   struct page *internal_pages[8] ;
};
struct kioctx {
   atomic_t users ;
   int dead ;
   struct mm_struct *mm ;
   unsigned long user_id ;
   struct hlist_node list ;
   wait_queue_head_t wait ;
   spinlock_t ctx_lock ;
   int reqs_active ;
   struct list_head active_reqs ;
   struct list_head run_list ;
   unsigned int max_reqs ;
   struct aio_ring_info ring_info ;
   struct delayed_work wq ;
   struct rcu_head rcu_head ;
};
struct mm_struct;
struct sighand_struct {
   atomic_t count ;
   struct k_sigaction action[64] ;
   spinlock_t siglock ;
   wait_queue_head_t signalfd_wqh ;
};
struct pacct_struct {
   int ac_flag ;
   long ac_exitcode ;
   unsigned long ac_mem ;
   cputime_t ac_utime ;
   cputime_t ac_stime ;
   unsigned long ac_minflt ;
   unsigned long ac_majflt ;
};
struct cpu_itimer {
   cputime_t expires ;
   cputime_t incr ;
   u32 error ;
   u32 incr_error ;
};
struct task_cputime {
   cputime_t utime ;
   cputime_t stime ;
   unsigned long long sum_exec_runtime ;
};
struct thread_group_cputimer {
   struct task_cputime cputime ;
   int running ;
   spinlock_t lock ;
};
struct autogroup;
struct autogroup;
struct autogroup;
struct taskstats;
struct taskstats;
struct tty_audit_buf;
struct tty_audit_buf;
struct signal_struct {
   atomic_t sigcnt ;
   atomic_t live ;
   int nr_threads ;
   wait_queue_head_t wait_chldexit ;
   struct task_struct *curr_target ;
   struct sigpending shared_pending ;
   int group_exit_code ;
   int notify_count ;
   struct task_struct *group_exit_task ;
   int group_stop_count ;
   unsigned int flags ;
   struct list_head posix_timers ;
   struct hrtimer real_timer ;
   struct pid *leader_pid ;
   ktime_t it_real_incr ;
   struct cpu_itimer it[2] ;
   struct thread_group_cputimer cputimer ;
   struct task_cputime cputime_expires ;
   struct list_head cpu_timers[3] ;
   struct pid *tty_old_pgrp ;
   int leader ;
   struct tty_struct *tty ;
   struct autogroup *autogroup ;
   cputime_t utime ;
   cputime_t stime ;
   cputime_t cutime ;
   cputime_t cstime ;
   cputime_t gtime ;
   cputime_t cgtime ;
   cputime_t prev_utime ;
   cputime_t prev_stime ;
   unsigned long nvcsw ;
   unsigned long nivcsw ;
   unsigned long cnvcsw ;
   unsigned long cnivcsw ;
   unsigned long min_flt ;
   unsigned long maj_flt ;
   unsigned long cmin_flt ;
   unsigned long cmaj_flt ;
   unsigned long inblock ;
   unsigned long oublock ;
   unsigned long cinblock ;
   unsigned long coublock ;
   unsigned long maxrss ;
   unsigned long cmaxrss ;
   struct task_io_accounting ioac ;
   unsigned long long sum_sched_runtime ;
   struct rlimit rlim[16] ;
   struct pacct_struct pacct ;
   struct taskstats *stats ;
   unsigned int audit_tty ;
   struct tty_audit_buf *tty_audit_buf ;
   struct rw_semaphore threadgroup_fork_lock ;
   int oom_adj ;
   int oom_score_adj ;
   int oom_score_adj_min ;
   struct mutex cred_guard_mutex ;
};
struct user_struct {
   atomic_t __count ;
   atomic_t processes ;
   atomic_t files ;
   atomic_t sigpending ;
   atomic_t inotify_watches ;
   atomic_t inotify_devs ;
   atomic_t fanotify_listeners ;
   atomic_long_t epoll_watches ;
   unsigned long mq_bytes ;
   unsigned long locked_shm ;
   struct key *uid_keyring ;
   struct key *session_keyring ;
   struct hlist_node uidhash_node ;
   uid_t uid ;
   struct user_namespace *user_ns ;
   atomic_long_t locked_vm ;
};
struct backing_dev_info;
struct reclaim_state;
struct reclaim_state;
struct reclaim_state;
struct sched_info {
   unsigned long pcount ;
   unsigned long long run_delay ;
   unsigned long long last_arrival ;
   unsigned long long last_queued ;
};
struct task_delay_info {
   spinlock_t lock ;
   unsigned int flags ;
   struct timespec blkio_start ;
   struct timespec blkio_end ;
   u64 blkio_delay ;
   u64 swapin_delay ;
   u32 blkio_count ;
   u32 swapin_count ;
   struct timespec freepages_start ;
   struct timespec freepages_end ;
   u64 freepages_delay ;
   u32 freepages_count ;
};
struct io_context;
struct io_context;
struct io_context;
struct audit_context;
struct mempolicy;
struct pipe_inode_info;
struct rq;
struct rq;
struct rq;
struct sched_class {
   struct sched_class const *next ;
   void (*enqueue_task)(struct rq *rq , struct task_struct *p , int flags ) ;
   void (*dequeue_task)(struct rq *rq , struct task_struct *p , int flags ) ;
   void (*yield_task)(struct rq *rq ) ;
   bool (*yield_to_task)(struct rq *rq , struct task_struct *p , bool preempt ) ;
   void (*check_preempt_curr)(struct rq *rq , struct task_struct *p , int flags ) ;
   struct task_struct *(*pick_next_task)(struct rq *rq ) ;
   void (*put_prev_task)(struct rq *rq , struct task_struct *p ) ;
   int (*select_task_rq)(struct task_struct *p , int sd_flag , int flags ) ;
   void (*pre_schedule)(struct rq *this_rq , struct task_struct *task ) ;
   void (*post_schedule)(struct rq *this_rq ) ;
   void (*task_waking)(struct task_struct *task ) ;
   void (*task_woken)(struct rq *this_rq , struct task_struct *task ) ;
   void (*set_cpus_allowed)(struct task_struct *p , struct cpumask const *newmask ) ;
   void (*rq_online)(struct rq *rq ) ;
   void (*rq_offline)(struct rq *rq ) ;
   void (*set_curr_task)(struct rq *rq ) ;
   void (*task_tick)(struct rq *rq , struct task_struct *p , int queued ) ;
   void (*task_fork)(struct task_struct *p ) ;
   void (*switched_from)(struct rq *this_rq , struct task_struct *task ) ;
   void (*switched_to)(struct rq *this_rq , struct task_struct *task ) ;
   void (*prio_changed)(struct rq *this_rq , struct task_struct *task , int oldprio ) ;
   unsigned int (*get_rr_interval)(struct rq *rq , struct task_struct *task ) ;
   void (*task_move_group)(struct task_struct *p , int on_rq ) ;
};
struct load_weight {
   unsigned long weight ;
   unsigned long inv_weight ;
};
struct sched_statistics {
   u64 wait_start ;
   u64 wait_max ;
   u64 wait_count ;
   u64 wait_sum ;
   u64 iowait_count ;
   u64 iowait_sum ;
   u64 sleep_start ;
   u64 sleep_max ;
   s64 sum_sleep_runtime ;
   u64 block_start ;
   u64 block_max ;
   u64 exec_max ;
   u64 slice_max ;
   u64 nr_migrations_cold ;
   u64 nr_failed_migrations_affine ;
   u64 nr_failed_migrations_running ;
   u64 nr_failed_migrations_hot ;
   u64 nr_forced_migrations ;
   u64 nr_wakeups ;
   u64 nr_wakeups_sync ;
   u64 nr_wakeups_migrate ;
   u64 nr_wakeups_local ;
   u64 nr_wakeups_remote ;
   u64 nr_wakeups_affine ;
   u64 nr_wakeups_affine_attempts ;
   u64 nr_wakeups_passive ;
   u64 nr_wakeups_idle ;
};
struct sched_entity {
   struct load_weight load ;
   struct rb_node run_node ;
   struct list_head group_node ;
   unsigned int on_rq ;
   u64 exec_start ;
   u64 sum_exec_runtime ;
   u64 vruntime ;
   u64 prev_sum_exec_runtime ;
   u64 nr_migrations ;
   struct sched_statistics statistics ;
   struct sched_entity *parent ;
   struct cfs_rq *cfs_rq ;
   struct cfs_rq *my_q ;
};
struct rt_rq;
struct rt_rq;
struct sched_rt_entity {
   struct list_head run_list ;
   unsigned long timeout ;
   unsigned int time_slice ;
   int nr_cpus_allowed ;
   struct sched_rt_entity *back ;
   struct sched_rt_entity *parent ;
   struct rt_rq *rt_rq ;
   struct rt_rq *my_q ;
};
struct css_set;
struct css_set;
struct compat_robust_list_head;
struct compat_robust_list_head;
struct ftrace_ret_stack;
struct ftrace_ret_stack;
struct mem_cgroup;
struct mem_cgroup;
struct memcg_batch_info {
   int do_batch ;
   struct mem_cgroup *memcg ;
   unsigned long nr_pages ;
   unsigned long memsw_nr_pages ;
};
struct task_struct {
   long volatile state ;
   void *stack ;
   atomic_t usage ;
   unsigned int flags ;
   unsigned int ptrace ;
   struct task_struct *wake_entry ;
   int on_cpu ;
   int on_rq ;
   int prio ;
   int static_prio ;
   int normal_prio ;
   unsigned int rt_priority ;
   struct sched_class const *sched_class ;
   struct sched_entity se ;
   struct sched_rt_entity rt ;
   struct hlist_head preempt_notifiers ;
   unsigned char fpu_counter ;
   unsigned int btrace_seq ;
   unsigned int policy ;
   cpumask_t cpus_allowed ;
   struct sched_info sched_info ;
   struct list_head tasks ;
   struct plist_node pushable_tasks ;
   struct mm_struct *mm ;
   struct mm_struct *active_mm ;
   unsigned int brk_randomized : 1 ;
   int exit_state ;
   int exit_code ;
   int exit_signal ;
   int pdeath_signal ;
   unsigned int group_stop ;
   unsigned int personality ;
   unsigned int did_exec : 1 ;
   unsigned int in_execve : 1 ;
   unsigned int in_iowait : 1 ;
   unsigned int sched_reset_on_fork : 1 ;
   unsigned int sched_contributes_to_load : 1 ;
   pid_t pid ;
   pid_t tgid ;
   unsigned long stack_canary ;
   struct task_struct *real_parent ;
   struct task_struct *parent ;
   struct list_head children ;
   struct list_head sibling ;
   struct task_struct *group_leader ;
   struct list_head ptraced ;
   struct list_head ptrace_entry ;
   struct pid_link pids[3] ;
   struct list_head thread_group ;
   struct completion *vfork_done ;
   int *set_child_tid ;
   int *clear_child_tid ;
   cputime_t utime ;
   cputime_t stime ;
   cputime_t utimescaled ;
   cputime_t stimescaled ;
   cputime_t gtime ;
   cputime_t prev_utime ;
   cputime_t prev_stime ;
   unsigned long nvcsw ;
   unsigned long nivcsw ;
   struct timespec start_time ;
   struct timespec real_start_time ;
   unsigned long min_flt ;
   unsigned long maj_flt ;
   struct task_cputime cputime_expires ;
   struct list_head cpu_timers[3] ;
   struct cred const *real_cred ;
   struct cred const *cred ;
   struct cred *replacement_session_keyring ;
   char comm[16] ;
   int link_count ;
   int total_link_count ;
   struct sysv_sem sysvsem ;
   unsigned long last_switch_count ;
   struct thread_struct thread ;
   struct fs_struct *fs ;
   struct files_struct *files ;
   struct nsproxy *nsproxy ;
   struct signal_struct *signal ;
   struct sighand_struct *sighand ;
   sigset_t blocked ;
   sigset_t real_blocked ;
   sigset_t saved_sigmask ;
   struct sigpending pending ;
   unsigned long sas_ss_sp ;
   size_t sas_ss_size ;
   int (*notifier)(void *priv ) ;
   void *notifier_data ;
   sigset_t *notifier_mask ;
   struct audit_context *audit_context ;
   uid_t loginuid ;
   unsigned int sessionid ;
   seccomp_t seccomp ;
   u32 parent_exec_id ;
   u32 self_exec_id ;
   spinlock_t alloc_lock ;
   struct irqaction *irqaction ;
   raw_spinlock_t pi_lock ;
   struct plist_head pi_waiters ;
   struct rt_mutex_waiter *pi_blocked_on ;
   struct mutex_waiter *blocked_on ;
   unsigned int irq_events ;
   unsigned long hardirq_enable_ip ;
   unsigned long hardirq_disable_ip ;
   unsigned int hardirq_enable_event ;
   unsigned int hardirq_disable_event ;
   int hardirqs_enabled ;
   int hardirq_context ;
   unsigned long softirq_disable_ip ;
   unsigned long softirq_enable_ip ;
   unsigned int softirq_disable_event ;
   unsigned int softirq_enable_event ;
   int softirqs_enabled ;
   int softirq_context ;
   u64 curr_chain_key ;
   int lockdep_depth ;
   unsigned int lockdep_recursion ;
   struct held_lock held_locks[48UL] ;
   gfp_t lockdep_reclaim_gfp ;
   void *journal_info ;
   struct bio_list *bio_list ;
   struct blk_plug *plug ;
   struct reclaim_state *reclaim_state ;
   struct backing_dev_info *backing_dev_info ;
   struct io_context *io_context ;
   unsigned long ptrace_message ;
   siginfo_t *last_siginfo ;
   struct task_io_accounting ioac ;
   u64 acct_rss_mem1 ;
   u64 acct_vm_mem1 ;
   cputime_t acct_timexpd ;
   nodemask_t mems_allowed ;
   int mems_allowed_change_disable ;
   int cpuset_mem_spread_rotor ;
   int cpuset_slab_spread_rotor ;
   struct css_set *cgroups ;
   struct list_head cg_list ;
   struct robust_list_head *robust_list ;
   struct compat_robust_list_head *compat_robust_list ;
   struct list_head pi_state_list ;
   struct futex_pi_state *pi_state_cache ;
   struct perf_event_context *perf_event_ctxp[2] ;
   struct mutex perf_event_mutex ;
   struct list_head perf_event_list ;
   struct mempolicy *mempolicy ;
   short il_next ;
   short pref_node_fork ;
   atomic_t fs_excl ;
   struct rcu_head rcu ;
   struct pipe_inode_info *splice_pipe ;
   struct task_delay_info *delays ;
   int make_it_fail ;
   struct prop_local_single dirties ;
   int latency_record_count ;
   struct latency_record latency_record[32] ;
   unsigned long timer_slack_ns ;
   unsigned long default_timer_slack_ns ;
   struct list_head *scm_work_list ;
   int curr_ret_stack ;
   struct ftrace_ret_stack *ret_stack ;
   unsigned long long ftrace_timestamp ;
   atomic_t trace_overrun ;
   atomic_t tracing_graph_pause ;
   unsigned long trace ;
   unsigned long trace_recursion ;
   struct memcg_batch_info memcg_batch ;
   atomic_t ptrace_bp_refcnt ;
};
struct pid_namespace;
struct usb_device;
struct usb_device;
struct usb_device;
struct usb_driver;
struct usb_driver;
struct usb_driver;
struct wusb_dev;
struct wusb_dev;
struct wusb_dev;
struct ep_device;
struct ep_device;
struct ep_device;
struct usb_host_endpoint {
   struct usb_endpoint_descriptor desc ;
   struct usb_ss_ep_comp_descriptor ss_ep_comp ;
   struct list_head urb_list ;
   void *hcpriv ;
   struct ep_device *ep_dev ;
   unsigned char *extra ;
   int extralen ;
   int enabled ;
};
struct usb_host_interface {
   struct usb_interface_descriptor desc ;
   struct usb_host_endpoint *endpoint ;
   char *string ;
   unsigned char *extra ;
   int extralen ;
};
enum usb_interface_condition {
    USB_INTERFACE_UNBOUND = 0,
    USB_INTERFACE_BINDING = 1,
    USB_INTERFACE_BOUND = 2,
    USB_INTERFACE_UNBINDING = 3
} ;
struct usb_interface {
   struct usb_host_interface *altsetting ;
   struct usb_host_interface *cur_altsetting ;
   unsigned int num_altsetting ;
   struct usb_interface_assoc_descriptor *intf_assoc ;
   int minor ;
   enum usb_interface_condition condition ;
   unsigned int sysfs_files_created : 1 ;
   unsigned int ep_devs_created : 1 ;
   unsigned int unregistering : 1 ;
   unsigned int needs_remote_wakeup : 1 ;
   unsigned int needs_altsetting0 : 1 ;
   unsigned int needs_binding : 1 ;
   unsigned int reset_running : 1 ;
   unsigned int resetting_device : 1 ;
   struct device dev ;
   struct device *usb_dev ;
   atomic_t pm_usage_cnt ;
   struct work_struct reset_ws ;
};
struct usb_interface_cache {
   unsigned int num_altsetting ;
   struct kref ref ;
   struct usb_host_interface altsetting[0] ;
};
struct usb_host_config {
   struct usb_config_descriptor desc ;
   char *string ;
   struct usb_interface_assoc_descriptor *intf_assoc[16] ;
   struct usb_interface *interface[32] ;
   struct usb_interface_cache *intf_cache[32] ;
   unsigned char *extra ;
   int extralen ;
};
struct usb_devmap {
   unsigned long devicemap[128UL / (8UL * sizeof(unsigned long ))] ;
};
struct mon_bus;
struct mon_bus;
struct usb_bus {
   struct device *controller ;
   int busnum ;
   char const *bus_name ;
   u8 uses_dma ;
   u8 uses_pio_for_control ;
   u8 otg_port ;
   unsigned int is_b_host : 1 ;
   unsigned int b_hnp_enable : 1 ;
   unsigned int sg_tablesize ;
   int devnum_next ;
   struct usb_devmap devmap ;
   struct usb_device *root_hub ;
   struct usb_bus *hs_companion ;
   struct list_head bus_list ;
   int bandwidth_allocated ;
   int bandwidth_int_reqs ;
   int bandwidth_isoc_reqs ;
   struct dentry *usbfs_dentry ;
   struct mon_bus *mon_bus ;
   int monitored ;
};
struct usb_tt;
struct usb_tt;
struct usb_tt;
struct usb_device {
   int devnum ;
   char devpath[16] ;
   u32 route ;
   enum usb_device_state state ;
   enum usb_device_speed speed ;
   struct usb_tt *tt ;
   int ttport ;
   unsigned int toggle[2] ;
   struct usb_device *parent ;
   struct usb_bus *bus ;
   struct usb_host_endpoint ep0 ;
   struct device dev ;
   struct usb_device_descriptor descriptor ;
   struct usb_host_config *config ;
   struct usb_host_config *actconfig ;
   struct usb_host_endpoint *ep_in[16] ;
   struct usb_host_endpoint *ep_out[16] ;
   char **rawdescriptors ;
   unsigned short bus_mA ;
   u8 portnum ;
   u8 level ;
   unsigned int can_submit : 1 ;
   unsigned int persist_enabled : 1 ;
   unsigned int have_langid : 1 ;
   unsigned int authorized : 1 ;
   unsigned int authenticated : 1 ;
   unsigned int wusb : 1 ;
   int string_langid ;
   char *product ;
   char *manufacturer ;
   char *serial ;
   struct list_head filelist ;
   struct device *usb_classdev ;
   struct dentry *usbfs_dentry ;
   int maxchild ;
   struct usb_device *children[31] ;
   u32 quirks ;
   atomic_t urbnum ;
   unsigned long active_duration ;
   unsigned long connect_time ;
   unsigned int do_remote_wakeup : 1 ;
   unsigned int reset_resume : 1 ;
   struct wusb_dev *wusb_dev ;
   int slot_id ;
};
struct usb_dynids {
   spinlock_t lock ;
   struct list_head list ;
};
struct usbdrv_wrap {
   struct device_driver driver ;
   int for_devices ;
};
struct usb_driver {
   char const *name ;
   int (*probe)(struct usb_interface *intf , struct usb_device_id const *id ) ;
   void (*disconnect)(struct usb_interface *intf ) ;
   int (*unlocked_ioctl)(struct usb_interface *intf , unsigned int code , void *buf ) ;
   int (*suspend)(struct usb_interface *intf , pm_message_t message ) ;
   int (*resume)(struct usb_interface *intf ) ;
   int (*reset_resume)(struct usb_interface *intf ) ;
   int (*pre_reset)(struct usb_interface *intf ) ;
   int (*post_reset)(struct usb_interface *intf ) ;
   struct usb_device_id const *id_table ;
   struct usb_dynids dynids ;
   struct usbdrv_wrap drvwrap ;
   unsigned int no_dynamic_id : 1 ;
   unsigned int supports_autosuspend : 1 ;
   unsigned int soft_unbind : 1 ;
};
struct usb_iso_packet_descriptor {
   unsigned int offset ;
   unsigned int length ;
   unsigned int actual_length ;
   int status ;
};
struct urb;
struct urb;
struct urb;
struct usb_anchor {
   struct list_head urb_list ;
   wait_queue_head_t wait ;
   spinlock_t lock ;
   unsigned int poisoned : 1 ;
};
struct scatterlist;
struct scatterlist;
struct urb {
   struct kref kref ;
   void *hcpriv ;
   atomic_t use_count ;
   atomic_t reject ;
   int unlinked ;
   struct list_head urb_list ;
   struct list_head anchor_list ;
   struct usb_anchor *anchor ;
   struct usb_device *dev ;
   struct usb_host_endpoint *ep ;
   unsigned int pipe ;
   unsigned int stream_id ;
   int status ;
   unsigned int transfer_flags ;
   void *transfer_buffer ;
   dma_addr_t transfer_dma ;
   struct scatterlist *sg ;
   int num_sgs ;
   u32 transfer_buffer_length ;
   u32 actual_length ;
   unsigned char *setup_packet ;
   dma_addr_t setup_dma ;
   int start_frame ;
   int number_of_packets ;
   int interval ;
   int error_count ;
   void *context ;
   void (*complete)(struct urb * ) ;
   struct usb_iso_packet_descriptor iso_frame_desc[0] ;
};
struct scatterlist;
struct serial_struct {
   int type ;
   int line ;
   unsigned int port ;
   int irq ;
   int flags ;
   int xmit_fifo_size ;
   int custom_divisor ;
   int baud_base ;
   unsigned short close_delay ;
   char io_type ;
   char reserved_char[1] ;
   int hub6 ;
   unsigned short closing_wait ;
   unsigned short closing_wait2 ;
   unsigned char *iomem_base ;
   unsigned short iomem_reg_shift ;
   unsigned int port_high ;
   unsigned long iomap_base ;
};
struct serial_icounter_struct {
   int cts ;
   int dsr ;
   int rng ;
   int dcd ;
   int rx ;
   int tx ;
   int frame ;
   int overrun ;
   int parity ;
   int brk ;
   int buf_overrun ;
   int reserved[9] ;
};
struct scatterlist {
   unsigned long sg_magic ;
   unsigned long page_link ;
   unsigned int offset ;
   unsigned int length ;
   dma_addr_t dma_address ;
   unsigned int dma_length ;
};
struct mempolicy;
struct anon_vma;
struct file_ra_state;
struct user_struct;
struct writeback_control;
struct mm_struct;
struct vm_area_struct;
struct vm_fault {
   unsigned int flags ;
   unsigned long pgoff ;
   void *virtual_address ;
   struct page *page ;
};
struct vm_operations_struct {
   void (*open)(struct vm_area_struct *area ) ;
   void (*close)(struct vm_area_struct *area ) ;
   int (*fault)(struct vm_area_struct *vma , struct vm_fault *vmf ) ;
   int (*page_mkwrite)(struct vm_area_struct *vma , struct vm_fault *vmf ) ;
   int (*access)(struct vm_area_struct *vma , unsigned long addr , void *buf , int len ,
                 int write ) ;
   int (*set_policy)(struct vm_area_struct *vma , struct mempolicy *new ) ;
   struct mempolicy *(*get_policy)(struct vm_area_struct *vma , unsigned long addr ) ;
   int (*migrate)(struct vm_area_struct *vma , nodemask_t const *from , nodemask_t const *to ,
                  unsigned long flags ) ;
};
struct inode;
struct page;
struct __kfifo {
   unsigned int in ;
   unsigned int out ;
   unsigned int mask ;
   unsigned int esize ;
   void *data ;
};
union __anonunion____missing_field_name_247 {
   struct __kfifo kfifo ;
   unsigned char *type ;
   char (*rectype)[0] ;
   void *ptr ;
   void const *ptr_const ;
};
struct kfifo {
   union __anonunion____missing_field_name_247 __annonCompField41 ;
   unsigned char buf[0] ;
};
enum port_dev_state {
    PORT_UNREGISTERED = 0,
    PORT_REGISTERING = 1,
    PORT_REGISTERED = 2,
    PORT_UNREGISTERING = 3
} ;
struct usb_serial;
struct usb_serial;
struct usb_serial_port {
   struct usb_serial *serial ;
   struct tty_port port ;
   spinlock_t lock ;
   unsigned char number ;
   unsigned char *interrupt_in_buffer ;
   struct urb *interrupt_in_urb ;
   __u8 interrupt_in_endpointAddress ;
   unsigned char *interrupt_out_buffer ;
   int interrupt_out_size ;
   struct urb *interrupt_out_urb ;
   __u8 interrupt_out_endpointAddress ;
   unsigned char *bulk_in_buffer ;
   int bulk_in_size ;
   struct urb *read_urb ;
   __u8 bulk_in_endpointAddress ;
   unsigned char *bulk_out_buffer ;
   int bulk_out_size ;
   struct urb *write_urb ;
   struct kfifo write_fifo ;
   int write_urb_busy ;
   unsigned char *bulk_out_buffers[2] ;
   struct urb *write_urbs[2] ;
   unsigned long write_urbs_free ;
   __u8 bulk_out_endpointAddress ;
   int tx_bytes ;
   unsigned long flags ;
   wait_queue_head_t write_wait ;
   struct work_struct work ;
   char throttled ;
   char throttle_req ;
   unsigned long sysrq ;
   struct device dev ;
   enum port_dev_state dev_state ;
};
struct usb_serial_driver;
struct usb_serial_driver;
struct usb_serial {
   struct usb_device *dev ;
   struct usb_serial_driver *type ;
   struct usb_interface *interface ;
   unsigned char disconnected : 1 ;
   unsigned char suspending : 1 ;
   unsigned char attached : 1 ;
   unsigned char minor ;
   unsigned char num_ports ;
   unsigned char num_port_pointers ;
   char num_interrupt_in ;
   char num_interrupt_out ;
   char num_bulk_in ;
   char num_bulk_out ;
   struct usb_serial_port *port[8] ;
   struct kref kref ;
   struct mutex disc_mutex ;
   void *private ;
};
struct usb_serial_driver {
   char const *description ;
   struct usb_device_id const *id_table ;
   char num_ports ;
   struct list_head driver_list ;
   struct device_driver driver ;
   struct usb_driver *usb_driver ;
   struct usb_dynids dynids ;
   size_t bulk_in_size ;
   size_t bulk_out_size ;
   int (*probe)(struct usb_serial *serial , struct usb_device_id const *id ) ;
   int (*attach)(struct usb_serial *serial ) ;
   int (*calc_num_ports)(struct usb_serial *serial ) ;
   void (*disconnect)(struct usb_serial *serial ) ;
   void (*release)(struct usb_serial *serial ) ;
   int (*port_probe)(struct usb_serial_port *port ) ;
   int (*port_remove)(struct usb_serial_port *port ) ;
   int (*suspend)(struct usb_serial *serial , pm_message_t message ) ;
   int (*resume)(struct usb_serial *serial ) ;
   int (*open)(struct tty_struct *tty , struct usb_serial_port *port ) ;
   void (*close)(struct usb_serial_port *port ) ;
   int (*write)(struct tty_struct *tty , struct usb_serial_port *port , unsigned char const *buf ,
                int count ) ;
   int (*write_room)(struct tty_struct *tty ) ;
   int (*ioctl)(struct tty_struct *tty , unsigned int cmd , unsigned long arg ) ;
   void (*set_termios)(struct tty_struct *tty , struct usb_serial_port *port , struct ktermios *old ) ;
   void (*break_ctl)(struct tty_struct *tty , int break_state ) ;
   int (*chars_in_buffer)(struct tty_struct *tty ) ;
   void (*throttle)(struct tty_struct *tty ) ;
   void (*unthrottle)(struct tty_struct *tty ) ;
   int (*tiocmget)(struct tty_struct *tty ) ;
   int (*tiocmset)(struct tty_struct *tty , unsigned int set , unsigned int clear ) ;
   int (*get_icount)(struct tty_struct *tty , struct serial_icounter_struct *icount ) ;
   void (*dtr_rts)(struct usb_serial_port *port , int on ) ;
   int (*carrier_raised)(struct usb_serial_port *port ) ;
   void (*init_termios)(struct tty_struct *tty ) ;
   void (*read_int_callback)(struct urb *urb ) ;
   void (*write_int_callback)(struct urb *urb ) ;
   void (*read_bulk_callback)(struct urb *urb ) ;
   void (*write_bulk_callback)(struct urb *urb ) ;
   void (*process_read_urb)(struct urb *urb ) ;
   int (*prepare_write_buffer)(struct usb_serial_port *port , void *dest , size_t size ) ;
};
struct firmware {
   size_t size ;
   u8 const *data ;
   struct page **pages ;
};
struct device;
struct ihex_binrec {
   __be32 addr ;
   __be16 len ;
   uint8_t data[0] ;
} __attribute__((__packed__)) ;
struct whiteheat_simple {
   __u8 port ;
};
struct whiteheat_port_settings {
   __u8 port ;
   __u32 baud ;
   __u8 bits ;
   __u8 stop ;
   __u8 parity ;
   __u8 sflow ;
   __u8 xoff ;
   __u8 xon ;
   __u8 hflow ;
   __u8 lloop ;
} __attribute__((__packed__)) ;
struct whiteheat_set_rdb {
   __u8 port ;
   __u8 state ;
};
struct whiteheat_purge {
   __u8 port ;
   __u8 what ;
};
struct whiteheat_dr_info {
   __u8 mcr ;
};
struct whiteheat_hw_eeprom_info {
   __u8 b0 ;
   __u8 vendor_id_low ;
   __u8 vendor_id_high ;
   __u8 product_id_low ;
   __u8 product_id_high ;
   __u8 device_id_low ;
   __u8 device_id_high ;
   __u8 not_used_1 ;
   __u8 serial_number_0 ;
   __u8 serial_number_1 ;
   __u8 serial_number_2 ;
   __u8 serial_number_3 ;
   __u8 not_used_2 ;
   __u8 not_used_3 ;
   __u8 checksum_low ;
   __u8 checksum_high ;
};
struct whiteheat_hw_info {
   __u8 hw_id ;
   __u8 sw_major_rev ;
   __u8 sw_minor_rev ;
   struct whiteheat_hw_eeprom_info hw_eeprom_info ;
};
struct whiteheat_command_private {
   struct mutex mutex ;
   __u8 port_running ;
   __u8 command_finished ;
   wait_queue_head_t wait_command ;
   __u8 result_buffer[64] ;
};
struct whiteheat_urb_wrap {
   struct list_head list ;
   struct urb *urb ;
};
struct whiteheat_private {
   spinlock_t lock ;
   __u8 flags ;
   __u8 mcr ;
   struct list_head rx_urbs_free ;
   struct list_head rx_urbs_submitted ;
   struct list_head rx_urb_q ;
   struct work_struct rx_work ;
   struct usb_serial_port *port ;
   struct list_head tx_urbs_free ;
   struct list_head tx_urbs_submitted ;
   struct mutex deathwarrant ;
};

__inline static __u32 __arch_swab32(__u32 val ) __attribute__((__const__)) ;
__inline static __u32 __arch_swab32(__u32 val ) __attribute__((__const__)) ;
__inline static __u32 __arch_swab32(__u32 val )
{

  {
  __asm__ ("bswapl %0": "=r" (val): "0" (val));
  return (val);
}
}
__inline static __u16 __fswab16(__u16 val ) __attribute__((__const__)) ;
__inline static __u16 __fswab16(__u16 val ) __attribute__((__const__)) ;
__inline static __u16 __fswab16(__u16 val )
{

  {
  return ((__u16 )((((int )val & 255) << 8) | (((int )val & 65280) >> 8)));
}
}
__inline static __u32 __fswab32(__u32 val ) __attribute__((__const__)) ;
__inline static __u32 __fswab32(__u32 val ) __attribute__((__const__)) ;
__inline static __u32 __fswab32(__u32 val )
{ __u32 tmp ;

  {
  {
  tmp = __arch_swab32(val);
  }
  return (tmp);
}
}
extern int printk(char const *fmt , ...) ;
extern void might_fault(void) ;
extern void __bad_percpu_size(void) ;
extern struct task_struct *current_task __attribute__((__section__(".data..percpu"))) ;
__inline static struct task_struct *( __attribute__((__always_inline__)) get_current)(void)
{ struct task_struct *pfo_ret__ ;

  {
  if ((int )sizeof(current_task) == 1) {
    goto case_1;
  } else
  if ((int )sizeof(current_task) == 2) {
    goto case_2;
  } else
  if ((int )sizeof(current_task) == 4) {
    goto case_4;
  } else
  if ((int )sizeof(current_task) == 8) {
    goto case_8;
  } else {
    goto switch_default;
    if (0) {
      case_1:
      __asm__ ("mov"
                "b "
                "%%"
                "gs"
                ":"
                "%P"
                "1"
                ",%0": "=q" (pfo_ret__): "p" (& current_task));
      goto switch_break;
      case_2:
      __asm__ ("mov"
                "w "
                "%%"
                "gs"
                ":"
                "%P"
                "1"
                ",%0": "=r" (pfo_ret__): "p" (& current_task));
      goto switch_break;
      case_4:
      __asm__ ("mov"
                "l "
                "%%"
                "gs"
                ":"
                "%P"
                "1"
                ",%0": "=r" (pfo_ret__): "p" (& current_task));
      goto switch_break;
      case_8:
      __asm__ ("mov"
                "q "
                "%%"
                "gs"
                ":"
                "%P"
                "1"
                ",%0": "=r" (pfo_ret__): "p" (& current_task));
      goto switch_break;
      switch_default:
      {
      __bad_percpu_size();
      }
    } else {
      switch_break: ;
    }
  }
  return (pfo_ret__);
}
}
extern void *__memcpy(void *to , void const *from , size_t len ) ;
extern void *memset(void *s , int c , size_t n ) ;
__inline static void INIT_LIST_HEAD(struct list_head *list )
{

  {
  list->next = list;
  list->prev = list;
  return;
}
}
extern void __list_add(struct list_head *new , struct list_head *prev , struct list_head *next ) ;
__inline static void list_add(struct list_head *new , struct list_head *head )
{

  {
  {
  __list_add(new, head, head->next);
  }
  return;
}
}
__inline static void list_add_tail(struct list_head *new , struct list_head *head )
{

  {
  {
  __list_add(new, head->prev, head);
  }
  return;
}
}
extern void __list_del_entry(struct list_head *entry ) ;
extern void list_del(struct list_head *entry ) ;
__inline static void list_move(struct list_head *list , struct list_head *head )
{

  {
  {
  __list_del_entry(list);
  list_add(list, head);
  }
  return;
}
}
__inline static int list_empty(struct list_head const *head )
{

  {
  return ((unsigned long )head->next == (unsigned long )head);
}
}
extern void lockdep_init_map(struct lockdep_map *lock , char const *name , struct lock_class_key *key ,
                             int subclass ) ;
extern void __raw_spin_lock_init(raw_spinlock_t *lock , char const *name , struct lock_class_key *key ) ;
extern void _raw_spin_lock(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
extern void _raw_spin_lock_irq(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
extern unsigned long _raw_spin_lock_irqsave(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
extern void _raw_spin_unlock(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
extern void _raw_spin_unlock_irq(raw_spinlock_t *lock ) __attribute__((__section__(".spinlock.text"))) ;
extern void _raw_spin_unlock_irqrestore(raw_spinlock_t *lock , unsigned long flags ) __attribute__((__section__(".spinlock.text"))) ;
__inline static raw_spinlock_t *spinlock_check(spinlock_t *lock )
{

  {
  return (& lock->__annonCompField18.rlock);
}
}
__inline static void spin_lock(spinlock_t *lock )
{

  {
  {
  _raw_spin_lock(& lock->__annonCompField18.rlock);
  }
  return;
}
}
__inline static void spin_lock_irq(spinlock_t *lock )
{

  {
  {
  _raw_spin_lock_irq(& lock->__annonCompField18.rlock);
  }
  return;
}
}
__inline static void spin_unlock(spinlock_t *lock )
{

  {
  {
  _raw_spin_unlock(& lock->__annonCompField18.rlock);
  }
  return;
}
}
__inline static void spin_unlock_irq(spinlock_t *lock )
{

  {
  {
  _raw_spin_unlock_irq(& lock->__annonCompField18.rlock);
  }
  return;
}
}
__inline static void spin_unlock_irqrestore(spinlock_t *lock , unsigned long flags )
{

  {
  {
  while (1) {
    while_continue: ;
    {
    _raw_spin_unlock_irqrestore(& lock->__annonCompField18.rlock, flags);
    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  return;
}
}
extern void __init_waitqueue_head(wait_queue_head_t *q , struct lock_class_key * ) ;
extern void __wake_up(wait_queue_head_t *q , unsigned int mode , int nr , void *key ) ;
extern void prepare_to_wait(wait_queue_head_t *q , wait_queue_t *wait , int state ) ;
extern void finish_wait(wait_queue_head_t *q , wait_queue_t *wait ) ;
extern int autoremove_wake_function(wait_queue_t *wait , unsigned int mode , int sync ,
                                    void *key ) ;
extern void __mutex_init(struct mutex *lock , char const *name , struct lock_class_key *key ) ;
extern void mutex_lock_nested(struct mutex *lock , unsigned int subclass ) ;
extern void mutex_unlock(struct mutex *lock ) ;
extern void __init_work(struct work_struct *work , int onstack ) ;
extern int schedule_work(struct work_struct *work ) ;
extern void kfree(void const * ) ;
extern void *kzalloc(size_t size , gfp_t flags ) ;
extern void *__kmalloc(size_t size , gfp_t flags ) ;
__inline static void *( __attribute__((__always_inline__)) kmalloc)(size_t size ,
                                                                    gfp_t flags )
{ void *tmp___2 ;

  {
  {
  tmp___2 = __kmalloc(size, flags);
  }
  return (tmp___2);
}
}
extern unsigned long __attribute__((__warn_unused_result__)) _copy_to_user(void *to ,
                                                                            void const *from ,
                                                                            unsigned int len ) ;
__inline static int __attribute__((__warn_unused_result__)) ( __attribute__((__always_inline__)) copy_to_user)(void *dst ,
                                                                                                                void const *src ,
                                                                                                                unsigned int size )
{ unsigned long tmp ;
  unsigned long tmp___0 ;

  {
  {
  might_fault();
  tmp___0 = (unsigned long )_copy_to_user(dst, src, size);
  tmp = tmp___0;
  }
  return ((int )tmp);
}
}
extern struct kernel_param_ops param_ops_int ;
extern struct kernel_param_ops param_ops_bool ;
int init_module(void) ;
void cleanup_module(void) ;
extern struct module __this_module ;
int device_private_init(struct device *dev)
{
  dev->p = kzalloc(sizeof(*dev->p), 208U);
  if (!dev->p)
    return -12;
  dev->p->device = dev;
  return 0;
}

void *dev_get_drvdata(struct device const *dev ) __attribute__((__ldv_model__));
void *dev_get_drvdata(struct device const *dev ) {
   if (dev && dev->p)
     return dev->p->driver_data;
   return 0;
}
extern int dev_set_drvdata(struct device *dev , void *data ) {
   int error;
 
   if (!dev->p) {
     error = device_private_init(dev);
     if (error)
       return error;
   }
   dev->p->driver_data = data;
   return 0;
}
extern int dev_printk(char const *level , struct device const *dev , char const *fmt
                      , ...) ;
extern int dev_err(struct device const *dev , char const *fmt , ...) ;
extern int _dev_info(struct device const *dev , char const *fmt , ...) ;
extern void tty_kref_put(struct tty_struct *tty ) ;
extern void tty_flip_buffer_push(struct tty_struct *tty ) ;
extern speed_t tty_get_baud_rate(struct tty_struct *tty ) ;
extern void tty_encode_baud_rate(struct tty_struct *tty , speed_t ibaud , speed_t obaud ) ;
extern struct tty_struct *tty_port_tty_get(struct tty_port *port ) ;
extern int tty_insert_flip_string_fixed_flag(struct tty_struct *tty , unsigned char const *chars ,
                                             char flag , size_t size ) ;
__inline static int tty_insert_flip_string(struct tty_struct *tty , unsigned char const *chars ,
                                           size_t size )
{ int tmp ;

  {
  {
  tmp = tty_insert_flip_string_fixed_flag(tty, chars, (char)0, size);
  }
  return (tmp);
}
}
extern long schedule_timeout(long timeout ) ;
extern int usb_register_driver(struct usb_driver * , struct module * , char const * ) ;
__inline static int usb_register(struct usb_driver *driver )
{ int tmp___7 ;

  {
  {
  tmp___7 = usb_register_driver(driver, & __this_module, "whiteheat");
  }
  return (tmp___7);
}
}
extern void usb_deregister(struct usb_driver * ) ;
__inline static void usb_fill_bulk_urb(struct urb *urb , struct usb_device *dev ,
                                       unsigned int pipe , void *transfer_buffer ,
                                       int buffer_length , void (*complete_fn)(struct urb * ) ,
                                       void *context )
{

  {
  urb->dev = dev;
  urb->pipe = pipe;
  urb->transfer_buffer = transfer_buffer;
  urb->transfer_buffer_length = (u32 )buffer_length;
  urb->complete = complete_fn;
  urb->context = context;
  return;
}
}
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags ) __attribute__((__ldv_model__)) ;
void usb_free_urb(struct urb *urb ) __attribute__((__ldv_model__)) ;
extern int usb_submit_urb(struct urb *urb , gfp_t mem_flags ) ;
extern void usb_kill_urb(struct urb *urb ) ;
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma ) __attribute__((__ldv_model__)) ;
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma ) __attribute__((__ldv_model__)) ;
extern int usb_bulk_msg(struct usb_device *usb_dev , unsigned int pipe , void *data ,
                        int len , int *actual_length , int timeout ) ;
extern int usb_clear_halt(struct usb_device *dev , int pipe ) ;
__inline static unsigned int __create_pipe(struct usb_device *dev , unsigned int endpoint )
{

  {
  return ((unsigned int )(dev->devnum << 8) | (endpoint << 15));
}
}
__inline static void *usb_get_serial_port_data(struct usb_serial_port *port )
{ void *tmp___7 ;

  {
  {
  tmp___7 = dev_get_drvdata((struct device const *)(& port->dev));
  }
  return (tmp___7);
}
}
__inline static void usb_set_serial_port_data(struct usb_serial_port *port , void *data )
{

  {
  {
  dev_set_drvdata(& port->dev, data);
  }
  return;
}
}
extern int usb_serial_register(struct usb_serial_driver *driver ) ;
extern void usb_serial_deregister(struct usb_serial_driver *driver ) ;
extern void usb_serial_port_softint(struct usb_serial_port *port ) ;
extern int usb_serial_probe(struct usb_interface *iface , struct usb_device_id const *id ) ;
extern void usb_serial_disconnect(struct usb_interface *iface ) ;
extern int ezusb_writememory(struct usb_serial *serial , int address , unsigned char *data ,
                             int length , __u8 bRequest ) ;
extern int ezusb_set_reset(struct usb_serial *serial , unsigned char reset_bit ) ;
__inline static void usb_serial_debug_data(int debug , struct device *dev , char const *function ,
                                           int size , unsigned char const *data )
{ int i ;

  {
  if (debug) {
    {
    dev_printk("<7>", (struct device const *)dev, "%s - length = %d, data = ", function,
               size);
    i = 0;
    }
    {
    while (1) {
      while_continue: ;
      if (i < size) {

      } else {
        goto while_break;
      }
      {
      printk("%.2x ", (int const )*(data + i));
      i = i + 1;
      }
    }
    while_break___0: ;
    }
    while_break:
    {
    printk("\n");
    }
  } else {

  }
  return;
}
}
extern int request_firmware(struct firmware const **fw , char const *name , struct device *device ) ;
extern void release_firmware(struct firmware const *fw ) ;
__inline static struct ihex_binrec const *ihex_next_binrec(struct ihex_binrec const *rec )
{ int next ;
  __u16 tmp___7 ;
  struct ihex_binrec const *tmp___9 ;
  __u16 tmp___10 ;

  {
  {
  tmp___7 = __fswab16((__be16 )rec->len);
  next = (((int )tmp___7 + 5) & -4) - 2;
  rec = (struct ihex_binrec const *)((void *)(& rec->data[next]));
  tmp___10 = __fswab16((__be16 )rec->len);
  }
  if ((int )tmp___10) {
    tmp___9 = rec;
  } else {
    tmp___9 = (struct ihex_binrec const *)((void *)0);
  }
  return (tmp___9);
}
}
__inline static int ihex_validate_fw(struct firmware const *fw )
{ struct ihex_binrec const *rec ;
  size_t ofs ;
  __u16 tmp___7 ;
  __u16 tmp___8 ;

  {
  ofs = (size_t )0;
  {
  while (1) {
    while_continue: ;
    if (ofs <= (size_t )(fw->size - (size_t const )sizeof(*rec))) {

    } else {
      goto while_break;
    }
    {
    rec = (struct ihex_binrec const *)((void *)(fw->data + ofs));
    tmp___7 = __fswab16((__be16 )rec->len);
    }
    if ((int )tmp___7) {

    } else {
      return (0);
    }
    {
    tmp___8 = __fswab16((__be16 )rec->len);
    ofs = ofs + (((sizeof(*rec) + (unsigned long )((int )tmp___8)) + 3UL) & 0x0ffffffffffffffcUL);
    }
  }
  while_break___0: ;
  }
  while_break: ;
  return (-22);
}
}
__inline static int request_ihex_firmware(struct firmware const **fw , char const *fw_name ,
                                          struct device *dev )
{ struct firmware const *lfw ;
  int ret ;

  {
  {
  ret = request_firmware(& lfw, fw_name, dev);
  }
  if (ret) {
    return (ret);
  } else {

  }
  {
  ret = ihex_validate_fw(lfw);
  }
  if (ret) {
    {
    dev_err((struct device const *)dev, "Firmware \"%s\" not valid IHEX records\n",
            fw_name);
    release_firmware(lfw);
    }
    return (ret);
  } else {

  }
  *fw = lfw;
  return (0);
}
}
static int debug ;
static struct usb_device_id const id_table_std[1] = { {(__u16 )3, (__u16 )1808, (__u16 )32769, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL}};
static struct usb_device_id const id_table_prerenumeration[1] = { {(__u16 )3, (__u16 )1808, (__u16 )1, (unsigned short)0, (unsigned short)0, (unsigned char)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      0UL}};
static struct usb_device_id const id_table_combined[2] = { {(__u16 )3, (__u16 )1808, (__u16 )32769, (unsigned short)0, (unsigned short)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      (unsigned char)0, 0UL},
        {(__u16 )3, (__u16 )1808, (__u16 )1, (unsigned short)0, (unsigned short)0, (unsigned char)0,
      (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0, (unsigned char)0,
      0UL}};
extern struct usb_device_id const __mod_usb_device_table __attribute__((__unused__,
__alias__("id_table_combined"))) ;
static struct usb_driver whiteheat_driver =
     {"whiteheat", & usb_serial_probe, & usb_serial_disconnect, (int (*)(struct usb_interface *intf ,
                                                                       unsigned int code ,
                                                                       void *buf ))0,
    (int (*)(struct usb_interface *intf , pm_message_t message ))0, (int (*)(struct usb_interface *intf ))0,
    (int (*)(struct usb_interface *intf ))0, (int (*)(struct usb_interface *intf ))0,
    (int (*)(struct usb_interface *intf ))0, id_table_combined, {{{{{0U}, 0U, 0U,
                                                                    (void *)0, {(struct lock_class_key *)0,
                                                                                {(struct lock_class *)0,
                                                                                 (struct lock_class *)0},
                                                                                (char const *)0,
                                                                                0,
                                                                                0UL}}}},
                                                                 {(struct list_head *)0,
                                                                  (struct list_head *)0}},
    {{(char const *)0, (struct bus_type *)0, (struct module *)0, (char const *)0,
      (_Bool)0, (struct of_device_id const *)0, (int (*)(struct device *dev ))0,
      (int (*)(struct device *dev ))0, (void (*)(struct device *dev ))0, (int (*)(struct device *dev ,
                                                                                  pm_message_t state ))0,
      (int (*)(struct device *dev ))0, (struct attribute_group const **)0, (struct dev_pm_ops const *)0,
      (struct driver_private *)0}, 0}, 1U, 0U, 0U};
static int whiteheat_firmware_download(struct usb_serial *serial , struct usb_device_id const *id ) ;
static int whiteheat_firmware_attach(struct usb_serial *serial ) ;
static int whiteheat_attach(struct usb_serial *serial ) ;
static void whiteheat_release(struct usb_serial *serial ) ;
static int whiteheat_open(struct tty_struct *tty , struct usb_serial_port *port ) ;
static void whiteheat_close(struct usb_serial_port *port ) ;
static int whiteheat_write(struct tty_struct *tty , struct usb_serial_port *port ,
                           unsigned char const *buf , int count ) ;
static int whiteheat_write_room(struct tty_struct *tty ) ;
static int whiteheat_ioctl(struct tty_struct *tty , unsigned int cmd , unsigned long arg ) ;
static void whiteheat_set_termios(struct tty_struct *tty , struct usb_serial_port *port ,
                                  struct ktermios *old_termios ) ;
static int whiteheat_tiocmget(struct tty_struct *tty ) ;
static int whiteheat_tiocmset(struct tty_struct *tty , unsigned int set , unsigned int clear ) ;
static void whiteheat_break_ctl(struct tty_struct *tty , int break_state ) ;
static int whiteheat_chars_in_buffer(struct tty_struct *tty ) ;
static void whiteheat_throttle(struct tty_struct *tty ) ;
static void whiteheat_unthrottle(struct tty_struct *tty ) ;
static void whiteheat_read_callback(struct urb *urb ) ;
static void whiteheat_write_callback(struct urb *urb ) ;
static struct usb_serial_driver whiteheat_fake_device =
     {"Connect Tech - WhiteHEAT - (prerenumeration)", id_table_prerenumeration, (char)1,
    {(struct list_head *)0, (struct list_head *)0}, {"whiteheatnofirm", (struct bus_type *)0,
                                                     & __this_module, (char const *)0,
                                                     (_Bool)0, (struct of_device_id const *)0,
                                                     (int (*)(struct device *dev ))0,
                                                     (int (*)(struct device *dev ))0,
                                                     (void (*)(struct device *dev ))0,
                                                     (int (*)(struct device *dev ,
                                                              pm_message_t state ))0,
                                                     (int (*)(struct device *dev ))0,
                                                     (struct attribute_group const **)0,
                                                     (struct dev_pm_ops const *)0,
                                                     (struct driver_private *)0},
    & whiteheat_driver, {{{{{0U}, 0U, 0U, (void *)0, {(struct lock_class_key *)0,
                                                      {(struct lock_class *)0, (struct lock_class *)0},
                                                      (char const *)0, 0, 0UL}}}},
                         {(struct list_head *)0, (struct list_head *)0}}, 0UL, 0UL,
    & whiteheat_firmware_download, & whiteheat_firmware_attach, (int (*)(struct usb_serial *serial ))0,
    (void (*)(struct usb_serial *serial ))0, (void (*)(struct usb_serial *serial ))0,
    (int (*)(struct usb_serial_port *port ))0, (int (*)(struct usb_serial_port *port ))0,
    (int (*)(struct usb_serial *serial , pm_message_t message ))0, (int (*)(struct usb_serial *serial ))0,
    (int (*)(struct tty_struct *tty , struct usb_serial_port *port ))0, (void (*)(struct usb_serial_port *port ))0,
    (int (*)(struct tty_struct *tty , struct usb_serial_port *port , unsigned char const *buf ,
             int count ))0, (int (*)(struct tty_struct *tty ))0, (int (*)(struct tty_struct *tty ,
                                                                          unsigned int cmd ,
                                                                          unsigned long arg ))0,
    (void (*)(struct tty_struct *tty , struct usb_serial_port *port , struct ktermios *old ))0,
    (void (*)(struct tty_struct *tty , int break_state ))0, (int (*)(struct tty_struct *tty ))0,
    (void (*)(struct tty_struct *tty ))0, (void (*)(struct tty_struct *tty ))0, (int (*)(struct tty_struct *tty ))0,
    (int (*)(struct tty_struct *tty , unsigned int set , unsigned int clear ))0, (int (*)(struct tty_struct *tty ,
                                                                                          struct serial_icounter_struct *icount ))0,
    (void (*)(struct usb_serial_port *port , int on ))0, (int (*)(struct usb_serial_port *port ))0,
    (void (*)(struct tty_struct *tty ))0, (void (*)(struct urb *urb ))0, (void (*)(struct urb *urb ))0,
    (void (*)(struct urb *urb ))0, (void (*)(struct urb *urb ))0, (void (*)(struct urb *urb ))0,
    (int (*)(struct usb_serial_port *port , void *dest , size_t size ))0};
static struct usb_serial_driver whiteheat_device =
     {"Connect Tech - WhiteHEAT", id_table_std, (char)4, {(struct list_head *)0, (struct list_head *)0},
    {"whiteheat", (struct bus_type *)0, & __this_module, (char const *)0, (_Bool)0,
     (struct of_device_id const *)0, (int (*)(struct device *dev ))0, (int (*)(struct device *dev ))0,
     (void (*)(struct device *dev ))0, (int (*)(struct device *dev , pm_message_t state ))0,
     (int (*)(struct device *dev ))0, (struct attribute_group const **)0, (struct dev_pm_ops const *)0,
     (struct driver_private *)0}, & whiteheat_driver, {{{{{0U}, 0U, 0U, (void *)0,
                                                          {(struct lock_class_key *)0,
                                                           {(struct lock_class *)0,
                                                            (struct lock_class *)0},
                                                           (char const *)0, 0, 0UL}}}},
                                                       {(struct list_head *)0, (struct list_head *)0}},
    0UL, 0UL, (int (*)(struct usb_serial *serial , struct usb_device_id const *id ))0,
    & whiteheat_attach, (int (*)(struct usb_serial *serial ))0, (void (*)(struct usb_serial *serial ))0,
    & whiteheat_release, (int (*)(struct usb_serial_port *port ))0, (int (*)(struct usb_serial_port *port ))0,
    (int (*)(struct usb_serial *serial , pm_message_t message ))0, (int (*)(struct usb_serial *serial ))0,
    & whiteheat_open, & whiteheat_close, & whiteheat_write, & whiteheat_write_room,
    & whiteheat_ioctl, & whiteheat_set_termios, & whiteheat_break_ctl, & whiteheat_chars_in_buffer,
    & whiteheat_throttle, & whiteheat_unthrottle, & whiteheat_tiocmget, & whiteheat_tiocmset,
    (int (*)(struct tty_struct *tty , struct serial_icounter_struct *icount ))0, (void (*)(struct usb_serial_port *port ,
                                                                                           int on ))0,
    (int (*)(struct usb_serial_port *port ))0, (void (*)(struct tty_struct *tty ))0,
    (void (*)(struct urb *urb ))0, (void (*)(struct urb *urb ))0, & whiteheat_read_callback,
    & whiteheat_write_callback, (void (*)(struct urb *urb ))0, (int (*)(struct usb_serial_port *port ,
                                                                        void *dest ,
                                                                        size_t size ))0};
static int urb_pool_size = 8;
static int start_command_port(struct usb_serial *serial ) ;
static void stop_command_port(struct usb_serial *serial ) ;
static void command_port_write_callback(struct urb *urb ) ;
static void command_port_read_callback(struct urb *urb ) ;
static int start_port_read(struct usb_serial_port *port ) ;
static struct whiteheat_urb_wrap *urb_to_wrap(struct urb *urb , struct list_head *head ) ;
static struct list_head *list_first(struct list_head *head ) ;
static void rx_data_softint(struct work_struct *work ) ;
static int firm_send_command(struct usb_serial_port *port , __u8 command , __u8 *data ,
                             __u8 datasize ) ;
static int firm_open(struct usb_serial_port *port ) ;
static int firm_close(struct usb_serial_port *port ) ;
static void firm_setup_port(struct tty_struct *tty ) ;
static int firm_set_rts(struct usb_serial_port *port , __u8 onoff ) ;
static int firm_set_dtr(struct usb_serial_port *port , __u8 onoff ) ;
static int firm_set_break(struct usb_serial_port *port , __u8 onoff ) ;
static int firm_purge(struct usb_serial_port *port , __u8 rxtx ) ;
static int firm_get_dtr_rts(struct usb_serial_port *port ) ;
static int firm_report_tx_done(struct usb_serial_port *port ) ;
static int whiteheat_firmware_download(struct usb_serial *serial , struct usb_device_id const *id )
{ int response ;
  int ret ;
  struct firmware const *loader_fw ;
  struct firmware const *firmware_fw ;
  struct ihex_binrec const *record ;
  int tmp___7 ;
  int tmp___8 ;
  __u16 tmp___9 ;
  __u32 tmp___10 ;
  __u16 tmp___11 ;
  __u32 tmp___12 ;
  __u32 tmp___13 ;
  __u16 tmp___14 ;
  __u32 tmp___15 ;
  __u16 tmp___16 ;
  __u32 tmp___17 ;
  __u16 tmp___18 ;
  __u32 tmp___19 ;
  __u16 tmp___20 ;
  __u32 tmp___21 ;
  __u32 tmp___22 ;

  {
  ret = -2;
  loader_fw = (struct firmware const *)((void *)0);
  firmware_fw = (struct firmware const *)((void *)0);
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_firmware_download");
      }
    } else {

    }
    goto while_break;
  }
  while_break___4: ;
  }
  while_break:
  {
  tmp___7 = request_ihex_firmware(& firmware_fw, "whiteheat.fw", & (serial->dev)->dev);
  }
  if (tmp___7) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s - request \"whiteheat.fw\" failed\n",
            "whiteheat_firmware_download");
    }
    goto out;
  } else {

  }
  {
  tmp___8 = request_ihex_firmware(& loader_fw, "whiteheat_loader.fw", & (serial->dev)->dev);
  }
  if (tmp___8) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s - request \"whiteheat_loader.fw\" failed\n",
            "whiteheat_firmware_download");
    }
    goto out;
  } else {

  }
  {
  ret = 0;
  response = ezusb_set_reset(serial, (unsigned char)1);
  record = (struct ihex_binrec const *)loader_fw->data;
  }
  {
  while (1) {
    while_continue___0: ;
    if (record) {

    } else {
      goto while_break___0;
    }
    {
    tmp___9 = __fswab16((__be16 )record->len);
    tmp___10 = __fswab32((__be32 )record->addr);
    response = ezusb_writememory(serial, (int )tmp___10, (unsigned char *)(record->data),
                                 (int )tmp___9, (__u8 )160);
    }
    if (response < 0) {
      {
      tmp___11 = __fswab16((__be16 )record->len);
      tmp___12 = __fswab32((__be32 )record->addr);
      dev_err((struct device const *)(& (serial->dev)->dev), "%s - ezusb_writememory failed for loader (%d %04X %p %d)\n",
              "whiteheat_firmware_download", response, tmp___12, record->data, (int )tmp___11);
      }
      goto while_break___0;
    } else {

    }
    {
    record = ihex_next_binrec(record);
    }
  }
  while_break___5: ;
  }
  while_break___0:
  {
  response = ezusb_set_reset(serial, (unsigned char)0);
  record = (struct ihex_binrec const *)firmware_fw->data;
  }
  {
  while (1) {
    while_continue___1: ;
    if (record) {
      {
      tmp___13 = __fswab32((__be32 )record->addr);
      }
      if (tmp___13 < 6976U) {

      } else {
        goto while_break___1;
      }
    } else {
      goto while_break___1;
    }
    {
    record = ihex_next_binrec(record);
    }
  }
  while_break___6: ;
  }
  while_break___1: ;
  {
  while (1) {
    while_continue___2: ;
    if (record) {

    } else {
      goto while_break___2;
    }
    {
    tmp___14 = __fswab16((__be16 )record->len);
    tmp___15 = __fswab32((__be32 )record->addr);
    response = ezusb_writememory(serial, (int )tmp___15, (unsigned char *)(record->data),
                                 (int )tmp___14, (__u8 )163);
    }
    if (response < 0) {
      {
      tmp___16 = __fswab16((__be16 )record->len);
      tmp___17 = __fswab32((__be32 )record->addr);
      dev_err((struct device const *)(& (serial->dev)->dev), "%s - ezusb_writememory failed for first firmware step (%d %04X %p %d)\n",
              "whiteheat_firmware_download", response, tmp___17, record->data, (int )tmp___16);
      }
      goto while_break___2;
    } else {

    }
    record = record + 1;
  }
  while_break___7: ;
  }
  while_break___2:
  {
  response = ezusb_set_reset(serial, (unsigned char)1);
  record = (struct ihex_binrec const *)firmware_fw->data;
  }
  {
  while (1) {
    while_continue___3: ;
    if (record) {
      {
      tmp___22 = __fswab32((__be32 )record->addr);
      }
      if (tmp___22 < 6976U) {

      } else {
        goto while_break___3;
      }
    } else {
      goto while_break___3;
    }
    {
    tmp___18 = __fswab16((__be16 )record->len);
    tmp___19 = __fswab32((__be32 )record->addr);
    response = ezusb_writememory(serial, (int )tmp___19, (unsigned char *)(record->data),
                                 (int )tmp___18, (__u8 )160);
    }
    if (response < 0) {
      {
      tmp___20 = __fswab16((__be16 )record->len);
      tmp___21 = __fswab32((__be32 )record->addr);
      dev_err((struct device const *)(& (serial->dev)->dev), "%s - ezusb_writememory failed for second firmware step (%d %04X %p %d)\n",
              "whiteheat_firmware_download", response, tmp___21, record->data, (int )tmp___20);
      }
      goto while_break___3;
    } else {

    }
    record = record + 1;
  }
  while_break___8: ;
  }
  while_break___3:
  {
  ret = 0;
  response = ezusb_set_reset(serial, (unsigned char)0);
  }
  out:
  {
  release_firmware(loader_fw);
  release_firmware(firmware_fw);
  }
  return (ret);
}
}
static int whiteheat_firmware_attach(struct usb_serial *serial )
{

  {
  return (1);
}
}
static struct lock_class_key __key___7 ;
static struct lock_class_key __key___8 ;
static struct lock_class_key __key___9 ;
static struct lock_class_key __key___10 ;
static struct lock_class_key __key___11 ;
static int whiteheat_attach(struct usb_serial *serial )
{ struct usb_serial_port *command_port ;
  struct whiteheat_command_private *command_info ;
  struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  struct whiteheat_hw_info *hw_info ;
  int pipe ;
  int ret ;
  int alen ;
  __u8 *command ;
  __u8 *result ;
  int i ;
  int j ;
  struct urb *urb ;
  int buf_size ;
  struct whiteheat_urb_wrap *wrap ;
  struct list_head *tmp___7 ;
  unsigned int tmp___8 ;
  void *tmp___9 ;
  void *tmp___10 ;
  unsigned int tmp___11 ;
  void *tmp___12 ;
  atomic_long_t __constr_expr_0 ;
  void *tmp___13 ;
  unsigned int tmp___14 ;
  void *tmp___15 ;
  unsigned int tmp___16 ;
  void *tmp___17 ;
  void *tmp___18 ;
  struct list_head const *__mptr ;
  struct list_head const *__mptr___0 ;

  {
  {
  command_port = serial->port[4];
  tmp___8 = __create_pipe(serial->dev, (unsigned int )command_port->bulk_out_endpointAddress);
  pipe = (int )((unsigned int )(3 << 30) | tmp___8);
  tmp___9 = kmalloc((size_t )2, 208U);
  command = (__u8 *)tmp___9;
  }
  if (! command) {
    goto no_command_buffer;
  } else {

  }
  {
  *(command + 0) = (__u8 )11;
  *(command + 1) = (__u8 )0;
  tmp___10 = kmalloc(sizeof(*hw_info) + 1UL, 208U);
  result = (__u8 *)tmp___10;
  }
  if (! result) {
    goto no_result_buffer;
  } else {

  }
  {
  usb_clear_halt(serial->dev, pipe);
  ret = usb_bulk_msg(serial->dev, (unsigned int )pipe, (void *)command, 2, & alen,
                     2000);
  }
  if (ret) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Couldn\'t send command [%d]\n",
            (serial->type)->description, ret);
    }
    goto no_firmware;
  } else
  if (alen != 2) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Send command incomplete [%d]\n",
            (serial->type)->description, alen);
    }
    goto no_firmware;
  } else {

  }
  {
  tmp___11 = __create_pipe(serial->dev, (unsigned int )command_port->bulk_in_endpointAddress);
  pipe = (int )(((unsigned int )(3 << 30) | tmp___11) | 128U);
  usb_clear_halt(serial->dev, pipe);
  ret = usb_bulk_msg(serial->dev, (unsigned int )pipe, (void *)result, (int )(sizeof(*hw_info) + 1UL),
                     & alen, 2000);
  }
  if (ret) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Couldn\'t get results [%d]\n",
            (serial->type)->description, ret);
    }
    goto no_firmware;
  } else
  if ((unsigned long )alen != sizeof(*hw_info) + 1UL) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Get results incomplete [%d]\n",
            (serial->type)->description, alen);
    }
    goto no_firmware;
  } else
  if ((int )*(result + 0) != (int )*(command + 0)) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Command failed [%d]\n",
            (serial->type)->description, (int )*(result + 0));
    }
    goto no_firmware;
  } else {

  }
  {
  hw_info = (struct whiteheat_hw_info *)(result + 1);
  _dev_info((struct device const *)(& (serial->dev)->dev), "%s: Driver %s: Firmware v%d.%02d\n",
            (serial->type)->description, "v2.0", (int )hw_info->sw_major_rev, (int )hw_info->sw_minor_rev);
  i = 0;
  }
  {
  while (1) {
    while_continue: ;
    if (i < (int )serial->num_ports) {

    } else {
      goto while_break;
    }
    {
    port = serial->port[i];
    tmp___12 = kmalloc(sizeof(struct whiteheat_private ), 208U);
    info = (struct whiteheat_private *)tmp___12;
    }
    if ((unsigned long )info == (unsigned long )((void *)0)) {
      {
      dev_err((struct device const *)(& port->dev), "%s: Out of memory for port structures\n",
              (serial->type)->description);
      }
      goto no_private;
    } else {

    }
    {
    while (1) {
      while_continue___0: ;
      {
      spinlock_check(& info->lock);
      }
      {
      while (1) {
        while_continue___1: ;
        {
        __raw_spin_lock_init(& info->lock.__annonCompField18.rlock, "&(&info->lock)->rlock",
                             & __key___7);
        }
        goto while_break___1;
      }
      while_break___13: ;
      }
      while_break___1: ;
      goto while_break___0;
    }
    while_break___12: ;
    }
    while_break___0: ;
    {
    while (1) {
      while_continue___2: ;
      {
      __mutex_init(& info->deathwarrant, "&info->deathwarrant", & __key___8);
      }
      goto while_break___2;
    }
    while_break___14: ;
    }
    while_break___2:
    info->flags = (__u8 )0;
    info->mcr = (__u8 )0;
    {
    while (1) {
      while_continue___3: ;

      {
      while (1) {
        while_continue___4: ;
        {
        __init_work(& info->rx_work, 0);
        __constr_expr_0.counter = 2097664L;
        info->rx_work.data = __constr_expr_0;
        lockdep_init_map(& info->rx_work.lockdep_map, "(&info->rx_work)", & __key___9,
                         0);
        INIT_LIST_HEAD(& info->rx_work.entry);
        }
        {
        while (1) {
          while_continue___5: ;
          info->rx_work.func = & rx_data_softint;
          goto while_break___5;
        }
        while_break___17: ;
        }
        while_break___5: ;
        goto while_break___4;
      }
      while_break___16: ;
      }
      while_break___4: ;
      goto while_break___3;
    }
    while_break___15: ;
    }
    while_break___3:
    {
    info->port = port;
    INIT_LIST_HEAD(& info->rx_urbs_free);
    INIT_LIST_HEAD(& info->rx_urbs_submitted);
    INIT_LIST_HEAD(& info->rx_urb_q);
    INIT_LIST_HEAD(& info->tx_urbs_free);
    INIT_LIST_HEAD(& info->tx_urbs_submitted);
    j = 0;
    }
    {
    while (1) {
      while_continue___6: ;
      if (j < urb_pool_size) {

      } else {
        goto while_break___6;
      }
      {
      urb = usb_alloc_urb(0, 208U);
      }
      if (! urb) {
        {
        dev_err((struct device const *)(& port->dev), "No free urbs available\n");
        }
        goto no_rx_urb;
      } else {

      }
      {
      buf_size = (int )(port->read_urb)->transfer_buffer_length;
      urb->transfer_buffer = kmalloc((size_t )buf_size, 208U);
      }
      if (! urb->transfer_buffer) {
        {
        dev_err((struct device const *)(& port->dev), "Couldn\'t allocate urb buffer\n");
        }
        goto no_rx_buf;
      } else {

      }
      {
      tmp___13 = kmalloc(sizeof(*wrap), 208U);
      wrap = (struct whiteheat_urb_wrap *)tmp___13;
      }
      if (! wrap) {
        {
        dev_err((struct device const *)(& port->dev), "Couldn\'t allocate urb wrapper\n");
        }
        goto no_rx_wrap;
      } else {

      }
      {
      tmp___14 = __create_pipe(serial->dev, (unsigned int )port->bulk_in_endpointAddress);
      usb_fill_bulk_urb(urb, serial->dev, ((unsigned int )(3 << 30) | tmp___14) | 128U,
                        urb->transfer_buffer, buf_size, & whiteheat_read_callback,
                        (void *)port);
      wrap->urb = urb;
      list_add(& wrap->list, & info->rx_urbs_free);
      urb = usb_alloc_urb(0, 208U);
      }
      if (! urb) {
        {
        dev_err((struct device const *)(& port->dev), "No free urbs available\n");
        }
        goto no_tx_urb;
      } else {

      }
      {
      buf_size = (int )(port->write_urb)->transfer_buffer_length;
      urb->transfer_buffer = kmalloc((size_t )buf_size, 208U);
      }
      if (! urb->transfer_buffer) {
        {
        dev_err((struct device const *)(& port->dev), "Couldn\'t allocate urb buffer\n");
        }
        goto no_tx_buf;
      } else {

      }
      {
      tmp___15 = kmalloc(sizeof(*wrap), 208U);
      wrap = (struct whiteheat_urb_wrap *)tmp___15;
      }
      if (! wrap) {
        {
        dev_err((struct device const *)(& port->dev), "Couldn\'t allocate urb wrapper\n");
        }
        goto no_tx_wrap;
      } else {

      }
      {
      tmp___16 = __create_pipe(serial->dev, (unsigned int )port->bulk_out_endpointAddress);
      usb_fill_bulk_urb(urb, serial->dev, (unsigned int )(3 << 30) | tmp___16, urb->transfer_buffer,
                        buf_size, & whiteheat_write_callback, (void *)port);
      wrap->urb = urb;
      list_add(& wrap->list, & info->tx_urbs_free);
      j = j + 1;
      }
    }
    while_break___18: ;
    }
    while_break___6:
    {
    usb_set_serial_port_data(port, (void *)info);
    i = i + 1;
    }
  }
  while_break___11: ;
  }
  while_break:
  {
  tmp___17 = kmalloc(sizeof(struct whiteheat_command_private ), 208U);
  command_info = (struct whiteheat_command_private *)tmp___17;
  }
  if ((unsigned long )command_info == (unsigned long )((void *)0)) {
    {
    dev_err((struct device const *)(& (serial->dev)->dev), "%s: Out of memory for port structures\n",
            (serial->type)->description);
    }
    goto no_command_private;
  } else {

  }
  {
  while (1) {
    while_continue___7: ;
    {
    __mutex_init(& command_info->mutex, "&command_info->mutex", & __key___10);
    }
    goto while_break___7;
  }
  while_break___19: ;
  }
  while_break___7:
  command_info->port_running = (__u8 )0;
  {
  while (1) {
    while_continue___8: ;
    {
    __init_waitqueue_head(& command_info->wait_command, & __key___11);
    }
    goto while_break___8;
  }
  while_break___20: ;
  }
  while_break___8:
  {
  usb_set_serial_port_data(command_port, (void *)command_info);
  (command_port->write_urb)->complete = & command_port_write_callback;
  (command_port->read_urb)->complete = & command_port_read_callback;
  kfree((void const *)result);
  kfree((void const *)command);
  }
  return (0);
  no_firmware:
  {
  dev_err((struct device const *)(& (serial->dev)->dev), "%s: Unable to retrieve firmware version, try replugging\n",
          (serial->type)->description);
  dev_err((struct device const *)(& (serial->dev)->dev), "%s: If the firmware is not running (status led not blinking)\n",
          (serial->type)->description);
  dev_err((struct device const *)(& (serial->dev)->dev), "%s: please contact support@connecttech.com\n",
          (serial->type)->description);
  kfree((void const *)result);
  }
  return (-19);
  no_command_private:
  i = (int )serial->num_ports - 1;
  {
  while (1) {
    while_continue___9: ;
    if (i >= 0) {

    } else {
      goto while_break___9;
    }
    {
    port = serial->port[i];
    tmp___18 = usb_get_serial_port_data(port);
    info = (struct whiteheat_private *)tmp___18;
    j = urb_pool_size - 1;
    }
    {
    while (1) {
      while_continue___10: ;
      if (j >= 0) {

      } else {
        goto while_break___10;
      }
      {
      tmp___7 = list_first(& info->tx_urbs_free);
      list_del(tmp___7);
      __mptr = (struct list_head const *)tmp___7;
      wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
      urb = wrap->urb;
      kfree((void const *)wrap);
      }
      no_tx_wrap:
      {
      kfree((void const *)urb->transfer_buffer);
      }
      no_tx_buf:
      {
      usb_free_urb(urb);
      }
      no_tx_urb:
      {
      tmp___7 = list_first(& info->rx_urbs_free);
      list_del(tmp___7);
      __mptr___0 = (struct list_head const *)tmp___7;
      wrap = (struct whiteheat_urb_wrap *)((char *)__mptr___0 - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
      urb = wrap->urb;
      kfree((void const *)wrap);
      }
      no_rx_wrap:
      {
      kfree((void const *)urb->transfer_buffer);
      }
      no_rx_buf:
      {
      usb_free_urb(urb);
      }
      no_rx_urb:
      j = j - 1;
    }
    while_break___22: ;
    }
    while_break___10:
    {
    kfree((void const *)info);
    }
    no_private:
    i = i - 1;
  }
  while_break___21: ;
  }
  while_break___9:
  {
  kfree((void const *)result);
  }
  no_result_buffer:
  {
  kfree((void const *)command);
  }
  no_command_buffer:
  return (-12);
}
}
static void whiteheat_release(struct usb_serial *serial )
{ struct usb_serial_port *command_port ;
  struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  struct whiteheat_urb_wrap *wrap ;
  struct urb *urb ;
  struct list_head *tmp___7 ;
  struct list_head *tmp2 ;
  int i ;
  void *tmp___8 ;
  void *tmp___9 ;
  struct list_head const *__mptr ;
  struct list_head const *__mptr___0 ;

  {
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_release");
      }
    } else {

    }
    goto while_break;
  }
  while_break___3: ;
  }
  while_break:
  {
  command_port = serial->port[4];
  tmp___8 = usb_get_serial_port_data(command_port);
  kfree((void const *)tmp___8);
  i = 0;
  }
  {
  while (1) {
    while_continue___0: ;
    if (i < (int )serial->num_ports) {

    } else {
      goto while_break___0;
    }
    {
    port = serial->port[i];
    tmp___9 = usb_get_serial_port_data(port);
    info = (struct whiteheat_private *)tmp___9;
    tmp___7 = info->rx_urbs_free.next;
    tmp2 = tmp___7->next;
    }
    {
    while (1) {
      while_continue___1: ;
      if ((unsigned long )tmp___7 != (unsigned long )(& info->rx_urbs_free)) {

      } else {
        goto while_break___1;
      }
      {
      list_del(tmp___7);
      __mptr = (struct list_head const *)tmp___7;
      wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
      urb = wrap->urb;
      kfree((void const *)wrap);
      kfree((void const *)urb->transfer_buffer);
      usb_free_urb(urb);
      tmp___7 = tmp2;
      tmp2 = tmp___7->next;
      }
    }
    while_break___5: ;
    }
    while_break___1:
    tmp___7 = info->tx_urbs_free.next;
    tmp2 = tmp___7->next;
    {
    while (1) {
      while_continue___2: ;
      if ((unsigned long )tmp___7 != (unsigned long )(& info->tx_urbs_free)) {

      } else {
        goto while_break___2;
      }
      {
      list_del(tmp___7);
      __mptr___0 = (struct list_head const *)tmp___7;
      wrap = (struct whiteheat_urb_wrap *)((char *)__mptr___0 - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
      urb = wrap->urb;
      kfree((void const *)wrap);
      kfree((void const *)urb->transfer_buffer);
      usb_free_urb(urb);
      tmp___7 = tmp2;
      tmp2 = tmp___7->next;
      }
    }
    while_break___6: ;
    }
    while_break___2:
    {
    kfree((void const *)info);
    i = i + 1;
    }
  }
  while_break___4: ;
  }
  while_break___0: ;
  return;
}
}
static int whiteheat_open(struct tty_struct *tty , struct usb_serial_port *port )
{ int retval ;

  {
  retval = 0;
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_open", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___1: ;
  }
  while_break:
  {
  retval = start_command_port(port->serial);
  }
  if (retval) {
    goto exit;
  } else {

  }
  if (tty) {
    tty->low_latency = (unsigned char)1;
  } else {

  }
  {
  retval = firm_open(port);
  }
  if (retval) {
    {
    stop_command_port(port->serial);
    }
    goto exit;
  } else {

  }
  {
  retval = firm_purge(port, (__u8 )3);
  }
  if (retval) {
    {
    firm_close(port);
    stop_command_port(port->serial);
    }
    goto exit;
  } else {

  }
  if (tty) {
    {
    firm_setup_port(tty);
    }
  } else {

  }
  {
  usb_clear_halt((port->serial)->dev, (int )(port->read_urb)->pipe);
  usb_clear_halt((port->serial)->dev, (int )(port->write_urb)->pipe);
  retval = start_port_read(port);
  }
  if (retval) {
    {
    dev_err((struct device const *)(& port->dev), "%s - failed submitting read urb, error %d\n",
            "whiteheat_open", retval);
    firm_close(port);
    stop_command_port(port->serial);
    }
    goto exit;
  } else {

  }
  exit:
  {
  while (1) {
    while_continue___0: ;
    if (debug) {
      {
      printk("<7>%s: %s - exit, retval = %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_open", retval);
      }
    } else {

    }
    goto while_break___0;
  }
  while_break___2: ;
  }
  while_break___0: ;
  return (retval);
}
}
static void whiteheat_close(struct usb_serial_port *port )
{ struct whiteheat_private *info ;
  void *tmp___7 ;
  struct whiteheat_urb_wrap *wrap ;
  struct urb *urb ;
  struct list_head *tmp___8 ;
  struct list_head *tmp2 ;
  struct list_head const *__mptr ;
  struct list_head const *__mptr___0 ;

  {
  {
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_close", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___3: ;
  }
  while_break:
  {
  firm_report_tx_done(port);
  firm_close(port);
  mutex_lock_nested(& info->deathwarrant, 0U);
  spin_lock_irq(& info->lock);
  tmp___8 = info->rx_urbs_submitted.next;
  tmp2 = tmp___8->next;
  }
  {
  while (1) {
    while_continue___0: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->rx_urbs_submitted)) {

    } else {
      goto while_break___0;
    }
    {
    __mptr = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    urb = wrap->urb;
    list_del(tmp___8);
    spin_unlock_irq(& info->lock);
    usb_kill_urb(urb);
    spin_lock_irq(& info->lock);
    list_add(tmp___8, & info->rx_urbs_free);
    tmp___8 = tmp2;
    tmp2 = tmp___8->next;
    }
  }
  while_break___4: ;
  }
  while_break___0:
  tmp___8 = info->rx_urb_q.next;
  tmp2 = tmp___8->next;
  {
  while (1) {
    while_continue___1: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->rx_urb_q)) {

    } else {
      goto while_break___1;
    }
    {
    list_move(tmp___8, & info->rx_urbs_free);
    tmp___8 = tmp2;
    tmp2 = tmp___8->next;
    }
  }
  while_break___5: ;
  }
  while_break___1:
  tmp___8 = info->tx_urbs_submitted.next;
  tmp2 = tmp___8->next;
  {
  while (1) {
    while_continue___2: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->tx_urbs_submitted)) {

    } else {
      goto while_break___2;
    }
    {
    __mptr___0 = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr___0 - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    urb = wrap->urb;
    list_del(tmp___8);
    spin_unlock_irq(& info->lock);
    usb_kill_urb(urb);
    spin_lock_irq(& info->lock);
    list_add(tmp___8, & info->tx_urbs_free);
    tmp___8 = tmp2;
    tmp2 = tmp___8->next;
    }
  }
  while_break___6: ;
  }
  while_break___2:
  {
  spin_unlock_irq(& info->lock);
  mutex_unlock(& info->deathwarrant);
  stop_command_port(port->serial);
  }
  return;
}
}
static int whiteheat_write(struct tty_struct *tty , struct usb_serial_port *port ,
                           unsigned char const *buf , int count )
{ struct usb_serial *serial ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  struct whiteheat_urb_wrap *wrap ;
  struct urb *urb ;
  int result ;
  int bytes ;
  int sent ;
  unsigned long flags ;
  struct list_head *tmp___8 ;
  raw_spinlock_t *tmp___9 ;
  int tmp___10 ;
  struct list_head const *__mptr ;
  size_t __len ;
  void *__ret ;
  raw_spinlock_t *tmp___11 ;
  raw_spinlock_t *tmp___12 ;

  {
  {
  serial = port->serial;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  sent = 0;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_write", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___8: ;
  }
  while_break: ;
  if (count == 0) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: %s - write request of 0 bytes\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "whiteheat_write");
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___9: ;
    }
    while_break___0: ;
    return (0);
  } else {

  }
  {
  while (1) {
    while_continue___1: ;
    if (count) {

    } else {
      goto while_break___1;
    }
    {
    while (1) {
      while_continue___2: ;

      {
      while (1) {
        while_continue___3: ;
        {
        tmp___9 = spinlock_check(& info->lock);
        flags = _raw_spin_lock_irqsave(tmp___9);
        }
        goto while_break___3;
      }
      while_break___12: ;
      }
      while_break___3: ;
      goto while_break___2;
    }
    while_break___11: ;
    }
    while_break___2:
    {
    tmp___10 = list_empty((struct list_head const *)(& info->tx_urbs_free));
    }
    if (tmp___10) {
      {
      spin_unlock_irqrestore(& info->lock, flags);
      }
      goto while_break___1;
    } else {

    }
    {
    tmp___8 = list_first(& info->tx_urbs_free);
    list_del(tmp___8);
    spin_unlock_irqrestore(& info->lock, flags);
    __mptr = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    urb = wrap->urb;
    }
    if (count > port->bulk_out_size) {
      bytes = port->bulk_out_size;
    } else {
      bytes = count;
    }
    {
    __len = (size_t )bytes;
    __ret = __builtin_memcpy(urb->transfer_buffer, (void const *)(buf + sent), __len);
    usb_serial_debug_data(debug, & port->dev, "whiteheat_write", bytes, (unsigned char const *)urb->transfer_buffer);
    urb->dev = serial->dev;
    urb->transfer_buffer_length = (u32 )bytes;
    result = usb_submit_urb(urb, 32U);
    }
    if (result) {
      {
      dev_err((struct device const *)(& port->dev), "%s - failed submitting write urb, error %d\n",
              "whiteheat_write", result);
      sent = result;
      }
      {
      while (1) {
        while_continue___4: ;

        {
        while (1) {
          while_continue___5: ;
          {
          tmp___11 = spinlock_check(& info->lock);
          flags = _raw_spin_lock_irqsave(tmp___11);
          }
          goto while_break___5;
        }
        while_break___14: ;
        }
        while_break___5: ;
        goto while_break___4;
      }
      while_break___13: ;
      }
      while_break___4:
      {
      list_add(tmp___8, & info->tx_urbs_free);
      spin_unlock_irqrestore(& info->lock, flags);
      }
      goto while_break___1;
    } else {
      sent = sent + bytes;
      count = count - bytes;
      {
      while (1) {
        while_continue___6: ;

        {
        while (1) {
          while_continue___7: ;
          {
          tmp___12 = spinlock_check(& info->lock);
          flags = _raw_spin_lock_irqsave(tmp___12);
          }
          goto while_break___7;
        }
        while_break___16: ;
        }
        while_break___7: ;
        goto while_break___6;
      }
      while_break___15: ;
      }
      while_break___6:
      {
      list_add(tmp___8, & info->tx_urbs_submitted);
      spin_unlock_irqrestore(& info->lock, flags);
      }
    }
  }
  while_break___10: ;
  }
  while_break___1: ;
  return (sent);
}
}
static int whiteheat_write_room(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  struct list_head *tmp___8 ;
  int room ;
  unsigned long flags ;
  raw_spinlock_t *tmp___9 ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  room = 0;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_write_room", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___4: ;
  }
  while_break: ;
  {
  while (1) {
    while_continue___0: ;

    {
    while (1) {
      while_continue___1: ;
      {
      tmp___9 = spinlock_check(& info->lock);
      flags = _raw_spin_lock_irqsave(tmp___9);
      }
      goto while_break___1;
    }
    while_break___6: ;
    }
    while_break___1: ;
    goto while_break___0;
  }
  while_break___5: ;
  }
  while_break___0:
  tmp___8 = info->tx_urbs_free.next;
  {
  while (1) {
    while_continue___2: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->tx_urbs_free)) {

    } else {
      goto while_break___2;
    }
    room = room + 1;
    tmp___8 = tmp___8->next;
  }
  while_break___7: ;
  }
  while_break___2:
  {
  spin_unlock_irqrestore(& info->lock, flags);
  room = room * port->bulk_out_size;
  }
  {
  while (1) {
    while_continue___3: ;
    if (debug) {
      {
      printk("<7>%s: %s - returns %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_write_room", room);
      }
    } else {

    }
    goto while_break___3;
  }
  while_break___8: ;
  }
  while_break___3: ;
  return (room);
}
}
static int whiteheat_tiocmget(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  unsigned int modem_signals ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  modem_signals = 0U;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_tiocmget", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break:
  {
  firm_get_dtr_rts(port);
  }
  if ((int )info->mcr & 1) {
    modem_signals = modem_signals | 2U;
  } else {

  }
  if ((int )info->mcr & 2) {
    modem_signals = modem_signals | 4U;
  } else {

  }
  return ((int )modem_signals);
}
}
static int whiteheat_tiocmset(struct tty_struct *tty , unsigned int set , unsigned int clear )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_tiocmset", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  if (set & 4U) {
    info->mcr = (__u8 )((int )info->mcr | 2);
  } else {

  }
  if (set & 2U) {
    info->mcr = (__u8 )((int )info->mcr | 1);
  } else {

  }
  if (clear & 4U) {
    info->mcr = (__u8 )((int )info->mcr & -3);
  } else {

  }
  if (clear & 2U) {
    info->mcr = (__u8 )((int )info->mcr & -2);
  } else {

  }
  {
  firm_set_dtr(port, (__u8 )((int )info->mcr & 1));
  firm_set_rts(port, (__u8 )((int )info->mcr & 2));
  }
  return (0);
}
}
static int whiteheat_ioctl(struct tty_struct *tty , unsigned int cmd , unsigned long arg )
{ struct usb_serial_port *port ;
  struct serial_struct serstruct ;
  void *user_arg ;
  int tmp___7 ;
  int tmp ;

  {
  port = (struct usb_serial_port *)tty->driver_data;
  user_arg = (void *)arg;
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d, cmd 0x%.4x\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_ioctl", (int )port->number, cmd);
      }
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  if ((int )cmd == 21534) {
    goto case_21534;
  } else {
    goto switch_default;
    if (0) {
      case_21534:
      {
      memset((void *)(& serstruct), 0, sizeof(serstruct));
      serstruct.type = 11;
      serstruct.line = (int )(port->serial)->minor;
      serstruct.port = (unsigned int )port->number;
      serstruct.flags = (int )((1U << 6) | (1U << 7));
      serstruct.xmit_fifo_size = port->bulk_out_size;
      serstruct.custom_divisor = 0;
      serstruct.baud_base = 460800;
      serstruct.close_delay = (unsigned short)7500;
      serstruct.closing_wait = (unsigned short)7500;
      tmp = (int )copy_to_user(user_arg, (void const *)(& serstruct), (unsigned int )sizeof(serstruct));
      tmp___7 = tmp;
      }
      if (tmp___7) {
        return (-14);
      } else {

      }
      goto switch_break;
      switch_default:
      goto switch_break;
    } else {
      switch_break: ;
    }
  }
  return (-515);
}
}
static void whiteheat_set_termios(struct tty_struct *tty , struct usb_serial_port *port ,
                                  struct ktermios *old_termios )
{

  {
  {
  firm_setup_port(tty);
  }
  return;
}
}
static void whiteheat_break_ctl(struct tty_struct *tty , int break_state )
{ struct usb_serial_port *port ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  firm_set_break(port, (__u8 )break_state);
  }
  return;
}
}
static int whiteheat_chars_in_buffer(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  struct list_head *tmp___8 ;
  struct whiteheat_urb_wrap *wrap ;
  int chars ;
  unsigned long flags ;
  raw_spinlock_t *tmp___9 ;
  struct list_head const *__mptr ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  chars = 0;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_chars_in_buffer", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___4: ;
  }
  while_break: ;
  {
  while (1) {
    while_continue___0: ;

    {
    while (1) {
      while_continue___1: ;
      {
      tmp___9 = spinlock_check(& info->lock);
      flags = _raw_spin_lock_irqsave(tmp___9);
      }
      goto while_break___1;
    }
    while_break___6: ;
    }
    while_break___1: ;
    goto while_break___0;
  }
  while_break___5: ;
  }
  while_break___0:
  tmp___8 = info->tx_urbs_submitted.next;
  {
  while (1) {
    while_continue___2: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->tx_urbs_submitted)) {

    } else {
      goto while_break___2;
    }
    __mptr = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    chars = (int )((u32 )chars + (wrap->urb)->transfer_buffer_length);
    tmp___8 = tmp___8->next;
  }
  while_break___7: ;
  }
  while_break___2:
  {
  spin_unlock_irqrestore(& info->lock, flags);
  }
  {
  while (1) {
    while_continue___3: ;
    if (debug) {
      {
      printk("<7>%s: %s - returns %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_chars_in_buffer", chars);
      }
    } else {

    }
    goto while_break___3;
  }
  while_break___8: ;
  }
  while_break___3: ;
  return (chars);
}
}
static void whiteheat_throttle(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_throttle", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break:
  {
  spin_lock_irq(& info->lock);
  info->flags = (__u8 )((int )info->flags | 1);
  spin_unlock_irq(& info->lock);
  }
  return;
}
}
static void whiteheat_unthrottle(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  int actually_throttled ;

  {
  {
  port = (struct usb_serial_port *)tty->driver_data;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_unthrottle", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break:
  {
  spin_lock_irq(& info->lock);
  actually_throttled = (int )info->flags & 2;
  info->flags = (__u8 )((int )info->flags & -4);
  spin_unlock_irq(& info->lock);
  }
  if (actually_throttled) {
    {
    rx_data_softint(& info->rx_work);
    }
  } else {

  }
  return;
}
}
static void command_port_write_callback(struct urb *urb )
{ int status ;

  {
  status = urb->status;
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "command_port_write_callback");
      }
    } else {

    }
    goto while_break;
  }
  while_break___1: ;
  }
  while_break: ;
  if (status) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: nonzero urb status: %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               status);
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___2: ;
    }
    while_break___0: ;
    return;
  } else {

  }
  return;
}
}
static void command_port_read_callback(struct urb *urb )
{ struct usb_serial_port *command_port ;
  struct whiteheat_command_private *command_info ;
  int status ;
  unsigned char *data ;
  int result ;
  void *tmp___7 ;
  size_t __len ;
  void *__ret ;

  {
  command_port = (struct usb_serial_port *)urb->context;
  status = urb->status;
  data = (unsigned char *)urb->transfer_buffer;
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "command_port_read_callback");
      }
    } else {

    }
    goto while_break;
  }
  while_break___5: ;
  }
  while_break:
  {
  tmp___7 = usb_get_serial_port_data(command_port);
  command_info = (struct whiteheat_command_private *)tmp___7;
  }
  if (! command_info) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: %s - command_info is NULL, exiting.\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "command_port_read_callback");
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___6: ;
    }
    while_break___0: ;
    return;
  } else {

  }
  if (status) {
    {
    while (1) {
      while_continue___1: ;
      if (debug) {
        {
        printk("<7>%s: %s - nonzero urb status: %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "command_port_read_callback", status);
        }
      } else {

      }
      goto while_break___1;
    }
    while_break___7: ;
    }
    while_break___1: ;
    if (status != -2) {
      command_info->command_finished = (__u8 )17;
    } else {

    }
    {
    __wake_up(& command_info->wait_command, 3U, 1, (void *)0);
    }
    return;
  } else {

  }
  {
  usb_serial_debug_data(debug, & command_port->dev, "command_port_read_callback",
                        (int )urb->actual_length, (unsigned char const *)data);
  }
  if ((int )*(data + 0) == 16) {
    {
    command_info->command_finished = (__u8 )16;
    __wake_up(& command_info->wait_command, 3U, 1, (void *)0);
    }
  } else
  if ((int )*(data + 0) == 17) {
    {
    command_info->command_finished = (__u8 )17;
    __wake_up(& command_info->wait_command, 3U, 1, (void *)0);
    }
  } else
  if ((int )*(data + 0) == 13) {
    {
    while (1) {
      while_continue___2: ;
      if (debug) {
        {
        printk("<7>%s: %s - event received\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "command_port_read_callback");
        }
      } else {

      }
      goto while_break___2;
    }
    while_break___8: ;
    }
    while_break___2: ;
  } else
  if ((int )*(data + 0) == 10) {
    {
    __len = (size_t )(urb->actual_length - 1U);
    __ret = __builtin_memcpy((void *)(command_info->result_buffer), (void const *)(data + 1),
                             __len);
    command_info->command_finished = (__u8 )16;
    __wake_up(& command_info->wait_command, 3U, 1, (void *)0);
    }
  } else {
    {
    while (1) {
      while_continue___3: ;
      if (debug) {
        {
        printk("<7>%s: %s - bad reply from firmware\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "command_port_read_callback");
        }
      } else {

      }
      goto while_break___3;
    }
    while_break___9: ;
    }
    while_break___3: ;
  }
  {
  (command_port->read_urb)->dev = (command_port->serial)->dev;
  result = usb_submit_urb(command_port->read_urb, 32U);
  }
  if (result) {
    {
    while (1) {
      while_continue___4: ;
      if (debug) {
        {
        printk("<7>%s: %s - failed resubmitting read urb, error %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "command_port_read_callback", result);
        }
      } else {

      }
      goto while_break___4;
    }
    while_break___10: ;
    }
    while_break___4: ;
  } else {

  }
  return;
}
}
static void whiteheat_read_callback(struct urb *urb )
{ struct usb_serial_port *port ;
  struct whiteheat_urb_wrap *wrap ;
  unsigned char *data ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  int status ;

  {
  {
  port = (struct usb_serial_port *)urb->context;
  data = (unsigned char *)urb->transfer_buffer;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  status = urb->status;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_read_callback", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___1: ;
  }
  while_break:
  {
  spin_lock(& info->lock);
  wrap = urb_to_wrap(urb, & info->rx_urbs_submitted);
  }
  if (! wrap) {
    {
    spin_unlock(& info->lock);
    dev_err((struct device const *)(& port->dev), "%s - Not my urb!\n", "whiteheat_read_callback");
    }
    return;
  } else {

  }
  {
  list_del(& wrap->list);
  spin_unlock(& info->lock);
  }
  if (status) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: %s - nonzero read bulk status received: %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "whiteheat_read_callback", status);
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___2: ;
    }
    while_break___0:
    {
    spin_lock(& info->lock);
    list_add(& wrap->list, & info->rx_urbs_free);
    spin_unlock(& info->lock);
    }
    return;
  } else {

  }
  {
  usb_serial_debug_data(debug, & port->dev, "whiteheat_read_callback", (int )urb->actual_length,
                        (unsigned char const *)data);
  spin_lock(& info->lock);
  list_add_tail(& wrap->list, & info->rx_urb_q);
  }
  if ((int )info->flags & 1) {
    {
    info->flags = (__u8 )((int )info->flags | 2);
    spin_unlock(& info->lock);
    }
    return;
  } else {

  }
  {
  spin_unlock(& info->lock);
  schedule_work(& info->rx_work);
  }
  return;
}
}
static void whiteheat_write_callback(struct urb *urb )
{ struct usb_serial_port *port ;
  struct whiteheat_private *info ;
  void *tmp___7 ;
  struct whiteheat_urb_wrap *wrap ;
  int status ;

  {
  {
  port = (struct usb_serial_port *)urb->context;
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  status = urb->status;
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - port %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "whiteheat_write_callback", (int )port->number);
      }
    } else {

    }
    goto while_break;
  }
  while_break___1: ;
  }
  while_break:
  {
  spin_lock(& info->lock);
  wrap = urb_to_wrap(urb, & info->tx_urbs_submitted);
  }
  if (! wrap) {
    {
    spin_unlock(& info->lock);
    dev_err((struct device const *)(& port->dev), "%s - Not my urb!\n", "whiteheat_write_callback");
    }
    return;
  } else {

  }
  {
  list_move(& wrap->list, & info->tx_urbs_free);
  spin_unlock(& info->lock);
  }
  if (status) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: %s - nonzero write bulk status received: %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "whiteheat_write_callback", status);
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___2: ;
    }
    while_break___0: ;
    return;
  } else {

  }
  {
  usb_serial_port_softint(port);
  }
  return;
}
}
static int firm_send_command(struct usb_serial_port *port , __u8 command , __u8 *data ,
                             __u8 datasize )
{ struct usb_serial_port *command_port ;
  struct whiteheat_command_private *command_info ;
  struct whiteheat_private *info ;
  __u8 *transfer_buffer ;
  int retval ;
  int t ;
  void *tmp___7 ;
  size_t __len ;
  void *__ret ;
  long __ret___0 ;
  wait_queue_t __wait ;
  struct task_struct *tmp___8 ;
  void *tmp___9 ;
  size_t __len___0 ;
  void *__ret___1 ;

  {
  retval = 0;
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - command %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_send_command", (int )command);
      }
    } else {

    }
    goto while_break;
  }
  while_break___6: ;
  }
  while_break:
  {
  command_port = (port->serial)->port[4];
  tmp___7 = usb_get_serial_port_data(command_port);
  command_info = (struct whiteheat_command_private *)tmp___7;
  mutex_lock_nested(& command_info->mutex, 0U);
  command_info->command_finished = (__u8 )0;
  transfer_buffer = (__u8 *)(command_port->write_urb)->transfer_buffer;
  *(transfer_buffer + 0) = command;
  __len = (size_t )datasize;
  __ret = __builtin_memcpy((void *)(transfer_buffer + 1), (void const *)data, __len);
  (command_port->write_urb)->transfer_buffer_length = (u32 )((int )datasize + 1);
  (command_port->write_urb)->dev = (port->serial)->dev;
  retval = usb_submit_urb(command_port->write_urb, 16U);
  }
  if (retval) {
    {
    while (1) {
      while_continue___0: ;
      if (debug) {
        {
        printk("<7>%s: %s - submit urb failed\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "firm_send_command");
        }
      } else {

      }
      goto while_break___0;
    }
    while_break___7: ;
    }
    while_break___0: ;
    goto exit;
  } else {

  }
  __ret___0 = 500L;
  if (! ((bool )command_info->command_finished)) {
    {
    while (1) {
      while_continue___1: ;
      {
      tmp___8 = get_current();
      __wait.flags = 0U;
      __wait.private = (void *)tmp___8;
      __wait.func = & autoremove_wake_function;
      __wait.task_list.next = & __wait.task_list;
      __wait.task_list.prev = & __wait.task_list;
      }
      {
      while (1) {
        while_continue___2: ;
        {
        prepare_to_wait(& command_info->wait_command, & __wait, 2);
        }
        if ((bool )command_info->command_finished) {
          goto while_break___2;
        } else {

        }
        {
        __ret___0 = schedule_timeout(__ret___0);
        }
        if (! __ret___0) {
          goto while_break___2;
        } else {

        }
      }
      while_break___9: ;
      }
      while_break___2:
      {
      finish_wait(& command_info->wait_command, & __wait);
      }
      goto while_break___1;
    }
    while_break___8: ;
    }
    while_break___1: ;
  } else {
 
  }
  t = (int )__ret___0;
  if (! t) {
    {
    usb_kill_urb(command_port->write_urb);
    }
  } else {

  }
  if ((int )command_info->command_finished == 0) {
    {
    while (1) {
      while_continue___3: ;
      if (debug) {
        {
        printk("<7>%s: %s - command timed out.\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "firm_send_command");
        }
      } else {

      }
      goto while_break___3;
    }
    while_break___10: ;
    }
    while_break___3:
    retval = -110;
    goto exit;
  } else {

  }
  if ((int )command_info->command_finished == 17) {
    {
    while (1) {
      while_continue___4: ;
      if (debug) {
        {
        printk("<7>%s: %s - command failed.\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "firm_send_command");
        }
      } else {

      }
      goto while_break___4;
    }
    while_break___11: ;
    }
    while_break___4:
    retval = -5;
    goto exit;
  } else {

  }
  if ((int )command_info->command_finished == 16) {
    {
    while (1) {
      while_continue___5: ;
      if (debug) {
        {
        printk("<7>%s: %s - command completed.\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
               "firm_send_command");
        }
      } else {

      }
      goto while_break___5;
    }
    while_break___12: ;
    }
    while_break___5: ;
    if ((int )command == 10) {
      goto case_10;
    } else
    if (0) {
      case_10:
      {
      tmp___9 = usb_get_serial_port_data(port);
      info = (struct whiteheat_private *)tmp___9;
      __len___0 = sizeof(struct whiteheat_dr_info );
      }
      if (__len___0 >= 64UL) {
        {
        __ret___1 = __memcpy((void *)(& info->mcr), (void const *)(command_info->result_buffer),
                             __len___0);
        }
      } else {
        {
        __ret___1 = __builtin_memcpy((void *)(& info->mcr), (void const *)(command_info->result_buffer),
                                     __len___0);
        }
      }
      goto switch_break;
    } else {
      switch_break: ;
    }
  } else {

  }
  exit:
  {
  mutex_unlock(& command_info->mutex);
  }
  return (retval);
}
}
static int firm_open(struct usb_serial_port *port )
{ struct whiteheat_simple open_command ;
  int tmp___7 ;

  {
  {
  open_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  tmp___7 = firm_send_command(port, (__u8 )1, (__u8 *)(& open_command), (__u8 )sizeof(open_command));
  }
  return (tmp___7);
}
}
static int firm_close(struct usb_serial_port *port )
{ struct whiteheat_simple close_command ;
  int tmp___7 ;

  {
  {
  close_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  tmp___7 = firm_send_command(port, (__u8 )2, (__u8 *)(& close_command), (__u8 )sizeof(close_command));
  }
  return (tmp___7);
}
}
static void firm_setup_port(struct tty_struct *tty )
{ struct usb_serial_port *port ;
  struct whiteheat_port_settings port_settings ;
  unsigned int cflag ;
  char const *tmp___7 ;
  char const *tmp___8 ;
  char const *tmp___9 ;
  char const *tmp___10 ;

  {
  port = (struct usb_serial_port *)tty->driver_data;
  cflag = (tty->termios)->c_cflag;
  port_settings.port = (__u8 )((int )port->number + 1);
  if ((int )(cflag & 48U) == 0) {
    goto case_0;
  } else
  if ((int )(cflag & 48U) == 16) {
    goto case_16;
  } else
  if ((int )(cflag & 48U) == 32) {
    goto case_32;
  } else {
    goto switch_default;
    if (0) {
      case_0:
      port_settings.bits = (__u8 )5;
      goto switch_break;
      case_16:
      port_settings.bits = (__u8 )6;
      goto switch_break;
      case_32:
      port_settings.bits = (__u8 )7;
      goto switch_break;
      switch_default:
      port_settings.bits = (__u8 )8;
      goto switch_break;
    } else {
      switch_break: ;
    }
  }
  {
  while (1) {
    while_continue: ;
    if (debug) {
      {
      printk("<7>%s: %s - data bits = %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", (int )port_settings.bits);
      }
    } else {

    }
    goto while_break;
  }
  while_break___6: ;
  }
  while_break: ;
  if (cflag & 256U) {
    if (cflag & 1073741824U) {
      if (cflag & 512U) {
        port_settings.parity = (__u8 )'1';
      } else {
        port_settings.parity = (__u8 )'0';
      }
    } else
    if (cflag & 512U) {
      port_settings.parity = (__u8 )'o';
    } else {
      port_settings.parity = (__u8 )'e';
    }
  } else {
    port_settings.parity = (__u8 )'n';
  }
  {
  while (1) {
    while_continue___0: ;
    if (debug) {
      {
      printk("<7>%s: %s - parity = %c\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", (int )port_settings.parity);
      }
    } else {

    }
    goto while_break___0;
  }
  while_break___7: ;
  }
  while_break___0: ;
  if (cflag & 64U) {
    port_settings.stop = (__u8 )2;
  } else {
    port_settings.stop = (__u8 )1;
  }
  {
  while (1) {
    while_continue___1: ;
    if (debug) {
      {
      printk("<7>%s: %s - stop bits = %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", (int )port_settings.stop);
      }
    } else {

    }
    goto while_break___1;
  }
  while_break___8: ;
  }
  while_break___1: ;
  if (cflag & 2147483648U) {
    port_settings.hflow = (__u8 )136;
  } else {
    port_settings.hflow = (__u8 )0;
  }
  {
  while (1) {
    while_continue___2: ;
    if (debug) {
      if ((int )port_settings.hflow & 2) {
        tmp___7 = "DTR";
      } else {
        tmp___7 = "";
      }
      if ((int )port_settings.hflow & 16) {
        tmp___8 = "DSR";
      } else {
        tmp___8 = "";
      }
      if ((int )port_settings.hflow & 128) {
        tmp___9 = "RTS";
      } else {
        tmp___9 = "";
      }
      if ((int )port_settings.hflow & 8) {
        tmp___10 = "CTS";
      } else {
        tmp___10 = "";
      }
      {
      printk("<7>%s: %s - hardware flow control = %s %s %s %s\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", tmp___10, tmp___9, tmp___8, tmp___7);
      }
    } else {

    }
    goto while_break___2;
  }
  while_break___9: ;
  }
  while_break___2: ;
  if ((tty->termios)->c_iflag & 4096U) {
    port_settings.sflow = (__u8 )'b';
  } else {
    port_settings.sflow = (__u8 )'n';
  }
  {
  while (1) {
    while_continue___3: ;
    if (debug) {
      {
      printk("<7>%s: %s - software flow control = %c\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", (int )port_settings.sflow);
      }
    } else {

    }
    goto while_break___3;
  }
  while_break___10: ;
  }
  while_break___3:
  port_settings.xon = (tty->termios)->c_cc[8];
  port_settings.xoff = (tty->termios)->c_cc[9];
  {
  while (1) {
    while_continue___4: ;
    if (debug) {
      {
      printk("<7>%s: %s - XON = %2x, XOFF = %2x\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", (int )port_settings.xon, (int )port_settings.xoff);
      }
    } else {

    }
    goto while_break___4;
  }
  while_break___11: ;
  }
  while_break___4:
  {
  port_settings.baud = tty_get_baud_rate(tty);
  }
  {
  while (1) {
    while_continue___5: ;
    if (debug) {
      {
      printk("<7>%s: %s - baud rate = %d\n", "/anthill/stuff/tacas-comp/work/current--X--drivers/usb/serial/whiteheat.ko--X--bulklinux-3.0.1--X--68_1/linux-3.0.1/csd_deg_dscv/11/dscv_tempdir/dscv/ri/68_1/drivers/usb/serial/whiteheat.c.common.c",
             "firm_setup_port", port_settings.baud);
      }
    } else {

    }
    goto while_break___5;
  }
  while_break___12: ;
  }
  while_break___5:
  {
  tty_encode_baud_rate(tty, port_settings.baud, port_settings.baud);
  port_settings.lloop = (__u8 )0;
  firm_send_command(port, (__u8 )3, (__u8 *)(& port_settings), (__u8 )sizeof(port_settings));
  }
  return;
}
}
static int firm_set_rts(struct usb_serial_port *port , __u8 onoff )
{ struct whiteheat_set_rdb rts_command ;
  int tmp___7 ;

  {
  {
  rts_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  rts_command.state = onoff;
  tmp___7 = firm_send_command(port, (__u8 )4, (__u8 *)(& rts_command), (__u8 )sizeof(rts_command));
  }
  return (tmp___7);
}
}
static int firm_set_dtr(struct usb_serial_port *port , __u8 onoff )
{ struct whiteheat_set_rdb dtr_command ;
  int tmp___7 ;

  {
  {
  dtr_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  dtr_command.state = onoff;
  tmp___7 = firm_send_command(port, (__u8 )5, (__u8 *)(& dtr_command), (__u8 )sizeof(dtr_command));
  }
  return (tmp___7);
}
}
static int firm_set_break(struct usb_serial_port *port , __u8 onoff )
{ struct whiteheat_set_rdb break_command ;
  int tmp___7 ;

  {
  {
  break_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  break_command.state = onoff;
  tmp___7 = firm_send_command(port, (__u8 )6, (__u8 *)(& break_command), (__u8 )sizeof(break_command));
  }
  return (tmp___7);
}
}
static int firm_purge(struct usb_serial_port *port , __u8 rxtx )
{ struct whiteheat_purge purge_command ;
  int tmp___7 ;

  {
  {
  purge_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  purge_command.what = rxtx;
  tmp___7 = firm_send_command(port, (__u8 )9, (__u8 *)(& purge_command), (__u8 )sizeof(purge_command));
  }
  return (tmp___7);
}
}
static int firm_get_dtr_rts(struct usb_serial_port *port )
{ struct whiteheat_simple get_dr_command ;
  int tmp___7 ;

  {
  {
  get_dr_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  tmp___7 = firm_send_command(port, (__u8 )10, (__u8 *)(& get_dr_command), (__u8 )sizeof(get_dr_command));
  }
  return (tmp___7);
}
}
static int firm_report_tx_done(struct usb_serial_port *port )
{ struct whiteheat_simple close_command ;
  int tmp___7 ;

  {
  {
  close_command.port = (__u8 )(((int )port->number - (int )(port->serial)->minor) + 1);
  tmp___7 = firm_send_command(port, (__u8 )12, (__u8 *)(& close_command), (__u8 )sizeof(close_command));
  }
  return (tmp___7);
}
}
static int start_command_port(struct usb_serial *serial )
{ struct usb_serial_port *command_port ;
  struct whiteheat_command_private *command_info ;
  int retval ;
  void *tmp___7 ;

  {
  {
  retval = 0;
  command_port = serial->port[4];
  tmp___7 = usb_get_serial_port_data(command_port);
  command_info = (struct whiteheat_command_private *)tmp___7;
  mutex_lock_nested(& command_info->mutex, 0U);
  }
  if (! command_info->port_running) {
    {
    usb_clear_halt(serial->dev, (int )(command_port->read_urb)->pipe);
    (command_port->read_urb)->dev = serial->dev;
    retval = usb_submit_urb(command_port->read_urb, 208U);
    }
    if (retval) {
      {
      dev_err((struct device const *)(& (serial->dev)->dev), "%s - failed submitting read urb, error %d\n",
              "start_command_port", retval);
      }
      goto exit;
    } else {

    }
  } else {

  }
  command_info->port_running = (__u8 )((int )command_info->port_running + 1);
  exit:
  {
  mutex_unlock(& command_info->mutex);
  }
  return (retval);
}
}
static void stop_command_port(struct usb_serial *serial )
{ struct usb_serial_port *command_port ;
  struct whiteheat_command_private *command_info ;
  void *tmp___7 ;

  {
  {
  command_port = serial->port[4];
  tmp___7 = usb_get_serial_port_data(command_port);
  command_info = (struct whiteheat_command_private *)tmp___7;
  mutex_lock_nested(& command_info->mutex, 0U);
  command_info->port_running = (__u8 )((int )command_info->port_running - 1);
  }
  if (! command_info->port_running) {
    {
    usb_kill_urb(command_port->read_urb);
    }
  } else {

  }
  {
  mutex_unlock(& command_info->mutex);
  }
  return;
}
}
static int start_port_read(struct usb_serial_port *port )
{ struct whiteheat_private *info ;
  void *tmp___7 ;
  struct whiteheat_urb_wrap *wrap ;
  struct urb *urb ;
  int retval ;
  unsigned long flags ;
  struct list_head *tmp___8 ;
  struct list_head *tmp2 ;
  raw_spinlock_t *tmp___9 ;
  struct list_head const *__mptr ;
  raw_spinlock_t *tmp___10 ;
  struct list_head const *__mptr___0 ;
  raw_spinlock_t *tmp___11 ;
  raw_spinlock_t *tmp___12 ;

  {
  {
  tmp___7 = usb_get_serial_port_data(port);
  info = (struct whiteheat_private *)tmp___7;
  retval = 0;
  }
  {
  while (1) {
    while_continue: ;

    {
    while (1) {
      while_continue___0: ;
      {
      tmp___9 = spinlock_check(& info->lock);
      flags = _raw_spin_lock_irqsave(tmp___9);
      }
      goto while_break___0;
    }
    while_break___10: ;
    }
    while_break___0: ;
    goto while_break;
  }
  while_break___9: ;
  }
  while_break:
  tmp___8 = info->rx_urbs_free.next;
  tmp2 = tmp___8->next;
  {
  while (1) {
    while_continue___1: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->rx_urbs_free)) {

    } else {
      goto while_break___1;
    }
    {
    list_del(tmp___8);
    __mptr = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    urb = wrap->urb;
    urb->dev = (port->serial)->dev;
    spin_unlock_irqrestore(& info->lock, flags);
    retval = usb_submit_urb(urb, 208U);
    }
    if (retval) {
      {
      while (1) {
        while_continue___2: ;

        {
        while (1) {
          while_continue___3: ;
          {
          tmp___10 = spinlock_check(& info->lock);
          flags = _raw_spin_lock_irqsave(tmp___10);
          }
          goto while_break___3;
        }
        while_break___13: ;
        }
        while_break___3: ;
        goto while_break___2;
      }
      while_break___12: ;
      }
      while_break___2:
      {
      list_add(tmp___8, & info->rx_urbs_free);
      tmp___8 = info->rx_urbs_submitted.next;
      tmp2 = tmp___8->next;
      }
      {
      while (1) {
        while_continue___4: ;
        if ((unsigned long )tmp___8 != (unsigned long )(& info->rx_urbs_submitted)) {

        } else {
          goto while_break___4;
        }
        {
        __mptr___0 = (struct list_head const *)tmp___8;
        wrap = (struct whiteheat_urb_wrap *)((char *)__mptr___0 - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
        urb = wrap->urb;
        list_del(tmp___8);
        spin_unlock_irqrestore(& info->lock, flags);
        usb_kill_urb(urb);
        }
        {
        while (1) {
          while_continue___5: ;

          {
          while (1) {
            while_continue___6: ;
            {
            tmp___11 = spinlock_check(& info->lock);
            flags = _raw_spin_lock_irqsave(tmp___11);
            }
            goto while_break___6;
          }
          while_break___16: ;
          }
          while_break___6: ;
          goto while_break___5;
        }
        while_break___15: ;
        }
        while_break___5:
        {
        list_add(tmp___8, & info->rx_urbs_free);
        tmp___8 = tmp2;
        tmp2 = tmp___8->next;
        }
      }
      while_break___14: ;
      }
      while_break___4: ;
      goto while_break___1;
    } else {

    }
    {
    while (1) {
      while_continue___7: ;

      {
      while (1) {
        while_continue___8: ;
        {
        tmp___12 = spinlock_check(& info->lock);
        flags = _raw_spin_lock_irqsave(tmp___12);
        }
        goto while_break___8;
      }
      while_break___18: ;
      }
      while_break___8: ;
      goto while_break___7;
    }
    while_break___17: ;
    }
    while_break___7:
    {
    list_add(tmp___8, & info->rx_urbs_submitted);
    tmp___8 = tmp2;
    tmp2 = tmp___8->next;
    }
  }
  while_break___11: ;
  }
  while_break___1:
  {
  spin_unlock_irqrestore(& info->lock, flags);
  }
  return (retval);
}
}
static struct whiteheat_urb_wrap *urb_to_wrap(struct urb *urb , struct list_head *head )
{ struct whiteheat_urb_wrap *wrap ;
  struct list_head *tmp___7 ;
  struct list_head const *__mptr ;

  {
  tmp___7 = head->next;
  {
  while (1) {
    while_continue: ;
    if ((unsigned long )tmp___7 != (unsigned long )head) {

    } else {
      goto while_break;
    }
    __mptr = (struct list_head const *)tmp___7;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    if ((unsigned long )wrap->urb == (unsigned long )urb) {
      return (wrap);
    } else {

    }
    tmp___7 = tmp___7->next;
  }
  while_break___0: ;
  }
  while_break: ;
  return ((struct whiteheat_urb_wrap *)((void *)0));
}
}
static struct list_head *list_first(struct list_head *head )
{

  {
  return (head->next);
}
}
static void rx_data_softint(struct work_struct *work )
{ struct whiteheat_private *info ;
  struct work_struct const *__mptr ;
  struct usb_serial_port *port ;
  struct tty_struct *tty ;
  struct tty_struct *tmp___7 ;
  struct whiteheat_urb_wrap *wrap ;
  struct urb *urb ;
  unsigned long flags ;
  struct list_head *tmp___8 ;
  struct list_head *tmp2 ;
  int result ;
  int sent ;
  raw_spinlock_t *tmp___9 ;
  struct list_head const *__mptr___0 ;
  int tmp___10 ;
  raw_spinlock_t *tmp___11 ;
  raw_spinlock_t *tmp___12 ;

  {
  {
  __mptr = (struct work_struct const *)work;
  info = (struct whiteheat_private *)((char *)__mptr - (unsigned int )(& ((struct whiteheat_private *)0)->rx_work));
  port = info->port;
  tmp___7 = tty_port_tty_get(& port->port);
  tty = tmp___7;
  sent = 0;
  }
  {
  while (1) {
    while_continue: ;

    {
    while (1) {
      while_continue___0: ;
      {
      tmp___9 = spinlock_check(& info->lock);
      flags = _raw_spin_lock_irqsave(tmp___9);
      }
      goto while_break___0;
    }
    while_break___7: ;
    }
    while_break___0: ;
    goto while_break;
  }
  while_break___6: ;
  }
  while_break: ;
  if ((int )info->flags & 1) {
    {
    spin_unlock_irqrestore(& info->lock, flags);
    }
    goto out;
  } else {

  }
  tmp___8 = info->rx_urb_q.next;
  tmp2 = tmp___8->next;
  {
  while (1) {
    while_continue___1: ;
    if ((unsigned long )tmp___8 != (unsigned long )(& info->rx_urb_q)) {

    } else {
      goto while_break___1;
    }
    {
    list_del(tmp___8);
    spin_unlock_irqrestore(& info->lock, flags);
    __mptr___0 = (struct list_head const *)tmp___8;
    wrap = (struct whiteheat_urb_wrap *)((char *)__mptr___0 - (unsigned int )(& ((struct whiteheat_urb_wrap *)0)->list));
    urb = wrap->urb;
    }
    if (tty) {
      if (urb->actual_length) {
        {
        tmp___10 = tty_insert_flip_string(tty, (unsigned char const *)urb->transfer_buffer,
                                          (size_t )urb->actual_length);
        sent = sent + tmp___10;
        }
      } else {

      }
    } else {

    }
    {
    urb->dev = (port->serial)->dev;
    result = usb_submit_urb(urb, 32U);
    }
    if (result) {
      {
      dev_err((struct device const *)(& port->dev), "%s - failed resubmitting read urb, error %d\n",
              "rx_data_softint", result);
      }
      {
      while (1) {
        while_continue___2: ;

        {
        while (1) {
          while_continue___3: ;
          {
          tmp___11 = spinlock_check(& info->lock);
          flags = _raw_spin_lock_irqsave(tmp___11);
          }
          goto while_break___3;
        }
        while_break___10: ;
        }
        while_break___3: ;
        goto while_break___2;
      }
      while_break___9: ;
      }
      while_break___2:
      {
      list_add(tmp___8, & info->rx_urbs_free);
      }
      goto __Cont;
    } else {

    }
    {
    while (1) {
      while_continue___4: ;

      {
      while (1) {
        while_continue___5: ;
        {
        tmp___12 = spinlock_check(& info->lock);
        flags = _raw_spin_lock_irqsave(tmp___12);
        }
        goto while_break___5;
      }
      while_break___12: ;
      }
      while_break___5: ;
      goto while_break___4;
    }
    while_break___11: ;
    }
    while_break___4:
    {
    list_add(tmp___8, & info->rx_urbs_submitted);
    }
    __Cont:
    tmp___8 = tmp2;
    tmp2 = tmp___8->next;
  }
  while_break___8: ;
  }
  while_break___1:
  {
  spin_unlock_irqrestore(& info->lock, flags);
  }
  if (sent) {
    {
    tty_flip_buffer_push(tty);
    }
  } else {

  }
  out:
  {
  tty_kref_put(tty);
  }
  return;
}
}
static int whiteheat_init(void) __attribute__((__section__(".init.text"), __no_instrument_function__)) ;
static int whiteheat_init(void) __attribute__((__section__(".init.text"), __no_instrument_function__)) ;
static int whiteheat_init(void)
{ int retval ;

  {
  {
  retval = usb_serial_register(& whiteheat_fake_device);
  }
  if (retval) {
    goto failed_fake_register;
  } else {

  }
  {
  retval = usb_serial_register(& whiteheat_device);
  }
  if (retval) {
    goto failed_device_register;
  } else {

  }
  {
  retval = usb_register(& whiteheat_driver);
  }
  if (retval) {
    goto failed_usb_register;
  } else {

  }
  {
  printk("<6>whiteheat: v2.0:USB ConnectTech WhiteHEAT driver\n");
  }
  return (0);
  failed_usb_register:
  {
  usb_serial_deregister(& whiteheat_device);
  }
  failed_device_register:
  {
  usb_serial_deregister(& whiteheat_fake_device);
  }
  failed_fake_register:
  return (retval);
}
}
static void whiteheat_exit(void) __attribute__((__section__(".exit.text"), __no_instrument_function__)) ;
static void whiteheat_exit(void) __attribute__((__section__(".exit.text"), __no_instrument_function__)) ;
static void whiteheat_exit(void)
{

  {
  {
  usb_deregister(& whiteheat_driver);
  usb_serial_deregister(& whiteheat_fake_device);
  usb_serial_deregister(& whiteheat_device);
  }
  return;
}
}
int init_module(void)
{ int tmp___7 ;

  {
  {
  tmp___7 = whiteheat_init();
  }
  return (tmp___7);
}
}
void cleanup_module(void)
{

  {
  {
  whiteheat_exit();
  }
  return;
}
}
static char const __mod_author1555[87] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
  { (char const )'a', (char const )'u', (char const )'t', (char const )'h',
        (char const )'o', (char const )'r', (char const )'=', (char const )'G',
        (char const )'r', (char const )'e', (char const )'g', (char const )' ',
        (char const )'K', (char const )'r', (char const )'o', (char const )'a',
        (char const )'h', (char const )'-', (char const )'H', (char const )'a',
        (char const )'r', (char const )'t', (char const )'m', (char const )'a',
        (char const )'n', (char const )' ', (char const )'<', (char const )'g',
        (char const )'r', (char const )'e', (char const )'g', (char const )'@',
        (char const )'k', (char const )'r', (char const )'o', (char const )'a',
        (char const )'h', (char const )'.', (char const )'c', (char const )'o',
        (char const )'m', (char const )'>', (char const )',', (char const )' ',
        (char const )'S', (char const )'t', (char const )'u', (char const )'a',
        (char const )'r', (char const )'t', (char const )' ', (char const )'M',
        (char const )'a', (char const )'c', (char const )'D', (char const )'o',
        (char const )'n', (char const )'a', (char const )'l', (char const )'d',
        (char const )' ', (char const )'<', (char const )'s', (char const )'t',
        (char const )'u', (char const )'a', (char const )'r', (char const )'t',
        (char const )'m', (char const )'@', (char const )'c', (char const )'o',
        (char const )'n', (char const )'n', (char const )'e', (char const )'c',
        (char const )'t', (char const )'t', (char const )'e', (char const )'c',
        (char const )'h', (char const )'.', (char const )'c', (char const )'o',
        (char const )'m', (char const )'>', (char const )'\000'};
static char const __mod_description1556[45] __attribute__((__used__, __unused__,
__section__(".modinfo"), __aligned__(1))) =
  { (char const )'d', (char const )'e', (char const )'s', (char const )'c',
        (char const )'r', (char const )'i', (char const )'p', (char const )'t',
        (char const )'i', (char const )'o', (char const )'n', (char const )'=',
        (char const )'U', (char const )'S', (char const )'B', (char const )' ',
        (char const )'C', (char const )'o', (char const )'n', (char const )'n',
        (char const )'e', (char const )'c', (char const )'t', (char const )'T',
        (char const )'e', (char const )'c', (char const )'h', (char const )' ',
        (char const )'W', (char const )'h', (char const )'i', (char const )'t',
        (char const )'e', (char const )'H', (char const )'E', (char const )'A',
        (char const )'T', (char const )' ', (char const )'d', (char const )'r',
        (char const )'i', (char const )'v', (char const )'e', (char const )'r',
        (char const )'\000'};
static char const __mod_license1557[12] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
  { (char const )'l', (char const )'i', (char const )'c', (char const )'e',
        (char const )'n', (char const )'s', (char const )'e', (char const )'=',
        (char const )'G', (char const )'P', (char const )'L', (char const )'\000'};
static char const __mod_firmware1559[22] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
  { (char const )'f', (char const )'i', (char const )'r', (char const )'m',
        (char const )'w', (char const )'a', (char const )'r', (char const )'e',
        (char const )'=', (char const )'w', (char const )'h', (char const )'i',
        (char const )'t', (char const )'e', (char const )'h', (char const )'e',
        (char const )'a', (char const )'t', (char const )'.', (char const )'f',
        (char const )'w', (char const )'\000'};
static char const __mod_firmware1560[29] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
  { (char const )'f', (char const )'i', (char const )'r', (char const )'m',
        (char const )'w', (char const )'a', (char const )'r', (char const )'e',
        (char const )'=', (char const )'w', (char const )'h', (char const )'i',
        (char const )'t', (char const )'e', (char const )'h', (char const )'e',
        (char const )'a', (char const )'t', (char const )'_', (char const )'l',
        (char const )'o', (char const )'a', (char const )'d', (char const )'e',
        (char const )'r', (char const )'.', (char const )'f', (char const )'w',
        (char const )'\000'};
static char const __param_str_urb_pool_size[14] =
  { (char const )'u', (char const )'r', (char const )'b', (char const )'_',
        (char const )'p', (char const )'o', (char const )'o', (char const )'l',
        (char const )'_', (char const )'s', (char const )'i', (char const )'z',
        (char const )'e', (char const )'\000'};
static struct kernel_param const __param_urb_pool_size __attribute__((__used__,
__unused__, __section__("__param"), __aligned__(sizeof(void *)))) = {__param_str_urb_pool_size, (struct kernel_param_ops const *)(& param_ops_int),
    (u16 )0, (u16 )0, {(void *)(& urb_pool_size)}};
static char const __mod_urb_pool_sizetype1562[27] __attribute__((__used__, __unused__,
__section__(".modinfo"), __aligned__(1))) =
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'t', (char const )'y', (char const )'p', (char const )'e',
        (char const )'=', (char const )'u', (char const )'r', (char const )'b',
        (char const )'_', (char const )'p', (char const )'o', (char const )'o',
        (char const )'l', (char const )'_', (char const )'s', (char const )'i',
        (char const )'z', (char const )'e', (char const )':', (char const )'i',
        (char const )'n', (char const )'t', (char const )'\000'};
static char const __mod_urb_pool_size1563[55] __attribute__((__used__, __unused__,
__section__(".modinfo"), __aligned__(1))) =
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'=', (char const )'u', (char const )'r', (char const )'b',
        (char const )'_', (char const )'p', (char const )'o', (char const )'o',
        (char const )'l', (char const )'_', (char const )'s', (char const )'i',
        (char const )'z', (char const )'e', (char const )':', (char const )'N',
        (char const )'u', (char const )'m', (char const )'b', (char const )'e',
        (char const )'r', (char const )' ', (char const )'o', (char const )'f',
        (char const )' ', (char const )'u', (char const )'r', (char const )'b',
        (char const )'s', (char const )' ', (char const )'t', (char const )'o',
        (char const )' ', (char const )'u', (char const )'s', (char const )'e',
        (char const )' ', (char const )'f', (char const )'o', (char const )'r',
        (char const )' ', (char const )'b', (char const )'u', (char const )'f',
        (char const )'f', (char const )'e', (char const )'r', (char const )'i',
        (char const )'n', (char const )'g', (char const )'\000'};
static char const __param_str_debug[6] = { (char const )'d', (char const )'e', (char const )'b', (char const )'u',
        (char const )'g', (char const )'\000'};
static struct kernel_param const __param_debug __attribute__((__used__, __unused__,
__section__("__param"), __aligned__(sizeof(void *)))) = {__param_str_debug, (struct kernel_param_ops const *)(& param_ops_bool), (u16 )420,
    (u16 )0, {(void *)(& debug)}};
static char const __mod_debugtype1565[20] __attribute__((__used__, __unused__,
__section__(".modinfo"), __aligned__(1))) =
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'t', (char const )'y', (char const )'p', (char const )'e',
        (char const )'=', (char const )'d', (char const )'e', (char const )'b',
        (char const )'u', (char const )'g', (char const )':', (char const )'b',
        (char const )'o', (char const )'o', (char const )'l', (char const )'\000'};
static char const __mod_debug1566[32] __attribute__((__used__, __unused__, __section__(".modinfo"),
__aligned__(1))) =
  { (char const )'p', (char const )'a', (char const )'r', (char const )'m',
        (char const )'=', (char const )'d', (char const )'e', (char const )'b',
        (char const )'u', (char const )'g', (char const )':', (char const )'D',
        (char const )'e', (char const )'b', (char const )'u', (char const )'g',
        (char const )' ', (char const )'e', (char const )'n', (char const )'a',
        (char const )'b', (char const )'l', (char const )'e', (char const )'d',
        (char const )' ', (char const )'o', (char const )'r', (char const )' ',
        (char const )'n', (char const )'o', (char const )'t', (char const )'\000'};
void ldv_check_final_state(void) __attribute__((__ldv_model__)) ;
extern void ldv_check_return_value(int res ) ;
extern void ldv_initialize(void) ;
extern int __VERIFIER_nondet_int(void) ;
int LDV_IN_INTERRUPT ;
static int res_whiteheat_firmware_download_0 ;
static int res_whiteheat_open_4 ;
int main(void)
{ struct usb_serial *var_group1 ;
  struct usb_device_id const *var_whiteheat_firmware_download_0_p1 ;
  struct tty_struct *var_group2 ;
  struct usb_serial_port *var_group3 ;
  unsigned char const *var_whiteheat_write_6_p2 ;
  int var_whiteheat_write_6_p3 ;
  unsigned int var_whiteheat_ioctl_10_p1 ;
  unsigned long var_whiteheat_ioctl_10_p2 ;
  struct ktermios *var_whiteheat_set_termios_11_p2 ;
  int var_whiteheat_break_ctl_12_p1 ;
  unsigned int var_whiteheat_tiocmset_9_p1 ;
  unsigned int var_whiteheat_tiocmset_9_p2 ;
  struct urb *var_group4 ;
  int tmp___7 ;
  int ldv_s_whiteheat_fake_device_usb_serial_driver ;
  int ldv_s_whiteheat_device_usb_serial_driver ;
  int tmp___8 ;
  int tmp___9 ;

  {
  {
  LDV_IN_INTERRUPT = 1;
  ldv_initialize();
  tmp___7 = whiteheat_init();
  }
  if (tmp___7) {
    goto ldv_final;
  } else {

  }
  ldv_s_whiteheat_fake_device_usb_serial_driver = 0;
  ldv_s_whiteheat_device_usb_serial_driver = 0;
  {
  while (1) {
    while_continue: ;
    {
    tmp___9 = __VERIFIER_nondet_int();
    }
    if (tmp___9) {

    } else
    if (! (ldv_s_whiteheat_fake_device_usb_serial_driver == 0)) {

    } else
    if (! (ldv_s_whiteheat_device_usb_serial_driver == 0)) {

    } else {
      goto while_break;
    }
    {
    tmp___8 = __VERIFIER_nondet_int();
    }
    if (tmp___8 == 0) {
      goto case_0;
    } else
    if (tmp___8 == 1) {
      goto case_1;
    } else
    if (tmp___8 == 2) {
      goto case_2;
    } else
    if (tmp___8 == 3) {
      goto case_3;
    } else
    if (tmp___8 == 4) {
      goto case_4;
    } else
    if (tmp___8 == 5) {
      goto case_5;
    } else
    if (tmp___8 == 6) {
      goto case_6;
    } else
    if (tmp___8 == 7) {
      goto case_7;
    } else
    if (tmp___8 == 8) {
      goto case_8;
    } else
    if (tmp___8 == 9) {
      goto case_9;
    } else
    if (tmp___8 == 10) {
      goto case_10;
    } else
    if (tmp___8 == 11) {
      goto case_11;
    } else
    if (tmp___8 == 12) {
      goto case_12;
    } else
    if (tmp___8 == 13) {
      goto case_13;
    } else
    if (tmp___8 == 14) {
      goto case_14;
    } else
    if (tmp___8 == 15) {
      goto case_15;
    } else
    if (tmp___8 == 16) {
      goto case_16;
    } else
    if (tmp___8 == 17) {
      goto case_17;
    } else {
      goto switch_default;
      if (0) {
        case_0:
        if (ldv_s_whiteheat_fake_device_usb_serial_driver == 0) {
          {
          res_whiteheat_firmware_download_0 = whiteheat_firmware_download(var_group1,
                                                                          var_whiteheat_firmware_download_0_p1);
          ldv_check_return_value(res_whiteheat_firmware_download_0);
          }
          if (res_whiteheat_firmware_download_0) {
            goto ldv_module_exit;
          } else {

          }
          ldv_s_whiteheat_fake_device_usb_serial_driver = 0;
        } else {

        }
        goto switch_break;
        case_1:
        {
        whiteheat_firmware_attach(var_group1);
        }
        goto switch_break;
        case_2:
        if (ldv_s_whiteheat_device_usb_serial_driver == 0) {
          {
          res_whiteheat_open_4 = whiteheat_open(var_group2, var_group3);
          ldv_check_return_value(res_whiteheat_open_4);
          }
          if (res_whiteheat_open_4) {
            goto ldv_module_exit;
          } else {

          }
          ldv_s_whiteheat_device_usb_serial_driver = ldv_s_whiteheat_device_usb_serial_driver + 1;
        } else {

        }
        goto switch_break;
        case_3:
        if (ldv_s_whiteheat_device_usb_serial_driver == 1) {
          {
          whiteheat_close(var_group3);
          ldv_s_whiteheat_device_usb_serial_driver = ldv_s_whiteheat_device_usb_serial_driver + 1;
          }
        } else {

        }
        goto switch_break;
        case_4:
        if (ldv_s_whiteheat_device_usb_serial_driver == 2) {
          {
          whiteheat_attach(var_group1);
          whiteheat_release(var_group1);
          ldv_s_whiteheat_device_usb_serial_driver = 0;
          }
        } else {

        }
        goto switch_break;
        case_5:
        {
        whiteheat_attach(var_group1);
        }
        goto switch_break;
        case_6:
        {
        whiteheat_write(var_group2, var_group3, var_whiteheat_write_6_p2, var_whiteheat_write_6_p3);
        }
        goto switch_break;
        case_7:
        {
        whiteheat_write_room(var_group2);
        }
        goto switch_break;
        case_8:
        {
        whiteheat_ioctl(var_group2, var_whiteheat_ioctl_10_p1, var_whiteheat_ioctl_10_p2);
        }
        goto switch_break;
        case_9:
        {
        whiteheat_set_termios(var_group2, var_group3, var_whiteheat_set_termios_11_p2);
        }
        goto switch_break;
        case_10:
        {
        whiteheat_break_ctl(var_group2, var_whiteheat_break_ctl_12_p1);
        }
        goto switch_break;
        case_11:
        {
        whiteheat_tiocmget(var_group2);
        }
        goto switch_break;
        case_12:
        {
        whiteheat_tiocmset(var_group2, var_whiteheat_tiocmset_9_p1, var_whiteheat_tiocmset_9_p2);
        }
        goto switch_break;
        case_13:
        {
        whiteheat_chars_in_buffer(var_group2);
        }
        goto switch_break;
        case_14:
        {
        whiteheat_throttle(var_group2);
        }
        goto switch_break;
        case_15:
        {
        whiteheat_unthrottle(var_group2);
        }
        goto switch_break;
        case_16:
        {
        whiteheat_read_callback(var_group4);
        }
        goto switch_break;
        case_17:
        {
        whiteheat_write_callback(var_group4);
        }
        goto switch_break;
        switch_default:
        goto switch_break;
      } else {
        switch_break: ;
      }
    }
  }
  while_break___0: ;
  }
  while_break: ;
  ldv_module_exit:
  {
  whiteheat_exit();
  }
  ldv_final:
  {
  ldv_check_final_state();
  }
  return 0;
}
}
void ldv_blast_assert(void)
{

  {
  ERROR: __VERIFIER_error();
}
}
extern void *ldv_undefined_pointer(void) ;
void ldv_assume_stop(void) __attribute__((__ldv_model_inline__)) ;
void ldv_assume_stop(void) __attribute__((__ldv_model_inline__)) ;
void ldv_assume_stop(void)
{

  {
  LDV_STOP:
  goto LDV_STOP;
}
}
int ldv_urb_state = 0;
int ldv_coherent_state = 0;
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma ) __attribute__((__ldv_model__)) ;
void *usb_alloc_coherent(struct usb_device *dev , size_t size , gfp_t mem_flags ,
                         dma_addr_t *dma )
{ void *arbitrary_memory ;
  void *tmp___7 ;

  {
  {
  while (1) {
    while_continue: ;
    {
    tmp___7 = ldv_undefined_pointer();
    arbitrary_memory = tmp___7;
    }
    if (! arbitrary_memory) {
      return ((void *)0);
    } else {

    }
    ldv_coherent_state = ldv_coherent_state + 1;
    return (arbitrary_memory);
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  return ((void *)0);
}
}
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma ) __attribute__((__ldv_model__)) ;
void usb_free_coherent(struct usb_device *dev , size_t size , void *addr , dma_addr_t dma )
{

  {
  {
  while (1) {
    while_continue: ;
    if (! ((unsigned long )addr != (unsigned long )((void *)0))) {
      {
      ldv_assume_stop();
      }
    } else {

    }
    if (addr) {
      if (ldv_coherent_state >= 1) {

      } else {
        {
        ldv_blast_assert();
        }
      }
      ldv_coherent_state = ldv_coherent_state - 1;
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  return;
}
}
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags ) __attribute__((__ldv_model__)) ;
struct urb *usb_alloc_urb(int iso_packets , gfp_t mem_flags )
{ void *arbitrary_memory ;
  void *tmp___7 ;

  {
  {
  while (1) {
    while_continue: ;
    {
    tmp___7 = ldv_undefined_pointer();
    arbitrary_memory = tmp___7;
    }
    if (! arbitrary_memory) {
      return ((struct urb *)((void *)0));
    } else {

    }
    ldv_urb_state = ldv_urb_state + 1;
    return ((struct urb *)arbitrary_memory);
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  return ((struct urb *)0);
}
}
void usb_free_urb(struct urb *urb ) __attribute__((__ldv_model__)) ;
void usb_free_urb(struct urb *urb )
{

  {
  {
  while (1) {
    while_continue: ;
    if (! ((unsigned long )urb != (unsigned long )((struct urb *)0))) {
      {
      ldv_assume_stop();
      }
    } else {

    }
    if (urb) {
      if (ldv_urb_state >= 1) {

      } else {
        {
        ldv_blast_assert();
        }
      }
      ldv_urb_state = ldv_urb_state - 1;
    } else {

    }
    goto while_break;
  }
  while_break___0: ;
  }
  while_break: ;
  return;
}
}
void ldv_check_final_state(void) __attribute__((__ldv_model__)) ;
void ldv_check_final_state(void)
{

  {
  if (ldv_urb_state == 0) {

  } else {
    {
    ldv_blast_assert();
    }
  }
  if (ldv_coherent_state == 0) {

  } else {
    {
    ldv_blast_assert();
    }
  }
  return;
}
}

var wflag : bool;
type STRUCT~sigevent;
type STRUCT~__locale_data;
implementation ULTIMATE.init() returns (){
    assume 0 == #valid[0];
    assume 0 < #StackHeapBarrier;
    call #Ultimate.allocInit(2, 1);
    call write~init~int(48, { base: 1, offset: 0 }, 1);
    call write~init~int(0, { base: 1, offset: 1 }, 1);
    call #Ultimate.allocInit(21, 2);
    ~x~0 := 0;
    ~y~0 := 0;
    call #Ultimate.allocInit(32, 3);
    ~#rwlock~0 := { base: 3, offset: 0 };
    call write~init~int(0, { base: ~#rwlock~0!base, offset: ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 4 + ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 8 + ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 12 + ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 16 + ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 20 + ~#rwlock~0!offset }, 4);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 24 + ~#rwlock~0!offset }, 1);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 25 + ~#rwlock~0!offset }, 1);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 26 + ~#rwlock~0!offset }, 1);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 27 + ~#rwlock~0!offset }, 1);
    call write~init~int(0, { base: ~#rwlock~0!base, offset: 28 + ~#rwlock~0!offset }, 4);
}

implementation ULTIMATE.start() returns (){
    var #t~ret9 : int;
    wflag := false;

    call ULTIMATE.init();
    call #t~ret9 := main();
}

implementation reach_error() returns (){
    var #t~nondet0 : $Pointer$;

    if (false) {
    } else {
        assume false;
    }
}

implementation thr1(#in~arg : $Pointer$) returns (#res : $Pointer$){
    var #t~ret1 : int;
    var #t~nondet2 : int;
    var #t~ret3 : int;
    var ~arg : $Pointer$;

    ~arg := #in~arg;
    atomic {
        call #t~ret1 := #PthreadsRwLockWriteLock(~#rwlock~0);
	assume !wflag;
	wflag := true;
    }
    havoc #t~ret1;
    ~x~0 := 3;
    havoc #t~nondet2;
    #race~x~0 := #t~nondet2;
    assert #race~x~0 == #t~nondet2;
    havoc #t~nondet2;
    atomic {
        call #t~ret3 := #PthreadsRwLockUnlock(~#rwlock~0);
	wflag := false;
    }
    havoc #t~ret3;
    #res := { base: 0, offset: 0 };
    return;
}

implementation thr2(#in~arg : $Pointer$) returns (#res : $Pointer$){
    var #t~ret4 : int;
    var #t~ret5 : int;
    var ~arg : $Pointer$;
    var ~l~0 : int;

    ~arg := #in~arg;
    atomic {
        call #t~ret4 := #PthreadsRwLockReadLock(~#rwlock~0);
	assume !wflag;
	wflag := true;
    }
    havoc #t~ret4;
    #race~x~0 := 0;
    assert 0 == #race~x~0;
    ~l~0 := ~x~0;
    atomic {
        call #t~ret5 := #PthreadsRwLockUnlock(~#rwlock~0);
	wflag := false;
    }
    havoc #t~ret5;
    #res := { base: 0, offset: 0 };
    return;
}

implementation main() returns (#res : int){
    var #t~pre6 : int;
    var #t~nondet7 : int;
    var #t~ret8 : $Pointer$;
    var ~t~0 : ~pthread_t~0;

    havoc ~t~0;
    #t~pre6 := #pthreadsForks;
    #pthreadsForks := 1 + #pthreadsForks;
    ~t~0 := #t~pre6;
    fork #t~pre6, 0 thr1({ base: 0, offset: 0 });
    havoc #t~pre6;
    havoc #t~nondet7;
    call #t~ret8 := thr2({ base: 0, offset: 0 });
    havoc #t~ret8;
    #res := 0;
    return;
}

const #funAddr~thr1 : $Pointer$;
axiom #funAddr~thr1 == { base: -1, offset: 0 };
type ~__u_char~0 = int;
type ~__u_short~0 = int;
type ~__u_int~0 = int;
type ~__u_long~0 = int;
type ~__int8_t~0 = int;
type ~__uint8_t~0 = int;
type ~__int16_t~0 = int;
type ~__uint16_t~0 = int;
type ~__int32_t~0 = int;
type ~__uint32_t~0 = int;
type ~__int64_t~0 = int;
type ~__uint64_t~0 = int;
type ~__int_least8_t~0 = ~__int8_t~0;
type ~__uint_least8_t~0 = ~__uint8_t~0;
type ~__int_least16_t~0 = ~__int16_t~0;
type ~__uint_least16_t~0 = ~__uint16_t~0;
type ~__int_least32_t~0 = ~__int32_t~0;
type ~__uint_least32_t~0 = ~__uint32_t~0;
type ~__int_least64_t~0 = ~__int64_t~0;
type ~__uint_least64_t~0 = ~__uint64_t~0;
type ~__quad_t~0 = int;
type ~__u_quad_t~0 = int;
type ~__intmax_t~0 = int;
type ~__uintmax_t~0 = int;
type ~__dev_t~0 = ~__uint64_t~0;
type ~__uid_t~0 = int;
type ~__gid_t~0 = int;
type ~__ino_t~0 = int;
type ~__ino64_t~0 = ~__uint64_t~0;
type ~__mode_t~0 = int;
type ~__nlink_t~0 = int;
type ~__off_t~0 = int;
type ~__off64_t~0 = ~__int64_t~0;
type ~__pid_t~0 = int;
type ~__fsid_t~0 = { __val : [int]int };
type ~__clock_t~0 = int;
type ~__rlim_t~0 = int;
type ~__rlim64_t~0 = ~__uint64_t~0;
type ~__id_t~0 = int;
type ~__time_t~0 = int;
type ~__useconds_t~0 = int;
type ~__suseconds_t~0 = int;
type ~__suseconds64_t~0 = ~__int64_t~0;
type ~__daddr_t~0 = int;
type ~__key_t~0 = int;
type ~__clockid_t~0 = int;
type ~__timer_t~0 = $Pointer$;
type ~__blksize_t~0 = int;
type ~__blkcnt_t~0 = int;
type ~__blkcnt64_t~0 = ~__int64_t~0;
type ~__fsblkcnt_t~0 = int;
type ~__fsblkcnt64_t~0 = ~__uint64_t~0;
type ~__fsfilcnt_t~0 = int;
type ~__fsfilcnt64_t~0 = ~__uint64_t~0;
type ~__fsword_t~0 = int;
type ~__ssize_t~0 = int;
type ~__syscall_slong_t~0 = int;
type ~__syscall_ulong_t~0 = int;
type ~__loff_t~0 = ~__off64_t~0;
type ~__caddr_t~0 = $Pointer$;
type ~__intptr_t~0 = int;
type ~__socklen_t~0 = int;
type ~__sig_atomic_t~0 = int;
type ~__time64_t~0 = ~__int64_t~0;
type ~size_t~0 = int;
type ~time_t~0 = ~__time_t~0;
type ~pid_t~0 = ~__pid_t~0;
type ~__cpu_mask~0 = int;
type ~cpu_set_t~0 = { __bits : [int]~__cpu_mask~0 };
type ~clock_t~0 = ~__clock_t~0;
type ~clockid_t~0 = ~__clockid_t~0;
type ~timer_t~0 = ~__timer_t~0;
type ~__locale_t~0 = $Pointer$;
type ~locale_t~0 = ~__locale_t~0;
type ~__atomic_wide_counter~0 = { __value64 : int, __value32 : { __low : int, __high : int } };
type ~__pthread_list_t~0 = { __prev : $Pointer$, __next : $Pointer$ };
type ~__pthread_slist_t~0 = { __next : $Pointer$ };
type ~__tss_t~0 = int;
type ~__thrd_t~0 = int;
type ~__once_flag~0 = { __data : int };
type ~pthread_t~0 = int;
type ~pthread_mutexattr_t~0 = { __size : [int]int, __align : int };
type ~pthread_condattr_t~0 = { __size : [int]int, __align : int };
type ~pthread_key_t~0 = int;
type ~pthread_once_t~0 = int;
type ~pthread_attr_t~0 = { __size : [int]int, __align : int };
type ~pthread_mutex_t~0 = { __data : { __lock : int, __count : int, __owner : int, __kind : int, __nusers : int }, __size : [int]int, __align : int };
type ~pthread_cond_t~0 = { __data : { __wseq : ~__atomic_wide_counter~0, __g1_start : ~__atomic_wide_counter~0, __g_refs : [int]int, __g_size : [int]int, __g1_orig_size : int, __wrefs : int, __g_signals : [int]int }, __size : [int]int, __align : int };
type ~pthread_rwlock_t~0 = { __data : { __readers : int, __writers : int, __wrphase_futex : int, __writers_futex : int, __pad3 : int, __pad4 : int, __flags : int, __shared : int, __rwelision : int, __pad2 : int, __cur_writer : int }, __size : [int]int, __align : int };
type ~pthread_rwlockattr_t~0 = { __size : [int]int, __align : int };
type ~pthread_spinlock_t~0 = int;
type ~pthread_barrier_t~0 = { __size : [int]int, __align : int };
type ~pthread_barrierattr_t~0 = { __size : [int]int, __align : int };
type ~__jmp_buf~0 = [int]int;
type ~__sigset_t~0 = { __val : [int]int };
type ~__pthread_unwind_buf_t~0 = { __cancel_jmp_buf : [int]{ __cancel_jmp_buf : ~__jmp_buf~0, __mask_was_saved : int }, __pad : [int]$Pointer$ };
const ~unnamed0~0~PTHREAD_CREATE_JOINABLE : int;
const ~unnamed0~0~PTHREAD_CREATE_DETACHED : int;
const ~unnamed1~0~PTHREAD_MUTEX_TIMED_NP : int;
const ~unnamed1~0~PTHREAD_MUTEX_RECURSIVE_NP : int;
const ~unnamed1~0~PTHREAD_MUTEX_ERRORCHECK_NP : int;
const ~unnamed1~0~PTHREAD_MUTEX_ADAPTIVE_NP : int;
const ~unnamed1~0~PTHREAD_MUTEX_NORMAL : int;
const ~unnamed1~0~PTHREAD_MUTEX_RECURSIVE : int;
const ~unnamed1~0~PTHREAD_MUTEX_ERRORCHECK : int;
const ~unnamed1~0~PTHREAD_MUTEX_DEFAULT : int;
const ~unnamed2~0~PTHREAD_MUTEX_STALLED : int;
const ~unnamed2~0~PTHREAD_MUTEX_STALLED_NP : int;
const ~unnamed2~0~PTHREAD_MUTEX_ROBUST : int;
const ~unnamed2~0~PTHREAD_MUTEX_ROBUST_NP : int;
const ~unnamed3~0~PTHREAD_PRIO_NONE : int;
const ~unnamed3~0~PTHREAD_PRIO_INHERIT : int;
const ~unnamed3~0~PTHREAD_PRIO_PROTECT : int;
const ~unnamed4~0~PTHREAD_RWLOCK_PREFER_READER_NP : int;
const ~unnamed4~0~PTHREAD_RWLOCK_PREFER_WRITER_NP : int;
const ~unnamed4~0~PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP : int;
const ~unnamed4~0~PTHREAD_RWLOCK_DEFAULT_NP : int;
const ~unnamed5~0~PTHREAD_INHERIT_SCHED : int;
const ~unnamed5~0~PTHREAD_EXPLICIT_SCHED : int;
const ~unnamed6~0~PTHREAD_SCOPE_SYSTEM : int;
const ~unnamed6~0~PTHREAD_SCOPE_PROCESS : int;
const ~unnamed7~0~PTHREAD_PROCESS_PRIVATE : int;
const ~unnamed7~0~PTHREAD_PROCESS_SHARED : int;
const ~unnamed8~0~PTHREAD_CANCEL_ENABLE : int;
const ~unnamed8~0~PTHREAD_CANCEL_DISABLE : int;
const ~unnamed9~0~PTHREAD_CANCEL_DEFERRED : int;
const ~unnamed9~0~PTHREAD_CANCEL_ASYNCHRONOUS : int;
axiom 0 == ~unnamed0~0~PTHREAD_CREATE_JOINABLE;
axiom 1 == ~unnamed0~0~PTHREAD_CREATE_DETACHED;
axiom 0 == ~unnamed1~0~PTHREAD_MUTEX_TIMED_NP;
axiom 1 == ~unnamed1~0~PTHREAD_MUTEX_RECURSIVE_NP;
axiom 2 == ~unnamed1~0~PTHREAD_MUTEX_ERRORCHECK_NP;
axiom 3 == ~unnamed1~0~PTHREAD_MUTEX_ADAPTIVE_NP;
axiom 0 == ~unnamed1~0~PTHREAD_MUTEX_NORMAL;
axiom 1 == ~unnamed1~0~PTHREAD_MUTEX_RECURSIVE;
axiom 2 == ~unnamed1~0~PTHREAD_MUTEX_ERRORCHECK;
axiom 0 == ~unnamed1~0~PTHREAD_MUTEX_DEFAULT;
axiom 0 == ~unnamed2~0~PTHREAD_MUTEX_STALLED;
axiom 0 == ~unnamed2~0~PTHREAD_MUTEX_STALLED_NP;
axiom 1 == ~unnamed2~0~PTHREAD_MUTEX_ROBUST;
axiom 1 == ~unnamed2~0~PTHREAD_MUTEX_ROBUST_NP;
axiom 0 == ~unnamed3~0~PTHREAD_PRIO_NONE;
axiom 1 == ~unnamed3~0~PTHREAD_PRIO_INHERIT;
axiom 2 == ~unnamed3~0~PTHREAD_PRIO_PROTECT;
axiom 0 == ~unnamed4~0~PTHREAD_RWLOCK_PREFER_READER_NP;
axiom 1 == ~unnamed4~0~PTHREAD_RWLOCK_PREFER_WRITER_NP;
axiom 2 == ~unnamed4~0~PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP;
axiom 0 == ~unnamed4~0~PTHREAD_RWLOCK_DEFAULT_NP;
axiom 0 == ~unnamed5~0~PTHREAD_INHERIT_SCHED;
axiom 1 == ~unnamed5~0~PTHREAD_EXPLICIT_SCHED;
axiom 0 == ~unnamed6~0~PTHREAD_SCOPE_SYSTEM;
axiom 1 == ~unnamed6~0~PTHREAD_SCOPE_PROCESS;
axiom 0 == ~unnamed7~0~PTHREAD_PROCESS_PRIVATE;
axiom 1 == ~unnamed7~0~PTHREAD_PROCESS_SHARED;
axiom 0 == ~unnamed8~0~PTHREAD_CANCEL_ENABLE;
axiom 1 == ~unnamed8~0~PTHREAD_CANCEL_DISABLE;
axiom 0 == ~unnamed9~0~PTHREAD_CANCEL_DEFERRED;
axiom 1 == ~unnamed9~0~PTHREAD_CANCEL_ASYNCHRONOUS;
var ~__tzname~0 : [int]$Pointer$;

var ~__daylight~0 : int;

var ~__timezone~0 : int;

var ~tzname~0 : [int]$Pointer$;

var ~daylight~0 : int;

var ~timezone~0 : int;

var ~x~0 : int;

var ~y~0 : int;

var ~#rwlock~0 : $Pointer$;

var #valid : [int]int;

var #length : [int]int;

var #memory_int : [$Pointer$]int;

var #pthreadsForks : int;

var #pthreadsRwLock : [$Pointer$]int;

var #StackHeapBarrier : int;

var #race : [$Pointer$]int;

var #race~x~0 : int;

type $Pointer$ = { base : int, offset : int };
procedure abort() returns ();
modifies ;

procedure __assert_fail(#in~__assertion : $Pointer$, #in~__file : $Pointer$, #in~__line : int, #in~__function : $Pointer$) returns ();
modifies ;

procedure __assert_perror_fail(#in~__errnum : int, #in~__file : $Pointer$, #in~__line : int, #in~__function : $Pointer$) returns ();
modifies ;

procedure __assert(#in~__assertion : $Pointer$, #in~__file : $Pointer$, #in~__line : int) returns ();
modifies ;

procedure reach_error() returns ();
modifies ;

procedure #Ultimate.allocInit(~size, ptrBase : int) returns ();
ensures 1 == #valid[ptrBase];
ensures #length[ptrBase] == ~size;
modifies ;

procedure __VERIFIER_atomic_begin() returns ();
modifies ;

procedure __VERIFIER_atomic_end() returns ();
modifies ;

procedure __sched_cpucount(#in~__setsize : int, #in~__setp : $Pointer$) returns (#res : int);
modifies ;

procedure __sched_cpualloc(#in~__count : int) returns (#res : $Pointer$);
modifies ;

procedure __sched_cpufree(#in~__set : $Pointer$) returns ();
modifies ;

procedure sched_setparam(#in~__pid : int, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure sched_getparam(#in~__pid : int, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure sched_setscheduler(#in~__pid : int, #in~__policy : int, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure sched_getscheduler(#in~__pid : int) returns (#res : int);
modifies ;

procedure sched_yield() returns (#res : int);
modifies ;

procedure sched_get_priority_max(#in~__algorithm : int) returns (#res : int);
modifies ;

procedure sched_get_priority_min(#in~__algorithm : int) returns (#res : int);
modifies ;

procedure sched_rr_get_interval(#in~__pid : int, #in~__t : $Pointer$) returns (#res : int);
modifies ;

procedure clock() returns (#res : ~clock_t~0);
modifies ;

procedure time(#in~__timer : $Pointer$) returns (#res : ~time_t~0);
modifies ;

procedure difftime(#in~__time1 : int, #in~__time0 : int) returns (#res : real);
modifies ;

procedure mktime(#in~__tp : $Pointer$) returns (#res : ~time_t~0);
modifies ;

procedure strftime(#in~__s : $Pointer$, #in~__maxsize : int, #in~__format : $Pointer$, #in~__tp : $Pointer$) returns (#res : ~size_t~0);
modifies ;

procedure strftime_l(#in~__s : $Pointer$, #in~__maxsize : int, #in~__format : $Pointer$, #in~__tp : $Pointer$, #in~__loc : $Pointer$) returns (#res : ~size_t~0);
modifies ;

procedure gmtime(#in~__timer : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure localtime(#in~__timer : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure gmtime_r(#in~__timer : $Pointer$, #in~__tp : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure localtime_r(#in~__timer : $Pointer$, #in~__tp : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure asctime(#in~__tp : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure ctime(#in~__timer : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure asctime_r(#in~__tp : $Pointer$, #in~__buf : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure ctime_r(#in~__timer : $Pointer$, #in~__buf : $Pointer$) returns (#res : $Pointer$);
modifies ;

procedure tzset() returns ();
modifies ;

procedure timegm(#in~__tp : $Pointer$) returns (#res : ~time_t~0);
modifies ;

procedure timelocal(#in~__tp : $Pointer$) returns (#res : ~time_t~0);
modifies ;

procedure dysize(#in~__year : int) returns (#res : int);
modifies ;

procedure nanosleep(#in~__requested_time : $Pointer$, #in~__remaining : $Pointer$) returns (#res : int);
modifies ;

procedure clock_getres(#in~__clock_id : int, #in~__res : $Pointer$) returns (#res : int);
modifies ;

procedure clock_gettime(#in~__clock_id : int, #in~__tp : $Pointer$) returns (#res : int);
modifies ;

procedure clock_settime(#in~__clock_id : int, #in~__tp : $Pointer$) returns (#res : int);
modifies ;

procedure clock_nanosleep(#in~__clock_id : int, #in~__flags : int, #in~__req : $Pointer$, #in~__rem : $Pointer$) returns (#res : int);
modifies ;

procedure clock_getcpuclockid(#in~__pid : int, #in~__clock_id : $Pointer$) returns (#res : int);
modifies ;

procedure timer_create(#in~__clock_id : int, #in~__evp : $Pointer$, #in~__timerid : $Pointer$) returns (#res : int);
modifies ;

procedure timer_delete(#in~__timerid : $Pointer$) returns (#res : int);
modifies ;

procedure timer_settime(#in~__timerid : $Pointer$, #in~__flags : int, #in~__value : $Pointer$, #in~__ovalue : $Pointer$) returns (#res : int);
modifies ;

procedure timer_gettime(#in~__timerid : $Pointer$, #in~__value : $Pointer$) returns (#res : int);
modifies ;

procedure timer_getoverrun(#in~__timerid : $Pointer$) returns (#res : int);
modifies ;

procedure timespec_get(#in~__ts : $Pointer$, #in~__base : int) returns (#res : int);
modifies ;

procedure pthread_create(#in~__newthread : $Pointer$, #in~__attr : $Pointer$, #in~__start_routine : $Pointer$, #in~__arg : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_exit(#in~__retval : $Pointer$) returns ();
modifies ;

procedure pthread_join(#in~__th : int, #in~__thread_return : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_detach(#in~__th : int) returns (#res : int);
modifies ;

procedure pthread_self() returns (#res : ~pthread_t~0);
modifies ;

procedure pthread_equal(#in~__thread1 : int, #in~__thread2 : int) returns (#res : int);
modifies ;

procedure pthread_attr_init(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_destroy(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_getdetachstate(#in~__attr : $Pointer$, #in~__detachstate : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setdetachstate(#in~__attr : $Pointer$, #in~__detachstate : int) returns (#res : int);
modifies ;

procedure pthread_attr_getguardsize(#in~__attr : $Pointer$, #in~__guardsize : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setguardsize(#in~__attr : $Pointer$, #in~__guardsize : int) returns (#res : int);
modifies ;

procedure pthread_attr_getschedparam(#in~__attr : $Pointer$, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setschedparam(#in~__attr : $Pointer$, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_getschedpolicy(#in~__attr : $Pointer$, #in~__policy : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setschedpolicy(#in~__attr : $Pointer$, #in~__policy : int) returns (#res : int);
modifies ;

procedure pthread_attr_getinheritsched(#in~__attr : $Pointer$, #in~__inherit : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setinheritsched(#in~__attr : $Pointer$, #in~__inherit : int) returns (#res : int);
modifies ;

procedure pthread_attr_getscope(#in~__attr : $Pointer$, #in~__scope : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setscope(#in~__attr : $Pointer$, #in~__scope : int) returns (#res : int);
modifies ;

procedure pthread_attr_getstackaddr(#in~__attr : $Pointer$, #in~__stackaddr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setstackaddr(#in~__attr : $Pointer$, #in~__stackaddr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_getstacksize(#in~__attr : $Pointer$, #in~__stacksize : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setstacksize(#in~__attr : $Pointer$, #in~__stacksize : int) returns (#res : int);
modifies ;

procedure pthread_attr_getstack(#in~__attr : $Pointer$, #in~__stackaddr : $Pointer$, #in~__stacksize : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_attr_setstack(#in~__attr : $Pointer$, #in~__stackaddr : $Pointer$, #in~__stacksize : int) returns (#res : int);
modifies ;

procedure pthread_setschedparam(#in~__target_thread : int, #in~__policy : int, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_getschedparam(#in~__target_thread : int, #in~__policy : $Pointer$, #in~__param : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_setschedprio(#in~__target_thread : int, #in~__prio : int) returns (#res : int);
modifies ;

procedure pthread_once(#in~__once_control : $Pointer$, #in~__init_routine : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_setcancelstate(#in~__state : int, #in~__oldstate : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_setcanceltype(#in~__type : int, #in~__oldtype : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cancel(#in~__th : int) returns (#res : int);
modifies ;

procedure pthread_testcancel() returns ();
modifies ;

procedure __pthread_register_cancel(#in~__buf : $Pointer$) returns ();
modifies ;

procedure __pthread_unregister_cancel(#in~__buf : $Pointer$) returns ();
modifies ;

procedure __pthread_unwind_next(#in~__buf : $Pointer$) returns ();
modifies ;

procedure __sigsetjmp_cancel(#in~__env : $Pointer$, #in~__savemask : int) returns (#res : int);
modifies ;

procedure pthread_mutex_init(#in~__mutex : $Pointer$, #in~__mutexattr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_destroy(#in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_trylock(#in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_lock(#in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_timedlock(#in~__mutex : $Pointer$, #in~__abstime : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_unlock(#in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_getprioceiling(#in~__mutex : $Pointer$, #in~__prioceiling : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_setprioceiling(#in~__mutex : $Pointer$, #in~__prioceiling : int, #in~__old_ceiling : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutex_consistent(#in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_init(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_destroy(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_getpshared(#in~__attr : $Pointer$, #in~__pshared : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_setpshared(#in~__attr : $Pointer$, #in~__pshared : int) returns (#res : int);
modifies ;

procedure pthread_mutexattr_gettype(#in~__attr : $Pointer$, #in~__kind : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_settype(#in~__attr : $Pointer$, #in~__kind : int) returns (#res : int);
modifies ;

procedure pthread_mutexattr_getprotocol(#in~__attr : $Pointer$, #in~__protocol : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_setprotocol(#in~__attr : $Pointer$, #in~__protocol : int) returns (#res : int);
modifies ;

procedure pthread_mutexattr_getprioceiling(#in~__attr : $Pointer$, #in~__prioceiling : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_setprioceiling(#in~__attr : $Pointer$, #in~__prioceiling : int) returns (#res : int);
modifies ;

procedure pthread_mutexattr_getrobust(#in~__attr : $Pointer$, #in~__robustness : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_mutexattr_setrobust(#in~__attr : $Pointer$, #in~__robustness : int) returns (#res : int);
modifies ;

procedure pthread_rwlock_init(#in~__rwlock : $Pointer$, #in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_destroy(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_rdlock(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_tryrdlock(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_timedrdlock(#in~__rwlock : $Pointer$, #in~__abstime : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_wrlock(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_trywrlock(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_timedwrlock(#in~__rwlock : $Pointer$, #in~__abstime : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlock_unlock(#in~__rwlock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_init(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_destroy(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_getpshared(#in~__attr : $Pointer$, #in~__pshared : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_setpshared(#in~__attr : $Pointer$, #in~__pshared : int) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_getkind_np(#in~__attr : $Pointer$, #in~__pref : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_rwlockattr_setkind_np(#in~__attr : $Pointer$, #in~__pref : int) returns (#res : int);
modifies ;

procedure pthread_cond_init(#in~__cond : $Pointer$, #in~__cond_attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cond_destroy(#in~__cond : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cond_signal(#in~__cond : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cond_broadcast(#in~__cond : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cond_wait(#in~__cond : $Pointer$, #in~__mutex : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_cond_timedwait(#in~__cond : $Pointer$, #in~__mutex : $Pointer$, #in~__abstime : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_condattr_init(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_condattr_destroy(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_condattr_getpshared(#in~__attr : $Pointer$, #in~__pshared : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_condattr_setpshared(#in~__attr : $Pointer$, #in~__pshared : int) returns (#res : int);
modifies ;

procedure pthread_condattr_getclock(#in~__attr : $Pointer$, #in~__clock_id : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_condattr_setclock(#in~__attr : $Pointer$, #in~__clock_id : int) returns (#res : int);
modifies ;

procedure pthread_spin_init(#in~__lock : $Pointer$, #in~__pshared : int) returns (#res : int);
modifies ;

procedure pthread_spin_destroy(#in~__lock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_spin_lock(#in~__lock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_spin_trylock(#in~__lock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_spin_unlock(#in~__lock : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrier_init(#in~__barrier : $Pointer$, #in~__attr : $Pointer$, #in~__count : int) returns (#res : int);
modifies ;

procedure pthread_barrier_destroy(#in~__barrier : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrier_wait(#in~__barrier : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrierattr_init(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrierattr_destroy(#in~__attr : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrierattr_getpshared(#in~__attr : $Pointer$, #in~__pshared : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_barrierattr_setpshared(#in~__attr : $Pointer$, #in~__pshared : int) returns (#res : int);
modifies ;

procedure pthread_key_create(#in~__key : $Pointer$, #in~__destr_function : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_key_delete(#in~__key : int) returns (#res : int);
modifies ;

procedure pthread_getspecific(#in~__key : int) returns (#res : $Pointer$);
modifies ;

procedure pthread_setspecific(#in~__key : int, #in~__pointer : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_getcpuclockid(#in~__thread_id : int, #in~__clock_id : $Pointer$) returns (#res : int);
modifies ;

procedure pthread_atfork(#in~__prepare : $Pointer$, #in~__parent : $Pointer$, #in~__child : $Pointer$) returns (#res : int);
modifies ;

procedure thr1(#in~arg : $Pointer$) returns (#res : $Pointer$);
modifies ~x~0, #race~x~0, #pthreadsRwLock, wflag;

procedure #PthreadsRwLockWriteLock(#inputPtr : $Pointer$) returns (#res : int);
free ensures 0 == old(#pthreadsRwLock)[#inputPtr];
free ensures #pthreadsRwLock == old(#pthreadsRwLock)[#inputPtr := -1];
free ensures 0 == #res;
modifies #pthreadsRwLock;

procedure #PthreadsRwLockUnlock(#inputPtr : $Pointer$) returns (#res : int);
free ensures #pthreadsRwLock == old(#pthreadsRwLock)[#inputPtr := (if old(#pthreadsRwLock)[#inputPtr] > 0 then old(#pthreadsRwLock)[#inputPtr] - 1 else 0)];
free ensures 0 == #res;
modifies ;

procedure thr2(#in~arg : $Pointer$) returns (#res : $Pointer$);
modifies #race~x~0, #pthreadsRwLock, wflag;

procedure #PthreadsRwLockReadLock(#inputPtr : $Pointer$) returns (#res : int);
free ensures old(#pthreadsRwLock)[#inputPtr] >= 0;
free ensures #pthreadsRwLock == old(#pthreadsRwLock)[#inputPtr := 1 + old(#pthreadsRwLock)[#inputPtr]];
free ensures 0 == #res;
modifies #pthreadsRwLock;

procedure main() returns (#res : int);
modifies #pthreadsForks, #race~x~0, #pthreadsRwLock, ~x~0, wflag;

procedure ULTIMATE.init() returns ();
modifies ~x~0, ~y~0, ~#rwlock~0, wflag;

procedure write~init~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
ensures #memory_int[#ptr] == #value;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ~x~0, ~y~0, ~#rwlock~0, #pthreadsForks, #race~x~0, #pthreadsRwLock, wflag;

procedure write~int(#value : int, #ptr : $Pointer$, #sizeOfWrittenType : int) returns ();
ensures #memory_int == old(#memory_int)[#ptr := #value];
modifies #memory_int;

procedure read~int(#ptr : $Pointer$, #sizeOfReadType : int) returns (#value : int);
ensures #value == #memory_int[#ptr];
modifies ;

procedure ULTIMATE.dealloc(~addr : $Pointer$) returns ();
free ensures #valid == old(#valid)[~addr!base := 0];
modifies #valid;



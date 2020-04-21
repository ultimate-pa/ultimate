// Version of LazycseqOctaveOfEaster.i where we replaced all
// bitwise OR operators by logics OR operators ("|" vs. "||")

# 1 "concurrency_2020/pthread/_cs_lazy01.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "concurrency_2020/pthread/_cs_lazy01.c"
# 72 "concurrency_2020/pthread/_cs_lazy01.c"
                         unsigned int __cs_active_thread[3 + 1] = {1};

                         unsigned int __cs_pc[3 + 1];

                         unsigned int __cs_pc_cs[3 + 1];

                         unsigned int __cs_thread_index;

                         unsigned int __cs_last_thread;

                         unsigned int __cs_thread_lines[] = {6, 3, 3, 3};

                         void __cs_init_scalar(void *__cs_var, unsigned int __cs_size)
                         {

                                   if (__cs_size == (sizeof(int)))

                                   * ((int *) __cs_var) = (__VERIFIER_nondet_int());
                                   else

                                             {

                                             __cs_var = (malloc(__cs_size));
                                   }

                         }


                         void __CSEQ_message(char *__cs_message)
                         {
                                   ;
                         }


                         typedef int cspthread_t;

                         void *__cs_threadargs[3 + 1];

                         typedef int cspthread_key_t;

                         cspthread_key_t __cs_keys[1][3 + 2];

                         void (*__cs_key_destructor[1])(void *);

                         int pthread_create_2(cspthread_t *__cs_new_thread_id, void *__cs_attr, void *(*__cs_func)(void *), void *__cs_arg, int __cs_threadID)
                         {

                                   if (__cs_threadID > 3)
                                             return (0);


                                   * __cs_new_thread_id = (__cs_threadID);

                                   __cs_active_thread[__cs_threadID] = (1);

                                   __cs_threadargs[__cs_threadID] = (__cs_arg);

                                   __CSEQ_message("thread spawned");

                                   return (0);
                         }


                         int pthread_join(cspthread_t __cs_id, void **__cs_value_ptr)
                         {

                                   __VERIFIER_assume(__cs_pc[__cs_id] == __cs_thread_lines[__cs_id]);

                                   return (0);
                         }


                         void pthread_exit(void *__cs_value_ptr)
                         {

                                   if ((__cs_key_destructor[0] != 0) && (__cs_keys[0][__cs_thread_index + 1] != 0))
                                   {

                                             __cs_key_destructor[0]((void *) __cs_keys[0][__cs_thread_index + 1]);
                                   }

                         }


                         int pthread_self(void)
                         {
                                   return (__cs_thread_index + 1);
                         }


                         typedef int cspthread_mutex_t;

                         typedef int cspthread_mutexattr_t;

                         int pthread_mutex_init(cspthread_mutex_t *__cs_m, cspthread_mutexattr_t *__cs_val)
                         {

                                   * __cs_m = (- 1);

                                   return (0);
                         }


                         int pthread_mutex_destroy(cspthread_mutex_t *__cs_mutex_to_destroy)
                         {

                                   * __cs_mutex_to_destroy = (- 2);

                                   __CSEQ_message("lock destroyed");

                                   return (0);
                         }


                         int pthread_mutex_lock(cspthread_mutex_t *__cs_mutex_to_lock)
                         {

                                   __VERIFIER_assume(((* __cs_mutex_to_lock) == (- 1)) || ((* __cs_mutex_to_lock) == 0));

                                   * __cs_mutex_to_lock = (__cs_thread_index + 1);

                                   __CSEQ_message("lock acquired");

                                   return (0);
                         }


                         int pthread_mutex_unlock(cspthread_mutex_t *__cs_mutex_to_unlock)
                         {

                                   __VERIFIER_assume((* __cs_mutex_to_unlock) == (__cs_thread_index + 1));

                                   * __cs_mutex_to_unlock = (- 1);

                                   __CSEQ_message("lock released");

                                   return (0);
                         }


                         typedef int cspthread_cond_t;

                         typedef int cspthread_condattr_t;

                         int pthread_cond_init(cspthread_cond_t *__cs_cond_to_init, cspthread_condattr_t *__cs_attr)
                         {

                                   * __cs_cond_to_init = (- 1);

                                   return (0);
                         }


                         int pthread_cond_destroy(cspthread_cond_t *__cs_cond_to_destroy)
                         {

                                   * __cs_cond_to_destroy = (- 2);

                                   return (0);
                         }


                         int pthread_cond_wait_1(cspthread_cond_t *__cs_cond_to_wait_for, cspthread_mutex_t *__cs_m)
                         {

                                   pthread_mutex_unlock(__cs_m);

                                   return (0);
                         }


                         int pthread_cond_wait_2(cspthread_cond_t *__cs_cond_to_wait_for, cspthread_mutex_t *__cs_m)
                         {

                                   _Bool b;

                                   if (b)
                                             __VERIFIER_assume((* __cs_cond_to_wait_for) == 1);


                                   pthread_mutex_lock(__cs_m);

                                   return (0);
                         }


                         int pthread_cond_signal(cspthread_cond_t *__cs_cond_to_signal)
                         {

                                   * __cs_cond_to_signal = (1);

                                   __CSEQ_message("conditional variable signal");

                                   return (0);
                         }


                         int pthread_cond_broadcast(cspthread_cond_t *__cs_cond_to_broadcast)
                         {

                                   * __cs_cond_to_broadcast = (1);

                                   __CSEQ_message("conditional variable broadcast");

                                   return (0);
                         }


                         typedef struct cspthread_barrier_t
                         {

                                   unsigned int init;

                                   unsigned int current;
                         } cspthread_barrier_t;

                         typedef int cspthread_barrierattr_t;

                         int pthread_barrier_init(cspthread_barrier_t *__cs_barrier_to_init, cspthread_barrierattr_t *__cs_attr, unsigned int count)
                         {

                                   __cs_barrier_to_init->current = (count);

                                   __cs_barrier_to_init->init = (count);

                                   return (0);
                         }


                         int pthread_barrier_destroy(cspthread_barrier_t *__cs_barrier_to_destroy)
                         {

                                   __cs_barrier_to_destroy->init = (- 1);

                                   __cs_barrier_to_destroy->current = (- 1);

                                   return (0);
                         }


                         int pthread_barrier_wait_1(cspthread_barrier_t *__cs_barrier_to_wait)
                         {

                                   __cs_barrier_to_wait->current--;

                                   return (0);
                         }


                         int pthread_barrier_wait_2(cspthread_barrier_t *__cs_barrier_to_wait)
                         {

                                   _Bool b;

                                   if (b)
                                             __VERIFIER_assume(__cs_barrier_to_wait->current == 0);


                                   __cs_barrier_to_wait->current = (__cs_barrier_to_wait->init);

                                   return (0);
                         }


                         int pthread_key_create(cspthread_key_t *key, void (*destructor)(void *))
                         {

                                   static int currentkey = (0);

                                   __cs_key_destructor[0] = (destructor);

                                   * key = (currentkey++);

                                   return (0);
                         }


                         int pthread_setspecific(cspthread_key_t key, void *value)
                         {

                                   __cs_keys[key][__cs_thread_index + 1] = ((cspthread_key_t) value);

                                   return (0);
                         }


                         void *pthread_getspecific(cspthread_key_t key)
                         {

                                   return ((void *) __cs_keys[key][__cs_thread_index + 1]);
                         }


                         void __CSEQ_noop(void)
                         {
                         }


                         void __VERIFIER_error();

                         typedef unsigned char __u_char;

                         typedef unsigned short int __u_short;

                         typedef unsigned int __u_int;

                         typedef unsigned long int __u_long;

                         typedef signed char __int8_t;

                         typedef unsigned char __uint8_t;

                         typedef signed short int __int16_t;

                         typedef unsigned short int __uint16_t;

                         typedef signed int __int32_t;

                         typedef unsigned int __uint32_t;

                         typedef signed long long int __int64_t;

                         typedef unsigned long long int __uint64_t;

                         typedef long long int __quad_t;

                         typedef unsigned long long int __u_quad_t;

                         typedef long long int __intmax_t;

                         typedef unsigned long long int __uintmax_t;

                         typedef __u_quad_t __dev_t;

                         typedef unsigned int __uid_t;

                         typedef unsigned int __gid_t;

                         typedef unsigned long int __ino_t;

                         typedef __u_quad_t __ino64_t;

                         typedef unsigned int __mode_t;

                         typedef unsigned int __nlink_t;

                         typedef long int __off_t;

                         typedef __quad_t __off64_t;

                         typedef int __pid_t;

                         typedef struct anonstruct_0
                         {

                                   int __val[2];
                         } __fsid_t;

                         typedef long int __clock_t;

                         typedef unsigned long int __rlim_t;

                         typedef __u_quad_t __rlim64_t;

                         typedef unsigned int __id_t;

                         typedef long int __time_t;

                         typedef unsigned int __useconds_t;

                         typedef long int __suseconds_t;

                         typedef int __daddr_t;

                         typedef int __key_t;

                         typedef int __clockid_t;

                         typedef void *__timer_t;

                         typedef long int __blksize_t;

                         typedef long int __blkcnt_t;

                         typedef __quad_t __blkcnt64_t;

                         typedef unsigned long int __fsblkcnt_t;

                         typedef __u_quad_t __fsblkcnt64_t;

                         typedef unsigned long int __fsfilcnt_t;

                         typedef __u_quad_t __fsfilcnt64_t;

                         typedef int __fsword_t;

                         typedef int __ssize_t;

                         typedef long int __syscall_slong_t;

                         typedef unsigned long int __syscall_ulong_t;

                         typedef __off64_t __loff_t;

                         typedef char *__caddr_t;

                         typedef int __intptr_t;

                         typedef unsigned int __socklen_t;

                         typedef int __sig_atomic_t;

                         typedef unsigned int size_t;

                         typedef __time_t time_t;

                         struct timespec
                         {

                                   __time_t tv_sec;

                                   __syscall_slong_t tv_nsec;
                         };

                         typedef __pid_t pid_t;

                         struct sched_param
                         {

                                   int sched_priority;
                         };

                         typedef unsigned long int __cpu_mask;

                         typedef struct anonstruct_1
                         {

                                   __cpu_mask __bits[1024 / (8 * (sizeof(__cpu_mask)))];
                         } cpu_set_t;

                         int __sched_cpucount(size_t __setsize, cpu_set_t *__setp);

                         cpu_set_t *__sched_cpualloc(size_t __count);

                         void __sched_cpufree(cpu_set_t *__set);

                         int sched_setparam(__pid_t __pid, struct sched_param *__param);

                         int sched_getparam(__pid_t __pid, struct sched_param *__param);

                         int sched_setscheduler(__pid_t __pid, int __policy,
                         struct sched_param *__param);

                         int sched_getscheduler(__pid_t __pid);

                         int sched_yield(void);

                         int sched_get_priority_max(int __algorithm);

                         int sched_get_priority_min(int __algorithm);

                         int sched_rr_get_interval(__pid_t __pid, struct timespec *__t);

                         typedef __clock_t clock_t;

                         struct tm
                         {

                                   int tm_sec;

                                   int tm_min;

                                   int tm_hour;

                                   int tm_mday;

                                   int tm_mon;

                                   int tm_year;

                                   int tm_wday;

                                   int tm_yday;

                                   int tm_isdst;

                                   long int tm_gmtoff;

                                   char *tm_zone;
                         };

                         typedef __clockid_t clockid_t;

                         typedef __timer_t timer_t;

                         struct itimerspec
                         {

                                   struct timespec it_interval;

                                   struct timespec it_value;
                         };

                         struct sigevent{ char dummy; };

                         struct __locale_struct
                         {

                                   struct __locale_data *__locales[13];

                                   unsigned short int *__ctype_b;

                                   int *__ctype_tolower;

                                   int *__ctype_toupper;

                                   char *__names[13];
                         };

                         typedef struct __locale_struct *__locale_t;

                         typedef __locale_t locale_t;

                         clock_t clock(void);

                         time_t time(time_t *__timer);

                         double difftime(time_t __time1, time_t __time0);

                         time_t mktime(struct tm *__tp);

                         size_t strftime(char *__s, size_t __maxsize,
                         char *__format,
                         struct tm *__tp);

                         size_t strftime_l(char *__s, size_t __maxsize,
                         char *__format,
                         struct tm *__tp,
                         locale_t __loc);

                         struct tm *gmtime(time_t *__timer);

                         struct tm *localtime(time_t *__timer);

                         struct tm *gmtime_r(time_t *__timer,
                         struct tm *__tp);

                         struct tm *localtime_r(time_t *__timer,
                         struct tm *__tp);

                         char *asctime(struct tm *__tp);

                         char *ctime(time_t *__timer);

                         char *asctime_r(struct tm *__tp,
                         char *__buf);

                         char *ctime_r(time_t *__timer,
                         char *__buf);

                         char *__tzname[2];

                         int __daylight;

                         long int __timezone;

                         char *tzname[2];

                         void tzset(void);

                         int daylight;

                         long int timezone;

                         int stime(time_t *__when);

                         time_t timegm(struct tm *__tp);

                         time_t timelocal(struct tm *__tp);

                         int dysize(int __year);

                         int nanosleep(struct timespec *__requested_time,
                         struct timespec *__remaining);

                         int clock_getres(clockid_t __clock_id, struct timespec *__res);

                         int clock_gettime(clockid_t __clock_id, struct timespec *__tp);

                         int clock_settime(clockid_t __clock_id, struct timespec *__tp);

                         int clock_nanosleep(clockid_t __clock_id, int __flags,
                         struct timespec *__req,
                         struct timespec *__rem);

                         int clock_getcpuclockid(pid_t __pid, clockid_t *__clock_id);

                         int timer_create(clockid_t __clock_id,
                         struct sigevent *__evp,
                         timer_t *__timerid);

                         int timer_delete(timer_t __timerid);

                         int timer_settime(timer_t __timerid, int __flags,
                         struct itimerspec *__value,
                         struct itimerspec *__ovalue);

                         int timer_gettime(timer_t __timerid, struct itimerspec *__value);

                         int timer_getoverrun(timer_t __timerid);

                         int timespec_get(struct timespec *__ts, int __base);

                         struct __pthread_rwlock_arch_t
                         {

                                   unsigned int __readers;

                                   unsigned int __writers;

                                   unsigned int __wrphase_futex;

                                   unsigned int __writers_futex;

                                   unsigned int __pad3;

                                   unsigned int __pad4;

                                   unsigned char __flags;

                                   unsigned char __shared;

                                   signed char __rwelision;

                                   unsigned char __pad2;

                                   int __cur_writer;
                         };

                         typedef struct __pthread_internal_slist
                         {

                                   struct __pthread_internal_slist *__next;
                         } __pthread_slist_t;

                         struct __pthread_mutex_s
                         {

                                   int __lock;

                                   unsigned int __count;

                                   int __owner;

                                   int __kind;

                                   unsigned int __nusers;

                                   struct anonstruct_2
                                   {


                                             struct anonstruct_3
                                             {

                                                       short __espins;

                                                       short __eelision;
                                             } __elision_data;

                                             __pthread_slist_t __list;
                                   };
                         };

                         struct __pthread_cond_s
                         {

                                   struct anonstruct_4
                                   {

                                             unsigned long long int __wseq;


                                             struct anonstruct_5
                                             {

                                                       unsigned int __low;

                                                       unsigned int __high;
                                             } __wseq32;
                                   };

                                   struct anonstruct_6
                                   {

                                             unsigned long long int __g1_start;


                                             struct anonstruct_7
                                             {

                                                       unsigned int __low;

                                                       unsigned int __high;
                                             } __g1_start32;
                                   };

                                   unsigned int __g_refs[2];

                                   unsigned int __g_size[2];

                                   unsigned int __g1_orig_size;

                                   unsigned int __wrefs;

                                   unsigned int __g_signals[2];
                         };

                         typedef unsigned long int pthread_t;

                         typedef struct anonstruct_8
                         {

                                   char __size[4];

                                   int __align;
                         } pthread_mutexattr_t;

                         typedef struct anonstruct_9
                         {

                                   char __size[4];

                                   int __align;
                         } pthread_condattr_t;

                         typedef unsigned int pthread_key_t;

                         typedef int pthread_once_t;

                         struct pthread_attr_t
                         {

                                   char __size[36];

                                   long int __align;
                         };

                         typedef struct pthread_attr_t pthread_attr_t;

                         typedef struct anonstruct_10
                         {

                                   struct __pthread_mutex_s __data;

                                   char __size[24];

                                   long int __align;
                         } pthread_mutex_t;

                         typedef struct anonstruct_11
                         {

                                   struct __pthread_cond_s __data;

                                   char __size[48];

                                   long long int __align;
                         } pthread_cond_t;

                         typedef struct anonstruct_12
                         {

                                   struct __pthread_rwlock_arch_t __data;

                                   char __size[32];

                                   long int __align;
                         } pthread_rwlock_t;

                         typedef struct anonstruct_13
                         {

                                   char __size[8];

                                   long int __align;
                         } pthread_rwlockattr_t;

                         typedef volatile int pthread_spinlock_t;

                         typedef struct anonstruct_14
                         {

                                   char __size[20];

                                   long int __align;
                         } pthread_barrier_t;

                         typedef struct anonstruct_15
                         {

                                   char __size[4];

                                   int __align;
                         } pthread_barrierattr_t;

                         typedef int __jmp_buf[6];

                         enum {PTHREAD_CREATE_JOINABLE, PTHREAD_CREATE_DETACHED};

                         enum {PTHREAD_MUTEX_TIMED_NP, PTHREAD_MUTEX_RECURSIVE_NP, PTHREAD_MUTEX_ERRORCHECK_NP, PTHREAD_MUTEX_ADAPTIVE_NP, PTHREAD_MUTEX_NORMAL =
                         PTHREAD_MUTEX_TIMED_NP, PTHREAD_MUTEX_RECURSIVE =
                         PTHREAD_MUTEX_RECURSIVE_NP, PTHREAD_MUTEX_ERRORCHECK =
                         PTHREAD_MUTEX_ERRORCHECK_NP, PTHREAD_MUTEX_DEFAULT =
                         PTHREAD_MUTEX_NORMAL};

                         enum {PTHREAD_MUTEX_STALLED, PTHREAD_MUTEX_STALLED_NP =
                         PTHREAD_MUTEX_STALLED, PTHREAD_MUTEX_ROBUST, PTHREAD_MUTEX_ROBUST_NP =
                         PTHREAD_MUTEX_ROBUST};

                         enum {PTHREAD_PRIO_NONE, PTHREAD_PRIO_INHERIT, PTHREAD_PRIO_PROTECT};

                         enum {PTHREAD_RWLOCK_PREFER_READER_NP, PTHREAD_RWLOCK_PREFER_WRITER_NP, PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP, PTHREAD_RWLOCK_DEFAULT_NP =
                         PTHREAD_RWLOCK_PREFER_READER_NP};

                         enum {PTHREAD_INHERIT_SCHED, PTHREAD_EXPLICIT_SCHED};

                         enum {PTHREAD_SCOPE_SYSTEM, PTHREAD_SCOPE_PROCESS};

                         enum {PTHREAD_PROCESS_PRIVATE, PTHREAD_PROCESS_SHARED};

                         struct _pthread_cleanup_buffer
                         {

                                   void (*__routine)(void *);

                                   void *__arg;

                                   int __canceltype;

                                   struct _pthread_cleanup_buffer *__prev;
                         };

                         enum {PTHREAD_CANCEL_ENABLE, PTHREAD_CANCEL_DISABLE};

                         enum {PTHREAD_CANCEL_DEFERRED, PTHREAD_CANCEL_ASYNCHRONOUS};

                         int pthread_create(cspthread_t *__newthread,
                         pthread_attr_t *__attr,
                         void *(*__start_routine)(void *),
                         void *__arg);

                         void pthread_exit(void *__retval);

                         int pthread_join(cspthread_t __th, void **__thread_return);

                         int pthread_detach(cspthread_t __th);

                         cspthread_t pthread_self(void);

                         int pthread_equal(cspthread_t __thread1, cspthread_t __thread2);

                         int pthread_attr_init(pthread_attr_t *__attr);

                         int pthread_attr_destroy(pthread_attr_t *__attr);

                         int pthread_attr_getdetachstate(pthread_attr_t *__attr,
                         int *__detachstate);

                         int pthread_attr_setdetachstate(pthread_attr_t *__attr,
                         int __detachstate);

                         int pthread_attr_getguardsize(pthread_attr_t *__attr,
                         size_t *__guardsize);

                         int pthread_attr_setguardsize(pthread_attr_t *__attr,
                         size_t __guardsize);

                         int pthread_attr_getschedparam(pthread_attr_t *__attr,
                         struct sched_param *__param);

                         int pthread_attr_setschedparam(pthread_attr_t *__attr,
                         struct sched_param *__param);

                         int pthread_attr_getschedpolicy(pthread_attr_t *__attr,
                         int *__policy);

                         int pthread_attr_setschedpolicy(pthread_attr_t *__attr, int __policy);

                         int pthread_attr_getinheritsched(pthread_attr_t *__attr,
                         int *__inherit);

                         int pthread_attr_setinheritsched(pthread_attr_t *__attr,
                         int __inherit);

                         int pthread_attr_getscope(pthread_attr_t *__attr,
                         int *__scope);

                         int pthread_attr_setscope(pthread_attr_t *__attr, int __scope);

                         int pthread_attr_getstackaddr(pthread_attr_t *__attr,
                         void **__stackaddr);

                         int pthread_attr_setstackaddr(pthread_attr_t *__attr,
                         void *__stackaddr);

                         int pthread_attr_getstacksize(pthread_attr_t *__attr,
                         size_t *__stacksize);

                         int pthread_attr_setstacksize(pthread_attr_t *__attr,
                         size_t __stacksize);

                         int pthread_attr_getstack(pthread_attr_t *__attr,
                         void **__stackaddr,
                         size_t *__stacksize);

                         int pthread_attr_setstack(pthread_attr_t *__attr, void *__stackaddr,
                         size_t __stacksize);

                         int pthread_setschedparam(cspthread_t __target_thread, int __policy,
                         struct sched_param *__param);

                         int pthread_getschedparam(cspthread_t __target_thread,
                         int *__policy,
                         struct sched_param *__param);

                         int pthread_setschedprio(cspthread_t __target_thread, int __prio);

                         int pthread_once(pthread_once_t *__once_control,
                         void (*__init_routine)(void));

                         int pthread_setcancelstate(int __state, int *__oldstate);

                         int pthread_setcanceltype(int __type, int *__oldtype);

                         int pthread_cancel(cspthread_t __th);

                         void pthread_testcancel(void);

                         typedef struct anonstruct_16
                         {


                                   struct anonstruct_17
                                   {

                                             __jmp_buf __cancel_jmp_buf;

                                             int __mask_was_saved;
                                   } __cancel_jmp_buf[1];

                                   void *__pad[4];
                         } __pthread_unwind_buf_t;

                         struct __pthread_cleanup_frame
                         {

                                   void (*__cancel_routine)(void *);

                                   void *__cancel_arg;

                                   int __do_it;

                                   int __cancel_type;
                         };

                         void __pthread_register_cancel(__pthread_unwind_buf_t *__buf);

                         void __pthread_unregister_cancel(__pthread_unwind_buf_t *__buf);

                         void __pthread_unwind_next(__pthread_unwind_buf_t *__buf);

                         struct __jmp_buf_tag{ char dummy; };

                         int __sigsetjmp(struct __jmp_buf_tag *__env, int __savemask);

                         int pthread_mutex_init(cspthread_mutex_t *__mutex,
                         cspthread_mutexattr_t *__mutexattr);

                         int pthread_mutex_destroy(cspthread_mutex_t *__mutex);

                         int pthread_mutex_trylock(cspthread_mutex_t *__mutex);

                         int pthread_mutex_lock(cspthread_mutex_t *__mutex);

                         int pthread_mutex_timedlock(cspthread_mutex_t *__mutex,
                         struct timespec *__abstime);

                         int pthread_mutex_unlock(cspthread_mutex_t *__mutex);

                         int pthread_mutex_getprioceiling(cspthread_mutex_t *__mutex,
                         int *__prioceiling);

                         int pthread_mutex_setprioceiling(cspthread_mutex_t *__mutex,
                         int __prioceiling,
                         int *__old_ceiling);

                         int pthread_mutex_consistent(cspthread_mutex_t *__mutex);

                         int pthread_mutexattr_init(cspthread_mutexattr_t *__attr);

                         int pthread_mutexattr_destroy(cspthread_mutexattr_t *__attr);

                         int pthread_mutexattr_getpshared(cspthread_mutexattr_t *__attr,
                         int *__pshared);

                         int pthread_mutexattr_setpshared(cspthread_mutexattr_t *__attr,
                         int __pshared);

                         int pthread_mutexattr_gettype(cspthread_mutexattr_t *__attr,
                         int *__kind);

                         int pthread_mutexattr_settype(cspthread_mutexattr_t *__attr, int __kind);

                         int pthread_mutexattr_getprotocol(cspthread_mutexattr_t *__attr,
                         int *__protocol);

                         int pthread_mutexattr_setprotocol(cspthread_mutexattr_t *__attr,
                         int __protocol);

                         int pthread_mutexattr_getprioceiling(cspthread_mutexattr_t *__attr,
                         int *__prioceiling);

                         int pthread_mutexattr_setprioceiling(cspthread_mutexattr_t *__attr,
                         int __prioceiling);

                         int pthread_mutexattr_getrobust(cspthread_mutexattr_t *__attr,
                         int *__robustness);

                         int pthread_mutexattr_setrobust(cspthread_mutexattr_t *__attr,
                         int __robustness);

                         int pthread_rwlock_init(pthread_rwlock_t *__rwlock,
                         pthread_rwlockattr_t *__attr);

                         int pthread_rwlock_destroy(pthread_rwlock_t *__rwlock);

                         int pthread_rwlock_rdlock(pthread_rwlock_t *__rwlock);

                         int pthread_rwlock_tryrdlock(pthread_rwlock_t *__rwlock);

                         int pthread_rwlock_timedrdlock(pthread_rwlock_t *__rwlock,
                         struct timespec *__abstime);

                         int pthread_rwlock_wrlock(pthread_rwlock_t *__rwlock);

                         int pthread_rwlock_trywrlock(pthread_rwlock_t *__rwlock);

                         int pthread_rwlock_timedwrlock(pthread_rwlock_t *__rwlock,
                         struct timespec *__abstime);

                         int pthread_rwlock_unlock(pthread_rwlock_t *__rwlock);

                         int pthread_rwlockattr_init(pthread_rwlockattr_t *__attr);

                         int pthread_rwlockattr_destroy(pthread_rwlockattr_t *__attr);

                         int pthread_rwlockattr_getpshared(pthread_rwlockattr_t *__attr,
                         int *__pshared);

                         int pthread_rwlockattr_setpshared(pthread_rwlockattr_t *__attr,
                         int __pshared);

                         int pthread_rwlockattr_getkind_np(pthread_rwlockattr_t *__attr,
                         int *__pref);

                         int pthread_rwlockattr_setkind_np(pthread_rwlockattr_t *__attr,
                         int __pref);

                         int pthread_cond_init(cspthread_cond_t *__cond,
                         cspthread_condattr_t *__cond_attr);

                         int pthread_cond_destroy(cspthread_cond_t *__cond);

                         int pthread_cond_signal(cspthread_cond_t *__cond);

                         int pthread_cond_broadcast(cspthread_cond_t *__cond);

                         int pthread_cond_wait(cspthread_cond_t *__cond,
                         cspthread_mutex_t *__mutex);

                         int pthread_cond_timedwait(cspthread_cond_t *__cond,
                         cspthread_mutex_t *__mutex,
                         struct timespec *__abstime);

                         int pthread_condattr_init(cspthread_condattr_t *__attr);

                         int pthread_condattr_destroy(cspthread_condattr_t *__attr);

                         int pthread_condattr_getpshared(cspthread_condattr_t *__attr,
                         int *__pshared);

                         int pthread_condattr_setpshared(cspthread_condattr_t *__attr,
                         int __pshared);

                         int pthread_condattr_getclock(cspthread_condattr_t *__attr,
                         __clockid_t *__clock_id);

                         int pthread_condattr_setclock(cspthread_condattr_t *__attr,
                         __clockid_t __clock_id);

                         int pthread_spin_init(pthread_spinlock_t *__lock, int __pshared);

                         int pthread_spin_destroy(pthread_spinlock_t *__lock);

                         int pthread_spin_lock(pthread_spinlock_t *__lock);

                         int pthread_spin_trylock(pthread_spinlock_t *__lock);

                         int pthread_spin_unlock(pthread_spinlock_t *__lock);

                         int pthread_barrier_init(cspthread_barrier_t *__barrier,
                         cspthread_barrierattr_t *__attr,
                         unsigned int __count);

                         int pthread_barrier_destroy(cspthread_barrier_t *__barrier);

                         int pthread_barrier_wait(cspthread_barrier_t *__barrier);

                         int pthread_barrierattr_init(cspthread_barrierattr_t *__attr);

                         int pthread_barrierattr_destroy(cspthread_barrierattr_t *__attr);

                         int pthread_barrierattr_getpshared(cspthread_barrierattr_t *__attr,
                         int *__pshared);

                         int pthread_barrierattr_setpshared(cspthread_barrierattr_t *__attr,
                         int __pshared);

                         int pthread_key_create(cspthread_key_t *__key,
                         void (*__destr_function)(void *));

                         int pthread_key_delete(cspthread_key_t __key);

                         void *pthread_getspecific(cspthread_key_t __key);

                         int pthread_setspecific(cspthread_key_t __key,
                         void *__pointer);

                         int pthread_getcpuclockid(cspthread_t __thread_id,
                         __clockid_t *__clock_id);

                         int pthread_atfork(void (*__prepare)(void),
                         void (*__parent)(void),
                         void (*__child)(void));

                         void __assert_fail(char *__assertion, char *__file,
                         unsigned int __line, char *__function);

                         void __assert_perror_fail(int __errnum, char *__file,
                         unsigned int __line, char *__function);

                         void __assert(char *__assertion, char *__file, int __line);

                         cspthread_mutex_t mutex;

                         int data = (0);

                         void *thread1_0(void *__cs_param_thread1_arg)

                         {

if ((__cs_pc[1] > 0) || (0 >= __cs_pc_cs[1])) goto tthread1_0_1;

                                   pthread_mutex_lock(& mutex);

tthread1_0_1: if ((__cs_pc[1] > 1) || (1 >= __cs_pc_cs[1])) goto tthread1_0_2;

                                   data++;

tthread1_0_2: if ((__cs_pc[1] > 2) || (2 >= __cs_pc_cs[1])) goto tthread1_0_3;

                                   pthread_mutex_unlock(& mutex);

                                   goto __exit_thread1;
                                   ;

                                   __exit_thread1:
                                   __VERIFIER_assume(__cs_pc_cs[1] >= 3);


                                   ;
                                   ;

tthread1_0_3:

                                   pthread_exit(0);
                         }


                         void *thread2_0(void *__cs_param_thread2_arg)

                         {

if ((__cs_pc[2] > 0) || (0 >= __cs_pc_cs[2])) goto tthread2_0_1;

                                   pthread_mutex_lock(& mutex);

tthread2_0_1: if ((__cs_pc[2] > 1) || (1 >= __cs_pc_cs[2])) goto tthread2_0_2;

                                   data += (2);

tthread2_0_2: if ((__cs_pc[2] > 2) || (2 >= __cs_pc_cs[2])) goto tthread2_0_3;

                                   pthread_mutex_unlock(& mutex);

                                   goto __exit_thread2;
                                   ;

                                   __exit_thread2:
                                   __VERIFIER_assume(__cs_pc_cs[2] >= 3);


                                   ;
                                   ;

tthread2_0_3:

                                   pthread_exit(0);
                         }


                         void *thread3_0(void *__cs_param_thread3_arg)

                         {

if ((__cs_pc[3] > 0) || (0 >= __cs_pc_cs[3])) goto tthread3_0_1;

                                   pthread_mutex_lock(& mutex);

                                   static _Bool __cs_local_thread3___cs_tmp_if_cond_0;

tthread3_0_1: if ((__cs_pc[3] > 1) || (1 >= __cs_pc_cs[3])) goto tthread3_0_2;

                                   __cs_local_thread3___cs_tmp_if_cond_0 = (data >= 3);

                                   if (__cs_local_thread3___cs_tmp_if_cond_0)

                                             {

                                             __VERIFIER_error();

                                             ;
                                             ;
                                   }


                                   ;

tthread3_0_2: if ((__cs_pc[3] > 2) || (2 >= __cs_pc_cs[3])) goto tthread3_0_3;

                                   pthread_mutex_unlock(& mutex);

                                   goto __exit_thread3;
                                   ;

                                   __exit_thread3:
                                   __VERIFIER_assume(__cs_pc_cs[3] >= 3);


                                   ;
                                   ;

tthread3_0_3:

                                   pthread_exit(0);
                         }


                         int main_thread(void)

                         {

if ((__cs_pc[0] > 0) || (0 >= __cs_pc_cs[0])) goto tmain_1;

                                   pthread_mutex_init(& mutex, 0);

                                   static cspthread_t __cs_local_main_t1;
                                   __cs_init_scalar(& __cs_local_main_t1, sizeof(cspthread_t));

                                   static cspthread_t __cs_local_main_t2;
                                   __cs_init_scalar(& __cs_local_main_t2, sizeof(cspthread_t));

                                   static cspthread_t __cs_local_main_t3;
                                   __cs_init_scalar(& __cs_local_main_t3, sizeof(cspthread_t));

                                   pthread_create_2(& __cs_local_main_t1, 0, thread1_0, 0, 1);

tmain_1: if ((__cs_pc[0] > 1) || (1 >= __cs_pc_cs[0])) goto tmain_2;

                                   pthread_create_2(& __cs_local_main_t2, 0, thread2_0, 0, 2);

tmain_2: if ((__cs_pc[0] > 2) || (2 >= __cs_pc_cs[0])) goto tmain_3;

                                   pthread_create_2(& __cs_local_main_t3, 0, thread3_0, 0, 3);

tmain_3: if ((__cs_pc[0] > 3) || (3 >= __cs_pc_cs[0])) goto tmain_4;

                                   pthread_join(__cs_local_main_t1, 0);

tmain_4: if ((__cs_pc[0] > 4) || (4 >= __cs_pc_cs[0])) goto tmain_5;

                                   pthread_join(__cs_local_main_t2, 0);

tmain_5: if ((__cs_pc[0] > 5) || (5 >= __cs_pc_cs[0])) goto tmain_6;

                                   pthread_join(__cs_local_main_t3, 0);

                                   goto __exit_main;
                                   ;

                                   __exit_main:
                                   __VERIFIER_assume(__cs_pc_cs[0] >= 6);


                                   ;
                                   ;

tmain_6:

                                   pthread_exit(0);
                         }


                         int main(void)
                         {





                                   __cs_thread_index = (0);

                                   unsigned int __cs_tmp_t0_r0;

                                   __cs_pc_cs[0] = (__cs_tmp_t0_r0);

                                   __VERIFIER_assume(__cs_pc_cs[0] > 0);

                                   __VERIFIER_assume(__cs_pc_cs[0] <= 6);

                                   main_thread();

                                   __cs_pc[0] = (__cs_pc_cs[0]);



                                   unsigned int __cs_tmp_t1_r0;

                                   if (__cs_active_thread[1])
                                   {

                                             __cs_thread_index = (1);

                                             __cs_pc_cs[1] = (__cs_tmp_t1_r0);

                                             __VERIFIER_assume(__cs_pc_cs[1] <= 3);

                                             thread1_0(__cs_threadargs[1]);

                                             __cs_pc[1] = (__cs_pc_cs[1]);
                                   }




                                   unsigned int __cs_tmp_t2_r0;

                                   if (__cs_active_thread[2])
                                   {

                                             __cs_thread_index = (2);

                                             __cs_pc_cs[2] = (__cs_tmp_t2_r0);

                                             __VERIFIER_assume(__cs_pc_cs[2] <= 3);

                                             thread2_0(__cs_threadargs[2]);

                                             __cs_pc[2] = (__cs_pc_cs[2]);
                                   }




                                   unsigned int __cs_tmp_t3_r0;

                                   if (__cs_active_thread[3])
                                   {

                                             __cs_thread_index = (3);

                                             __cs_pc_cs[3] = (__cs_tmp_t3_r0);

                                             __VERIFIER_assume(__cs_pc_cs[3] <= 3);

                                             thread3_0(__cs_threadargs[3]);

                                             __cs_pc[3] = (__cs_pc_cs[3]);
                                   }


                                   unsigned int __cs_tmp_t0_r1;

                                   if (__cs_active_thread[0])
                                   {

                                             __cs_thread_index = (0);

                                             __cs_pc_cs[0] = (__cs_tmp_t0_r1);

                                             __VERIFIER_assume(__cs_pc_cs[0] >= __cs_pc[0]);

                                             __VERIFIER_assume(__cs_pc_cs[0] <= 6);

                                             main_thread();
                                   }


                                   return (0);
                         }

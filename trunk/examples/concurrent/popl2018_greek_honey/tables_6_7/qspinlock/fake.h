/*
 * "Fake" declarations to scaffold a Linux-kernel SMP environment.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-2.0.html.
 *
 * Author: Michalis Kokologiannakis <mixaskok@gmail.com>
 */

#ifndef __FAKE_H
#define __FAKE_H

#include <assert.h>
#include <stdatomic.h>
#include "ordering.h"

/* Stub some compiler directives */
#ifndef __always_inline
#define __always_inline
#endif

#define __percpu
#define __pure

#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

#define prefetchw(x) do {} while (0)

#define EXPORT_SYMBOL(sym)

/* Various data types */
typedef _Bool bool;

enum {
	false	= 0,
	true	= 1
};

typedef int8_t s8;
typedef uint8_t u8;
typedef int16_t s16;
typedef uint16_t u16;
typedef int32_t s32;
typedef uint32_t u32;
typedef int64_t s64;
typedef uint64_t u64;

typedef int8_t __s8;
typedef uint8_t __u8;
typedef int16_t __s16;
typedef uint16_t __u16;
typedef int32_t __s32;
typedef uint32_t __u32;
typedef int64_t __s64;
typedef uint64_t __u64;

/* "Cheater" options based on specific Kconfig build */
#ifndef CONFIG_NR_CPUS
#define CONFIG_NR_CPUS (1U << 14) /* We want 1 pending bit only! */
#endif
#ifndef NR_CPUS
#define NR_CPUS 2
#endif

#ifndef __LITTLE_ENDIAN
#define __LITTLE_ENDIAN
#endif
#define CONFIG_DEBUG_SPINLOCK

/* BUG() statements and relatives */
#define BUG() assert(0)
#define BUG_ON(x) assert(!(x))
#define BUILD_BUG_ON(x) BUG_ON(x)


/* Some basic percpu stuff */
int __thread __running_cpu;
#define get_cpu()    ({ __running_cpu; })
#define set_cpu(cpu) ({ __running_cpu = cpu; })

#define smp_processor_id() get_cpu()

#define DEFINE_PER_CPU(type, name) type name[NR_CPUS];
#define DEFINE_PER_CPU_ALIGNED(type, name) DEFINE_PER_CPU(type, name)

#define per_cpu_ptr(ptr, cpu) (&(ptr)[cpu])
#define this_cpu_ptr(ptr)     per_cpu_ptr(ptr, get_cpu())

/* RC11 semantics for memory barriers */
#define barrier() atomic_signal_fence(mo_acq_rel)
#define smp_mb()  atomic_thread_fence(mo_seq_cst)

#define smp_rmb() atomic_thread_fence(mo_acq_rel)
#define smp_wmb() atomic_thread_fence(mo_acq_rel)

#define smp_read_barrier_depends()    do {} while (0)
#define smp_acquire__after_ctrl_dep() barrier() /* no load speculation */

#define smp_cond_load_acquire(ptr, cond_expr) ({		\
	typeof(ptr) __PTR = (ptr);				\
	typeof(*ptr) VAL;					\
	for (;;) {						\
		VAL = READ_ONCE(*__PTR);			\
		if (cond_expr)					\
			break;					\
		cpu_relax();					\
	}							\
	smp_acquire__after_ctrl_dep();				\
	VAL;							\
})

/* RC11 semantics for various atomic types and ops */
typedef struct {
	atomic_int counter;
} atomic_t;

#define ATOMIC_INIT(i) { ATOMIC_VAR_INIT(i) }

#define atomic_read(v)   atomic_load_explicit(&(v)->counter, mo_relaxed)
#define atomic_add(i, v) atomic_fetch_add_explicit(&(v)->counter, i, mo_relaxed)

#define READ_ONCE(x)     atomic_load_explicit(&x, mo_relaxed)
#define WRITE_ONCE(x, v) atomic_store_explicit(&x, v, mo_relaxed)

#define smp_store_release(p, v)			        \
	atomic_store_explicit(p, v, mo_release)
#define smp_load_acquire(p)			        \
	atomic_load_explicit(p, mo_acquire)

#define xchg(p, v)					\
	atomic_exchange_explicit(p, v, mo_acq_rel)

#define __cmpxchg(ptr, old, new, ord)		        \
({					                \
	__typeof__(old) __old = (old);			\
	atomic_compare_exchange_strong_explicit(ptr,	\
				&__old, new, ord, ord);	\
	__old;						\
})
#define cmpxchg_relaxed(...) __cmpxchg(__VA_ARGS__, mo_relaxed)
#define cmpxchg_acquire(...) __cmpxchg(__VA_ARGS__, mo_acquire)
#define cmpxchg_release(...) __cmpxchg(__VA_ARGS__, mo_release)
#define cmpxchg_acq_rel(...) __cmpxchg(__VA_ARGS__, mo_acq_rel)
#define cmpxchg(...) cmpxchg_acq_rel(__VA_ARGS__) /* should suffice... */

#define atomic_cmpxchg(v, o, n) (cmpxchg(&((v)->counter), (o), (n)))
#define atomic_cmpxchg_relaxed(v, o, n) \
	cmpxchg_relaxed(&((v)->counter), (o), (n))
#define atomic_cmpxchg_acquire(v, o, n) \
	cmpxchg_acquire(&((v)->counter), (o), (n))
#define atomic_cmpxchg_release(v, o, n) \
	cmpxchg_release(&((v)->counter), (o), (n))

#define __atomic_sub_return(val, ptr, ord)		\
({						        \
	__typeof__(val) __ret;				\
	__ret = atomic_fetch_sub_explicit(&(ptr)->counter, val, ord);	\
	__ret = __ret - val;				\
	__ret;						\
})
#define atomic_sub_return_relaxed(...)			\
	__atomic_sub_return(__VA_ARGS__, mo_relaxed)
#define atomic_sub_return_acquire(...)			\
	__atomic_sub_return(__VA_ARGS__, mo_acquire)
#define atomic_sub_return_release(...)			\
	__atomic_sub_return(__VA_ARGS__, mo_release)
#define atomic_sub_return_acq_rel(...)			\
	__atomic_sub_return(__VA_ARGS__, mo_acq_rel)
#define atomic_sub_return(...)				\
	atomic_sub_return_acq_rel(__VA_ARGS__) /* should suffice... */


/* Normally a REP NOP, but do not bother with cpu stuff */
#define cpu_relax() do {} while (0)

#endif /* __FAKE_H */

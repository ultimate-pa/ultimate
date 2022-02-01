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

#include <stdatomic.h>
#include "ordering.h"

/* Branch prediction hints */
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)

/* Normally a REP NOP, but do not bother with cpu stuff */
#define cpu_relax() do {} while (0)

/* RC11 semantics for some atomic ops */
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
#define cmpxchg(...) cmpxchg_relaxed(__VA_ARGS__)

#endif /* __FAKE_H */

/*
 * Wrappers for C11 memory orderings.
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

#ifndef __ORDERING_H
#define __ORDERING_H

#ifdef MAKE_ACCESSES_SC
# define mo_relaxed memory_order_seq_cst
# define mo_acquire memory_order_seq_cst
# define mo_release memory_order_seq_cst
# define mo_acq_rel memory_order_seq_cst
# define mo_seq_cst memory_order_seq_cst
#else
# define mo_relaxed memory_order_relaxed
# define mo_acquire memory_order_acquire
# define mo_release memory_order_release
# define mo_acq_rel memory_order_acq_rel
# define mo_seq_cst memory_order_seq_cst
#endif

#endif /* __ORDERING_H */

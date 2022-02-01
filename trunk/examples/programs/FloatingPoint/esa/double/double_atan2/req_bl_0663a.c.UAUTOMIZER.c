
/* Copyright (C) 1991-2016 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */




/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */

/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 8.0.0.  Version 8.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2014, plus Amendment 1 (published
   2015-05-15).  */


/* We do not support C11 <threads.h>.  */

/*
 * Copyright (c) 1990 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by the University of California, Berkeley.  The name of the
 * University may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 *	@(#)stdio.h	5.3 (Berkeley) 3/15/86
 */

/*
 * NB: to fit things in six character monocase externals, the
 * stdio code uses the prefix `__s' for stdio objects, typically
 * followed by a three-character attempt at a mnemonic.
 */




/* Provide support for both ANSI and non-ANSI environments.  */

/* Some ANSI environments are "broken" in the sense that __STDC__ cannot be
   relied upon to have it's intended meaning.  Therefore we must use our own
   concoction: _HAVE_STDC.  Always use _HAVE_STDC instead of __STDC__ in newlib
   sources!

   To get a strict ANSI C environment, define macro __STRICT_ANSI__.  This will
   "comment out" the non-ANSI parts of the ANSI header files (non-ANSI header
   files aren't affected).  */




/* dummy file for external tools to use.  Real file is created by
   newlib configuration. */



/*
 *  Written by Joel Sherrill <joel@OARcorp.com>.
 *
 *  COPYRIGHT (c) 1989-2014.
 *
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Permission to use, copy, modify, and distribute this software for any
 *  purpose without fee is hereby granted, provided that this entire notice
 *  is included in all copies of any software which is or includes a copy
 *  or modification of this software.
 *
 *  THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 *  WARRANTY.  IN PARTICULAR,  THE AUTHOR MAKES NO REPRESENTATION
 *  OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY OF THIS
 *  SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 *
 *  $Id$
 */
/* dummy file for external tools to use.  Real file is created by
   newlib configuration. */

/* Macro to test version of GCC.  Returns 0 for non-GCC or too old GCC. */
/* Version with trailing underscores for BSD compatibility. */



/*
 * Feature test macros control which symbols are exposed by the system
 * headers.  Any of these must be defined before including any headers.
 *
 * __STRICT_ANSI__ (defined by gcc -ansi, -std=c90, -std=c99, or -std=c11)
 *	ISO C
 *
 * _POSIX_SOURCE (deprecated by _POSIX_C_SOURCE=1)
 * _POSIX_C_SOURCE >= 1
 * 	POSIX.1-1990
 *
 * _POSIX_C_SOURCE >= 2
 * 	POSIX.2-1992
 *
 * _POSIX_C_SOURCE >= 199309L
 * 	POSIX.1b-1993 Real-time extensions
 *
 * _POSIX_C_SOURCE >= 199506L
 * 	POSIX.1c-1995 Threads extensions
 *
 * _POSIX_C_SOURCE >= 200112L
 * 	POSIX.1-2001 and C99
 *
 * _POSIX_C_SOURCE >= 200809L
 * 	POSIX.1-2008
 *
 * _XOPEN_SOURCE
 *	POSIX.1-1990 and XPG4
 *
 * _XOPEN_SOURCE_EXTENDED
 *	SUSv1 (POSIX.2-1992 plus XPG4v2)
 *
 * _XOPEN_SOURCE >= 500
 *	SUSv2 (POSIX.1c-1995 plus XSI)
 *
 * _XOPEN_SOURCE >= 600
 *	SUSv3 (POSIX.1-2001 plus XSI) and C99
 *
 * _XOPEN_SOURCE >= 700
 *	SUSv4 (POSIX.1-2008 plus XSI)
 *
 * _ISOC99_SOURCE or gcc -std=c99 or g++
 * 	ISO C99
 *
 * _ISOC11_SOURCE or gcc -std=c11 or g++ -std=c++11
 * 	ISO C11
 *
 * _ATFILE_SOURCE (implied by _POSIX_C_SOURCE >= 200809L)
 *	"at" functions
 *
 * _LARGEFILE_SOURCE (deprecated by _XOPEN_SOURCE >= 500)
 *	fseeko, ftello
 *
 * _GNU_SOURCE
 * 	All of the above plus GNU extensions
 *
 * _BSD_SOURCE (deprecated by _DEFAULT_SOURCE)
 * _SVID_SOURCE (deprecated by _DEFAULT_SOURCE)
 * _DEFAULT_SOURCE (or none of the above)
 * 	POSIX-1.2008 with BSD and SVr4 extensions
 */
/*
 * The following private macros are used throughout the headers to control
 * which symbols should be exposed.  They are for internal use only, as
 * indicated by the leading double underscore, and must never be used outside
 * of these headers.
 *
 * __POSIX_VISIBLE
 * 	any version of POSIX.1; enabled by default, or with _POSIX_SOURCE,
 * 	any value of _POSIX_C_SOURCE, or _XOPEN_SOURCE >= 500.
 *
 * __POSIX_VISIBLE >= 2
 * 	POSIX.2-1992; enabled by default, with _POSIX_C_SOURCE >= 2,
 * 	or _XOPEN_SOURCE >= 500.
 *
 * __POSIX_VISIBLE >= 199309
 * 	POSIX.1b-1993; enabled by default, with _POSIX_C_SOURCE >= 199309L,
 * 	or _XOPEN_SOURCE >= 500.
 *
 * __POSIX_VISIBLE >= 199506
 * 	POSIX.1c-1995; enabled by default, with _POSIX_C_SOURCE >= 199506L,
 * 	or _XOPEN_SOURCE >= 500.
 *
 * __POSIX_VISIBLE >= 200112
 * 	POSIX.1-2001; enabled by default, with _POSIX_C_SOURCE >= 200112L,
 * 	or _XOPEN_SOURCE >= 600.
 *
 * __POSIX_VISIBLE >= 200809
 * 	POSIX.1-2008; enabled by default, with _POSIX_C_SOURCE >= 200809L,
 * 	or _XOPEN_SOURCE >= 700.
 *
 * __XSI_VISIBLE
 *	XPG4 XSI extensions; enabled with any version of _XOPEN_SOURCE.
 *
 * __XSI_VISIBLE >= 4
 *	SUSv1 XSI extensions; enabled with both _XOPEN_SOURCE and
 * 	_XOPEN_SOURCE_EXTENDED together.
 *
 * __XSI_VISIBLE >= 500
 *	SUSv2 XSI extensions; enabled with _XOPEN_SOURCE >= 500.
 *
 * __XSI_VISIBLE >= 600
 *	SUSv3 XSI extensions; enabled with _XOPEN_SOURCE >= 600.
 *
 * __XSI_VISIBLE >= 700
 *	SUSv4 XSI extensions; enabled with _XOPEN_SOURCE >= 700.
 *
 * __ISO_C_VISIBLE >= 1999
 * 	ISO C99; enabled with gcc -std=c99 or newer (on by default since GCC 5),
 * 	any version of C++, or with _ISOC99_SOURCE, _POSIX_C_SOURCE >= 200112L,
 * 	or _XOPEN_SOURCE >= 600.
 *
 * __ISO_C_VISIBLE >= 2011
 * 	ISO C11; enabled with gcc -std=c11 or newer (on by default since GCC 5),
 * 	g++ -std=c++11 or newer (on by default since GCC 6), or with
 * 	_ISOC11_SOURCE.
 *
 * __ATFILE_VISIBLE
 *	"at" functions; enabled by default, with _ATFILE_SOURCE,
 * 	_POSIX_C_SOURCE >= 200809L, or _XOPEN_SOURCE >= 700.
 *
 * __LARGEFILE_VISIBLE
 *	fseeko, ftello; enabled with _LARGEFILE_SOURCE or _XOPEN_SOURCE >= 500.
 *
 * __BSD_VISIBLE
 * 	BSD extensions; enabled by default, or with _BSD_SOURCE.
 *
 * __SVID_VISIBLE
 * 	SVr4 extensions; enabled by default, or with _SVID_SOURCE.
 *
 * __MISC_VISIBLE
 * 	Extensions found in both BSD and SVr4 (shorthand for
 * 	(__BSD_VISIBLE || __SVID_VISIBLE)), or newlib-specific
 * 	extensions; enabled by default.
 *
 * __GNU_VISIBLE
 * 	GNU extensions; enabled with _GNU_SOURCE.
 *
 * In all cases above, "enabled by default" means either by defining
 * _DEFAULT_SOURCE, or by not defining any of the public feature test macros.
 * Defining _GNU_SOURCE makes all of the above avaliable.
 */
/* RTEMS adheres to POSIX -- 1003.1b with some features from annexes.  */
/* XMK loosely adheres to POSIX -- 1003.1 */





/* exceptions first */







/* 16 bit integer machines */
/* For the PowerPC eabi, force the _impure_ptr to be in .sdata */
/* Configure small REENT structure for Xilinx MicroBlaze platforms */
/* This block should be kept in sync with GCC's limits.h.  The point
   of having these definitions here is to not include limits.h, which
   would pollute the user namespace, while still using types of the
   the correct widths when deciding how to define __int32_t and
   __int64_t.  */
/* End of block that should be kept in sync with GCC's limits.h.  */
/* Define return type of read/write routines.  In POSIX, the return type
   for read()/write() is "ssize_t" but legacy newlib code has been using
   "int" for some time.  If not specified, "int" is defaulted.  */



/* Define `count' parameter of read/write routines.  In POSIX, the `count'
   parameter is "size_t" but legacy newlib code has been using "int" for some
   time.  If not specified, "int" is defaulted.  */
/* See if small reent asked for at configuration time and
   is not chosen by the platform by default.  */






/* If _MB_EXTENDED_CHARSETS_ALL is set, we want all of the extended
   charsets.  The extended charsets add a few functions and a couple
   of tables of a few K each. */

/* First try to figure out whether we really are in an ANSI C environment.  */
/* FIXME: This probably needs some work.  Perhaps sys/config.h can be
   prevailed upon to give us a clue.  */





/*  ISO C++.  */
/* Support gcc's __attribute__ facility.  */







/*  The traditional meaning of 'extern inline' for GCC is not
  to emit the function body unless the address is explicitly
  taken.  However this behaviour is changing to match the C99
  standard, which uses 'extern inline' to indicate that the
  function body *must* be emitted.  Likewise, a function declared
  without either 'extern' or 'static' defaults to extern linkage
  (C99 6.2.2p5), and the compiler may choose whether to use the
  inline version or call the extern linkage version (6.7.4p6).
  If we are using GCC, but do not have the new behaviour, we need
  to use extern inline; if we are using a new GCC with the
  C99-compatible behaviour, or a non-GCC compiler (which we will
  have to hope is C99, since there is no other way to achieve the
  effect of omitting the function if it isn't referenced) we use
  'static inline', which c99 defines to mean more-or-less the same
  as the Gnu C 'extern inline'.  */




/* We're using GCC in C99 mode, or an unknown compiler which
  we just have to hope obeys the C99 semantics of inline.  */





/* libc/sys/linux/sys/cdefs.h - Helper macros for K&R vs. ANSI C compat. */

/* Written 2000 by Werner Almesberger */

/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 * $FreeBSD$
 */




/*
 *  $Id$
 */




/*
 *  Written by Joel Sherrill <joel@OARcorp.com>.
 *
 *  COPYRIGHT (c) 1989-2014.
 *
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Permission to use, copy, modify, and distribute this software for any
 *  purpose without fee is hereby granted, provided that this entire notice
 *  is included in all copies of any software which is or includes a copy
 *  or modification of this software.
 *
 *  THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 *  WARRANTY.  IN PARTICULAR,  THE AUTHOR MAKES NO REPRESENTATION
 *  OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY OF THIS
 *  SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 *
 *  $Id$
 */

/*
 * Guess on types by examining *_MIN / *_MAX defines.
 */

/* GCC >= 3.3.0 has __<val>__ implicitly defined. */
typedef signed char __int8_t;

typedef unsigned char __uint8_t;
typedef short int __int16_t;

typedef short unsigned int __uint16_t;
typedef int __int32_t;

typedef unsigned int __uint32_t;
typedef long int __int64_t;

typedef long unsigned int __uint64_t;
typedef signed char __int_least8_t;

typedef unsigned char __uint_least8_t;
typedef short int __int_least16_t;

typedef short unsigned int __uint_least16_t;
typedef int __int_least32_t;

typedef unsigned int __uint_least32_t;
typedef long int __int_least64_t;

typedef long unsigned int __uint_least64_t;
typedef long int __intptr_t;

typedef long unsigned int __uintptr_t;
/*
 *  Written by Joel Sherrill <joel@OARcorp.com>.
 *
 *  COPYRIGHT (c) 1989-2014.
 *
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Permission to use, copy, modify, and distribute this software for any
 *  purpose without fee is hereby granted, provided that this entire notice
 *  is included in all copies of any software which is or includes a copy
 *  or modification of this software.
 *
 *  THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 *  WARRANTY.  IN PARTICULAR,  THE AUTHOR MAKES NO REPRESENTATION
 *  OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY OF THIS
 *  SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 *
 *  $Id$
 */

/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.17  Common definitions  <stddef.h>
 */






/* Any one of these symbols __need_* means that GNU libc
   wants us just to define one data type.  So don't define
   the symbols that indicate this file's entire job has been done.  */
/* This avoids lossage on SunOS but only if stdtypes.h comes first.
   There's no way to win with the other order!  Sun lossage.  */

/* On 4.3bsd-net2, make sure ansi.h is included, so we have
   one less case to deal with in the following.  */



/* On FreeBSD 5, machine/ansi.h does not exist anymore... */




/* In 4.3bsd-net2, machine/ansi.h defines these symbols, which are
   defined if the corresponding type is *not* defined.
   FreeBSD-2.1 defines _MACHINE_ANSI_H_ instead of _ANSI_H_.
   NetBSD defines _I386_ANSI_H_ and _X86_64_ANSI_H_ instead of _ANSI_H_ */
/* Sequent's header files use _PTRDIFF_T_ in some conflicting way.
   Just ignore it.  */




/* On VxWorks, <type/vxTypesBase.h> may have defined macros like
   _TYPE_size_t which will typedef size_t.  fixincludes patched the
   vxTypesBase.h so that this macro is only defined if _GCC_SIZE_T is
   not defined, and so that defining this macro defines _GCC_SIZE_T.
   If we find that the macros are still defined at this point, we must
   invoke them so that the type is defined as expected.  */
/* In case nobody has defined these types, but we aren't running under
   GCC 2.00, make sure that __PTRDIFF_TYPE__, __SIZE_TYPE__, and
   __WCHAR_TYPE__ have reasonable values.  This can happen if the
   parts of GCC is compiled by an older compiler, that actually
   include gstddef.h, such as collect2.  */

/* Signed type of difference of two pointers.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/* Unsigned type of `sizeof' something.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
typedef long unsigned int size_t;
/* Wide character type.
   Locale-writers should change this as necessary to
   be big enough to hold unique values not between 0 and 127,
   and not (wchar_t) -1, for each defined multibyte character.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/*  In 4.3bsd-net2, leave these undefined to indicate that size_t, etc.
    are already defined.  */
/*  BSD/OS 3.1 and FreeBSD [23].x require the MACHINE_ANSI_H check here.  */
/*  NetBSD 5 requires the I386_ANSI_H and X86_64_ANSI_H checks here.  */
/* A null pointer constant.  */

/*
 * Testing against Clang-specific extensions.
 */
/*
 * This code has been put in place to help reduce the addition of
 * compiler specific defines in FreeBSD code.  It helps to aid in
 * having a compiler-agnostic source tree.
 */
/*
 * Compiler memory barriers, specific to gcc and clang.
 */
/* XXX: if __GNUC__ >= 2: not tested everywhere originally, where replaced */
/*
 * The __CONCAT macro is used to concatenate parts of symbol names, e.g.
 * with "#define OLD(foo) __CONCAT(old,foo)", OLD(foo) produces oldfoo.
 * The __CONCAT macro is a bit tricky to use if it must work in non-ANSI
 * mode -- there must be no spaces between its arguments, and for nested
 * __CONCAT's, all the __CONCAT's must be at the left.  __CONCAT can also
 * concatenate double-quoted strings produced by the __STRING macro, but
 * this only works with ANSI C.
 *
 * __XSTRING is like __STRING, but it expands any macros in its argument
 * first.  It is only available with ANSI C.
 */
/*
 * Compiler-dependent macros to help declare dead (non-returning) and
 * pure (no side effects) functions, and unused variables.  They are
 * null except for versions of gcc that are known to support the features
 * properly (old versions of gcc-2 supported the dead and pure features
 * in a different (wrong) way).  If we do not provide an implementation
 * for a given compiler, let the compile fail if it is told to use
 * a feature that we cannot live without.
 */
/*
 * Keywords added in C11.
 */
/*
 * Emulation of C11 _Generic().  Unlike the previously defined C11
 * keywords, it is not possible to implement this using exactly the same
 * syntax.  Therefore implement something similar under the name
 * __generic().  Unlike _Generic(), this macro can only distinguish
 * between a single type, so it requires nested invocations to
 * distinguish multiple cases.
 */
/*
 * C99 Static array indices in function parameter declarations.  Syntax such as:
 * void bar(int myArray[static 10]);
 * is allowed in C99 but not in C++.  Define __min_size appropriately so
 * headers using it can be compiled in either language.  Use like this:
 * void bar(int myArray[__min_size(10)]);
 */
/* XXX: should use `#if __STDC_VERSION__ < 199901'. */




/*
 * GCC 2.95 provides `__restrict' as an extension to C90 to support the
 * C99-specific `restrict' type qualifier.  We happen to use `__restrict' as
 * a way to define the `restrict' type qualifier without disturbing older
 * software that is unaware of C99 keywords.
 */
/*
 * GNU C version 2.96 adds explicit branch prediction so that
 * the CPU back-end can hint the processor and also so that
 * code blocks can be reordered such that the predicted path
 * sees a more linear flow, thus improving cache behavior, etc.
 *
 * The following two macros provide us with a way to utilize this
 * compiler feature.  Use __predict_true() if you expect the expression
 * to evaluate to true, and __predict_false() if you expect the
 * expression to evaluate to false.
 *
 * A few notes about usage:
 *
 *	* Generally, __predict_false() error condition checks (unless
 *	  you have some _strong_ reason to do otherwise, in which case
 *	  document it), and/or __predict_true() `no-error' condition
 *	  checks, assuming you want to optimize for the no-error case.
 *
 *	* Other than that, if you don't know the likelihood of a test
 *	  succeeding from empirical or other `hard' evidence, don't
 *	  make predictions.
 *
 *	* These are meant to be used in places that are run `a lot'.
 *	  It is wasteful to make predictions in code that is run
 *	  seldomly (e.g. at subsystem initialization time) as the
 *	  basic block reordering that this affects can often generate
 *	  larger code.
 */
/* Only default visibility is supported on PE/COFF targets. */
/*
 * Given the pointer x to the member m of the struct s, return
 * a pointer to the containing structure.  When using GCC, we first
 * assign pointer x to a local variable, to check that its type is
 * compatible with member m.
 */
/*
 * Compiler-dependent macros to declare that functions take printf-like
 * or scanf-like arguments.  They are null except for versions of gcc
 * that are known to support the features properly (old versions of gcc-2
 * didn't permit keeping the keywords out of the application namespace).
 */
/* Compiler-dependent macros that rely on FreeBSD-specific extensions. */
/*
 * Nullability qualifiers: currently only supported by Clang.
 */
/*
 * Type Safety Checking
 *
 * Clang provides additional attributes to enable checking type safety
 * properties that cannot be enforced by the C type system. 
 */
/*
 * Lock annotations.
 *
 * Clang provides support for doing basic thread-safety tests at
 * compile-time, by marking which locks will/should be held when
 * entering/leaving a functions.
 *
 * Furthermore, it is also possible to annotate variables and structure
 * members to enforce that they are only accessed when certain locks are
 * held.
 */







/* Structure implements a lock. */


/* Function acquires an exclusive or shared lock. */





/* Function attempts to acquire an exclusive or shared lock. */





/* Function releases a lock. */


/* Function asserts that an exclusive or shared lock is held. */





/* Function requires that an exclusive or shared lock is or is not held. */







/* Function should not be analyzed. */


/* Guard variables and structure members by lock. */

/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.17  Common definitions  <stddef.h>
 */






/* Any one of these symbols __need_* means that GNU libc
   wants us just to define one data type.  So don't define
   the symbols that indicate this file's entire job has been done.  */





/* snaroff@next.com says the NeXT needs this.  */




/* This avoids lossage on SunOS but only if stdtypes.h comes first.
   There's no way to win with the other order!  Sun lossage.  */

/* On 4.3bsd-net2, make sure ansi.h is included, so we have
   one less case to deal with in the following.  */



/* On FreeBSD 5, machine/ansi.h does not exist anymore... */




/* In 4.3bsd-net2, machine/ansi.h defines these symbols, which are
   defined if the corresponding type is *not* defined.
   FreeBSD-2.1 defines _MACHINE_ANSI_H_ instead of _ANSI_H_.
   NetBSD defines _I386_ANSI_H_ and _X86_64_ANSI_H_ instead of _ANSI_H_ */
/* Sequent's header files use _PTRDIFF_T_ in some conflicting way.
   Just ignore it.  */




/* On VxWorks, <type/vxTypesBase.h> may have defined macros like
   _TYPE_size_t which will typedef size_t.  fixincludes patched the
   vxTypesBase.h so that this macro is only defined if _GCC_SIZE_T is
   not defined, and so that defining this macro defines _GCC_SIZE_T.
   If we find that the macros are still defined at this point, we must
   invoke them so that the type is defined as expected.  */
/* In case nobody has defined these types, but we aren't running under
   GCC 2.00, make sure that __PTRDIFF_TYPE__, __SIZE_TYPE__, and
   __WCHAR_TYPE__ have reasonable values.  This can happen if the
   parts of GCC is compiled by an older compiler, that actually
   include gstddef.h, such as collect2.  */

/* Signed type of difference of two pointers.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
typedef long int ptrdiff_t;
/* If this symbol has done its job, get rid of it.  */




/* Unsigned type of `sizeof' something.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/* Wide character type.
   Locale-writers should change this as necessary to
   be big enough to hold unique values not between 0 and 127,
   and not (wchar_t) -1, for each defined multibyte character.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/* On BSD/386 1.1, at least, machine/ansi.h defines _BSD_WCHAR_T_
   instead of _WCHAR_T_, and _BSD_RUNE_T_ (which, unlike the other
   symbols in the _FOO_T_ family, stays defined even after its
   corresponding type is defined).  If we define wchar_t, then we
   must undef _WCHAR_T_; for BSD/386 1.1 (and perhaps others), if
   we undef _WCHAR_T_, then we must also define rune_t, since 
   headers like runetype.h assume that if machine/ansi.h is included,
   and _BSD_WCHAR_T_ is not defined, then rune_t is available.
   machine/ansi.h says, "Note that _WCHAR_T_ and _RUNE_T_ must be of
   the same type." */
/* FreeBSD 5 can't be handled well using "traditional" logic above
   since it no longer defines _BSD_RUNE_T_ yet still desires to export
   rune_t in some cases... */
typedef int wchar_t;
/*  In 4.3bsd-net2, leave these undefined to indicate that size_t, etc.
    are already defined.  */
/*  BSD/OS 3.1 and FreeBSD [23].x require the MACHINE_ANSI_H check here.  */
/*  NetBSD 5 requires the I386_ANSI_H and X86_64_ANSI_H checks here.  */
/* A null pointer constant.  */
/* Offset of member MEMBER in a struct of type TYPE. */






/* Type whose alignment is supported in every context and is at least
   as great as that of any standard type not using alignment
   specifiers.  */
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
} max_align_t;


/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.15  Variable arguments  <stdarg.h>
 */
/* Define __gnuc_va_list.  */



typedef __builtin_va_list __gnuc_va_list;


/* Define the standard macros for the user,
   if this invocation was from the user program.  */


/*
 * <sys/reent.h> defines __FILE, _fpos_t.
 * They must be defined there because struct _reent needs them (and we don't
 * want reent.h to include this file.
 */

/* This header file provides the reentrancy.  */

/* WARNING: All identifiers here must begin with an underscore.  This file is
   included by stdio.h and others and we therefore must only use identifiers
   in the namespace allotted to us.  */







/* Provide support for both ANSI and non-ANSI environments.  */

/* Some ANSI environments are "broken" in the sense that __STDC__ cannot be
   relied upon to have it's intended meaning.  Therefore we must use our own
   concoction: _HAVE_STDC.  Always use _HAVE_STDC instead of __STDC__ in newlib
   sources!

   To get a strict ANSI C environment, define macro __STRICT_ANSI__.  This will
   "comment out" the non-ANSI parts of the ANSI header files (non-ANSI header
   files aren't affected).  */

/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.17  Common definitions  <stddef.h>
 */

/* ANSI C namespace clean utility typedefs */

/* This file defines various typedefs needed by the system calls that support
   the C library.  Basically, they're just the POSIX versions with an '_'
   prepended.  This file lives in the `sys' directory so targets can provide
   their own if desired (or they can put target dependant conditionals here).
*/




/*
 *  $Id$
 */



/*
 *  $Id$
 */



/* dummy lock routines for single-threaded aps */

typedef int _LOCK_T;
typedef int _LOCK_RECURSIVE_T;

/* Provide support for both ANSI and non-ANSI environments.  */

/* Some ANSI environments are "broken" in the sense that __STDC__ cannot be
   relied upon to have it's intended meaning.  Therefore we must use our own
   concoction: _HAVE_STDC.  Always use _HAVE_STDC instead of __STDC__ in newlib
   sources!

   To get a strict ANSI C environment, define macro __STRICT_ANSI__.  This will
   "comment out" the non-ANSI parts of the ANSI header files (non-ANSI header
   files aren't affected).  */


typedef long _off_t;



typedef short __dev_t;



typedef unsigned short __uid_t;


typedef unsigned short __gid_t;



__extension__ typedef long long _off64_t;


/*
 * We need fpos_t for the following, but it doesn't have a leading "_",
 * so we use _fpos_t instead.
 */

typedef long _fpos_t; /* XXX must match off_t in <sys/types.h> */
    /* (and must be `long' for now) */
/* If __SIZE_TYPE__ is defined (gcc) we define ssize_t based on size_t.
   We simply change "unsigned" to "signed" for this single definition
   to make sure ssize_t and size_t only differ by their signedness. */

typedef long signed int _ssize_t;

/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.17  Common definitions  <stddef.h>
 */






/* Any one of these symbols __need_* means that GNU libc
   wants us just to define one data type.  So don't define
   the symbols that indicate this file's entire job has been done.  */
/* This avoids lossage on SunOS but only if stdtypes.h comes first.
   There's no way to win with the other order!  Sun lossage.  */

/* On 4.3bsd-net2, make sure ansi.h is included, so we have
   one less case to deal with in the following.  */



/* On FreeBSD 5, machine/ansi.h does not exist anymore... */




/* In 4.3bsd-net2, machine/ansi.h defines these symbols, which are
   defined if the corresponding type is *not* defined.
   FreeBSD-2.1 defines _MACHINE_ANSI_H_ instead of _ANSI_H_.
   NetBSD defines _I386_ANSI_H_ and _X86_64_ANSI_H_ instead of _ANSI_H_ */
/* Sequent's header files use _PTRDIFF_T_ in some conflicting way.
   Just ignore it.  */




/* On VxWorks, <type/vxTypesBase.h> may have defined macros like
   _TYPE_size_t which will typedef size_t.  fixincludes patched the
   vxTypesBase.h so that this macro is only defined if _GCC_SIZE_T is
   not defined, and so that defining this macro defines _GCC_SIZE_T.
   If we find that the macros are still defined at this point, we must
   invoke them so that the type is defined as expected.  */
/* In case nobody has defined these types, but we aren't running under
   GCC 2.00, make sure that __PTRDIFF_TYPE__, __SIZE_TYPE__, and
   __WCHAR_TYPE__ have reasonable values.  This can happen if the
   parts of GCC is compiled by an older compiler, that actually
   include gstddef.h, such as collect2.  */

/* Signed type of difference of two pointers.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/* If this symbol has done its job, get rid of it.  */




/* Unsigned type of `sizeof' something.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
/* Wide character type.
   Locale-writers should change this as necessary to
   be big enough to hold unique values not between 0 and 127,
   and not (wchar_t) -1, for each defined multibyte character.  */

/* Define this type if we are doing the whole job,
   or if we want this type in particular.  */
typedef unsigned int wint_t;




/*  In 4.3bsd-net2, leave these undefined to indicate that size_t, etc.
    are already defined.  */
/*  BSD/OS 3.1 and FreeBSD [23].x require the MACHINE_ANSI_H check here.  */
/*  NetBSD 5 requires the I386_ANSI_H and X86_64_ANSI_H checks here.  */
/* A null pointer constant.  */
/* Offset of member MEMBER in a struct of type TYPE. */



/* Conversion state information.  */
typedef struct
{
  int __count;
  union
  {
    wint_t __wch;
    unsigned char __wchb[4];
  } __value; /* Value so far.  */
} _mbstate_t;



typedef _LOCK_RECURSIVE_T _flock_t;



/* Iconv descriptor type */
typedef void *_iconv_t;
typedef unsigned int __ULong;
struct _reent;

/*
 * If _REENT_SMALL is defined, we make struct _reent as small as possible,
 * by having nearly everything possible allocated at first use.
 */

struct _Bigint
{
  struct _Bigint *_next;
  int _k, _maxwds, _sign, _wds;
  __ULong _x[1];
};

/* needed by reentrant structure */
struct __tm
{
  int __tm_sec;
  int __tm_min;
  int __tm_hour;
  int __tm_mday;
  int __tm_mon;
  int __tm_year;
  int __tm_wday;
  int __tm_yday;
  int __tm_isdst;
};

/*
 * atexit() support.
 */



struct _on_exit_args {
 void * _fnargs[32 /* must be at least 32 to guarantee ANSI conformance */]; /* user fn args */
 void * _dso_handle[32 /* must be at least 32 to guarantee ANSI conformance */];
 /* Bitmask is set if user function takes arguments.  */
 __ULong _fntypes; /* type of exit routine -
				   Must have at least _ATEXIT_SIZE bits */
 /* Bitmask is set if function was registered via __cxa_atexit.  */
 __ULong _is_cxa;
};
struct _atexit {
 struct _atexit *_next; /* next in list */
 int _ind; /* next index in this table */
 /* Some entries may already have been called, and will be NULL.  */
 void (*_fns[32 /* must be at least 32 to guarantee ANSI conformance */])(void); /* the table itself */
        struct _on_exit_args _on_exit_args;
};
/*
 * Stdio buffers.
 *
 * This and __FILE are defined here because we need them for struct _reent,
 * but we don't want stdio.h included when stdlib.h is.
 */

struct __sbuf {
 unsigned char *_base;
 int _size;
};

/*
 * Stdio state variables.
 *
 * The following always hold:
 *
 *	if (_flags&(__SLBF|__SWR)) == (__SLBF|__SWR),
 *		_lbfsize is -_bf._size, else _lbfsize is 0
 *	if _flags&__SRD, _w is 0
 *	if _flags&__SWR, _r is 0
 *
 * This ensures that the getc and putc macros (or inline functions) never
 * try to write or read from a file that is in `read' or `write' mode.
 * (Moreover, they can, and do, automatically switch from read mode to
 * write mode, and back, on "r+" and "w+" files.)
 *
 * _lbfsize is used only to make the inline line-buffered output stream
 * code as compact as possible.
 *
 * _ub, _up, and _ur are used when ungetc() pushes back more characters
 * than fit in the current _bf, or when ungetc() pushes back a character
 * that does not match the previous one in _bf.  When this happens,
 * _ub._base becomes non-nil (i.e., a stream has ungetc() data iff
 * _ub._base!=NULL) and _up and _ur save the current values of _p and _r.
 */
struct __sFILE {
  unsigned char *_p; /* current position in (some) buffer */
  int _r; /* read space left for getc() */
  int _w; /* write space left for putc() */
  short _flags; /* flags, below; this FILE is free if 0 */
  short _file; /* fileno, if Unix descriptor, else -1 */
  struct __sbuf _bf; /* the buffer (at least 1 byte, if !NULL) */
  int _lbfsize; /* 0 or -_bf._size, for inline putc */





  /* operations */
  void * _cookie; /* cookie passed to io functions */

  int (* _read) (struct _reent *, void *, char *, int)
                                          ;
  int (* _write) (struct _reent *, void *, const char *, int)

                                   ;
  _fpos_t (* _seek) (struct _reent *, void *, _fpos_t, int);
  int (* _close) (struct _reent *, void *);

  /* separate buffer for long sequences of ungetc() */
  struct __sbuf _ub; /* ungetc buffer */
  unsigned char *_up; /* saved _p when _p is doing ungetc data */
  int _ur; /* saved _r when _r is counting ungetc data */

  /* tricks to meet minimum requirements even when malloc() fails */
  unsigned char _ubuf[3]; /* guarantee an ungetc() buffer */
  unsigned char _nbuf[1]; /* guarantee a getc() buffer */

  /* separate buffer for fgetline() when line crosses buffer boundary */
  struct __sbuf _lb; /* buffer for fgetline() */

  /* Unix stdio files get aligned to block boundaries on fseek() */
  int _blksize; /* stat.st_blksize (may be != _bf._size) */
  _off_t _offset; /* current lseek offset */


  struct _reent *_data; /* Here for binary compatibility? Remove? */



  _flock_t _lock; /* for thread-safety locking */

  _mbstate_t _mbstate; /* for wide char stdio functions. */
  int _flags2; /* for future use */
};
typedef struct __sFILE __FILE;



struct _glue
{
  struct _glue *_next;
  int _niobs;
  __FILE *_iobs;
};

/*
 * rand48 family support
 *
 * Copyright (c) 1993 Martin Birgmeier
 * All rights reserved.
 *
 * You may redistribute unmodified or modified versions of this source
 * code provided that the above copyright notice and this and the
 * following conditions are retained.
 *
 * This software is provided ``as is'', and comes with no warranties
 * of any kind. I shall in no event be liable for anything that happens
 * to anyone/anything when using this software.
 */







struct _rand48 {
  unsigned short _seed[3];
  unsigned short _mult[3];
  unsigned short _add;




};

/* How big the some arrays are.  */




/*
 * struct _reent
 *
 * This structure contains *all* globals needed by the library.
 * It's raison d'etre is to facilitate threads by making all library routines
 * reentrant.  IE: All state information is contained here.
 */
struct _reent
{
  int _errno; /* local copy of errno */

  /* FILE is a big struct and may change over time.  To try to achieve binary
     compatibility with future versions, put stdin,stdout,stderr here.
     These are pointers into member __sf defined below.  */
  __FILE *_stdin, *_stdout, *_stderr;

  int _inc; /* used by tmpnam */
  char _emergency[25];

  int _current_category; /* used by setlocale */
  const char *_current_locale;

  int __sdidinit; /* 1 means stdio has been init'd */

  void (* __cleanup) (struct _reent *);

  /* used by mprec routines */
  struct _Bigint *_result;
  int _result_k;
  struct _Bigint *_p5s;
  struct _Bigint **_freelist;

  /* used by some fp conversion routines */
  int _cvtlen; /* should be size_t */
  char *_cvtbuf;

  union
    {
      struct
        {
          unsigned int _unused_rand;
          char * _strtok_last;
          char _asctime_buf[26];
          struct __tm _localtime_buf;
          int _gamma_signgam;
          __extension__ unsigned long long _rand_next;
          struct _rand48 _r48;
          _mbstate_t _mblen_state;
          _mbstate_t _mbtowc_state;
          _mbstate_t _wctomb_state;
          char _l64a_buf[8];
          char _signal_buf[24];
          int _getdate_err;
          _mbstate_t _mbrlen_state;
          _mbstate_t _mbrtowc_state;
          _mbstate_t _mbsrtowcs_state;
          _mbstate_t _wcrtomb_state;
          _mbstate_t _wcsrtombs_state;
   int _h_errno;
        } _reent;
  /* Two next two fields were once used by malloc.  They are no longer
     used. They are used to preserve the space used before so as to
     allow addition of new reent fields and keep binary compatibility.   */
      struct
        {

          unsigned char * _nextf[30];
          unsigned int _nmalloc[30];
        } _unused;
    } _new;


  /* atexit stuff */
  struct _atexit *_atexit; /* points to head of LIFO stack */
  struct _atexit _atexit0; /* one guaranteed table, required by ANSI */


  /* signal info */
  void (**(_sig_func))(int);

  /* These are here last so that __FILE can grow without changing the offsets
     of the above members (on the off chance that future binary compatibility
     would be broken otherwise).  */
  struct _glue __sglue; /* root of glue chain */
  __FILE __sf[3]; /* first three file descriptors */
};
/* This value is used in stdlib/misc.c.  reent/reent.c has to know it
   as well to make sure the freelist is correctly free'd.  Therefore
   we define it here, rather than in stdlib/misc.c, as before. */


/*
 * All references to struct _reent are via this pointer.
 * Internally, newlib routines that need to reference it should use _REENT.
 */





extern struct _reent *_impure_ptr ;
extern struct _reent *const _global_impure_ptr ;

void _reclaim_reent (struct _reent *);

/* #define _REENT_ONLY define this to get only reentrant routines */
/* unified sys/types.h: 
   start with sef's sysvi386 version.
   merge go32 version -- a few ifdefs.
   h8300hms, h8300xray, and sysvnecv70 disagree on the following types:

   typedef int gid_t;
   typedef int uid_t;
   typedef int dev_t;
   typedef int ino_t;
   typedef int mode_t;
   typedef int caddr_t;

   however, these aren't "reasonable" values, the sysvi386 ones make far 
   more sense, and should work sufficiently well (in particular, h8300 
   doesn't have a stat, and the necv70 doesn't matter.) -- eichin
 */



/* Provide support for both ANSI and non-ANSI environments.  */

/* Some ANSI environments are "broken" in the sense that __STDC__ cannot be
   relied upon to have it's intended meaning.  Therefore we must use our own
   concoction: _HAVE_STDC.  Always use _HAVE_STDC instead of __STDC__ in newlib
   sources!

   To get a strict ANSI C environment, define macro __STRICT_ANSI__.  This will
   "comment out" the non-ANSI parts of the ANSI header files (non-ANSI header
   files aren't affected).  */
/* libc/sys/linux/sys/cdefs.h - Helper macros for K&R vs. ANSI C compat. */

/* Written 2000 by Werner Almesberger */

/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 * $FreeBSD$
 */
/*
 *  $Id$
 */

/* BSD types permitted by POSIX and always exposed as in Glibc.  Only provided
   for backward compatibility with BSD code.  The uintN_t standard types should
   be preferred in new code. */

typedef __uint8_t u_int8_t;


typedef __uint16_t u_int16_t;


typedef __uint32_t u_int32_t;


typedef __uint64_t u_int64_t;
/* ANSI C namespace clean utility typedefs */

/* This file defines various typedefs needed by the system calls that support
   the C library.  Basically, they're just the POSIX versions with an '_'
   prepended.  This file lives in the `sys' directory so targets can provide
   their own if desired (or they can put target dependant conditionals here).
*/
/*
 * Copyright (c) 2004, 2005 by
 * Ralf Corsepius, Ulm/Germany. All rights reserved.
 *
 * Permission to use, copy, modify, and distribute this software
 * is freely granted, provided that this notice is preserved.
 */




/*
 *  $Id$
 */






typedef __int8_t int8_t ;
typedef __uint8_t uint8_t ;




typedef __int16_t int16_t ;
typedef __uint16_t uint16_t ;




typedef __int32_t int32_t ;
typedef __uint32_t uint32_t ;




typedef __int64_t int64_t ;
typedef __uint64_t uint64_t ;



typedef __intptr_t intptr_t;
typedef __uintptr_t uintptr_t;








/* Copyright (C) 1989-2015 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

/*
 * ISO C Standard:  7.17  Common definitions  <stddef.h>
 */




/*
 *  The following section is RTEMS specific and is needed to more
 *  closely match the types defined in the BSD machine/types.h.
 *  This is needed to let the RTEMS/BSD TCP/IP stack compile.
 */
typedef long int __off_t;
typedef int __pid_t;

__extension__ typedef long long int __loff_t;





typedef long __suseconds_t; /* microseconds (signed) */

/* To ensure the stat struct's layout doesn't change when sizeof(int), etc.
   changes, we assume sizeof short and long never change and have all types
   used to define struct stat use them and not int where possible.
   Where not possible, _ST_INTxx are used.  It would be preferable to not have
   such assumptions, but until the extra fluff is necessary, it's avoided.
   No 64 bit targets use stat yet.  What to do about them is postponed
   until necessary.  */







/* select.h
   Copyright 1998, 1999, 2000, 2001, 2005, 2009 Red Hat, Inc.

   Written by Geoffrey Noer <noer@cygnus.com>

This file is part of Cygwin.

This software is a copyrighted work licensed under the terms of the
Cygwin license.  Please consult the file "CYGWIN_LICENSE" for
details. */




/* We don't define fd_set and friends if we are compiling POSIX
   source, or if we have included (or may include as indicated
   by __USE_W32_SOCKETS) the W32api winsock[2].h header which
   defines Windows versions of them.   Note that a program which
   includes the W32api winsock[2].h header must know what it is doing;
   it must not call the Cygwin select function.
*/


/* libc/sys/linux/sys/cdefs.h - Helper macros for K&R vs. ANSI C compat. */

/* Written 2000 by Werner Almesberger */

/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 * $FreeBSD$
 */
/*-
 * Copyright (c) 1982, 1986, 1989, 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 * (c) UNIX System Laboratories, Inc.
 * All or some portions of this file are derived from material licensed
 * to the University of California by American Telephone and Telegraph
 * Co. or Unix System Laboratories, Inc. and are reproduced herein with
 * the permission of UNIX System Laboratories, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)signal.h	8.4 (Berkeley) 5/4/95
 * $FreeBSD$
 */




typedef unsigned long __sigset_t;
/*-
 * Copyright (c) 2002 Mike Barcroft <mike@FreeBSD.org>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * $FreeBSD$
 */







typedef __suseconds_t suseconds_t;




typedef long /* time() */ time_t;



/* This define is also used outside of Newlib, e.g. in MinGW-w64 */



/*
 * Structure returned by gettimeofday(2) system call, and used in other calls.
 */
struct timeval {
 time_t tv_sec; /* seconds */
 suseconds_t tv_usec; /* and microseconds */
};
/*-
 * Copyright (c) 1982, 1986, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)time.h	8.5 (Berkeley) 5/4/95
 * from: FreeBSD: src/sys/sys/time.h,v 1.43 2000/03/20 14:09:05 phk Exp
 *	$FreeBSD$
 */




/* libc/sys/linux/sys/cdefs.h - Helper macros for K&R vs. ANSI C compat. */

/* Written 2000 by Werner Almesberger */

/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 * $FreeBSD$
 */
/*-
 * Copyright (c) 1982, 1986, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)time.h	8.5 (Berkeley) 5/4/95
 * from: FreeBSD: src/sys/sys/time.h,v 1.43 2000/03/20 14:09:05 phk Exp
 *	$FreeBSD$
 */
struct timespec {
 time_t tv_sec; /* seconds */
 long tv_nsec; /* and nanoseconds */
};
/*
 * Structure defined by POSIX.1b to be like a itimerval, but with
 * timespecs. Used in the timer_*() system calls.
 */
struct itimerspec {
 struct timespec it_interval;
 struct timespec it_value;
};



typedef __sigset_t sigset_t;



/*
 * Select uses bit masks of file descriptors in longs.
 * These macros manipulate such bit fields (the filesystem macros use chars).
 * FD_SETSIZE may be defined by the user, but the default here
 * should be >= NOFILE (param.h).
 */




typedef unsigned long fd_mask;





/* We use a macro for fd_set so that including Sockets.h afterwards
   can work.  */
typedef struct _types_fd_set {
 fd_mask fds_bits[(((64)+(((sizeof (fd_mask) * 8) /* bits per mask */)-1))/((sizeof (fd_mask) * 8) /* bits per mask */))];
} _types_fd_set;


int select (int __n, _types_fd_set *__readfds, _types_fd_set *__writefds, _types_fd_set *__exceptfds, struct timeval *__timeout) /* full-blown ANSI C */
                                                   ;

int pselect (int __n, _types_fd_set *__readfds, _types_fd_set *__writefds, _types_fd_set *__exceptfds, const struct timespec *__timeout, const sigset_t *__set) /* full-blown ANSI C */

                           ;









/* also defined in mingw/gmon.h and in w32api/winsock[2].h */

typedef unsigned char u_char;



typedef unsigned short u_short;



typedef unsigned int u_int;



typedef unsigned long u_long;







typedef unsigned short ushort; /* System V compatibility */
typedef unsigned int uint; /* System V compatibility */
typedef unsigned long ulong; /* System V compatibility */



typedef unsigned long /* clock() */ clock_t;
typedef long daddr_t;



typedef char * caddr_t;
typedef unsigned short ino_t;
/*
 * All these should be machine specific - right now they are all broken.
 * However, for all of Cygnus' embedded targets, we want them to all be
 * the same.  Otherwise things like sizeof (struct stat) might depend on
 * how the file was compiled (e.g. -mint16 vs -mint32, etc.).
 */


typedef _off_t off_t;
typedef __dev_t dev_t;
typedef __uid_t uid_t;
typedef __gid_t gid_t;





typedef int pid_t;







typedef long key_t;



typedef _ssize_t ssize_t;
typedef unsigned int mode_t __attribute__ ((__mode__ (__SI__)));




typedef unsigned short nlink_t;






typedef unsigned long clockid_t;




typedef unsigned long timer_t;



typedef unsigned long useconds_t;






typedef __int64_t sbintime_t;

/*
 *  Written by Joel Sherrill <joel@OARcorp.com>.
 *
 *  COPYRIGHT (c) 1989-2014.
 *
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Permission to use, copy, modify, and distribute this software for any
 *  purpose without fee is hereby granted, provided that this entire notice
 *  is included in all copies of any software which is or includes a copy
 *  or modification of this software.
 *
 *  THIS SOFTWARE IS BEING PROVIDED "AS IS", WITHOUT ANY EXPRESS OR IMPLIED
 *  WARRANTY.  IN PARTICULAR,  THE AUTHOR MAKES NO REPRESENTATION
 *  OR WARRANTY OF ANY KIND CONCERNING THE MERCHANTABILITY OF THIS
 *  SOFTWARE OR ITS FITNESS FOR ANY PARTICULAR PURPOSE.
 *
 *  $Id$
 */


/* Cygwin will probably never have full posix compliance due to little things
 * like an inability to set the stackaddress. Cygwin is also using void *  
 * pointers rather than structs to ensure maximum binary compatability with
 * previous releases.
 * This means that we don't use the types defined here, but rather in
 * <cygwin/types.h>
 */
/* POSIX Barrier Types */
/* POSIX Spin Lock Types */





/* POSIX Reader/Writer Lock Types */




typedef __FILE FILE;






typedef _fpos_t fpos_t;









/* This header file provides the reentrancy.  */

/* WARNING: All identifiers here must begin with an underscore.  This file is
   included by stdio.h and others and we therefore must only use identifiers
   in the namespace allotted to us.  */

/* Internal locking macros, used to protect stdio functions.  In the
   general case, expand to nothing. Use __SSTR flag in FILE _flags to
   detect if FILE is private to sprintf/sscanf class of functions; if
   set then do nothing as lock is not initialised. */





 /* RD and WR are never simultaneously asserted */
/* _flags2 flags */



/*
 * The following three definitions are for ANSI C, which took them
 * from System V, which stupidly took internal interface macros and
 * made them official arguments to setvbuf(), without renaming them.
 * Hence, these ugly _IOxxx names are *supposed* to appear in user code.
 *
 * Although these happen to match their counterparts above, the
 * implementation does not rely on that (so these could be renumbered).
 */
/*
 * Functions defined in ANSI C standard.
 */
FILE * tmpfile (void);
char * tmpnam (char *);

char * tempnam (const char *, const char *);

int fclose (FILE *);
int fflush (FILE *);
FILE * freopen (const char *restrict, const char *restrict, FILE *restrict);
void setbuf (FILE *restrict, char *restrict);
int setvbuf (FILE *restrict, char *restrict, int, size_t);
int fprintf (FILE *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int fscanf (FILE *restrict, const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
int printf (const char *restrict, ...) __attribute__ ((__format__ (__printf__, 1, 2)))
                                                            ;
int scanf (const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 1, 2)))
                                                           ;
int sscanf (const char *restrict, const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
int vfprintf (FILE *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int vprintf (const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 1, 0)))
                                                            ;
int vsprintf (char *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int fgetc (FILE *);
char * fgets (char *restrict, int, FILE *restrict);
int fputc (int, FILE *);
int fputs (const char *restrict, FILE *restrict);
int getc (FILE *);
int getchar (void);
char * gets (char *);
int putc (int, FILE *);
int putchar (int);
int puts (const char *);
int ungetc (int, FILE *);
size_t fread (void * restrict, size_t _size, size_t _n, FILE *restrict);
size_t fwrite (const void * restrict , size_t _size, size_t _n, FILE *);



int fgetpos (FILE *restrict, fpos_t *restrict);

int fseek (FILE *, long, int);



int fsetpos (FILE *, const fpos_t *);

long ftell ( FILE *);
void rewind (FILE *);
void clearerr (FILE *);
int feof (FILE *);
int ferror (FILE *);
void perror (const char *);

FILE * fopen (const char *restrict _name, const char *restrict _type);
int sprintf (char *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int remove (const char *);
int rename (const char *, const char *);
int fseeko (FILE *, off_t, int);
off_t ftello ( FILE *);







int snprintf (char *restrict, size_t, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int vsnprintf (char *restrict, size_t, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int vfscanf (FILE *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int vscanf (const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 1, 0)))
                                                           ;
int vsscanf (const char *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int asiprintf (char **, const char *, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
char * asniprintf (char *, size_t *, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
char * asnprintf (char *restrict, size_t *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;

int diprintf (int, const char *, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;

int fiprintf (FILE *, const char *, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int fiscanf (FILE *, const char *, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
int iprintf (const char *, ...) __attribute__ ((__format__ (__printf__, 1, 2)))
                                                            ;
int iscanf (const char *, ...) __attribute__ ((__format__ (__scanf__, 1, 2)))
                                                           ;
int siprintf (char *, const char *, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int siscanf (const char *, const char *, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
int sniprintf (char *, size_t, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int vasiprintf (char **, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
char * vasniprintf (char *, size_t *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
char * vasnprintf (char *, size_t *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int vdiprintf (int, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int vfiprintf (FILE *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int vfiscanf (FILE *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int viprintf (const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 1, 0)))
                                                            ;
int viscanf (const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 1, 0)))
                                                           ;
int vsiprintf (char *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int vsiscanf (const char *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int vsniprintf (char *, size_t, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;



/*
 * Routines in POSIX 1003.1:2001.
 */



FILE * fdopen (int, const char *);

int fileno (FILE *);


int pclose (FILE *);
FILE * popen (const char *, const char *);



void setbuffer (FILE *, char *, int);
int setlinebuf (FILE *);



int getw (FILE *);
int putw (int, FILE *);


int getc_unlocked (FILE *);
int getchar_unlocked (void);
void flockfile (FILE *);
int ftrylockfile (FILE *);
void funlockfile (FILE *);
int putc_unlocked (int, FILE *);
int putchar_unlocked (int);


/*
 * Routines in POSIX 1003.1:200x.
 */




int dprintf (int, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;

FILE * fmemopen (void *restrict, size_t, const char *restrict);
/* getdelim - see __getdelim for now */
/* getline - see __getline for now */
FILE * open_memstream (char **, size_t *);
int vdprintf (int, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;



int renameat (int, const char *, int, const char *);


/*
 * Recursive versions of the above.
 */

int _asiprintf_r (struct _reent *, char **, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
char * _asniprintf_r (struct _reent *, char *, size_t *, const char *, ...) __attribute__ ((__format__ (__printf__, 4, 5)))
                                                            ;
char * _asnprintf_r (struct _reent *, char *restrict, size_t *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 4, 5)))
                                                            ;
int _asprintf_r (struct _reent *, char **restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _diprintf_r (struct _reent *, int, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _dprintf_r (struct _reent *, int, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _fclose_r (struct _reent *, FILE *);
int _fcloseall_r (struct _reent *);
FILE * _fdopen_r (struct _reent *, int, const char *);
int _fflush_r (struct _reent *, FILE *);
int _fgetc_r (struct _reent *, FILE *);
int _fgetc_unlocked_r (struct _reent *, FILE *);
char * _fgets_r (struct _reent *, char *restrict, int, FILE *restrict);
char * _fgets_unlocked_r (struct _reent *, char *restrict, int, FILE *restrict);




int _fgetpos_r (struct _reent *, FILE *, fpos_t *);
int _fsetpos_r (struct _reent *, FILE *, const fpos_t *);

int _fiprintf_r (struct _reent *, FILE *, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _fiscanf_r (struct _reent *, FILE *, const char *, ...) __attribute__ ((__format__ (__scanf__, 3, 4)))
                                                           ;
FILE * _fmemopen_r (struct _reent *, void *restrict, size_t, const char *restrict);
FILE * _fopen_r (struct _reent *, const char *restrict, const char *restrict);
FILE * _freopen_r (struct _reent *, const char *restrict, const char *restrict, FILE *restrict);
int _fprintf_r (struct _reent *, FILE *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _fpurge_r (struct _reent *, FILE *);
int _fputc_r (struct _reent *, int, FILE *);
int _fputc_unlocked_r (struct _reent *, int, FILE *);
int _fputs_r (struct _reent *, const char *restrict, FILE *restrict);
int _fputs_unlocked_r (struct _reent *, const char *restrict, FILE *restrict);
size_t _fread_r (struct _reent *, void * restrict, size_t _size, size_t _n, FILE *restrict);
size_t _fread_unlocked_r (struct _reent *, void * restrict, size_t _size, size_t _n, FILE *restrict);
int _fscanf_r (struct _reent *, FILE *restrict, const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 3, 4)))
                                                           ;
int _fseek_r (struct _reent *, FILE *, long, int);
int _fseeko_r (struct _reent *, FILE *, _off_t, int);
long _ftell_r (struct _reent *, FILE *);
_off_t _ftello_r (struct _reent *, FILE *);
void _rewind_r (struct _reent *, FILE *);
size_t _fwrite_r (struct _reent *, const void * restrict, size_t _size, size_t _n, FILE *restrict);
size_t _fwrite_unlocked_r (struct _reent *, const void * restrict, size_t _size, size_t _n, FILE *restrict);
int _getc_r (struct _reent *, FILE *);
int _getc_unlocked_r (struct _reent *, FILE *);
int _getchar_r (struct _reent *);
int _getchar_unlocked_r (struct _reent *);
char * _gets_r (struct _reent *, char *);
int _iprintf_r (struct _reent *, const char *, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int _iscanf_r (struct _reent *, const char *, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
FILE * _open_memstream_r (struct _reent *, char **, size_t *);
void _perror_r (struct _reent *, const char *);
int _printf_r (struct _reent *, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 2, 3)))
                                                            ;
int _putc_r (struct _reent *, int, FILE *);
int _putc_unlocked_r (struct _reent *, int, FILE *);
int _putchar_unlocked_r (struct _reent *, int);
int _putchar_r (struct _reent *, int);
int _puts_r (struct _reent *, const char *);
int _remove_r (struct _reent *, const char *);
int _rename_r (struct _reent *, const char *_old, const char *_new)
                                          ;
int _scanf_r (struct _reent *, const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 2, 3)))
                                                           ;
int _siprintf_r (struct _reent *, char *, const char *, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _siscanf_r (struct _reent *, const char *, const char *, ...) __attribute__ ((__format__ (__scanf__, 3, 4)))
                                                           ;
int _sniprintf_r (struct _reent *, char *, size_t, const char *, ...) __attribute__ ((__format__ (__printf__, 4, 5)))
                                                            ;
int _snprintf_r (struct _reent *, char *restrict, size_t, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 4, 5)))
                                                            ;
int _sprintf_r (struct _reent *, char *restrict, const char *restrict, ...) __attribute__ ((__format__ (__printf__, 3, 4)))
                                                            ;
int _sscanf_r (struct _reent *, const char *restrict, const char *restrict, ...) __attribute__ ((__format__ (__scanf__, 3, 4)))
                                                           ;
char * _tempnam_r (struct _reent *, const char *, const char *);
FILE * _tmpfile_r (struct _reent *);
char * _tmpnam_r (struct _reent *, char *);
int _ungetc_r (struct _reent *, int, FILE *);
int _vasiprintf_r (struct _reent *, char **, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
char * _vasniprintf_r (struct _reent*, char *, size_t *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 4, 0)))
                                                            ;
char * _vasnprintf_r (struct _reent*, char *, size_t *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 4, 0)))
                                                            ;
int _vasprintf_r (struct _reent *, char **, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vdiprintf_r (struct _reent *, int, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vdprintf_r (struct _reent *, int, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vfiprintf_r (struct _reent *, FILE *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vfiscanf_r (struct _reent *, FILE *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 3, 0)))
                                                           ;
int _vfprintf_r (struct _reent *, FILE *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vfscanf_r (struct _reent *, FILE *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 3, 0)))
                                                           ;
int _viprintf_r (struct _reent *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int _viscanf_r (struct _reent *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int _vprintf_r (struct _reent *, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 2, 0)))
                                                            ;
int _vscanf_r (struct _reent *, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 2, 0)))
                                                           ;
int _vsiprintf_r (struct _reent *, char *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vsiscanf_r (struct _reent *, const char *, const char *, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 3, 0)))
                                                           ;
int _vsniprintf_r (struct _reent *, char *, size_t, const char *, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 4, 0)))
                                                            ;
int _vsnprintf_r (struct _reent *, char *restrict, size_t, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 4, 0)))
                                                            ;
int _vsprintf_r (struct _reent *, char *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__printf__, 3, 0)))
                                                            ;
int _vsscanf_r (struct _reent *, const char *restrict, const char *restrict, __gnuc_va_list) __attribute__ ((__format__ (__scanf__, 3, 0)))
                                                           ;

/* Other extensions.  */

int fpurge (FILE *);
ssize_t __getdelim (char **, size_t *, int, FILE *);
ssize_t __getline (char **, size_t *, FILE *);


void clearerr_unlocked (FILE *);
int feof_unlocked (FILE *);
int ferror_unlocked (FILE *);
int fileno_unlocked (FILE *);
int fflush_unlocked (FILE *);
int fgetc_unlocked (FILE *);
int fputc_unlocked (int, FILE *);
size_t fread_unlocked (void * restrict, size_t _size, size_t _n, FILE *restrict);
size_t fwrite_unlocked (const void * restrict , size_t _size, size_t _n, FILE *);
/*
 * Routines internal to the implementation.
 */

int __srget_r (struct _reent *, FILE *);
int __swbuf_r (struct _reent *, int, FILE *);

/*
 * Stdio function-access interface.
 */
FILE *funopen (const void * __cookie, int (*__readfn)(void * __cookie, char *__buf, int __n), int (*__writefn)(void * __cookie, const char *__buf, int __n), fpos_t (*__seekfn)(void * __cookie, fpos_t __off, int __whence), int (*__closefn)(void * __cookie))





                                   ;
FILE *_funopen_r (struct _reent *, const void * __cookie, int (*__readfn)(void * __cookie, char *__buf, int __n), int (*__writefn)(void * __cookie, const char *__buf, int __n), fpos_t (*__seekfn)(void * __cookie, fpos_t __off, int __whence), int (*__closefn)(void * __cookie))





                                   ;
/*
 * The __sfoo macros are here so that we can 
 * define function versions in the C library.
 */
static __inline__ int __sputc_r(struct _reent *_ptr, int _c, FILE *_p) {




 if (--_p->_w >= 0 || (_p->_w >= _p->_lbfsize && (char)_c != '\n'))
  return (*_p->_p++ = _c);
 else
  return (__swbuf_r(_ptr, _c, _p));
}
/* fast always-buffered version, true iff error */


/*
* Defines for the different tools.
*/
  extern void __VERIFIER_error() __attribute__ ((__noreturn__));
  extern float __VERIFIER_nondet_float();
  extern float __VERIFIER_nondet_double();
void __VERIFIER_precond_reach() {



}




/* This header file provides the reentrancy.  */

/* WARNING: All identifiers here must begin with an underscore.  This file is
   included by stdio.h and others and we therefore must only use identifiers
   in the namespace allotted to us.  */
/* libc/sys/linux/sys/cdefs.h - Helper macros for K&R vs. ANSI C compat. */

/* Written 2000 by Werner Almesberger */

/*-
 * Copyright (c) 1991, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Berkeley Software Design, Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)cdefs.h	8.8 (Berkeley) 1/9/95
 * $FreeBSD$
 */
/* Provide support for both ANSI and non-ANSI environments.  */

/* Some ANSI environments are "broken" in the sense that __STDC__ cannot be
   relied upon to have it's intended meaning.  Therefore we must use our own
   concoction: _HAVE_STDC.  Always use _HAVE_STDC instead of __STDC__ in newlib
   sources!

   To get a strict ANSI C environment, define macro __STRICT_ANSI__.  This will
   "comment out" the non-ANSI parts of the ANSI header files (non-ANSI header
   files aren't affected).  */



/* __dmath, __fmath, and __ldmath are only here for backwards compatibility
 * in case any code used them.  They are no longer used by Newlib, itself,
 * other than legacy.  */
union __dmath
{
  double d;
  __ULong i[2];
};

union __fmath
{
  float f;
  __ULong i[1];
};
/* Natural log of 2 */



 /* gcc >= 3.3 implicitly defines builtins for HUGE_VALx values.  */
/* Reentrant ANSI C functions.  */


extern double atan (double);
extern double cos (double);
extern double sin (double);
extern double tan (double);
extern double tanh (double);
extern double frexp (double, int *);
extern double modf (double, double *);
extern double ceil (double);
extern double fabs (double);
extern double floor (double);


/* Non reentrant ANSI C functions.  */



extern double acos (double);
extern double asin (double);
extern double atan2 (double, double);
extern double cosh (double);
extern double sinh (double);
extern double exp (double);
extern double ldexp (double, int);
extern double log (double);
extern double log10 (double);
extern double pow (double, double);
extern double sqrt (double);
extern double fmod (double, double);




/* ISO C99 types and macros. */

/* FIXME:  FLT_EVAL_METHOD should somehow be gotten from float.h (which is hard,
 * considering that the standard says the includes it defines should not
 * include other includes that it defines) and that value used.  (This can be
 * solved, but autoconf has a bug which makes the solution more difficult, so
 * it has been skipped for now.)  */






    typedef float float_t;
    typedef double double_t;
extern int __isinff (float x);
extern int __isinfd (double x);
extern int __isnanf (float x);
extern int __isnand (double x);
extern int __fpclassifyf (float x);
extern int __fpclassifyd (double x);
extern int __signbitf (float x);
extern int __signbitd (double x);

/* Note: isinf and isnan were once functions in newlib that took double
 *       arguments.  C99 specifies that these names are reserved for macros
 *       supporting multiple floating point types.  Thus, they are
 *       now defined as macros.  Implementations of the old functions
 *       taking double arguments still exist for compatibility purposes
 *       (prototypes for them are in <ieeefp.h>).  */
/* Non ANSI long double precision functions.  */

extern int finitel (long double);

/* Non ANSI double precision functions.  */

extern double infinity (void);
extern double nan (const char *);
extern int finite (double);
extern double copysign (double, double);
extern double logb (double);
extern int ilogb (double);

extern double asinh (double);
extern double cbrt (double);
extern double nextafter (double, double);
extern double rint (double);
extern double scalbn (double, int);

extern double exp2 (double);
extern double scalbln (double, long int);
extern double tgamma (double);
extern double nearbyint (double);
extern long int lrint (double);
extern long long int llrint (double);
extern double round (double);
extern long int lround (double);
extern long long int llround (double);
extern double trunc (double);
extern double remquo (double, double, int *);
extern double fdim (double, double);
extern double fmax (double, double);
extern double fmin (double, double);
extern double fma (double, double, double);


extern double log1p (double);
extern double expm1 (double);



extern double acosh (double);
extern double atanh (double);
extern double remainder (double, double);
extern double gamma (double);
extern double lgamma (double);
extern double erf (double);
extern double erfc (double);
extern double log2 (double);





extern double hypot (double, double);




/* Single precision versions of ANSI functions.  */

extern float atanf (float);
extern float cosf (float);
extern float sinf (float);
extern float tanf (float);
extern float tanhf (float);
extern float frexpf (float, int *);
extern float modff (float, float *);
extern float ceilf (float);
extern float fabsf (float);
extern float floorf (float);


extern float acosf (float);
extern float asinf (float);
extern float atan2f (float, float);
extern float coshf (float);
extern float sinhf (float);
extern float expf (float);
extern float ldexpf (float, int);
extern float logf (float);
extern float log10f (float);
extern float powf (float, float);
extern float sqrtf (float);
extern float fmodf (float, float);


/* Other single precision functions.  */

extern float exp2f (float);
extern float scalblnf (float, long int);
extern float tgammaf (float);
extern float nearbyintf (float);
extern long int lrintf (float);
extern long long int llrintf (float);
extern float roundf (float);
extern long int lroundf (float);
extern long long int llroundf (float);
extern float truncf (float);
extern float remquof (float, float, int *);
extern float fdimf (float, float);
extern float fmaxf (float, float);
extern float fminf (float, float);
extern float fmaf (float, float, float);

extern float infinityf (void);
extern float nanf (const char *);
extern int finitef (float);
extern float copysignf (float, float);
extern float logbf (float);
extern int ilogbf (float);

extern float asinhf (float);
extern float cbrtf (float);
extern float nextafterf (float, float);
extern float rintf (float);
extern float scalbnf (float, int);
extern float log1pf (float);
extern float expm1f (float);


extern float acoshf (float);
extern float atanhf (float);
extern float remainderf (float, float);
extern float gammaf (float);
extern float lgammaf (float);
extern float erff (float);
extern float erfcf (float);
extern float log2f (float);
extern float hypotf (float, float);


/* Newlib doesn't fully support long double math functions so far.
   On platforms where long double equals double the long double functions
   simply call the double functions.  On Cygwin the long double functions
   are implemented independently from newlib to be able to use optimized
   assembler functions despite using the Microsoft x86_64 ABI. */
extern long double hypotl (long double, long double);
extern long double sqrtl (long double);
extern double drem (double, double);
extern float dremf (float, float);



extern double gamma_r (double, int *);
extern double lgamma_r (double, int *);
extern float gammaf_r (float, int *);
extern float lgammaf_r (float, int *);



extern double y0 (double);
extern double y1 (double);
extern double yn (int, double);
extern double j0 (double);
extern double j1 (double);
extern double jn (int, double);



extern float y0f (float);
extern float y1f (float);
extern float ynf (int, float);
extern float j0f (float);
extern float j1f (float);
extern float jnf (int, float);


/* GNU extensions */
/* The gamma functions use a global variable, signgam.  */


extern int *__signgam (void);






/* The exception structure passed to the matherr routine.  */
/* We have a problem when using C++ since `exception' is a reserved
   name in C++.  */



struct exception

{
  int type;
  char *name;
  double arg1;
  double arg2;
  double retval;
  int err;
};




extern int matherr (struct exception *e);


/* Values for the type field of struct exception.  */
/* Useful constants.  */
/* Global control over fdlibm error handling.  */

enum __fdlibm_version
{
  __fdlibm_ieee = -1,
  __fdlibm_svid,
  __fdlibm_xopen,
  __fdlibm_posix
};




extern enum __fdlibm_version __fdlib_version;


/* @(#)fdlibm.h 5.1 93/09/24 */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */

/* REDHAT LOCAL: Include files.  */

/* unified sys/types.h: 
   start with sef's sysvi386 version.
   merge go32 version -- a few ifdefs.
   h8300hms, h8300xray, and sysvnecv70 disagree on the following types:

   typedef int gid_t;
   typedef int uid_t;
   typedef int dev_t;
   typedef int ino_t;
   typedef int mode_t;
   typedef int caddr_t;

   however, these aren't "reasonable" values, the sysvi386 ones make far 
   more sense, and should work sufficiently well (in particular, h8300 
   doesn't have a stat, and the necv70 doesn't matter.) -- eichin
 */

/* REDHAT LOCAL: Default to XOPEN_MODE.  */


/* Most routines need to check whether a float is finite, infinite, or not a
   number, and many need to know whether the result of an operation will
   overflow.  These conditions depend on whether the largest exponent is
   used for NaNs & infinities, or whether it's used for finite numbers.  The
   macros below wrap up that kind of information:

   FLT_UWORD_IS_FINITE(X)
	True if a positive float with bitmask X is finite.

   FLT_UWORD_IS_NAN(X)
	True if a positive float with bitmask X is not a number.

   FLT_UWORD_IS_INFINITE(X)
	True if a positive float with bitmask X is +infinity.

   FLT_UWORD_MAX
	The bitmask of FLT_MAX.

   FLT_UWORD_HALF_MAX
	The bitmask of FLT_MAX/2.

   FLT_UWORD_EXP_MAX
	The bitmask of the largest finite exponent (129 if the largest
	exponent is used for finite numbers, 128 otherwise).

   FLT_UWORD_LOG_MAX
	The bitmask of log(FLT_MAX), rounded down.  This value is the largest
	input that can be passed to exp() without producing overflow.

   FLT_UWORD_LOG_2MAX
	The bitmask of log(2*FLT_MAX), rounded down.  This value is the
	largest input than can be passed to cosh() without producing
	overflow.

   FLT_LARGEST_EXP
	The largest biased exponent that can be used for finite numbers
	(255 if the largest exponent is used for finite numbers, 254
	otherwise) */
/* Many routines check for zero and subnormal numbers.  Such things depend
   on whether the target supports denormals or not:

   FLT_UWORD_IS_ZERO(X)
	True if a positive float with bitmask X is +0.	Without denormals,
	any float with a zero exponent is a +0 representation.	With
	denormals, the only +0 representation is a 0 bitmask.

   FLT_UWORD_IS_SUBNORMAL(X)
	True if a non-zero positive float with bitmask X is subnormal.
	(Routines should check for zeros first.)

   FLT_UWORD_MIN
	The bitmask of the smallest float above +0.  Call this number
	REAL_FLT_MIN...

   FLT_UWORD_EXP_MIN
	The bitmask of the float representation of REAL_FLT_MIN's exponent.

   FLT_UWORD_LOG_MIN
	The bitmask of |log(REAL_FLT_MIN)|, rounding down.

   FLT_SMALLEST_EXP
	REAL_FLT_MIN's exponent - EXP_BIAS (1 if denormals are not supported,
	-22 if they are).
*/
/*
 * set X_TLOSS = pi*2**52, which is possibly defined in <values.h>
 * (one may replace the following line by "#include <values.h>")
 */



/* Functions that are not documented, and are not in <math.h>.  */




extern double scalb (double, double);

extern double significand (double);

extern long double __ieee754_hypotl (long double, long double);

/* ieee style elementary functions */
extern double __ieee754_sqrt (double);
extern double __ieee754_acos (double);
extern double __ieee754_acosh (double);
extern double __ieee754_log (double);
extern double __ieee754_atanh (double);
extern double __ieee754_asin (double);
extern double __ieee754_atan2 (double,double);
extern double __ieee754_exp (double);
extern double __ieee754_cosh (double);
extern double __ieee754_fmod (double,double);
extern double __ieee754_pow (double,double);
extern double __ieee754_lgamma_r (double,int *);
extern double __ieee754_gamma_r (double,int *);
extern double __ieee754_log10 (double);
extern double __ieee754_sinh (double);
extern double __ieee754_hypot (double,double);
extern double __ieee754_j0 (double);
extern double __ieee754_j1 (double);
extern double __ieee754_y0 (double);
extern double __ieee754_y1 (double);
extern double __ieee754_jn (int,double);
extern double __ieee754_yn (int,double);
extern double __ieee754_remainder (double,double);
extern __int32_t __ieee754_rem_pio2 (double,double*);



extern double __ieee754_scalb (double,double);


/* fdlibm kernel function */
extern double __kernel_standard (double,double,int);
extern double __kernel_sin (double,double,int);
extern double __kernel_cos (double,double);
extern double __kernel_tan (double,double,int);
extern int __kernel_rem_pio2 (double*,double*,int,int,int,const __int32_t*);

/* Undocumented float functions.  */



extern float scalbf (float, float);

extern float significandf (float);

/* ieee style elementary float functions */
extern float __ieee754_sqrtf (float);
extern float __ieee754_acosf (float);
extern float __ieee754_acoshf (float);
extern float __ieee754_logf (float);
extern float __ieee754_atanhf (float);
extern float __ieee754_asinf (float);
extern float __ieee754_atan2f (float,float);
extern float __ieee754_expf (float);
extern float __ieee754_coshf (float);
extern float __ieee754_fmodf (float,float);
extern float __ieee754_powf (float,float);
extern float __ieee754_lgammaf_r (float,int *);
extern float __ieee754_gammaf_r (float,int *);
extern float __ieee754_log10f (float);
extern float __ieee754_sinhf (float);
extern float __ieee754_hypotf (float,float);
extern float __ieee754_j0f (float);
extern float __ieee754_j1f (float);
extern float __ieee754_y0f (float);
extern float __ieee754_y1f (float);
extern float __ieee754_jnf (int,float);
extern float __ieee754_ynf (int,float);
extern float __ieee754_remainderf (float,float);
extern __int32_t __ieee754_rem_pio2f (float,float*);



extern float __ieee754_scalbf (float,float);


/* float versions of fdlibm kernel functions */
extern float __kernel_sinf (float,float,int);
extern float __kernel_cosf (float,float);
extern float __kernel_tanf (float,float,int);
extern int __kernel_rem_pio2f (float*,float*,int,int,int,const __int32_t*);

/* The original code used statements like
	n0 = ((*(int*)&one)>>29)^1;		* index of high word *
	ix0 = *(n0+(int*)&x);			* high word of x *
	ix1 = *((1-n0)+(int*)&x);		* low word of x *
   to dig two 32 bit words out of the 64 bit IEEE floating point
   value.  That is non-ANSI, and, moreover, the gcc instruction
   scheduler gets it wrong.  We instead use the following macros.
   Unlike the original code, we determine the endianness at compile
   time, not at run time; I don't see much benefit to selecting
   endianness at run time.  */







/* A union which permits us to convert between a double and two 32 bit
   ints.  */
typedef union
{
  double value;
  struct
  {
    __uint32_t lsw;
    __uint32_t msw;
  } parts;
} ieee_double_shape_type;



/* Get two 32 bit ints from a double.  */
/* Get the more significant 32 bit int from a double.  */
/* Get the less significant 32 bit int from a double.  */
/* Set a double from two 32 bit ints.  */
/* Set the more significant 32 bits of a double from an int.  */
/* Set the less significant 32 bits of a double from an int.  */
/* A union which permits us to convert between a float and a 32 bit
   int.  */

typedef union
{
  float value;
  __uint32_t word;
} ieee_float_shape_type;

/* Get a 32 bit int from a float.  */
/* Set a float from a 32 bit int.  */
/* Macros to avoid undefined behaviour that can arise if the amount
   of a shift is exactly equal to the size of the shifted operand.  */
static const double huge_floor = 1.0e300;

double floor_double(double x) {
 __int32_t i0,i1,j0;
 __uint32_t i,j;
 do { ieee_double_shape_type ew_u; ew_u.value = (x); (i0) = ew_u.parts.msw; (i1) = ew_u.parts.lsw; } while (0);
 j0 = ((i0>>20)&0x7ff)-0x3ff;
 if(j0<20) {
     if(j0<0) {
  if(huge_floor+x>0.0) {
      if(i0>=0) {i0=i1=0;}
      else if(((i0&0x7fffffff)|i1)!=0)
   { i0=0xbff00000;i1=0;}
  }
     } else {
  i = (0x000fffff)>>j0;
  if(((i0&i)|i1)==0) return x;
  if(huge_floor+x>0.0) {
      if(i0<0) i0 += (0x00100000)>>j0;
      i0 &= (~i); i1=0;
  }
     }
 } else if (j0>51) {
     if(j0==0x400) return x+x;
     else return x;
 } else {
     i = ((__uint32_t)(0xffffffff))>>(j0-20);
     if((i1&i)==0) return x;
     if(huge_floor+x>0.0) {
  if(i0<0) {
      if(j0==20) i0+=1;
      else {
   j = i1+(1<<(52-j0));
   if(j<i1) i0 +=1 ;
   i1=j;
      }
  }
  i1 &= (~i);
     }
 }
 do { ieee_double_shape_type iw_u; iw_u.parts.msw = (i0); iw_u.parts.lsw = (i1); (x) = iw_u.value; } while (0);
 return x;
}

/*
* preprocessed newlib functions
*/

// infinity check for doubles
int isinf_double(double x) {
 __int32_t hx,lx;
 do { ieee_double_shape_type ew_u; ew_u.value = (x); (hx) = ew_u.parts.msw; (lx) = ew_u.parts.lsw; } while (0);
 hx &= 0x7fffffff;
 hx |= (__uint32_t)(lx|(-lx))>>31;
 hx = 0x7ff00000 - hx;
 return 1 - (int)((__uint32_t)(hx|(-hx))>>31);
}

// nan check for doubles
int isnan_double(double x) {

    return x != x;
}

int isfinite_double(double x){
__int32_t hx;
do { ieee_double_shape_type gh_u; gh_u.value = (x); (hx) = gh_u.parts.msw; } while (0);
return (int)((__uint32_t)((hx&0x7fffffff)-0x7ff00000)>>31);
}

/*
 * __fpclassify Categorizes floating point value arg into the following categories:
 * zero, subnormal, normal, infinite, NAN, or implementation-defined category.
 * Returns One of FP_INFINITE, FP_NAN, FP_NORMAL, FP_SUBNORMAL, FP_ZERO or implementation-defined type, specifying the category of arg.
 */

int __fpclassify_double (double x) {
  __uint32_t msw, lsw;

  do { ieee_double_shape_type ew_u; ew_u.value = (x); (msw) = ew_u.parts.msw; (lsw) = ew_u.parts.lsw; } while (0);

  if ((msw == 0x00000000 && lsw == 0x00000000) ||
      (msw == 0x80000000 && lsw == 0x00000000))
    return 2;
  else if ((msw >= 0x00100000 && msw <= 0x7fefffff) ||
           (msw >= 0x80100000 && msw <= 0xffefffff))
    return 4;
  else if ((msw >= 0x00000000 && msw <= 0x000fffff) ||
           (msw >= 0x80000000 && msw <= 0x800fffff))

    return 3;
  else if ((msw == 0x7ff00000 && lsw == 0x00000000) ||
           (msw == 0xfff00000 && lsw == 0x00000000))
    return 1;
  else
    return 0;
}

/*
 * returns 1 if x is an integer.
 * returns false for NaNs (NaNs always compare unequal)
 * returns true for +-infinity,
 * floorf does not have the problem with overflowing the integer type used to hold the truncated result, because floorf() returns a float.
 */
int isinteger_double(double x){
  return (floor_double(x) == x);
}
double fabs_double(double x) {
__uint32_t high;
do { ieee_double_shape_type gh_u; gh_u.value = (x); (high) = gh_u.parts.msw; } while (0);
do { ieee_double_shape_type sh_u; sh_u.value = (x); sh_u.parts.msw = (high&0x7fffffff); (x) = sh_u.value; } while (0);
       return x;
}

/*
 * Preprocessed code for the function libs/newlib/math/s_atan.c
 */

 static const double atanhi_atan[] = {
   4.63647609000806093515e-01,
   7.85398163397448278999e-01,
   9.82793723247329054082e-01,
   1.57079632679489655800e+00,
 };


 static const double atanlo_atan[] = {
   2.26987774529616870924e-17,
   3.06161699786838301793e-17,
   1.39033110312309984516e-17,
   6.12323399573676603587e-17,
 };


 static const double aT_atan[] = {
   3.33333333333329318027e-01,
  -1.99999999998764832476e-01,
   1.42857142725034663711e-01,
  -1.11111104054623557880e-01,
   9.09088713343650656196e-02,
  -7.69187620504482999495e-02,
   6.66107313738753120669e-02,
  -5.83357013379057348645e-02,
   4.97687799461593236017e-02,
  -3.65315727442169155270e-02,
   1.62858201153657823623e-02,
 };


static const double one_atan = 1.0,
pi_o_4 = 7.8539816339744827900E-01,
pi_o_2 = 1.5707963267948965580E+00,
pi = 3.1415926535897931160E+00,
 huge_atan = 1.0e300;

double atan_double(double x) {
 double w,s1,s2,z;
 __int32_t ix,hx,id;

 do { ieee_double_shape_type gh_u; gh_u.value = (x); (hx) = gh_u.parts.msw; } while (0);
 ix = hx&0x7fffffff;
 if(ix>=0x44100000) {
     __uint32_t low;
     do { ieee_double_shape_type gl_u; gl_u.value = (x); (low) = gl_u.parts.lsw; } while (0);
     if(ix>0x7ff00000||
  (ix==0x7ff00000&&(low!=0)))
  return x+x;
     if(hx>0) return atanhi_atan[3]+atanlo_atan[3];
     else return -atanhi_atan[3]-atanlo_atan[3];
 } if (ix < 0x3fdc0000) {
     if (ix < 0x3e200000) {
  if(huge_atan+x>one_atan) return x;
     }
     id = -1;
 } else {
 x = fabs_double(x);
 if (ix < 0x3ff30000) {
     if (ix < 0x3fe60000) {
  id = 0; x = (2.0*x-one_atan)/(2.0+x);
     } else {
  id = 1; x = (x-one_atan)/(x+one_atan);
     }
 } else {
     if (ix < 0x40038000) {
  id = 2; x = (x-1.5)/(one_atan+1.5*x);
     } else {
  id = 3; x = -1.0/x;
     }
 }}

 z = x*x;
 w = z*z;

 s1 = z*(aT_atan[0]+w*(aT_atan[2]+w*(aT_atan[4]+w*(aT_atan[6]+w*(aT_atan[8]+w*aT_atan[10])))));
 s2 = w*(aT_atan[1]+w*(aT_atan[3]+w*(aT_atan[5]+w*(aT_atan[7]+w*aT_atan[9]))));
 if (id<0) return x - x*(s1+s2);
 else {
     z = atanhi_atan[id] - ((x*(s1+s2) - atanlo_atan[id]) - x);
     return (hx<0)? -z:z;
 }
}

/*
 * Preprocessed code for the function libs/newlib/math/e_atan2.c (Constants are defined in requrements/includes/math_constants_double.h)
 */

 static const double tiny_atan2 = 1.0e-300,
 zero_atan2 = 0.0,
 pi_lo_atan2 = 1.2246467991473531772E-16;


double __ieee754_atan2(double y, double x) {
  double z;
  __int32_t k,m,hx,hy,ix,iy;
  __uint32_t lx,ly;

  do { ieee_double_shape_type ew_u; ew_u.value = (x); (hx) = ew_u.parts.msw; (lx) = ew_u.parts.lsw; } while (0);
  ix = hx&0x7fffffff;
  do { ieee_double_shape_type ew_u; ew_u.value = (y); (hy) = ew_u.parts.msw; (ly) = ew_u.parts.lsw; } while (0);
  iy = hy&0x7fffffff;
  if(((ix|((lx|-lx)>>31))>0x7ff00000)||
     ((iy|((ly|-ly)>>31))>0x7ff00000))
     return x+y;
  if(((hx-0x3ff00000)|lx)==0) return atan_double(y);
  m = ((hy>>31)&1)|((hx>>30)&2);


  if((iy|ly)==0) {
      switch(m) {
   case 0:
   case 1: return y;
   case 2: return pi+tiny_atan2;
   case 3: return -pi-tiny_atan2;
      }
  }

  if((ix|lx)==0) return (hy<0)? -pi_o_2-tiny_atan2: pi_o_2+tiny_atan2;


  if(ix==0x7ff00000) {
      if(iy==0x7ff00000) {
   switch(m) {
       case 0: return pi_o_4+tiny_atan2;
       case 1: return -pi_o_4-tiny_atan2;
       case 2: return 3.0*pi_o_4+tiny_atan2;
       case 3: return -3.0*pi_o_4-tiny_atan2;
   }
      } else {
   switch(m) {
       case 0: return zero_atan2 ;
       case 1: return -zero_atan2 ;
       case 2: return pi+tiny_atan2 ;
       case 3: return -pi-tiny_atan2 ;
   }
      }
  }

  if(iy==0x7ff00000) return (hy<0)? -pi_o_2-tiny_atan2: pi_o_2+tiny_atan2;


  k = (iy-ix)>>20;
  if(k > 60) z=pi_o_2+0.5*pi_lo_atan2;
  else if(hx<0&&k<-60) z=0.0;
  else z=atan_double(fabs_double(y/x));
  switch (m) {
      case 0: return z ;
      case 1: {
             __uint32_t zh;
         do { ieee_double_shape_type gh_u; gh_u.value = (z); (zh) = gh_u.parts.msw; } while (0);
         do { ieee_double_shape_type sh_u; sh_u.value = (z); sh_u.parts.msw = (zh ^ 0x80000000); (z) = sh_u.value; } while (0);
       }
       return z ;
      case 2: return pi-(z-pi_lo_atan2);
      default:
           return (z-pi_lo_atan2)-pi;
  }
 }


int main()
{

  /* REQ-BL-0663:
   * The atan2 and atan2f procedures shall return pi/2, if the argument y is > 0 and the argument x is +-0
   */

   double x = -0.0;
   double y = __VERIFIER_nondet_double();

   if (y > 0.0) {
     __VERIFIER_precond_reach();

     double res = __ieee754_atan2(y, x);

     // x is -0, y is > 0, the result shall be +pi/2
     if (res != pi_o_2) {
       __VERIFIER_error();
       return 1;
     }
  }
  return 0;
}

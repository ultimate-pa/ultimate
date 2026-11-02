/*
 * Copyright (C) 2026 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/** Models the Linux errno.h error constants as integer literals. */
public class ErrnoLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;

	public ErrnoLibraryModel(final FunctionModelHelper helper) {
		mHelper = helper;
	}

	private ConstantModel constant(final String name, final int value) {
		return new ConstantModel(name, loc -> mHelper.constructIntegerLiteral(loc, BigInteger.valueOf(value),
				new CPrimitive(CPrimitives.INT)));
	}

	@Override
	public Collection<ConstantModel> getConstantModels() {
		// Use the same values as GCC
		return List.of(constant("E2BIG", 7), constant("EACCES", 13), constant("EADDRINUSE", 98),
				constant("EADDRNOTAVAIL", 99), constant("EAFNOSUPPORT", 97), constant("EAGAIN", 11),
				constant("EALREADY", 114), constant("EBADE", 52), constant("EBADF", 9), constant("EBADFD", 77),
				constant("EBADMSG", 74), constant("EBADR", 53), constant("EBADRQC", 56), constant("EBADSLT", 57),
				constant("EBUSY", 16), constant("ECANCELED", 125), constant("ECHILD", 10), constant("ECHRNG", 44),
				constant("ECOMM", 70), constant("ECONNABORTED", 103), constant("ECONNREFUSED", 111),
				constant("ECONNRESET", 104), constant("EDEADLK", 35), constant("EDEADLOCK", 35),
				constant("EDESTADDRREQ", 89), constant("EDOM", 33), constant("EDQUOT", 122), constant("EEXIST", 17),
				constant("EFAULT", 14), constant("EFBIG", 27), constant("EHOSTDOWN", 112),
				constant("EHOSTUNREACH", 113), constant("EHWPOISON", 133), constant("EIDRM", 43),
				constant("EILSEQ", 84), constant("EINPROGRESS", 115), constant("EINTR", 4), constant("EINVAL", 22),
				constant("EIO", 5), constant("EISCONN", 106), constant("EISDIR", 21), constant("EISNAM", 120),
				constant("EKEYEXPIRED", 127), constant("EKEYREJECTED", 129), constant("EKEYREVOKED", 128),
				constant("EL2HLT", 51), constant("EL2NSYNC", 45), constant("EL3HLT", 46), constant("EL3RST", 47),
				constant("ELIBACC", 79), constant("ELIBBAD", 80), constant("ELIBMAX", 82), constant("ELIBSCN", 81),
				constant("ELIBEXEC", 83), constant("ELNRNG", 48), constant("ELOOP", 40), constant("EMEDIUMTYPE", 124),
				constant("EMFILE", 24), constant("EMLINK", 31), constant("EMSGSIZE", 90), constant("EMULTIHOP", 72),
				constant("ENAMETOOLONG", 36), constant("ENETDOWN", 100), constant("ENETRESET", 102),
				constant("ENETUNREACH", 101), constant("ENFILE", 23), constant("ENOANO", 55), constant("ENOBUFS", 105),
				constant("ENODATA", 61), constant("ENODEV", 19), constant("ENOENT", 2), constant("ENOEXEC", 8),
				constant("ENOKEY", 126), constant("ENOLCK", 37), constant("ENOLINK", 67), constant("ENOMEDIUM", 123),
				constant("ENOMEM", 12), constant("ENOMSG", 42), constant("ENONET", 64), constant("ENOPKG", 65),
				constant("ENOPROTOOPT", 92), constant("ENOSPC", 28), constant("ENOSR", 63), constant("ENOSTR", 60),
				constant("ENOSYS", 38), constant("ENOTBLK", 15), constant("ENOTCONN", 107), constant("ENOTDIR", 20),
				constant("ENOTEMPTY", 39), constant("ENOTRECOVERABLE", 131), constant("ENOTSOCK", 88),
				constant("ENOTSUP", 95), constant("ENOTTY", 25), constant("ENOTUNIQ", 76), constant("ENXIO", 6),
				constant("EOPNOTSUPP", 95), constant("EOVERFLOW", 75), constant("EOWNERDEAD", 130),
				constant("EPERM", 1), constant("EPFNOSUPPORT", 96), constant("EPIPE", 32), constant("EPROTO", 71),
				constant("EPROTONOSUPPORT", 93), constant("EPROTOTYPE", 91), constant("ERANGE", 34),
				constant("EREMCHG", 78), constant("EREMOTE", 66), constant("EREMOTEIO", 121), constant("ERESTART", 85),
				constant("ERFKILL", 132), constant("EROFS", 30), constant("ESHUTDOWN", 108), constant("ESPIPE", 29),
				constant("ESOCKTNOSUPPORT", 94), constant("ESRCH", 3), constant("ESTALE", 116),
				constant("ESTRPIPE", 86), constant("ETIME", 62), constant("ETIMEDOUT", 110),
				constant("ETOOMANYREFS", 109), constant("ETXTBSY", 26), constant("EUCLEAN", 117),
				constant("EUNATCH", 49), constant("EUSERS", 87), constant("EWOULDBLOCK", 11), constant("EXDEV", 18),
				constant("EXFULL", 54));
	}
}
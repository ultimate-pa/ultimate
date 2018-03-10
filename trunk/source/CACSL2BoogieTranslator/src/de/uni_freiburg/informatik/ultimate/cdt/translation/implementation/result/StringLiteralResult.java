/*
 * Copyright (C) 2017 Alexander Nutz
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.CStringLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

/**
 * A Result that carries the information for all the possible uses of a C string literal.
 * There are two uses:
 * <li> for initializing an array, then we use the characters of the string directly, the extra char[] field has this
 *  function
 * <li> for modeling C's special (read-only) memory area for string literals; for this we use the ExpressionResult
 *  aspects of this class, where we store the allocation- an write-statements and an RValue that points to the beginning
 *  of that memory area.
 *
 * <p>
 * <br>
 *
 * Overview about the treatment of string literals in C according to the C11 standard:
 * Summary of 6.4.5 for our purposes:
 * <li> String literals have static storage duration. They are stored in their own memory area, writing to that area is
 *  undefined behavior.
 * <li> When a string literal is stored, it is automatically terminated by a '\0'-character (in case it is stored into
 *  a char[], the \0 may be dropped if the char[] is not large enough).
 * <li> The type of a string literal is char[].
 * <li> If a string literal is used for initializing a char[], its contents are copied into the char[]'s memory
 *  location. (An exception to the 'no array assignments'-rule in C.) Assigning a string literal to a char[] outside of
 *  initialization is forbidden.
 * <li> If a string literal is used for initializing, or assigning to, a char*, then the pointer points to the
 *  (read-only) memory location of the string literal afterwards.
 * <li> string literals may or may not be unified (and even overlapped??) in their memory area. This is implementation-
 *  defined. (example: 'char *p = "bla"; char *q = "bla";' after executing this code, p and q may or may not be equal,
 *  depending on the C compiler.)
 *
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StringLiteralResult extends ExpressionResult {

	private final CStringLiteral mStringLiteral;
	private final boolean mOverapproximatesLongStringLiteral;
	private final AuxVarInfo mAuxVarName;

	/**
	 *
	 * Note that a StringLiteralResults need no fields for declarations and statements because the literals have static
	 * storage duration and thus are handled by StaticObjectsHandler.
	 * (whenever a StringLiteralResult is created, the statements and declarations must thus be registered in the
	 *  StaticObjectsHandler)
	 *
	 * @param lrVal
	 * @param overapproxList
	 * @param auxVarName
	 * @param stringLiteral
	 * @param overAppLongLiteral
	 */
	public StringLiteralResult(final LRValue lrVal, final List<Overapprox> overapproxList,
			final AuxVarInfo auxVarName, final CStringLiteral stringLiteral, final boolean overAppLongLiteral) {
		super(Collections.emptyList(), lrVal, Collections.emptyList(), Collections.emptySet(), overapproxList);
		mAuxVarName = auxVarName;
		mStringLiteral = stringLiteral;
		mOverapproximatesLongStringLiteral = overAppLongLiteral;
	}

	public CStringLiteral getLiteralString() {
		return mStringLiteral;
	}

	@Override
	public String toString() {
		return "StringLiteralResult: " + mStringLiteral;
	}

	/**
	 * We overapproximate string literals that are longer than a certain threshold by a nondeterministic value.
	 *
	 * @return true iff the string literal that this StringLiteralResult represents is being overapproximated
	 */
	public boolean overApproximatesLongStringLiteral() {
		return mOverapproximatesLongStringLiteral;
	}

	/**
	 * Returns the name of the auxiliary variable that marks the memory location of the string in our Boogie heap array.
	 * @return
	 */
	public AuxVarInfo getAuxVar() {
		return mAuxVarName;
	}
}

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

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

	private final char[] mString;
	private final boolean mOverapproximatesLongStringLiteral;
	private final AuxVarInfo mAuxVarName;

	/**
	 *
	 * @param stmt
	 * @param lrVal
	 * @param decl
	 * @param auxVars
	 * @param overapproxList
	 * @param auxVarName
	 * @param string
	 * @param overAppLongLiteral
	 */
	public StringLiteralResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overapproxList,
			final AuxVarInfo auxVarName, final char[] string, final boolean overAppLongLiteral) {
		super(stmt, lrVal, decl, auxVars, overapproxList);
		mAuxVarName = auxVarName;
		mString = string;
		mOverapproximatesLongStringLiteral = overAppLongLiteral;
	}

	public char[] getLiteralString() {
		return mString;
	}

	@Override
	public String toString() {
		return "StringLiteralResult: " + Arrays.toString(mString);
	}

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

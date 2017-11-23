package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A Result that carries the information for all the possible uses of a C string literal.
 * There are two uses:
 * <li> for inititalizing an array, then we use the characters of the string directly, the extra char[] field has this
 *  function
 * <li> for modeling C's special (read-only) memory area for string literals; for this we use the ExpressionResult
 *  aspects of this class, where we store the allocation- an write-statements and an RValue that points to the beginning
 *  of that memory area.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StringLiteralResult extends ExpressionResult {

	private final char[] mString;

	public StringLiteralResult(final List<Statement> stmt, final LRValue lrVal, final List<Declaration> decl,
			final Map<VariableDeclaration, ILocation> auxVars, final List<Overapprox> overapproxList,
			final char[] string) {
		super(stmt, lrVal, decl, auxVars, overapproxList);
		mString = string;
	}

	public char[] getLiteralString() {
		return mString;
	}

	@Override
	public String toString() {
		return "StringLiteralResult: " + Arrays.toString(mString);
	}
}

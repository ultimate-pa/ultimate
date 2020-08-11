package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

/**
 * Represents an expression that has an incomplete type. For such an ExpressionResult we forbid getLrValue, but we still
 * allow getCType.
 *
 * Example: Assume, p has been declared as a void pointer. <code>void *p;</code> Now, the expression <code>*p</code> has
 * type void, which is an incomplete type.
 *
 * An expression with an incomplete type has no value, however, it is sometimes used in a sizeof expression.
 *
 * @author nutz@cs.uni-freiburg.de
 */
public class ExpressionWithIncompleteTypeResult extends ExpressionResult {

	public ExpressionWithIncompleteTypeResult(final List<Statement> stmt, final LRValue lrVal,
			final List<Declaration> decl, final Set<AuxVarInfo> auxVars, final List<Overapprox> overapproxList) {
		super(stmt, lrVal, decl, auxVars, overapproxList);

	}

	@Override
	public LRValue getLrValue() {
		throw new UnsupportedOperationException(
				"taking the value of an expression with incomplete type is forbidden " + toString());
	}

	@Override
	public CType getCType() {
		return super.getLrValue().getCType();
	}

}

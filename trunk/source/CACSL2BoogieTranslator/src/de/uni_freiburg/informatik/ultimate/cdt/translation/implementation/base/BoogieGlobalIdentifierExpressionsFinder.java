package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;

/**
 * Looks for all IdentifierExpressions with a global variable inside a given Expression.
 * Note that this will crash if any IdentifierExpression.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class BoogieGlobalIdentifierExpressionsFinder extends BoogieVisitor {

	private final Set<IdentifierExpression> mResult = new LinkedHashSet<>();

	@Override
	protected void visit(final IdentifierExpression idex) {
		if (idex.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
			mResult.add(idex);
		}
		super.visit(idex);
	}

	public Set<IdentifierExpression> getGlobalIdentifierExpressions(final Expression expr) {
		super.processExpression(expr);
		return Collections.unmodifiableSet(mResult);
	}
}
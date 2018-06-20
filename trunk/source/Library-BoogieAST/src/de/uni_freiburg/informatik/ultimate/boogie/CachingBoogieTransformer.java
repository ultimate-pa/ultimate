package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

/**
 * Applies a cache in order to not recompute the result of processExpression, if we already computed the result for the
 * given argument.
 * Caution: The result of this BoogieTransformer is only guaranteed to be the same as BoogieTransformer, if
 * processExpression has no side effects.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CachingBoogieTransformer extends BoogieTransformer {

	Map<Expression, Expression> mCache = new HashMap<>();

	@Override
	protected Expression processExpression(final Expression expr) {
		Expression result = mCache.get(expr);
		if (result == null) {
			result = super.processExpression(expr);
			mCache.put(expr, result);
		}
		return result;
	}


}

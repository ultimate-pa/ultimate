package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;

public class CongruenceDomain implements IDomain {
	private final SymbolicTools mTools;

	public CongruenceDomain(final SymbolicTools tools) {
		mTools = tools;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		return widen(lhs, rhs);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		return mTools.top();
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		final ResultForAlteredInputs result = new ResultForAlteredInputs(mTools.top(), mTools.bottom());
		result.mResult = false;
		result.mAbstracted = true;
		return result;
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		final ResultForAlteredInputs result = new ResultForAlteredInputs(mTools.top(), mTools.top());
		result.mResult = true;
		result.mAbstracted = true;
		return result;
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		return pred;
	}
}
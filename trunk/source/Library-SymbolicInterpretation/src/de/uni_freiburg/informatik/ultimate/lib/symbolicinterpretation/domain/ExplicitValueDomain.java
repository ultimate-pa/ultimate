package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class ExplicitValueDomain implements IDomain {

	private PredicateUtils mPredicateUtils;

	public ExplicitValueDomain(final PredicateUtils predicateUtils) {
		mPredicateUtils = predicateUtils;
	}

	@Override
	public IPredicate join(IPredicate first, IPredicate second) {
		// TODO decide whether or not to use simplification or use a setting
		final boolean simplifyDDA = true;
		return mPredicateUtils.getFactory().or(simplifyDDA, first, second);
	}

	@Override
	public IPredicate widen(IPredicate old, IPredicate widenWith) {
		// TODO implement non-trivial version
		return mPredicateUtils.top();
	}

	@Override
	public boolean isBottom(IPredicate pred) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isSubsetEq(IPredicate subset, IPredicate superset) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IPredicate alpha(IPredicate pred) {
		// TODO Auto-generated method stub
		return null;
	}

}

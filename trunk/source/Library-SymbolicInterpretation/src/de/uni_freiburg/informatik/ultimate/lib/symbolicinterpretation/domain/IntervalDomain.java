package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class IntervalDomain implements IDomain {

	private final SymbolicTools mTools;
	private final IUltimateServiceProvider mServices;

	public IntervalDomain(final IUltimateServiceProvider services, final SymbolicTools tools) {
		mTools = tools;
		mServices = services;
	}
	@Override
	public IPredicate join(final IPredicate first, final IPredicate second) {
		// TODO Auto-generated method stub
		return mTools.or(first, second);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO Auto-generated method stub
		return mTools.top();
	}

	@Override
	public boolean isBottom(final IPredicate pred) {
		// TODO do not use SMT solver
		return mTools.isFalse(pred);
	}

	@Override
	public boolean isSubsetEq(final IPredicate subset, final IPredicate superset) {
		// TODO do not use SMT solver
		return mTools.implies(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		// TODO consider using QuantifierPusher to push quantifiers as inward as possible
		final Term dnf = SmtUtils.toDnf(mServices, mTools.getManagedScript(), pred.getFormula(),
				SmtUtils.XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final DnfToExplicitValue rewriter = new DnfToExplicitValue(mServices, mTools);
		final Term[] rewrittenDisjuncts = Arrays.stream(SmtUtils.getDisjuncts(dnf))
				.map(rewriter::transform)
				.toArray(Term[]::new);
		//return mTools.or(joinAccordingToMax(rewrittenDisjuncts));
		// TODO return value
		return null;
	}

}

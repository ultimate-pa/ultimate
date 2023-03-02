package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.RewriteEqualityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class OctagonDomain extends AbstractStateBasedDomain<OctagonState> {

	public OctagonDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		super(logger, tools, maxDisjuncts, timeout);
	}

	@Override
	public OctagonState toState(final Term[] conjuncts) {
		return OctagonState.from(conjuncts, mTools.getScript());
	}

	@Override
	public OctagonState getTopState() {
		return OctagonState.TOP;
	}

	@Override
	protected Term transformTerm(final Term term) {
		// TODO consider removing boolean sub-terms before computing DNF as we don't use the boolean terms anyways
		return new RewriteEqualityTransformer(mTools.getScript()).transform(term);
	}
}

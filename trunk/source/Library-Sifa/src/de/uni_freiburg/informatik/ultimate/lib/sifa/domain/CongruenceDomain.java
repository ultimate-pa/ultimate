package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class CongruenceDomain extends StateBasedDomain<CongruenceState> {

	public CongruenceDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new CongruenceStateProvider());
		// TODO Auto-generated constructor stub
	}

	private static class CongruenceStateProvider implements IStateProvider<CongruenceState> {

		@Override
		public CongruenceState toState(final Term[] conjuncts) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CongruenceState getTopState() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Term preprocessTerm(final Term term) {
			// TODO Auto-generated method stub
			return term;
		}

	}

}
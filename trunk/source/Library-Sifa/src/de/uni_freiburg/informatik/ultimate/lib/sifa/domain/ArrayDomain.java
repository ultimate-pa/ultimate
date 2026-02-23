package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class ArrayDomain extends StateBasedDomain<ArrayState> {

	public ArrayDomain(final SymbolicTools tools, final int maxDisjuncts, final ILogger logger,
			final Supplier<IProgressAwareTimer> timeout) {
		super(tools, maxDisjuncts, logger, timeout, new ArrayStateProvider());
		// TODO Auto-generated constructor stub
	}

	private static class ArrayStateProvider implements IStateProvider<ArrayState> {

		@Override
		public ArrayState toState(final Term[] conjuncts) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public ArrayState getTopState() {
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
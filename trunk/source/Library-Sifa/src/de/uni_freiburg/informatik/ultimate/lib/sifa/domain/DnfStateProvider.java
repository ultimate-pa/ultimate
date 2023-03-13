/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StateBasedDomain.IStateProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Implements an {@link IStateProvider} that uses a DNF representation of the predicates.
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The abstract state that is used internally
 */
public class DnfStateProvider<STATE extends IAbstractState<STATE>> implements IStateProvider<STATE> {
	private final IConjunctiveStateProvider<STATE> mConjunctiveStateProvider;
	private final SymbolicTools mTools;
	private final ILogger mLogger;
	private final Supplier<IProgressAwareTimer> mTimeout;

	public DnfStateProvider(final IConjunctiveStateProvider<STATE> conjunctiveStateProvider, final SymbolicTools tools,
			final ILogger logger, final Supplier<IProgressAwareTimer> timeout) {
		mConjunctiveStateProvider = conjunctiveStateProvider;
		mTools = tools;
		mLogger = logger;
		mTimeout = timeout;
	}

	@Override
	public List<STATE> toStates(final IPredicate pred) {
		final IProgressAwareTimer timer = mTimeout.get();
		final Term[] disjuncts = mTools.dnfDisjuncts(pred, mConjunctiveStateProvider::preprocessTerm);
		final List<STATE> result = new ArrayList<>(disjuncts.length);
		for (final Term dnfDisjunct : disjuncts) {
			if (!timer.continueProcessing()) {
				mLogger.warn(getClass().getSimpleName()
						+ " alpha timed out before all disjuncts were processed. Continuing with top.");
				return List.of(mConjunctiveStateProvider.getTopState());
			}
			if (SmtUtils.isFalseLiteral(dnfDisjunct)) {
				continue;
			}
			final STATE state = mConjunctiveStateProvider.toState(SmtUtils.getConjuncts(dnfDisjunct));
			if (!state.isBottom()) {
				result.add(state);
			}
		}
		return result;
	}

	public interface IConjunctiveStateProvider<STATE extends IAbstractState<STATE>> {
		/**
		 * Returns the internal state representation for the given conjuncts.
		 */
		STATE toState(Term[] conjuncts);

		/**
		 * Returns the internal state that that represents top.
		 */
		STATE getTopState();

		/**
		 * Transformations that are applied before converting the DNF to improve the states that are produced from the
		 * DNF. This method has to return an overapproximation of {@code term}.
		 */
		Term preprocessTerm(final Term term);
	}
}

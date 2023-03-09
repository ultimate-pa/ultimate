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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Abstract class for an {@link IDomain} that uses states and a DNF representation of the predicates. The class uses the
 * method {@code toState} to convert a conjunction to an abstract state.
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The abstract state that is used internally
 */
public abstract class StateBasedDomainWithDnf<STATE extends IAbstractState<STATE>> extends StateBasedDomain<STATE> {
	public StateBasedDomainWithDnf(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		super(logger, tools, maxDisjuncts, timeout);
	}

	@Override
	protected List<STATE> toStates(final IPredicate pred) {
		final IProgressAwareTimer timer = mTimeout.get();
		final Term[] disjuncts = mTools.dnfDisjuncts(pred, this::transformTerm);
		final List<STATE> result = new ArrayList<>(disjuncts.length);
		for (final Term dnfDisjunct : disjuncts) {
			if (!timer.continueProcessing()) {
				mLogger.warn(getClass().getSimpleName()
						+ " alpha timed out before all disjuncts were processed. Continuing with top.");
				return List.of(getTopState());
			}
			if (SmtUtils.isFalseLiteral(dnfDisjunct)) {
				continue;
			}
			final STATE state = toState(SmtUtils.getConjuncts(dnfDisjunct));
			if (!state.isBottom()) {
				result.add(state);
			}
		}
		// TODO join disjuncts if there are too many of them
		return result;
	}

	/**
	 * Transformations that are applied before converting the DNF to improve the states that are produced from the DNF.
	 * This method has to return an overapproximation of {@code term}.
	 */
	protected Term transformTerm(final Term term) {
		return term;
	}

	/**
	 * Returns the internal state representation for the given conjuncts.
	 */
	protected abstract STATE toState(Term[] conjuncts);

	/**
	 * Returns the internal state that that represents top.
	 */
	protected abstract STATE getTopState();
}

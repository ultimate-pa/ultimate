/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Given a nested word automaton, implementing classes computes a binary relation over the states where pairs of states
 * {@code (p, q)} have been removed if clearly {@code q} does not <i>x-simulate</i> {@code p} according to some
 * definition of <i>x-simulation</i>. The exception is that reflexive pairs are always omitted but should always be
 * present.
 * <p>
 * <i>x-simulation</i> can be either <i>bisimulation</i> or <i>simulation</i>.
 * <p>
 * The result is in general only an overapproximation (if one adds the reflexive pairs) of such an <i>x-simulation</i>
 * even for finite automata in the presence of nondeterminism. Hence implementing classes are typically used for
 * preprocessing purposes only.
 * <p>
 * This class supports ordinary and direct <i>x-simulation</i>. See the implementing classes for more information.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <T>
 *            type of data structure in the result
 * @see NwaApproximateSimulation
 */
public abstract class NwaApproximateXsimulation<LETTER, STATE, T> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	protected final INestedWordAutomaton<LETTER, STATE> mOperand;

	/**
	 * Type of simulation that should be approximated.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum SimulationType {
		/**
		 * Ordinary simulation.
		 */
		ORDINARY,
		/**
		 * Direct simulation.
		 */
		DIRECT
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @param operand
	 *            operand
	 */
	public NwaApproximateXsimulation(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
	}

	/**
	 * @return The resulting set of pairs.
	 */
	public abstract ISetOfPairs<STATE, T> getResult();

	protected final void run(final SimulationType simulationType, final boolean separateByTransitionConstraints)
			throws AutomataOperationCanceledException {
		initialize(simulationType);

		/*
		 * TODO Christian 2017-03-23 This method is optional if the flag 'separateByTransitionConstraints' is false.
		 *      We should evaluate whether in this case it has positive or negative performance impact.
		 *      If it has negative impact, we should only call it if the flag is true.
		 */
		separateByDifferentSymbols();

		if (separateByTransitionConstraints) {
			separateByTransitionConstraints();
		}
	}

	protected final void initialize(final SimulationType simulationType) throws AutomataOperationCanceledException {
		switch (simulationType) {
			case ORDINARY:
				initializeAllNonreflexivePairs();
				break;
			case DIRECT:
				initializeAllNonreflexivePairsRespectingAcceptance();
				break;
			default:
				throw new IllegalArgumentException("Unknown simulation type: " + simulationType);
		}
	}

	protected abstract void initializeAllNonreflexivePairs() throws AutomataOperationCanceledException;

	protected abstract void initializeAllNonreflexivePairsRespectingAcceptance()
			throws AutomataOperationCanceledException;

	protected abstract void separateByDifferentSymbols() throws AutomataOperationCanceledException;

	protected abstract void separateByTransitionConstraints() throws AutomataOperationCanceledException;

	protected final List<LETTER> getCommonIncomingLetters(final STATE lhs, final STATE rhs,
			final Function<STATE, Set<LETTER>> letterProvider) {
		final Set<LETTER> lhsLetters = letterProvider.apply(lhs);
		final List<LETTER> commonLetters = new ArrayList<>(lhsLetters.size());
		for (final LETTER letter : letterProvider.apply(rhs)) {
			if (lhsLetters.contains(letter)) {
				commonLetters.add(letter);
			}
		}
		return commonLetters;
	}
}

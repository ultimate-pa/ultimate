/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSO Library package.
 *
 * The ULTIMATE MSO Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSO Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSO Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSO Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSO Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment Class.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODAutomataOperations {

	/**
	 * Constructs an empty automaton.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> emptyAutomaton(final AutomataLibraryServices services) {

		final Set<MSODAlphabetSymbol> alphabet = new HashSet<>();
		final VpAlphabet<MSODAlphabetSymbol> vpAlphabet = new VpAlphabet<>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<>(services, vpAlphabet, stringFactory);
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing represents an Int variable.
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> intVariableAutomaton(final AutomataLibraryServices services,
			final Term x) {

		if (!MSODUtils.isIntVariable(x)) {
			throw new IllegalArgumentException("Input x must be an Int variable.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbols = MSODUtils.createAlphabet(x);
		automaton.getAlphabet().addAll(symbols.values());

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");

		automaton.addInternalTransition("init", symbols.get("x0"), "init");
		automaton.addInternalTransition("init", symbols.get("x1"), "final");
		automaton.addInternalTransition("final", symbols.get("x0"), "final");

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing a copy of the given automaton with the extended or reduced
	 * alphabet.
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> reconstruct(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result;

		result = emptyAutomaton(services);
		result.getAlphabet().addAll(alphabet);

		for (final String state : automaton.getStates()) {
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
		}

		for (final String state : automaton.getStates()) {

			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state)) {

				final Iterator<MSODAlphabetSymbol> itMatches =
						isExtended ? alphabet.stream().filter(e -> e.contains(transition.getLetter())).iterator()
								: alphabet.stream().filter(e -> transition.getLetter().contains(e)).iterator();

				while (itMatches.hasNext()) {
					result.addInternalTransition(state, itMatches.next(), transition.getSucc());
				}
			}
		}

		return result;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that represents the MSOD-complement of the two given automata. The
	 * MSOD-complement performs the complement of two automata and additionally ensures that Integer variables are
	 * represented correctly in the resulting automaton.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Complement} or {@link BuchiComplementFKV} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents the MSOD-union of the two given automata. The MSOD-union
	 * performs the union of two automata and additionally ensures that Integer variables are represented correctly in
	 * the resulting automaton.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> union(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new Union<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		result = minimize(services, result);

		if (result.getAlphabet().isEmpty()) {
			return result;
		}

		// Find all Int variables contained in the alphabet.
		final Set<Term> intVars = result.getAlphabet().iterator().next().containsSort(SmtSortUtils.INT_SORT);

		// Intersect with an automaton that ensures that each Int variable is represented correctly.
		for (final Term intVar : intVars) {
			INestedWordAutomaton<MSODAlphabetSymbol, String> varAutomaton;
			varAutomaton = intVariableAutomaton(services, intVar);
			varAutomaton = reconstruct(services, varAutomaton, result.getAlphabet(), true);

			result = intersect(services, result, varAutomaton);
		}

		return result;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that represents the intersection of the two given automata.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect} or {@link BuchiIntersect} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a possibly minimized version of the given automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> minimize(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataOperationCanceledException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new MinimizeSevpa<>(services, new MSODStringFactory(), automaton).getResult();

		return result;
	}

	/**
	 * Returns an automaton where additionally the given states are made final.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if construction of {@link NestedWordAutomatonReachableStates} fails.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> makeStatesFinal(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<String> states)
			throws AutomataOperationCanceledException {

		NestedWordAutomatonReachableStates<MSODAlphabetSymbol, String> nwaReachableStates;
		nwaReachableStates = new NestedWordAutomatonReachableStates<>(services, automaton);

		final Set<String> finals = new HashSet<>(automaton.getFinalStates());
		finals.addAll(states);

		return new NestedWordAutomatonFilteredStates<>(services, nwaReachableStates, automaton.getStates(),
				automaton.getInitialStates(), finals);
	}
}

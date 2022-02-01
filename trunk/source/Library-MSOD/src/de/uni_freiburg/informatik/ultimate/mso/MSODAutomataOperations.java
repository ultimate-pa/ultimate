/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSOD Library package.
 *
 * The ULTIMATE MSOD Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSOD Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSOD Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSOD Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSOD Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class provides methods to manipulate automata that correspond to MSOD-Formulas.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODAutomataOperations {

	/**
	 * Returns an empty {@link NestedWordAutomaton}.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			emptyAutomaton(final AutomataLibraryServices services) {

		return new NestedWordAutomaton<>(services, new VpAlphabet<>(new HashSet<>()), new MSODStringFactory());
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that is the projection of the given automaton onto the given alphabet.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 */
	public static INestedWordAutomaton<MSODAlphabetSymbol, String> project(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) throws AutomataLibraryException {

		alphabet.containsAll(automaton.getAlphabet());

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result = emptyAutomaton(services);
		result.getAlphabet().addAll(alphabet);

		for (final String state : automaton.getStates()) {
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
		}

		for (final String state : automaton.getStates()) {
			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state)) {

				if (isExtended) {
					alphabet.stream().filter(e -> e.contains(transition.getLetter()))
							.forEach(e -> result.addInternalTransition(state, e, transition.getSucc()));
				}

				if (!isExtended) {
					alphabet.stream().filter(e -> transition.getLetter().contains(e))
							.forEach(e -> result.addInternalTransition(state, e, transition.getSucc()));
				}
			}
		}

		return new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();
	}

	/**
	 * Returns an {@link INestedWordAutomaton} extended automaton that additionally accepts a word "w" if the word
	 * "w∘symbol" is accepted in the given automaton.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 */
	public static INestedWordAutomaton<MSODAlphabetSymbol, String> saturate(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final MSODAlphabetSymbol symbol)
			throws AutomataLibraryException {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result =
				(NestedWordAutomaton<MSODAlphabetSymbol, String>) automaton;

		final Set<IncomingInternalTransition<MSODAlphabetSymbol, String>> transitions = new HashSet<>();
		final Deque<String> queue = new ArrayDeque<>(result.getFinalStates());
		final Set<String> visited = new HashSet<>();
		boolean isInitial = false;

		while (!queue.isEmpty()) {
			final String state = queue.pop();

			for (final String pred : MSODUtils.hierarchicalPredecessorsIncoming(result, state, symbol)) {

				if (!visited.add(state)) {
					continue;
				}

				isInitial = isInitial || result.isInitial(pred);
				result.internalPredecessors(pred).forEach(a -> transitions.add(a));
				queue.add(pred);
			}
		}

		final String state = ((MSODStringFactory) result.getStateFactory()).newString();
		result.addState(isInitial, true, state);

		for (final IncomingInternalTransition<MSODAlphabetSymbol, String> transition : transitions) {
			result.addInternalTransition(transition.getPred(), transition.getLetter(), state);
		}

		return new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents an Int variable.
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			intVariableAutomaton(final AutomataLibraryServices services, final Term x) {

		if (!MSODUtils.isIntConstantOrTermVariable(x)) {
			throw new IllegalArgumentException("Input x must be an Int variable.");
		}

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");

		automaton.addInternalTransition("init", x0, "init");
		automaton.addInternalTransition("init", x1, "final");
		automaton.addInternalTransition("final", x0, "final");

		return automaton;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that is the given automaton intersected with automata that ensure that
	 * that Int variables are matched to exactly one value.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect}, {@link BuchiIntersect} fails.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 *
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> fixIntVariables(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = automaton;

		if (!result.getAlphabet().isEmpty()) {
			// Find all Int variables in the alphabet.
			final Set<Term> intVariables = result.getAlphabet().iterator().next().containsSort(SmtSortUtils.INT_SORT);

			// Intersect with an automata that ensure that Int variables are matched to exactly one value.
			for (final Term intVariable : intVariables) {
				INestedWordAutomaton<MSODAlphabetSymbol, String> variableAutomaton =
						intVariableAutomaton(services, intVariable);

				variableAutomaton = project(services, variableAutomaton, result.getAlphabet(), true);
				result = intersect(services, result, variableAutomaton);
			}
		}

		return result;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that is the MSOD-union of the two given automata. The MSOD-union performs
	 * the union of two automata and additionally ensures that Integer variables are represented correctly in the
	 * resulting automaton.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Intersect}, {@link BuchiIntersect} fails.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 */
	public INestedWordAutomaton<MSODAlphabetSymbol, String> union(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new Union<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		result = fixIntVariables(services, result);

		return new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that is the MSOD-Complement of the given automaton. The MSOD-Complement
	 * performs the {@link Complement} and additionally ensures that integer variables are represented correctly.
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that is the intersection of the two given automata.
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException;

	/**
	 * Returns a {@link NestedLassoWord} accepted by the given automaton, or null if language of automaton is empty. In
	 * case of finite automata the loop is an empty {@link NestedWord}.
	 */
	public abstract NestedLassoWord<MSODAlphabetSymbol> getWord(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException;
}

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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;

/**
 * This class provides methods to manipulate Büchi automata that correspond to MSOD-Formulas.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODAutomataOperationsBuchi extends MSODAutomataOperations {

	/**
	 * @throws AutomataLibraryException
	 *             if construction of {@link BuchiComplementFKV} fails.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link BuchiIntersect} fails.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> complement(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result = null;

		// TODO: Remove if {@link BuchiComplementFKV} supports automaton with empty set of states.
		if (automaton.getStates().isEmpty()) {
			result = new Complement<>(services, new MSODStringFactory(), automaton).getResult();
		} else {
			result = new BuchiComplementFKV<>(services, new MSODStringFactory(), automaton).getResult();
		}

		result = fixIntVariables(services, result);

		return new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();
	}

	/**
	 * @throws AutomataLibraryException
	 *             if construction of {@link BuchiIntersect} fails.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if minimization is canceled.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> intersect(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton1,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton2) throws AutomataLibraryException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> result =
				new BuchiIntersect<>(services, new MSODStringFactory(), automaton1, automaton2).getResult();

		return new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();
	}

	/**
	 * @throws AutomataLibraryException
	 *             if {@link BuchiIsEmpty} fails.
	 */
	@Override
	public NestedLassoWord<MSODAlphabetSymbol> getWord(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton)
			throws AutomataOperationCanceledException {

		final NestedLassoRun<MSODAlphabetSymbol, String> run =
				(new BuchiIsEmpty<>(services, automaton)).getAcceptingNestedLassoRun();

		return run != null ? run.getNestedLassoWord() : null;
	}
}

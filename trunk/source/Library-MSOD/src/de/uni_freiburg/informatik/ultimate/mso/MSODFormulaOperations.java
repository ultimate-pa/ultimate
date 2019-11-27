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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class provides methods to construct automata that correspond to a given MSOD-Formula.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public abstract class MSODFormulaOperations {

	/**
	 * Returns an empty {@link NestedWordAutomaton}.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			emptyAutomaton(final AutomataLibraryServices services) {

		return new NestedWordAutomaton<>(services, new VpAlphabet<>(new HashSet<>()), new MSODStringFactory());
	}

	/**
	 * Returns an {@link NestedWordAutomaton} that represents "true".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			trueAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Returns an {@link NestedWordAutomaton} that represents "false".
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String>
			falseAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "x-y < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
					throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict inequality of the form "-x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a strict subset relation of the form "X ⊊ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents a subset relation of the form "X ⊆ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			subsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Returns an {@link INestedWordAutomaton} that represents an element relation of the form "x+c ∈ Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			elementAutomaton(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException;

	/**
	 * Returns an {@link INestedWordAutomaton} that represents an element relation of the form "c ∈ X".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x);

	/**
	 * Returns integer value that corresponds to the given index.
	 */
	public abstract int indexToInteger(final int index);
}
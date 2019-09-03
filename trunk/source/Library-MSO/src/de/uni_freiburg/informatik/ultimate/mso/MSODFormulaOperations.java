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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class MSODFormulaOperations {

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
	 * Constructs an automaton that represents "true".
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> trueAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "false".
	 */
	public NestedWordAutomaton<MSODAlphabetSymbol, String> falseAutomaton(final AutomataLibraryServices services) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol symbol = new MSODAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Constructs an automaton that represents "x-y < c".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
					throws AutomataLibraryException;

	/**
	 * Constructs an automaton that represents "-x < c".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c);

	/**
	 * Constructs an automaton that represents "X strictSubsetInt Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Constructs an automaton that represents "X subsetInt Y".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			subsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y);

	/**
	 * Constructs an automaton that represents "x+c element Y".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			elementAutomaton(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException;

	/**
	 * Constructs an automaton that represents "c element X".
	 */
	public abstract INestedWordAutomaton<MSODAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x);
}
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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class provides methods to construct automata that correspond to a given MSOD-Formula over the set of natural
 * numbers.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODFormulaOperationsNat extends MSODFormulaOperations {

	/**
	 * @throws IllegalArgumentException
	 *             if x is not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c) {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");
		}

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		if (c.signum() != 1) {
			return automaton;
		}

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");

		String pred = "init";
		for (int i = 0; i < cInt - 1; i++) {
			final String state = "c" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, x1, "final");
			automaton.addInternalTransition(pred, x0, state);
			pred = state;
		}
		automaton.addInternalTransition(pred, x1, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational c) {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || !MSODUtils.isIntConstantOrTermVariable(y) || c.isNegative()) {
			throw new IllegalArgumentException("Input x, y must be Int variables and c must be >= 0.");
		}

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s0");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy10, "s0");
		automaton.addInternalTransition("s0", xy00, "s0");
		automaton.addInternalTransition("s0", xy01, "final");
		automaton.addInternalTransition("final", xy00, "final");

		if (cInt == 0) {
			return automaton;
		}

		automaton.addInternalTransition("init", xy11, "final");

		if (cInt == 1) {
			return automaton;
		}

		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", xy01, "s1");

		String pred = "s1";
		for (int i = 0; i < cInt - 2; i++) {
			final String state = "c" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, xy00, state);
			automaton.addInternalTransition(pred, xy10, "final");
			pred = state;
		}
		automaton.addInternalTransition(pred, xy10, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x is not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");
		}

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");

		String pred = "init";
		if (c.signum() == 0) {
			automaton.addState(false, false, "s0");
			automaton.addInternalTransition("init", x0, "s0");
			automaton.addInternalTransition("s0", x0, "s0");
			pred = "s0";
		} else {
			automaton.addInternalTransition("init", x0, "init");
		}
		automaton.addInternalTransition(pred, x1, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictSubsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntConstantOrTermVariable(x) || !MSODUtils.isSetOfIntConstantOrTermVariable(y)) {
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");
		}

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy11, "init");
		automaton.addInternalTransition("init", xy01, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");
		automaton.addInternalTransition("final", xy11, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> subsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntConstantOrTermVariable(x) || !MSODUtils.isSetOfIntConstantOrTermVariable(y)) {
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");
		}

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy01, "init");
		automaton.addInternalTransition("init", xy11, "init");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int, SetOfInt or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c, final Term y) {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || !MSODUtils.isSetOfIntConstantOrTermVariable(y)
				|| c.isNegative()) {
			throw new IllegalArgumentException("Input x, y must be Int, SetOfInt variables and c must be >= 0.");
		}

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy01, "init");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		if (c.signum() == 0) {
			automaton.addInternalTransition("init", xy11, "final");
			return automaton;
		}

		automaton.addState(false, false, "s0");
		automaton.addInternalTransition("init", xy10, "s0");
		automaton.addInternalTransition("init", xy11, "s0");

		String pred = "s0";
		for (int i = 0; i < cInt - 1; i++) {
			final String state = "c" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, xy00, state);
			automaton.addInternalTransition(pred, xy01, state);
			pred = state;
		}
		automaton.addInternalTransition(pred, xy01, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> constElementAutomaton(final AutomataLibraryServices services,
			final Rational c, final Term x) {

		if (!MSODUtils.isSetOfIntConstantOrTermVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be a SetOfInt variable and c must be >= 0.");
		}
		final int cInt = SmtUtils.toInt(c).intValueExact();
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");
		automaton.addInternalTransition("final", x1, "final");

		String pred = "init";
		for (int i = 0; i < cInt; i++) {
			final String state = "c" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, x0, state);
			automaton.addInternalTransition(pred, x1, state);
			pred = state;
		}
		automaton.addInternalTransition(pred, x1, "final");

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if index is less than 0.
	 */
	@Override
	public int indexToInteger(final int index) {
		if (index < 0) {
			throw new IllegalArgumentException("Index must be >= 0.");
		}

		return index;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if length is less than 0.
	 */
	@Override
	public Pair<Integer, Integer> stemBounds(final int length) {
		if (length < 0) {
			throw new IllegalArgumentException("Length must be >= 0.");
		}

		return new Pair<>(-1, indexToInteger(length));
	}
}

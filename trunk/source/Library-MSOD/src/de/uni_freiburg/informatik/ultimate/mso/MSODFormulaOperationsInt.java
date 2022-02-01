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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Determinize;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class provides methods to construct automata that correspond to a given MSOD-Formula over the set of integer
 * numbers.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODFormulaOperationsInt extends MSODFormulaOperations {

	/**
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational constant) {

		if (!MSODUtils.isIntConstantOrTermVariable(x)) {
			throw new IllegalArgumentException("Input x must be an Int variable.");
		}

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");

		if (c <= 0) {
			automaton.addState(false, false, "s0");
			automaton.addInternalTransition("init", x0, "s0");

			String pred = "s0";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				pred = state;
			}
			automaton.addInternalTransition(pred, x1, "final");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition(pred, x0, "s1");
			automaton.addInternalTransition("s1", x0, pred);

		}

		if (c > 0) {
			automaton.addInternalTransition("init", x1, "final");

			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				automaton.addInternalTransition(state, x1, "final");
				pred = state;
			}

			automaton.addState(false, false, "s0");
			automaton.addInternalTransition(pred, x0, "s0");
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("s0", x0, "s1");
			automaton.addInternalTransition("s0", x1, "final");
			automaton.addInternalTransition("s1", x0, "s0");
		}

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational constant) throws AutomataLibraryException {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || !MSODUtils.isIntConstantOrTermVariable(y)) {
			throw new IllegalArgumentException("Input x, y must be Int variables.");
		}

		INestedWordAutomaton<MSODAlphabetSymbol, String> automaton =
				strictIneqAtomatonPartOne(services, x, y, constant);

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				strictIneqAtomatonPartTwo(services, x, y, constant)).getResult();

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				strictIneqAtomatonPartThree(services, x, y, constant)).getResult();

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				strictIneqAtomatonPartFour(services, x, y, constant)).getResult();

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #strictIneqAutomaton(AutomataLibraryServices, Term, Term, Rational)}. Part: x >= 0 and y >= 0.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartOne(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational constant) {

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");

		automaton.addState(false, false, "s0");
		automaton.addState(false, false, "s1");
		automaton.addState(false, false, "s2");
		automaton.addState(false, false, "s3");
		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("s0", xy00, "init");
		automaton.addInternalTransition("init", xy10, "s1");
		automaton.addInternalTransition("s1", xy00, "s2");

		if (c <= 0) {
			String pred = "s2";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				pred = state;
			}
			automaton.addInternalTransition(pred, xy00, "s3");
			automaton.addInternalTransition("s3", xy00, pred);
			automaton.addInternalTransition(pred, xy01, "final");
		}

		if (c > 0) {
			automaton.addInternalTransition("s2", xy00, "s3");
			automaton.addInternalTransition("s3", xy00, "s2");
			// automaton.addState(false, false, "c1");
			automaton.addInternalTransition("init", xy11, "final");
			automaton.addInternalTransition("s2", xy01, "final");
			// automaton.addInternalTransition("c1", xy10, "final");

			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c_" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, i == 0 ? xy01 : xy00, state);

				if (i % 2 == 1) {
					automaton.addInternalTransition(state, xy10, "final");
				}
				pred = state;
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #strictIneqAutomaton(AutomataLibraryServices, Term, Term, Rational)}. Part: x < 0 and y < 0.
	 */

	private static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartTwo(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational constant) {

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");

		automaton.addState(false, false, "s0");
		automaton.addState(false, false, "s1");
		automaton.addState(false, false, "s2");
		automaton.addState(false, false, "s3");
		automaton.addState(false, false, "s4");

		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("s0", xy00, "s1");
		automaton.addInternalTransition("s1", xy00, "s0");
		automaton.addInternalTransition("s0", xy01, "s2");
		automaton.addInternalTransition("s2", xy00, "s3");

		if (c <= 0) {
			String pred = "s3";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				pred = state;
			}
			automaton.addInternalTransition(pred, xy00, "s4");
			automaton.addInternalTransition("s4", xy00, pred);
			automaton.addInternalTransition(pred, xy10, "final");
		}

		if (c > 0) {
			automaton.addInternalTransition("s0", xy11, "final");
			automaton.addInternalTransition("s3", xy10, "final");

			String pred = "s0";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c_" + i + "_0";
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, i == 0 ? xy10 : xy00, state);

				if (i % 2 == 1) {
					automaton.addInternalTransition(state, xy01, "final");
				}
				pred = state;
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #strictIneqAutomaton(AutomataLibraryServices, Term, Term, Rational)}. Part: x >= 0 and y < 0.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartThree(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational constant) {

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		if (c <= 0) {
			return automaton;
		}

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");

		String pred = "init";
		for (int i = 0; i < (Math.abs(c) - 1); i++) {
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
			}

			final String state1 = "s" + i + "_1";
			String predInner = state1;
			automaton.addState(false, false, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy10, state1);
				automaton.addInternalTransition(state1, xy01, "final");
			} else {
				automaton.addInternalTransition(state0, xy01, state1);
				automaton.addInternalTransition(state1, xy10, "final");
			}

			for (int j = 0; j < 2 * (Math.abs(c) - (i + 2)); j++) {
				final String state = "c" + i + "_" + j;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(predInner, xy00, state);

				if (j % 2 != 0 && i % 2 == 0) {
					automaton.addInternalTransition(state, xy01, "final");
				}
				if (j % 2 != 0 && i % 2 != 0) {
					automaton.addInternalTransition(state, xy10, "final");
				}
				predInner = state;
			}
			pred = state0;
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #strictIneqAutomaton(AutomataLibraryServices, Term, Term, Rational)}. Part: x < 0 and y >= 0.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartFour(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational constant) {

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");

		if (c >= 0) {
			automaton.addState(false, false, "s0");
			automaton.addState(false, false, "s1");
			automaton.addState(false, false, "s2");
			automaton.addState(false, false, "s3");
			automaton.addState(false, false, "s4");

			automaton.addInternalTransition("init", xy01, "s0");
			automaton.addInternalTransition("init", xy00, "s2");
			automaton.addInternalTransition("s2", xy00, "init");
			automaton.addInternalTransition("s0", xy10, "final");
			automaton.addInternalTransition("s0", xy00, "s1");
			automaton.addInternalTransition("s1", xy00, "s0");
			automaton.addInternalTransition("s2", xy10, "s3");
			automaton.addInternalTransition("s3", xy00, "s4");
			automaton.addInternalTransition("s4", xy00, "s3");
			automaton.addInternalTransition("s3", xy01, "final");

			return automaton;
		}

		String pred = "init";
		for (int i = 0; i < Math.abs(c) + 2; i++) {
			String state0 = pred;
			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
			}

			String predInner = state1;
			for (int j = 0; j < 2 * (Math.abs(c) - i); j++) {
				final String state = "c" + i + "_" + j;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(predInner, xy00, state);
				predInner = state;
			}

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy01, state1);
				automaton.addInternalTransition(predInner, xy10, "final");
			} else {
				automaton.addInternalTransition(state0, xy10, state1);
				automaton.addInternalTransition(predInner, xy01, "final");
			}

			automaton.addState(false, false, "l_" + i);
			automaton.addInternalTransition(predInner, xy00, "l_" + i);
			automaton.addInternalTransition("l_" + i, xy00, predInner);

			if (i == Math.abs(c) + 1) {
				automaton.addInternalTransition(state0, xy00, pred);
			}
			pred = state0;
		}

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational constant) {

		if (!MSODUtils.isIntConstantOrTermVariable(x)) {
			throw new IllegalArgumentException("Input x must be an Int variable.");
		}

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");

		if (c <= 0) {
			// automaton.addState(false, false, "s0");
			// automaton.addInternalTransition("init", x0, "s0");
			// automaton.addInternalTransition("s0", x0, "init");

			automaton.addState(false, false, "s0");
			automaton.addInternalTransition("init", x0, "s0");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("s0", x0, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				pred = state;
			}

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, x0, "s2");
			automaton.addInternalTransition("s2", x0, pred);
			automaton.addInternalTransition(pred, x1, "final");
		}

		if (c > 0) {
			automaton.addInternalTransition("init", x1, "final");

			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				automaton.addInternalTransition(state, x1, "final");
				pred = state;
			}

			automaton.addState(false, false, "s0");
			automaton.addState(false, false, "s1");
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, x0, "s0");
			automaton.addInternalTransition("s0", x0, "s1");
			automaton.addInternalTransition("s1", x0, "s2");
			automaton.addInternalTransition("s2", x0, "s1");
			automaton.addInternalTransition("s1", x1, "final");
		}

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
	 *             if x, y are not of type Int respectively SetOfInt.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational constant, final Term y) throws AutomataLibraryException {

		if (!MSODUtils.isIntConstantOrTermVariable(x) || !MSODUtils.isSetOfIntConstantOrTermVariable(y)) {
			throw new IllegalArgumentException("Input x, y must be Int respectively SetOfInt variables.");
		}

		INestedWordAutomaton<MSODAlphabetSymbol, String> automaton = elementAutomatonPartOne(services, x, constant, y);

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				elementAutomatonPartTwo(services, x, constant, y)).getResult();

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				elementAutomatonPartThree(services, x, constant, y)).getResult();

		automaton = new Union<>(services, new MSODStringFactory(), automaton,
				elementAutomatonPartFour(services, x, constant, y)).getResult();

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #elementAutomaton(AutomataLibraryServices, Term, Rational, Term)}. Part: x+c >= 0 and x >= 0.
	 */
	private static INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartOne(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y) {
		INestedWordAutomaton<MSODAlphabetSymbol, String> result;

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		automaton.addState(false, false, "s0");
		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("init", xy01, "s0");
		automaton.addInternalTransition("s0", xy00, "init");
		automaton.addInternalTransition("s0", xy01, "init");

		if (c == 0) {
			automaton.addInternalTransition("init", xy11, "final");
			return automaton;
		}

		automaton.addState(false, false, "s1");
		automaton.addState(false, false, "s2");
		automaton.addInternalTransition("s1", xy00, "s2");
		automaton.addInternalTransition("s1", xy01, "s2");

		String pred = "s2";
		for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
			final String state = "c0_" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, xy00, state);
			automaton.addInternalTransition(pred, xy01, state);
			pred = state;
		}

		if (c < 0) {
			automaton.addInternalTransition("init", xy01, "s1");
			automaton.addInternalTransition(pred, xy10, "final");
			automaton.addInternalTransition(pred, xy11, "final");
		}

		if (c > 0) {
			automaton.addInternalTransition("init", xy10, "s1");
			automaton.addInternalTransition("init", xy11, "s1");
			automaton.addInternalTransition(pred, xy01, "final");
		}

		if (!automaton.isDeterministic()) {
			Determinize<MSODAlphabetSymbol, String> determinized;
			try {
				determinized = new Determinize<>(services, new MSODStringFactory(), automaton);
				result = determinized.getResult();
				return result;
			} catch (final AutomataOperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #elementAutomaton(AutomataLibraryServices, Term, Rational, Term)}. Part: x+c < 0 and x < 0.
	 */
	private static INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartTwo(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y) {
		INestedWordAutomaton<MSODAlphabetSymbol, String> result;
		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		automaton.addState(false, false, "s0");
		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("init", xy01, "s0");

		automaton.addInternalTransition("s0", xy00, "s1");
		automaton.addInternalTransition("s0", xy01, "s1");
		automaton.addInternalTransition("s1", xy00, "s0");
		automaton.addInternalTransition("s1", xy01, "s0");

		if (c == 0) {
			automaton.addInternalTransition("s0", xy11, "final");
			return automaton;
		}

		automaton.addState(false, false, "s2");
		automaton.addState(false, false, "s3");
		automaton.addInternalTransition("s2", xy00, "s3");
		automaton.addInternalTransition("s2", xy01, "s3");

		String pred = "s3";
		for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
			final String state = "c0_" + i;
			automaton.addState(false, false, state);
			automaton.addInternalTransition(pred, xy00, state);
			automaton.addInternalTransition(pred, xy01, state);
			pred = state;
		}

		if (c > 0) {
			automaton.addInternalTransition("s0", xy01, "s2");
			automaton.addInternalTransition(pred, xy10, "final");
			automaton.addInternalTransition(pred, xy11, "final");
		}

		if (c < 0) {
			automaton.addInternalTransition("s0", xy10, "s2");
			automaton.addInternalTransition("s0", xy11, "s2");
			automaton.addInternalTransition(pred, xy01, "final");
		}

		if (!automaton.isDeterministic()) {
			Determinize<MSODAlphabetSymbol, String> determinized;
			try {
				determinized = new Determinize<>(services, new MSODStringFactory(), automaton);
				result = determinized.getResult();
				return result;
			} catch (final AutomataOperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #elementAutomaton(AutomataLibraryServices, Term, Rational, Term)}. Part: x+c >= 0 and x < 0.
	 */
	private static INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartThree(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y) {

		INestedWordAutomaton<MSODAlphabetSymbol, String> result;
		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		if (c <= 0) {
			return automaton;
		}

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		String pred = "init";
		for (int i = 0; i < Math.abs(c); i++) {
			final int n = (int) (0.5 * i + 0.5);
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
				automaton.addInternalTransition(pred, xy01, state0);
			}

			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy01, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n - 1); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);
					automaton.addInternalTransition(predInner, xy01, state);
					predInner = state;
				}

				automaton.addInternalTransition(predInner, xy10, "final");
				automaton.addInternalTransition(predInner, xy11, "final");
			}

			if (i % 2 != 0) {
				automaton.addInternalTransition(state0, xy10, state1);
				automaton.addInternalTransition(state0, xy11, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);
					automaton.addInternalTransition(predInner, xy01, state);
					predInner = state;
				}
				automaton.addInternalTransition(predInner, xy01, "final");
			}
			pred = state0;
		}

		if (!automaton.isDeterministic()) {
			Determinize<MSODAlphabetSymbol, String> determinized;
			try {
				determinized = new Determinize<>(services, new MSODStringFactory(), automaton);
				result = determinized.getResult();
				return result;
			} catch (final AutomataOperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} that represents a part of the
	 * {@link #elementAutomaton(AutomataLibraryServices, Term, Rational, Term)}. Part: x+c < 0 and x >= 0.
	 */
	private static INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartFour(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y) {
		INestedWordAutomaton<MSODAlphabetSymbol, String> result;
		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		if (c >= 0) {
			return automaton;
		}

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		String pred = "init";
		for (int i = 0; i < Math.abs(c); i++) {
			final int n = (int) (0.5 * i + 0.5);
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
				automaton.addInternalTransition(pred, xy01, state0);
			}

			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy10, state1);
				automaton.addInternalTransition(state0, xy11, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n - 1); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);
					automaton.addInternalTransition(predInner, xy01, state);
					predInner = state;
				}
				automaton.addInternalTransition(predInner, xy01, "final");
			}

			if (i % 2 != 0) {
				automaton.addInternalTransition(state0, xy01, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);
					automaton.addInternalTransition(predInner, xy01, state);
					predInner = state;
				}
				automaton.addInternalTransition(predInner, xy10, "final");
				automaton.addInternalTransition(predInner, xy11, "final");
			}
			pred = state0;
		}
		if (!automaton.isDeterministic()) {
			Determinize<MSODAlphabetSymbol, String> determinized;
			try {
				determinized = new Determinize<>(services, new MSODStringFactory(), automaton);
				result = determinized.getResult();
				return result;
			} catch (final AutomataOperationCanceledException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

		return automaton;
	}

	/**
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> constElementAutomaton(final AutomataLibraryServices services,
			final Rational constant, final Term x) {

		if (!MSODUtils.isSetOfIntConstantOrTermVariable(x)) {
			throw new IllegalArgumentException("Input x must be a SetOfInt variable.");
		}

		final int c = SmtUtils.toInt(constant).intValueExact();
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");
		automaton.addInternalTransition("final", x1, "final");

		if (c >= 0) {
			String pred = "init";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				automaton.addInternalTransition(pred, x1, state);
				pred = state;
			}

			automaton.addInternalTransition(pred, x1, "final");
		}

		if (c < 0) {
			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				automaton.addInternalTransition(pred, x1, state);
				pred = state;
			}

			automaton.addState(false, false, "s0");
			automaton.addInternalTransition(pred, x0, "s0");
			automaton.addInternalTransition(pred, x1, "s0");
			automaton.addInternalTransition("s0", x1, "final");
		}

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

		return (index % 2 == 0 ? 1 : -1) * (index + 1) / 2;
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

		return new Pair<>(Math.min(indexToInteger(length), indexToInteger(length + 1)),
				Math.max(indexToInteger(length), indexToInteger(length + 1)));
	}
}
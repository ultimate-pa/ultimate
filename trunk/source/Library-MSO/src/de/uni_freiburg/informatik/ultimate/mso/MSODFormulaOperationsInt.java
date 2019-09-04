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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment Class.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MSODFormulaOperationsInt extends MSODFormulaOperations {

	/**
	 * Returns a {@link NestedWordAutomaton} representing a strict inequality of the form "x < c".
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational constant) {

		if (!MSODUtils.isIntVariable(x)) {
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
			automaton.addInternalTransition("s0", x0, "init");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", x0, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				pred = state;
			}

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, x0, "s2");
			automaton.addInternalTransition("s2", x1, "final");
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
			automaton.addInternalTransition("s0", x0, pred);
		}

		return automaton;
	}

	/**
	 * Returns an {@link INestedWordAutomaton} representing a strict inequality of the form "x - y < c". The automaton
	 * consists of four parts, one for each of the following case distinctions:
	 * <ul>
	 * <li>x > 0 &and; y > 0
	 * <li>x <= 0 &and; y <= 0
	 * <li>x > 0 &and; y <= 0
	 * <li>x <= 0 &and; y > 0
	 * </ul>
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational constant) throws AutomataLibraryException {

		if (!MSODUtils.isIntVariable(x) || !MSODUtils.isIntVariable(y)) {
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
	 * Returns a {@link NestedWordAutomaton} representing one part of the strict inequality automaton of "x - y < c",
	 * for x > 0 and y > 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartOne(
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
		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("s0", xy00, "init");

		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", xy00, "s1");

		if (c <= 0) {
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s1", xy10, "s2");

			String pred = "s2";
			for (int i = 0; i < 2 * Math.abs(c); i++) {

				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				pred = state;
			}

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition(pred, xy00, "s3");
			automaton.addInternalTransition("s3", xy01, "final");

			automaton.addState(false, false, "s4");
			automaton.addInternalTransition("s3", xy00, "s4");
			automaton.addInternalTransition("s4", xy00, "s3");
		}

		if (c > 0) {
			automaton.addInternalTransition("s1", xy11, "final");

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s1", xy10, "s2");

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition("s2", xy00, "s3");
			automaton.addInternalTransition("s3", xy01, "final");

			automaton.addState(false, false, "s4");
			automaton.addInternalTransition("s3", xy00, "s4");
			automaton.addInternalTransition("s4", xy00, "s3");

			String pred = "s1";
			for (int i = 0; i < 2 * (Math.abs(c) - 1) - 1; i++) {
				final String state0 = "c_" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, i == 0 ? xy01 : xy00, state0);

				if (i % 2 == 0) {
					final String state1 = "c_" + i + "_1";
					automaton.addState(false, false, state1);
					automaton.addInternalTransition(state0, xy00, state1);
					automaton.addInternalTransition(state1, xy10, "final");
				}

				pred = state0;
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the strict inequality automaton of "x - y < c",
	 * for x <= 0 and y <= 0.
	 */

	private NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartTwo(
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
		automaton.addInternalTransition("init", xy00, "s0");
		automaton.addInternalTransition("s0", xy00, "init");

		if (c <= 0) {
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", xy01, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * Math.abs(c); i++) {

				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				pred = state;
			}

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, xy00, "s2");
			automaton.addInternalTransition("s2", xy10, "final");

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition("s2", xy00, "s3");
			automaton.addInternalTransition("s3", xy00, "s2");
		}

		if (c > 0) {
			automaton.addInternalTransition("init", xy11, "final");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", xy01, "s1");

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s1", xy00, "s2");
			automaton.addInternalTransition("s2", xy10, "final");

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition("s2", xy00, "s3");
			automaton.addInternalTransition("s3", xy00, "s2");

			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1) - 1; i++) {
				final String state0 = "c_" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, i == 0 ? xy10 : xy00, state0);

				if (i % 2 == 0) {
					final String state1 = "c_" + i + "_1";
					automaton.addState(false, false, state1);
					automaton.addInternalTransition(state0, xy00, state1);
					automaton.addInternalTransition(state1, xy01, "final");
				}

				pred = state0;
			}
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the strict inequality automaton of "x - y < c",
	 * for x > 0 and y <= 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartThree(
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
			final int n = (int) (0.5 * i + 0.5);
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
			}

			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy01, state1);
				automaton.addInternalTransition(state1, xy10, "final");

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n - 2); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);

					if (j % 2 != 0) {
						automaton.addInternalTransition(state, xy10, "final");
					}

					predInner = state;
				}
			}

			if (i % 2 != 0) {
				automaton.addInternalTransition(state0, xy10, state1);
				automaton.addInternalTransition(state1, xy01, "final");

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n - 1); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);

					if (j % 2 != 0) {
						automaton.addInternalTransition(state, xy01, "final");
					}

					predInner = state;
				}
			}

			pred = state0;
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the strict inequality automaton of "x - y < c",
	 * for x <= 0 and y > 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartFour(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational constant) {

		final int c = SmtUtils.toInt(constant).intValueExact();

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		if (c > 0) {
			return automaton;
		}

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", xy00, "final");

		String pred = "init";
		for (int i = 0; i < Math.abs(c) + 2; i++) {
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
			}

			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy10, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - i); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);

					predInner = state;
				}

				automaton.addInternalTransition(predInner, xy01, "final");

				automaton.addState(false, false, "l_1_" + i);
				automaton.addInternalTransition(predInner, xy00, "l_1_" + i);
				automaton.addInternalTransition("l_1_" + i, xy00, predInner);
			}

			if (i % 2 != 0) {
				automaton.addInternalTransition(state0, xy01, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - i); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);

					predInner = state;
				}

				automaton.addInternalTransition(predInner, xy10, "final");
				automaton.addState(false, false, "l_1_" + i);
				automaton.addInternalTransition(predInner, xy00, "l_1_" + i);
				automaton.addInternalTransition("l_1_" + i, xy00, predInner);
			}

			pred = state0;

			if (i == Math.abs(c)) {
				automaton.addState(false, false, "l_0");
				automaton.addInternalTransition(pred, xy00, "l_0");
				automaton.addInternalTransition("l_0", xy00, pred);
			}

		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing a strict inequality of the form "-x < c".
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational constant) {

		if (!MSODUtils.isIntVariable(x)) {
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
			automaton.addInternalTransition("s0", x0, "init");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", x0, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * Math.abs(c); i++) {
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				pred = state;
			}

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
			automaton.addInternalTransition(pred, x0, "s0");
			automaton.addInternalTransition("s0", x1, "final");

			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("s0", x0, "s1");
			automaton.addInternalTransition("s1", x0, "s0");
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing a strict subset relation of the form " X ⊊ Y".
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictSubsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntVariable(x) || !MSODUtils.isSetOfIntVariable(y)) {
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
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy11, "init");
		automaton.addInternalTransition("init", xy01, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");
		automaton.addInternalTransition("final", xy11, "final");

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing a strict subset relation of the form " X ⊆ Y".
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> subsetAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntVariable(x) || !MSODUtils.isSetOfIntVariable(y)) {
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
	 * Returns an {@link INestedWordAutomaton} representing an element relation of the form "x + c ∈ Y". The automaton
	 * consists of four parts, one for each of the following case distinctions:
	 * <ul>
	 * <li>x + c <= 0 &and; x <= 0
	 * <li>x + c <= 0 &and; x > 0
	 * <li>x + c > 0 &and; x <= 0
	 * <li>x + c > 0 &and; x > 0
	 * </ul>
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int respectively SetOfInt.
	 */
	@Override
	public INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational constant, final Term y) throws AutomataLibraryException {

		if (!MSODUtils.isIntVariable(x) || !MSODUtils.isSetOfIntVariable(y)) {
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
	 * Returns a {@link NestedWordAutomaton} representing one part of the elementAutomaton of "x + c ∈ Y", for x + c <=
	 * 0 and; x <= 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartOne(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y)
			throws AutomataLibraryException {

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
		}

		if (c < 0) {
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", xy10, "s1");
			automaton.addInternalTransition("init", xy11, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c0_" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				automaton.addInternalTransition(pred, xy01, state);
				pred = state;
			}

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, xy00, "s2");
			automaton.addInternalTransition(pred, xy01, "s2");
			automaton.addInternalTransition("s2", xy01, "final");
		}

		if (c > 0) {
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", xy01, "s1");

			String pred = "s1";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c0_" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				automaton.addInternalTransition(pred, xy01, state);
				pred = state;
			}

			automaton.addState(false, false, "s2");
			automaton.addInternalTransition(pred, xy00, "s2");
			automaton.addInternalTransition(pred, xy01, "s2");

			automaton.addInternalTransition("s2", xy10, "final");
			automaton.addInternalTransition("s2", xy11, "final");
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the elementAutomaton of "x + c ∈ Y", for x + c <=
	 * 0 and; x > 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartTwo(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y)
			throws AutomataLibraryException {

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
		}

		if (c < 0) {
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s0", xy01, "s2");

			String pred = "s2";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c0_" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				automaton.addInternalTransition(pred, xy01, state);
				pred = state;
			}

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition(pred, xy00, "s3");
			automaton.addInternalTransition(pred, xy01, "s3");

			automaton.addInternalTransition("s3", xy10, "final");
			automaton.addInternalTransition("s3", xy11, "final");
		}

		if (c > 0) {
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s0", xy10, "s2");
			automaton.addInternalTransition("s0", xy11, "s2");

			String pred = "s2";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++) {
				final String state = "c0_" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, xy00, state);
				automaton.addInternalTransition(pred, xy01, state);
				pred = state;
			}

			automaton.addState(false, false, "s3");
			automaton.addInternalTransition(pred, xy00, "s3");
			automaton.addInternalTransition(pred, xy01, "s3");
			automaton.addInternalTransition("s3", xy01, "final");
		}

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the elementAutomaton of "x + c ∈ Y", for x + c > 0
	 * and; x <= 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartThree(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y)
			throws AutomataLibraryException {

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

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing one part of the elementAutomaton of "x + c ∈ Y", for x + c > 0
	 * and; x > 0.
	 */
	private NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartFour(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y)
			throws AutomataLibraryException {

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

		return automaton;
	}

	/**
	 * Returns a {@link NestedWordAutomaton} representing an element relation of the form " c ∈ X".
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> constElementAutomaton(final AutomataLibraryServices services,
			final Rational constant, final Term x) {

		if (!MSODUtils.isSetOfIntVariable(x)) {
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

		if (c <= 0) {
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

		if (c > 0) {
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
}
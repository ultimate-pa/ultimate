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

public abstract class MSODIntOperationsBase extends MSODOperationsBase {

	/**
	 * Constructs an automaton that represents "x < c".
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
	 * Constructs an automaton that represents x-y < c. The automaton consists of four parts, one for each of the
	 * following case distinctions: x < 0 && y < 0; x >= 0 && y >= 0; x < 0 && y >= 0; x >= 0 && y < 0.
	 *
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int.
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
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
	 * TODO: Comment.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartOne(
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
	 * TODO: Comment.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartTwo(
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
	 * TODO: Comment.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartThree(
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
	 * TODO: Comment.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonPartFour(
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
		for (int i = 0; i < 2 * Math.abs(c) + 1; i++) {
			final int n = (int) (0.5 * i + 0.5);
			String state0 = pred;

			if (i > 0) {
				state0 = "s" + i + "_0";
				automaton.addState(false, false, state0);
				automaton.addInternalTransition(pred, xy00, state0);
			}

			final String state1 = "s" + i + "_1";
			automaton.addState(false, false, state1);

			final String state2 = "s" + i + "_2";
			automaton.addState(false, false, state2);
			automaton.addInternalTransition(state1, xy00, state2);
			automaton.addInternalTransition(state2, xy00, state1);

			if (i % 2 == 0) {
				automaton.addInternalTransition(state0, xy10, state1);

				String predInner = state1;
				for (int j = 0; j < 2 * (Math.abs(c) - 2 * n); j++) {
					final String state = "c" + i + "_" + j;
					automaton.addState(false, false, state);
					automaton.addInternalTransition(predInner, xy00, state);

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

					predInner = state;
				}

				automaton.addInternalTransition(predInner, xy10, "final");
			}

			pred = state0;
		}

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "-x < c".
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
	 * Constructs an automaton that represents "X strictSubsetInt Y".
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
	 * Constructs an automaton that represents "X subsetInt Y".
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
	 * Constructs an automaton that represents "x+c element Y".
	 *
	 * @throws AutomataLibraryException
	 *             if construction of {@link Union} fails
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
	 * TODO: Comment.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartOne(
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
	 * TODO: Comment.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartTwo(
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
	 * TODO: Comment.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartThree(
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
	 * TODO: Comment.
	 */
	private static NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomatonPartFour(
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
	 * Constructs an automaton that represents "c element X".
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

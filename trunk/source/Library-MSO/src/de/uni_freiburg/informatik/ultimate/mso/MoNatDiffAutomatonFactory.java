/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * TODO: Check inputs.
 * 
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public final class MoNatDiffAutomatonFactory {

	/**
	 * Constructs an empty automaton.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> emptyAutomaton(
			final AutomataLibraryServices services) {

		final Set<MoNatDiffAlphabetSymbol> alphabet = new HashSet<MoNatDiffAlphabetSymbol>();
		final VpAlphabet<MoNatDiffAlphabetSymbol> vpAlphabet = new VpAlphabet<MoNatDiffAlphabetSymbol>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>(services, vpAlphabet, stringFactory);
	}

	/**
	 * Constructs an automaton that represents "true".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> trueAutomaton(
			final AutomataLibraryServices services) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol symbol = new MoNatDiffAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "false".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> falseAutomaton(
			final AutomataLibraryServices services) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol symbol = new MoNatDiffAlphabetSymbol();
		automaton.getAlphabet().add(symbol);

		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", symbol, "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents an Int variable.
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> intVariableAutomaton(
			final AutomataLibraryServices services, final Term x) {

		if (!MoNatDiffUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, false);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, true);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", x0, "init");
		automaton.addInternalTransition("init", x1, "final");
		automaton.addInternalTransition("final", x0, "final");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "x < c".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int or c is smaller than 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, false);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, true);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		if (c.signum() == 1) {
			automaton.addState(true, false, "init");
			automaton.addState(false, true, "final");
			automaton.addInternalTransition("init", x1, "final");
			automaton.addInternalTransition("final", x0, "final");
			addUpToConstPart(automaton, c.add(Rational.MONE), x0, x0, x1);
		}

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "x-y < c".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int or c is smaller than 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int variables and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy10, "s1");
		automaton.addInternalTransition("s1", xy00, "s1");
		automaton.addInternalTransition("s1", xy01, "final");
		automaton.addInternalTransition("final", xy00, "final");

		if (c.signum() == 1) {
			automaton.addInternalTransition("init", xy11, "final");
			addUpToConstPart(automaton, c.add(Rational.MONE), xy01, xy00, xy10);
		}

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "-x < c".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int or c is smaller than 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictNegIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, false);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, true);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", x0, "init");
		automaton.addInternalTransition("final", x0, "final");

		if (c.signum() == 0) {
			automaton.addState(true, false, "s1");
			automaton.addInternalTransition("init", x0, "s1");
			automaton.addInternalTransition("s1", x1, "final");
		}

		if (c.signum() == 1)
			automaton.addInternalTransition("init", x1, "final");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "X strictSubsetInt Y".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictSubsetAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
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
	 * Constructs an automaton that represents "X nonStrictSubsetInt Y".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> subsetAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", xy00, "final");
		automaton.addInternalTransition("init", xy01, "final");
		automaton.addInternalTransition("init", xy11, "final");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");
		automaton.addInternalTransition("final", xy11, "final");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "x+c element Y".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int, SetOfInt or c is smaller than 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> elementAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational c, final Term y) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int, SetOfInt variables and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MoNatDiffAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy01, "init");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		if (c.signum() == 0)
			automaton.addInternalTransition("init", xy11, "final");

		addConstPart(automaton, c, xy10, xy11, xy00, xy01, xy01);

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "c element X".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt or c is smaller than 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> constElementAutomaton(
			final AutomataLibraryServices services, final Rational c, final Term x) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be a SetOfInt variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, false);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, true);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");
		automaton.addInternalTransition("final", x1, "final");

		if (c.signum() == 0)
			automaton.addInternalTransition("init", x1, "final");

		addConstPart(automaton, c, x0, x1, x0, x1, x1);

		return automaton;
	}

	/**
	 * Constructs a copy of the given automaton with the extended or reduced alphabet.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> reconstruct(
			final AutomataLibraryServices services,
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final Set<MoNatDiffAlphabetSymbol> alphabet, final boolean isExtended) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result;

		result = MoNatDiffAutomatonFactory.emptyAutomaton(services);
		result.getAlphabet().addAll(alphabet);

		for (final String state : automaton.getStates())
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);

		for (final String state : automaton.getStates()) {

			for (final OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state)) {

				final Iterator<MoNatDiffAlphabetSymbol> itMatches = isExtended
						? alphabet.stream().filter(e -> e.contains(transition.getLetter())).iterator()
						: alphabet.stream().filter(e -> transition.getLetter().contains(e)).iterator();

				while (itMatches.hasNext()) {
					result.addInternalTransition(state, itMatches.next(), transition.getSucc());
				}
			}
		}

		return result;
	}

	/**
	 * Adds a part to the given automaton that represents the value of constant c.
	 */
	private static void addConstPart(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final Rational c, final MoNatDiffAlphabetSymbol initToState1, final MoNatDiffAlphabetSymbol initToState2,
			final MoNatDiffAlphabetSymbol predToState1, final MoNatDiffAlphabetSymbol predToState2,
			final MoNatDiffAlphabetSymbol stateToFinal) {

		final int cInt = SmtUtils.toInt(c).intValueExact();

		for (int i = 0; i < cInt; i++) {
			final String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);

			if (i == 0) {
				automaton.addInternalTransition("init", initToState1, state);
				automaton.addInternalTransition("init", initToState2, state);
			}

			if (i > 0) {
				final String pred = "c" + String.valueOf(i);
				automaton.addInternalTransition(pred, predToState1, state);
				automaton.addInternalTransition(pred, predToState2, state);
			}

			if (i == cInt - 1)
				automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}

	/**
	 * Adds a part to the given automaton that represents values from 0 up to
	 * constant c.
	 */
	private static void addUpToConstPart(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final Rational c, final MoNatDiffAlphabetSymbol initToState, final MoNatDiffAlphabetSymbol predToState,
			final MoNatDiffAlphabetSymbol stateToFinal) {

		final int cInt = SmtUtils.toInt(c).intValueExact();

		for (int i = 0; i < cInt; i++) {
			final String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);

			if (i == 0)
				automaton.addInternalTransition("init", initToState, state);

			if (i > 0) {
				final String pred = "c" + String.valueOf(i);
				automaton.addInternalTransition(pred, predToState, state);
			}

			automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}
}
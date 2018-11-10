/*
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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/*
 * TODO: Comment.
 * TODO: CHECK INPUTS !
 */
public final class MoNatDiffAutomatonFactory {

	/*
	 * Constructs empty automaton.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> emptyAutomaton(
			final AutomataLibraryServices automataLibraryServices) {

		final Set<MoNatDiffAlphabetSymbol> alphabet = new HashSet<MoNatDiffAlphabetSymbol>();
		final VpAlphabet<MoNatDiffAlphabetSymbol> vpAlphabet = new VpAlphabet<MoNatDiffAlphabetSymbol>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>(automataLibraryServices, vpAlphabet,
				stringFactory);
	}
	
	/*
	 * Constructs automaton for atomic formula "true".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> trueAutomaton(
			final AutomataLibraryServices automataLibraryServices) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol emptyWord = new MoNatDiffAlphabetSymbol();
		
		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", emptyWord, "init");

		return automaton;
	}
	
	/*
	 * Constructs automaton for atomic formula "false".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> falseAutomaton(
			final AutomataLibraryServices automataLibraryServices) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol emptyWord = new MoNatDiffAlphabetSymbol();
		
		automaton.addState(true, false, "init");
		automaton.addInternalTransition("init", emptyWord, "init");

		return automaton;
	}

	/*
	 * Constructs automaton that represents an Int variable.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> intVariableAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x) {

		if (!MoNatDiffUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", x0, "init");
		automaton.addInternalTransition("init", x1, "final");
		automaton.addInternalTransition("final", x0, "final");

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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

	/*
	 * Constructs automaton for atomic formula "x-y < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Term y, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int variables and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		final MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		final MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		final MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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

	/*
	 * Constructs automaton for atomic formula "-x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictNegIneqAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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

	/*
	 * Constructs automaton for atomic formula "X strictSubsetInt Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictSubsetAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		final MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		final MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		final MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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

	/*
	 * Constructs automaton for atomic formula "X nonStrictSubsetInt Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> subsetAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		final MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		final MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		final MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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

	/*
	 * Constructs automaton for atomic formula "x+c element Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> elementAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Term x, final Rational c, final Term y) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int, SetOfInt variables and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		final MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		final MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		final MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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

	/*
	 * Constructs automaton for atomic formula "c element X".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> constElementAutomaton(
			final AutomataLibraryServices automataLibraryServices, final Rational c, final Term x) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be a SetOfInt variable and c must be >= 0.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		final MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		final MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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

	/*
	 * TODO: Comment.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> reconstruct(
			final AutomataLibraryServices automataLibraryServices,
			final INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final Set<MoNatDiffAlphabetSymbol> alphabet, final boolean isExtended, final ILogger mLogger) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result = MoNatDiffAutomatonFactory
				.emptyAutomaton(automataLibraryServices);

		result.getAlphabet().addAll(alphabet);
		final Iterator<String> itStates = automaton.getStates().iterator();

		while (itStates.hasNext()) {
			final String state = itStates.next();
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);
			final Iterator<OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String>> itTransitions = automaton
					.internalSuccessors(state).iterator();

			while (itTransitions.hasNext()) {
				final OutgoingInternalTransition<MoNatDiffAlphabetSymbol, String> transition = itTransitions.next();
				Iterator<MoNatDiffAlphabetSymbol> itMatches;

				if (isExtended)
					itMatches = alphabet.stream().filter(e -> e.contains(transition.getLetter())).iterator();
				else
					itMatches = alphabet.stream().filter(e -> transition.getLetter().contains(e)).iterator();

				while (itMatches.hasNext()) {
					result.addInternalTransition(state, itMatches.next(), transition.getSucc());
				}
			}
		}

		return result;
	}

	/*
	 * Adds a part to automaton that represents the value of constant c.
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

	/*
	 * Adds a part to automaton that represents values from zero up to constant c.
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
/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
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
	 * Constructs automaton for atomic formula "x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(
			AutomataLibraryServices automataLibraryServices, Term x, Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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
			AutomataLibraryServices automataLibraryServices, Term x, Term y, Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int variables and c must be >= 0.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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
			addUpToConstPart(automaton, c.add(Rational.MONE), xy01, xy01, xy10);
		}

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "-x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictNegIneqAutomaton(
			AutomataLibraryServices automataLibraryServices, Term x, Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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
			AutomataLibraryServices automataLibraryServices, Term x, Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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
			AutomataLibraryServices automataLibraryServices, Term x, Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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
			AutomataLibraryServices automataLibraryServices, Term x, Rational c, Term y) {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y) || c.isNegative())
			throw new IllegalArgumentException("Input x, y must be Int, SetOfInt variables and c must be >= 0.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol xy00 = new MoNatDiffAlphabetSymbol(x, y, 0, 0);
		MoNatDiffAlphabetSymbol xy01 = new MoNatDiffAlphabetSymbol(x, y, 0, 1);
		MoNatDiffAlphabetSymbol xy10 = new MoNatDiffAlphabetSymbol(x, y, 1, 0);
		MoNatDiffAlphabetSymbol xy11 = new MoNatDiffAlphabetSymbol(x, y, 1, 1);
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
			AutomataLibraryServices automataLibraryServices, Rational c, Term x) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || c.isNegative())
			throw new IllegalArgumentException("Input x must be a SetOfInt variable and c must be >= 0.");

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);
		MoNatDiffAlphabetSymbol x0 = new MoNatDiffAlphabetSymbol(x, 0);
		MoNatDiffAlphabetSymbol x1 = new MoNatDiffAlphabetSymbol(x, 1);
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
	 * Adds a part to automaton that represents the value of constant c.
	 */
	private static void addConstPart(NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, Rational c,
			MoNatDiffAlphabetSymbol initToState1, MoNatDiffAlphabetSymbol initToState2,
			MoNatDiffAlphabetSymbol predToState1, MoNatDiffAlphabetSymbol predToState2,
			MoNatDiffAlphabetSymbol stateToFinal) {
		
		int cInt = SmtUtils.toInt(c).intValueExact();

		for (int i = 0; i < cInt; i++) {
			String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);

			if (i == 0) {
				automaton.addInternalTransition("init", initToState1, state);
				automaton.addInternalTransition("init", initToState2, state);
			}

			if (i > 0) {
				String pred = "c" + String.valueOf(i);
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
	private static void addUpToConstPart(NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, Rational c,
			MoNatDiffAlphabetSymbol initToState, MoNatDiffAlphabetSymbol predToState,
			MoNatDiffAlphabetSymbol stateToFinal) {
		
		int cInt = SmtUtils.toInt(c).intValueExact();

		for (int i = 0; i < cInt; i++) {
			String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);

			if (i == 0)
				automaton.addInternalTransition("init", initToState, state);

			if (i > 0) {
				String pred = "c" + String.valueOf(i);
				automaton.addInternalTransition(pred, predToState, state);
			}

			automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}

	/*
	 * Constructs empty automaton.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> emptyAutomaton(
			AutomataLibraryServices automataLibraryServices) {

		Set<MoNatDiffAlphabetSymbol> alphabet = new HashSet<MoNatDiffAlphabetSymbol>();
		VpAlphabet<MoNatDiffAlphabetSymbol> vpAlphabet = new VpAlphabet<MoNatDiffAlphabetSymbol>(alphabet);
		StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>(automataLibraryServices, vpAlphabet,
				stringFactory);
	}
}
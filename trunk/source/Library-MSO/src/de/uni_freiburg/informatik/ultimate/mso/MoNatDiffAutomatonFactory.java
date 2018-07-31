/*
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/*
 * TODO: Comment.
 */
public final class MoNatDiffAutomatonFactory {

	/*
	 * Constructs empty automaton.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> emptyAutomaton(
			AutomataLibraryServices automataLibraryServices) {

		Set<MoNatDiffAlphabetSymbol> alphabet = null;
		VpAlphabet<MoNatDiffAlphabetSymbol> vpAlphabet = new VpAlphabet<MoNatDiffAlphabetSymbol>(alphabet);
		StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>(automataLibraryServices, vpAlphabet,
				stringFactory);
	}

	/*
	 * Constructs automaton for atomic formula "x-y < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(Term x, Term y, int c,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "init");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 1, 0), "s1");
		automaton.addInternalTransition("s1", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "s1");
		automaton.addInternalTransition("s1", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "final");

		if (c > 0) {
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "final");

			addUpToConstPart(automaton, c - 1, new MoNatDiffAlphabetSymbol(x, y, 0, 1),
					new MoNatDiffAlphabetSymbol(x, y, 0, 1), new MoNatDiffAlphabetSymbol(x, y, 1, 0));
		}

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "x-y <= c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nonStrictIneqAutomaton(Term x, Term y, int c,
			AutomataLibraryServices automataLibraryServices) {

		return strictIneqAutomaton(x, y, c + 1, automataLibraryServices);
	}

	/*
	 * Constructs automaton for atomic formula "x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomaton(Term x, int c,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		if (c > 0) {
			automaton.addState(true, false, "init");
			automaton.addState(false, true, "final");
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, 1), "final");
			automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, 0), "final");

			addUpToConstPart(automaton, c - 1, new MoNatDiffAlphabetSymbol(x, 0), new MoNatDiffAlphabetSymbol(x, 0),
					new MoNatDiffAlphabetSymbol(x, 1));
		}

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "x <= c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nonStrictIneqAutomaton(Term x, int c,
			AutomataLibraryServices automataLibraryServices) {

		return strictIneqAutomaton(x, c + 1, automataLibraryServices);
	}

	/*
	 * Constructs automaton for atomic formula "-x < c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictNegIneqAutomaton(Term x, int c,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, 0), "init");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, 0), "final");

		if (c == 0) {
			automaton.addState(true, false, "s1");
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, 0), "s1");
			automaton.addInternalTransition("s1", new MoNatDiffAlphabetSymbol(x, 1), "final");
		}

		if (c > 0)
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, 1), "final");

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "-x <= c".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nonStrictNegIneqAutomaton(Term x, int c,
			AutomataLibraryServices automataLibraryServices) {

		return strictNegIneqAutomaton(x, c + 1, automataLibraryServices);
	}

	/*
	 * Constructs automaton for atomic formula "X strictSubsetInt Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictSubsetAutomaton(Term x, Term y,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "init");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "init");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "final");

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "X nonStrictSubsetInt Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> nonStrictSubsetAutomaton(Term x, Term y,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "final");

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "x element Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> elementAutomaton(Term x, Term y,
			AutomataLibraryServices automataLibraryServices) {

		return elementAutomaton(x, y, 0, automataLibraryServices);
	}

	/*
	 * Constructs automaton for atomic formula "x+c element Y".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> elementAutomaton(Term x, Term y, int c,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "init");
		automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "init");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 0), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, y, 0, 1), "final");

		if (c == 0)
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, y, 1, 1), "final");

		addConstPart(automaton, c, new MoNatDiffAlphabetSymbol(x, y, 1, 0), new MoNatDiffAlphabetSymbol(x, y, 1, 1),
				new MoNatDiffAlphabetSymbol(x, y, 0, 0), new MoNatDiffAlphabetSymbol(x, y, 0, 1),
				new MoNatDiffAlphabetSymbol(x, y, 0, 1));

		return automaton;
	}

	/*
	 * Constructs automaton for atomic formula "c element X".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> constElementAutomaton(Term x, int c,
			AutomataLibraryServices automataLibraryServices) {

		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(automataLibraryServices);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, 0), "final");
		automaton.addInternalTransition("final", new MoNatDiffAlphabetSymbol(x, 1), "final");

		if (c == 0)
			automaton.addInternalTransition("init", new MoNatDiffAlphabetSymbol(x, 1), "final");

		addConstPart(automaton, c, new MoNatDiffAlphabetSymbol(x, 0), new MoNatDiffAlphabetSymbol(x, 1),
				new MoNatDiffAlphabetSymbol(x, 0), new MoNatDiffAlphabetSymbol(x, 1),
				new MoNatDiffAlphabetSymbol(x, 1));

		return automaton;
	}

	/*
	 * Adds a part to automaton that represents the value of constant.
	 */
	private static void addConstPart(NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, int constant,
			MoNatDiffAlphabetSymbol initToState1, MoNatDiffAlphabetSymbol initToState2,
			MoNatDiffAlphabetSymbol predToState1, MoNatDiffAlphabetSymbol predToState2,
			MoNatDiffAlphabetSymbol stateToFinal) {

		for (int i = 0; i < constant; i++) {
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

			if (i == constant - 1)
				automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}

	/*
	 * Adds a part to automaton that represents values from zero up to constant.
	 */
	private static void addUpToConstPart(NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, int constant,
			MoNatDiffAlphabetSymbol initToState, MoNatDiffAlphabetSymbol predToState,
			MoNatDiffAlphabetSymbol stateToFinal) {

		for (int i = 0; i < constant; i++) {
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
}
/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
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

/**
 * TODO:
 * 
 * 1. Find meaningful names for the automata representing only one case of the complete automaton. 2. Test all (new) Int
 * automata. 3. Note: Some methods are redundant to the ones in MoNatDiffAutomatonFactory (even though some are
 * shortened by the use of createAlphabet) including: emptyAutomaton, trueAutomaton, falseAutomaton,
 * intVariableAutomaton, reconstruct, createAlphabet, strictSubsetAutomaton, nonStrictSubsetAutomaton 4. nonStrictSubset
 * currently requires at least one transition in order to return an accepted word, even for {} \subset {}. An automaton
 * consisting of only one state might already be sufficient.
 * 
 */

public class MSODiffIntAutomatonFactory {

	/**
	 * Constructs an empty automaton.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			emptyAutomaton(final AutomataLibraryServices services) {

		final Set<MoNatDiffAlphabetSymbol> alphabet = new HashSet<MoNatDiffAlphabetSymbol>();
		final VpAlphabet<MoNatDiffAlphabetSymbol> vpAlphabet = new VpAlphabet<MoNatDiffAlphabetSymbol>(alphabet);
		final StringFactory stringFactory = new StringFactory();

		return new NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>(services, vpAlphabet, stringFactory);
	}

	/**
	 * Constructs an automaton that represents "true".
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			trueAutomaton(final AutomataLibraryServices services) {

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
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			falseAutomaton(final AutomataLibraryServices services) {

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
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			intVariableAutomaton(final AutomataLibraryServices services, final Term x) {

		if (!MoNatDiffUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", symbol.get("x0"), "init");
		automaton.addInternalTransition("init", symbol.get("x1"), "final");
		automaton.addInternalTransition("final", symbol.get("x0"), "final");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "x < c".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);
		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("x0"), "final");

		if (cInt > 0) {
			automaton.addInternalTransition("init", symbol.get("x1"), "final");

			for (int i = 1; i <= (2 * cInt - 2); i++) {
				String prevState = "c" + (i - 1);
				String state = "c" + i;

				automaton.addState(false, false, state);

				if (i == 1)
					prevState = "init";

				automaton.addInternalTransition(prevState, symbol.get("x0"), state);
				automaton.addInternalTransition(state, symbol.get("x1"), "final");

				if (i == (2 * cInt - 2)) {
					automaton.addState(false, false, "l0");
					automaton.addInternalTransition(state, symbol.get("x0"), "l0");
					automaton.addInternalTransition("l0", symbol.get("x0"), state);
				}

			}
		}

		else {
			for (int i = 1; i <= (2 * cIntAbs + 2); i++) {
				String prevState = "c" + (i - 1);
				String state = "c" + i;

				automaton.addState(false, false, state);

				if (i == 1)
					prevState = "init";

				automaton.addInternalTransition(prevState, symbol.get("x0"), state);

				if (i == (2 * cIntAbs + 2)) {
					automaton.addState(false, false, "l0");
					automaton.addInternalTransition(state, symbol.get("x0"), "l0");
					automaton.addInternalTransition("l0", symbol.get("x0"), state);
					automaton.addInternalTransition(state, symbol.get("x1"), "final");
				}
			}
		}

		return automaton;
	}

	/**
	 * Create automaton for x - y < c. The automaton consists of four parts, one for each of the following case
	 * distinctions: x,y < 0; x,y >= 0; x < 0, y >= 0 and x >= 0, y < 0.
	 * 
	 * @throws AutomataLibraryException
	 */

	public static INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			strictIneqAutomaton(final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
					throws AutomataLibraryException {

		Set<MoNatDiffAlphabetSymbol> symbols;
		List<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>> automata =
				new ArrayList<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>>();
		automata.add(strictIneqAtomatonCase1(services, x, y, c));
		automata.add(strictIneqAutomatonCase2(services, x, y, c));
		automata.add(strictIneqAutomatonCase3(services, x, y, c));
		automata.add(strictIneqAutomatonCase4(services, x, y, c));

		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result;
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> tmp;

		result = automata.get(0);
		for (int i = 1; i < 4; i++) {
			symbols = MoNatDiffUtils.mergeAlphabets(result.getAlphabet(), automata.get(i).getAlphabet());
			result = reconstruct(services, result, symbols, true);
			tmp = reconstruct(services, automata.get(i), symbols, true);
			result = new Union<>(services, new MoNatDiffStringFactory(), result, tmp).getResult();
		}

		return result;
	}

	/**
	 * Create automaton for x - y < c, case distinction: x, y < 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAtomatonCase1(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		if (cInt > 0) {
			// |y| <= |x|
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", symbol.get("xy00"), "s1");
			repeatingPart(automaton, symbol.get("xy01"), symbol.get("xy10"), symbol.get("xy00"), symbol.get("xy11"),
					true);
			automaton.addInternalTransition("s1", symbol.get("xy00"), "q1");

			// |y| > |x|
			if (cInt > 1) {
				repeatingPartConst(automaton, symbol.get("xy10"), symbol.get("xy01"), symbol.get("xy00"),
						symbol.get("xy11"), c);
				automaton.addInternalTransition("s1", symbol.get("xy00"), "p1");
			}
		} else {
			for (int i = 0; i <= 3; i++)
				automaton.addState(false, false, "s" + i);

			for (int i = 1; i <= (2 * cIntAbs + 2); i++) {
				automaton.addState(false, false, "c" + i);

				if (i == 1)
					automaton.addInternalTransition("s1", symbol.get("xy01"), "c" + i);
				else
					automaton.addInternalTransition("c" + (i - 1), symbol.get("xy00"), "c" + i);

				if (i == (2 * cIntAbs + 2)) {
					automaton.addInternalTransition("c" + i, symbol.get("xy00"), "s3");
					automaton.addInternalTransition("s3", symbol.get("xy00"), "c" + i);
					automaton.addInternalTransition("c" + i, symbol.get("xy10"), "final");
				}
			}
			automaton.addInternalTransition("init", symbol.get("xy00"), "s0");
			automaton.addInternalTransition("s0", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s2");
			automaton.addInternalTransition("s2", symbol.get("xy00"), "s1");
		}

		return automaton;
	}

	/**
	 * Create automaton for x - y < c, case distinction: x, y >= 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomatonCase2(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		if (cInt > 0) {
			// x <= y
			repeatingPart(automaton, symbol.get("xy10"), symbol.get("xy01"), symbol.get("xy00"), symbol.get("xy11"),
					true);
			automaton.addInternalTransition("init", symbol.get("xy00"), "q1");
			automaton.addInternalTransition("init", symbol.get("xy10"), "q3");
			automaton.addInternalTransition("init", symbol.get("xy11"), "final");

			// x > y
			automaton.addState(false, false, "s1");
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("init", symbol.get("xy01"), "s1");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s2");
			automaton.addInternalTransition("s2", symbol.get("xy10"), "final");

			if (cInt > 1) {
				repeatingPartConst(automaton, symbol.get("xy01"), symbol.get("xy10"), symbol.get("xy00"),
						symbol.get("xy11"), c);
				automaton.addInternalTransition("init", symbol.get("xy00"), "p1");
				automaton.addInternalTransition("s2", symbol.get("xy00"), "c1");
			}
		}

		else {
			for (int i = 0; i <= 2; i++)
				automaton.addState(false, false, "s" + i);

			for (int i = 1; i <= (2 * cIntAbs + 2); i++) {
				automaton.addState(false, false, "c" + i);

				if (i == 1)
					automaton.addInternalTransition("s0", symbol.get("xy10"), "c" + i);
				else
					automaton.addInternalTransition("c" + (i - 1), symbol.get("xy00"), "c" + i);

				if (i == (2 * cIntAbs + 2)) {
					automaton.addInternalTransition("c" + i, symbol.get("xy00"), "s2");
					automaton.addInternalTransition("s2", symbol.get("xy00"), "c" + i);
					automaton.addInternalTransition("c" + i, symbol.get("xy01"), "final");
				}
			}
			automaton.addInternalTransition("init", symbol.get("xy00"), "s0");
			automaton.addInternalTransition("s0", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s0");
			automaton.addInternalTransition("s0", symbol.get("xy10"), "c1");
		}

		return automaton;
	}

	/**
	 * Create automaton for x - y < c, case distinction: x < 0, y >= 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomatonCase3(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);
		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		if (cInt > 0) {
			for (int i = 1; i <= 7; i++)
				automaton.addState(false, false, "s" + i);

			automaton.addInternalTransition("init", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("init", symbol.get("xy01"), "s3");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s2");
			automaton.addInternalTransition("s1", symbol.get("xy01"), "s3");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s5");
			automaton.addInternalTransition("s2", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("s3", symbol.get("xy00"), "s4");
			automaton.addInternalTransition("s3", symbol.get("xy10"), "final");
			automaton.addInternalTransition("s4", symbol.get("xy00"), "s3");
			automaton.addInternalTransition("s5", symbol.get("xy10"), "s6");
			automaton.addInternalTransition("s6", symbol.get("xy00"), "s7");
			automaton.addInternalTransition("s6", symbol.get("xy01"), "final");
			automaton.addInternalTransition("s7", symbol.get("xy00"), "s6");
		} else {
			// Add branching states
			for (int i = 1; i <= Math.max(0, cIntAbs - 1) + 2; i++) {
				String prevState = "s" + (i - 1);
				String state = "s" + i;

				if (i == 1)
					prevState = "init";

				automaton.addState(false, false, state);
				automaton.addInternalTransition(prevState, symbol.get("xy00"), state);

				if (i == Math.max(0, cIntAbs - 1) + 1) {
					automaton.addState(false, false, "l");
					automaton.addInternalTransition(state, symbol.get("xy00"), "l");
					automaton.addInternalTransition("l", symbol.get("xy00"), state);
				}
			}

			// Add x and y states
			for (int i = 0; i <= Math.max(0, cIntAbs - 1) + 2; i++) {
				int loopCond = Math.max(1, (2 * cIntAbs - 2 * i + 1));

				if (i == 0) {
					loopCond = 2 * (cIntAbs + 1);
					if (cIntAbs == 0)
						loopCond = 2;
				}

				for (int j = 1; j <= loopCond; j++) {
					String prevState = "c" + i + (j - 1);
					String state = "c" + i + j;
					String letter1 = "xy01";
					String letter2 = "xy10";

					automaton.addState(false, false, state);

					if (i % 2 == 0 && i != 0) {
						letter1 = "xy10";
						letter2 = "xy01";
					}

					if (j == 1) {
						if (i == 0)
							automaton.addInternalTransition("init", symbol.get(letter1), state);
						else
							automaton.addInternalTransition("s" + i, symbol.get(letter1), state);
					} else
						automaton.addInternalTransition(prevState, symbol.get("xy00"), state);

					if (j == loopCond) {
						automaton.addState(false, false, "l" + i);
						automaton.addInternalTransition(state, symbol.get("xy00"), "l" + i);
						automaton.addInternalTransition("l" + i, symbol.get("xy00"), state);
						automaton.addInternalTransition(state, symbol.get(letter2), "final");
					}
				}
			}
		}

		return automaton;
	}

	/**
	 * Create automaton for x - y < c, case distinction: x >= 0, y < 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> strictIneqAutomatonCase4(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		int cInt = SmtUtils.toInt(c).intValueExact();
		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		// No accepting run if c <= 0.
		if (cInt <= 0)
			return falseAutomaton(services);

		// No accepting run if c = 1.
		if (cInt == 1)
			return falseAutomaton(services);

		// Add part representing x = 0, y < 0. Accepting run if c > 1.
		for (int i = 1; i <= (2 * cInt - 2); i++) {
			String prevState = "c" + (i - 1);
			String state = "c" + i;
			automaton.addState(false, false, state);

			if (i == 1)
				automaton.addInternalTransition("init", symbol.get("xy10"), state);
			else
				automaton.addInternalTransition(prevState, symbol.get("xy00"), state);

			if (i % 2 == 0)
				automaton.addInternalTransition(state, symbol.get("xy01"), "final");
		}

		if (cInt == 2)
			return automaton;

		// Add part representing x > 0, y < 0. Accepting run if c > 2.
		// Add states for the branches representing x (y) set to values from |1| to
		// |c-2|
		for (int i = 1; i <= (cInt - 2); i++) {
			String prevState = "s" + (i - 1);
			String state = "s" + i;

			if (i == 1)
				prevState = "init";

			automaton.addState(false, false, state);
			automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
		}

		// Add "x-states" and transitions
		for (int i = 1; i <= (cInt - 2); i++) {
			for (int j = 1; j <= 2 * cInt - 4 * i - 1; j++) {
				String prevStateX = "x" + i + (j - 1);
				String stateX = "x" + i + j;
				automaton.addState(false, false, stateX);

				if (j % 2 == 1)
					automaton.addInternalTransition(stateX, symbol.get("xy01"), "final");

				if (j == 1)
					automaton.addInternalTransition("s" + (2 * i - 1), symbol.get("xy10"), stateX);
				else
					automaton.addInternalTransition(prevStateX, symbol.get("xy00"), stateX);
			}
		}

		// Add "y-states" and transitions
		for (int i = 1; i <= (cInt - 2); i++) {
			for (int j = 1; j <= 2 * cInt - 4 * i - 3; j++) {
				String prevStateY = "y" + i + (j - 1);
				String stateY = "y" + i + j;
				automaton.addState(false, false, stateY);

				if (j % 2 == 1)
					automaton.addInternalTransition(stateY, symbol.get("xy10"), "final");

				if (j == 1)
					automaton.addInternalTransition("s" + (2 * i), symbol.get("xy01"), stateY);
				else
					automaton.addInternalTransition(prevStateY, symbol.get("xy00"), stateY);
			}
		}

		return automaton;
	}

	/**
	 * Create an automaton that represents "-x < c".
	 *
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MoNatDiffUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be Int variable.");

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);
		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("x0"), "final");

		if (cInt == 0) {
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition("init", symbol.get("x0"), "s1");
			automaton.addInternalTransition("s1", symbol.get("x0"), "init");
			automaton.addInternalTransition("s1", symbol.get("x1"), "final");
		}

		if (cInt > 0) {
			automaton.addInternalTransition("init", symbol.get("x1"), "final");

			for (int i = 1; i <= 2 * cInt - 1; i++) {
				String prevState = (i == 1) ? "init" : "c" + (i - 1);
				String state = "c" + i;

				automaton.addState(false, false, state);
				automaton.addInternalTransition(prevState, symbol.get("x0"), state);
				automaton.addInternalTransition(state, symbol.get("x1"), "final");

				if (i == 2 * cInt - 1)
					automaton.addInternalTransition(state, symbol.get("x0"), prevState);
			}
		}

		if (cInt < 0) {
			for (int i = 1; i <= 2 * cIntAbs + 1; i++) {
				String prevState = (i == 1) ? "init" : "c" + (i - 1);
				String state = "c" + i;

				automaton.addState(false, false, state);
				automaton.addInternalTransition(prevState, symbol.get("x0"), state);

				if (i == 2 * cIntAbs + 1) {
					automaton.addInternalTransition(state, symbol.get("x0"), prevState);
					automaton.addInternalTransition(state, symbol.get("x1"), "final");
				}
			}
		}

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "X strictSubsetInt Y".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			strictSubsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", symbol.get("xy00"), "init");
		automaton.addInternalTransition("init", symbol.get("xy11"), "init");
		automaton.addInternalTransition("init", symbol.get("xy01"), "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");
		automaton.addInternalTransition("final", symbol.get("xy11"), "final");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "X nonStrictSubsetInt Y".
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			subsetAutomaton(final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", symbol.get("xy00"), "final");
		automaton.addInternalTransition("init", symbol.get("xy01"), "final");
		automaton.addInternalTransition("init", symbol.get("xy11"), "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");
		automaton.addInternalTransition("final", symbol.get("xy11"), "final");

		return automaton;
	}

	/**
	 * Creates an automaton that represents "x+c element Y".
	 * 
	 * @throws AutomataLibraryException
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int respectively SetOfInt.
	 */
	public static INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			elementAutomaton(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException {

		if (!MoNatDiffUtils.isIntVariable(x) || !MoNatDiffUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be Int respectively SetOfInt variables.");

		Set<MoNatDiffAlphabetSymbol> symbols;
		List<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>> automata =
				new ArrayList<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>>();
		automata.add(elementAutomatonCase1(services, x, c, y));
		automata.add(elementAutomatonCase2(services, x, c, y));
		automata.add(elementAutomatonCase3(services, x, c, y));
		automata.add(elementAutomatonCase4(services, x, c, y));

		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> result;
		INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> tmp;

		result = automata.get(0);
		for (int i = 1; i < 4; i++) {
			symbols = MoNatDiffUtils.mergeAlphabets(result.getAlphabet(), automata.get(i).getAlphabet());
			result = reconstruct(services, result, symbols, true);
			tmp = reconstruct(services, automata.get(i), symbols, true);
			result = new Union<>(services, new MoNatDiffStringFactory(), result, tmp).getResult();
		}

		return result;

	}

	/**
	 * Create an automaton that represents "x+c element Y", case distinction: x+c<=0, i%2=0 (means: x is 0 or negative).
	 * 
	 * @throws AutomataLibraryException
	 * 
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			elementAutomatonCase1(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException {

		int cInt = SmtUtils.toInt(c).intValueExact();
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "l0");
		automaton.addInternalTransition("init", symbol.get("xy00"), "l0");
		automaton.addInternalTransition("init", symbol.get("xy01"), "l0");
		automaton.addInternalTransition("l0", symbol.get("xy00"), "init");
		automaton.addInternalTransition("l0", symbol.get("xy01"), "init");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");

		if (cInt == 0)
			automaton.addInternalTransition("init", symbol.get("xy11"), "final");

		for (int i = 1; i <= 2 * cInt; i++) {
			String prevState = "c" + (i - 1);
			String state = "c" + i;

			automaton.addState(false, false, state);

			if (i > 1) {
				automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
				automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
			}

			if (i == 2 * cInt) {
				if (cInt > 0) {
					automaton.addInternalTransition("init", symbol.get("xy01"), "c1");
					automaton.addInternalTransition(state, symbol.get("xy10"), "final");
					automaton.addInternalTransition(state, symbol.get("xy11"), "final");
				} else {
					automaton.addInternalTransition("init", symbol.get("xy10"), "c1");
					automaton.addInternalTransition("init", symbol.get("xy11"), "c1");
					automaton.addInternalTransition(state, symbol.get("xy01"), "final");
				}
			}
		}

		// Make sure that x+c<=0, by ensuring that i>=2c.
		if (cInt > 0) {
			final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> tmp = emptyAutomaton(services);
			Map<String, MoNatDiffAlphabetSymbol> tmpSymbol = createAlphabet(tmp, x, y);

			tmp.addState(true, false, "init");
			tmp.addState(false, true, "final");
			tmp.addInternalTransition("final", tmpSymbol.get("xy00"), "final");
			tmp.addInternalTransition("final", tmpSymbol.get("xy01"), "final");

			for (int i = 1; i <= 2 * cInt; i++) {
				String prevState = i == 1 ? "init" : "c" + (i - 1);
				String state = "c" + i;

				tmp.addState(false, false, state);
				tmp.addInternalTransition(prevState, tmpSymbol.get("xy00"), state);
				tmp.addInternalTransition(prevState, tmpSymbol.get("xy01"), state);

				if (i == 2 * cInt) {
					tmp.addState(false, false, "l0");
					tmp.addInternalTransition(state, symbol.get("xy00"), "l0");
					tmp.addInternalTransition(state, symbol.get("xy01"), "l0");
					tmp.addInternalTransition("l0", symbol.get("xy00"), state);
					tmp.addInternalTransition("l0", symbol.get("xy01"), state);
					tmp.addInternalTransition(state, tmpSymbol.get("xy10"), "final");
					tmp.addInternalTransition(state, tmpSymbol.get("xy10"), "final");
				}
			}

			automaton = (NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>) new Intersect<>(services,
					new MoNatDiffStringFactory(), automaton, tmp).getResult();
		}

		return automaton;
	}

	/**
	 * Create an automaton that represents "x+c element Y", case distinction: x+c<=0, i%2=1 (means: x is positive).
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			elementAutomatonCase2(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException {

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");

		// TODO: Check if this works..
		if (cInt >= 0)
			return falseAutomaton(services);

		// Create one branch for each possible value of i: i<=2|c|-1 && i%2=1
		for (int i = 1; i <= 2 * cIntAbs - 1; i += 2) {
			int posXPlusC = 2 * cIntAbs - i - 1;
			int loopCond = Math.max(posXPlusC, i);

			// Create the right number of states for each branch. #states is the maximum of pos(x+c) and i.
			for (int j = 1; i <= loopCond; j++) {
				String prevState = (j == 1) ? "init" : "c" + i + (j - 1);
				String state = "c" + i + j;
				automaton.addState(false, false, state);

				// Set x at position i (= transition from ith to i+1th state).
				if (j == i + 1) {
					automaton.addInternalTransition(prevState, symbol.get("xy10"), state);
					automaton.addInternalTransition(prevState, symbol.get("xy11"), state);
				}
				// Make sure this also works at the end of the loop (= transition from ith to final state).
				else if (j == i & j == loopCond) {
					automaton.addInternalTransition(state, symbol.get("xy10"), "final");
					automaton.addInternalTransition(state, symbol.get("xy11"), "final");
				}
				// Set x+c at position posXPlusC
				else if (j == posXPlusC + 1) {
					automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
				}
				// Make sure this also works at the end of the loop
				else if (j == posXPlusC & j == loopCond) {
					automaton.addInternalTransition(state, symbol.get("xy01"), "final");
				} else {
					automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
					automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
				}
			}
		}

		return null;
	}

	/**
	 * Create an automaton that represents "x+c element Y", case distinction: x+c>0, i%2=0 (means: x is 0 or negative).
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			elementAutomatonCase3(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException {

		int cInt = SmtUtils.toInt(c).intValueExact();
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");

		// TODO: Check if this works..
		if (cInt <= 0)
			return falseAutomaton(services);

		// Create one branch for each possible value of i: i<=2c-1 && i%2=0
		for (int i = 0; i <= 2 * cInt - 1; i += 2) {
			int posXPlusC = 2 * cInt - i - 1;
			int loopCond = Math.max(posXPlusC, i);

			// Create the right number of states for each branch. #states is the maximum of pos(x+c) and i.
			for (int j = 1; i <= loopCond; j++) {
				String prevState = (j == 1) ? "init" : "c" + i + (j - 1);
				String state = "c" + i + j;
				automaton.addState(false, false, state);

				// Set x at position i (= transition from ith to i+1th state).
				if (j == i + 1) {
					automaton.addInternalTransition(prevState, symbol.get("xy10"), state);
					automaton.addInternalTransition(prevState, symbol.get("xy11"), state);
				}
				// Make sure this also works at the end of the loop (= transition from ith to final state).
				else if (j == i & j == loopCond) {
					automaton.addInternalTransition(state, symbol.get("xy10"), "final");
					automaton.addInternalTransition(state, symbol.get("xy11"), "final");
				}
				// Set x+c at position posXPlusC
				else if (j == posXPlusC + 1) {
					automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
				}
				// Make sure this also works at the end of the loop
				else if (j == posXPlusC & j == loopCond) {
					automaton.addInternalTransition(state, symbol.get("xy01"), "final");
				} else {
					automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
					automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
				}
			}
		}

		return null;
	}

	/**
	 * Create an automaton that represents "x+c element Y", case distinction: x+c>0, i%2=1 (means: x is positive).
	 * 
	 * @throws AutomataLibraryException
	 * 
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			elementAutomatonCase4(final AutomataLibraryServices services, final Term x, final Rational c, final Term y)
					throws AutomataLibraryException {

		int cInt = SmtUtils.toInt(c).intValueExact();
		NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addState(false, false, "s1");
		automaton.addInternalTransition("init", symbol.get("xy00"), "s1");
		automaton.addInternalTransition("init", symbol.get("xy01"), "s1");
		automaton.addInternalTransition("s1", symbol.get("xy00"), "init");
		automaton.addInternalTransition("s1", symbol.get("xy01"), "init");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");
		automaton.addInternalTransition("final", symbol.get("xy01"), "final");

		if (cInt == 0)
			automaton.addInternalTransition("s1", symbol.get("xy11"), "final");

		for (int i = 1; i <= 2 * cInt; i++) {
			String prevState = "c" + (i - 1);
			String state = "c" + i;

			automaton.addState(false, false, state);

			if (i > 1) {
				automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
				automaton.addInternalTransition(prevState, symbol.get("xy01"), state);
			}

			if (i == 2 * cInt) {
				if (cInt > 0) {
					automaton.addInternalTransition("s1", symbol.get("xy10"), "c1");
					automaton.addInternalTransition("s1", symbol.get("xy11"), "c1");
					automaton.addInternalTransition(state, symbol.get("xy01"), "final");
				} else {
					automaton.addInternalTransition("s1", symbol.get("xy01"), "c1");
					automaton.addInternalTransition(state, symbol.get("xy10"), "final");
					automaton.addInternalTransition(state, symbol.get("xy11"), "final");
				}
			}
		}

		// Make sure that position of x+c >= 0, by ensuring that i>=2c.
		if (cInt < 0) {
			final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> tmp = emptyAutomaton(services);
			Map<String, MoNatDiffAlphabetSymbol> tmpSymbol = createAlphabet(tmp, x, y);

			tmp.addState(true, false, "init");
			tmp.addState(false, true, "final");
			tmp.addInternalTransition("final", tmpSymbol.get("xy00"), "final");
			tmp.addInternalTransition("final", tmpSymbol.get("xy01"), "final");

			for (int i = 1; i <= 2 * cInt; i++) {
				String prevState = i == 1 ? "init" : "c" + (i - 1);
				String state = "c" + i;

				tmp.addState(false, false, state);
				tmp.addInternalTransition(prevState, tmpSymbol.get("xy00"), state);
				tmp.addInternalTransition(prevState, tmpSymbol.get("xy01"), state);

				if (i == 2 * cInt) {
					tmp.addState(false, false, "l0");
					tmp.addInternalTransition(state, symbol.get("xy00"), "l0");
					tmp.addInternalTransition(state, symbol.get("xy01"), "l0");
					tmp.addInternalTransition("l0", symbol.get("xy00"), state);
					tmp.addInternalTransition("l0", symbol.get("xy01"), state);
					tmp.addInternalTransition(state, tmpSymbol.get("xy10"), "final");
					tmp.addInternalTransition(state, tmpSymbol.get("xy11"), "final");
				}
			}

			automaton = (NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>) new Intersect<>(services,
					new MoNatDiffStringFactory(), automaton, tmp).getResult();
		}

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "c element X".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String>
			constElementAutomaton(final AutomataLibraryServices services, final Rational c, final Term x) {

		if (!MoNatDiffUtils.isSetOfIntVariable(x))
			throw new IllegalArgumentException("Input x must be a SetOfInt variable.");

		int cInt = SmtUtils.toInt(c).intValueExact();
		int cIntAbs = Math.abs(cInt);
		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton = emptyAutomaton(services);
		Map<String, MoNatDiffAlphabetSymbol> symbol = createAlphabet(automaton, x);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("x0"), "final");
		automaton.addInternalTransition("final", symbol.get("x1"), "final");

		if (cInt == 0)
			automaton.addInternalTransition("init", symbol.get("x1"), "final");

		int loopCond = cInt > 0 ? 2 * cInt - 1 : 2 * cIntAbs;

		for (int i = 1; i <= loopCond; i++) {
			String prevState = "c" + (i - 1);
			String state = "c" + i;

			automaton.addState(false, false, state);

			if (i == 1)
				prevState = "init";

			automaton.addInternalTransition(prevState, symbol.get("x0"), state);
			automaton.addInternalTransition(prevState, symbol.get("x1"), state);

			if (i == loopCond)
				automaton.addInternalTransition(state, symbol.get("x1"), "final");
		}

		return automaton;
	}

	/**
	 * Some repeating part with constant in the automaton
	 */
	private static void repeatingPartConst(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final MoNatDiffAlphabetSymbol first, final MoNatDiffAlphabetSymbol second,
			final MoNatDiffAlphabetSymbol xy00, final MoNatDiffAlphabetSymbol xy11, final Rational c) {

		int cInt = SmtUtils.toInt(c).intValueExact();

		if (cInt == 1)
			return;

		automaton.addState(false, false, "p1");
		automaton.addState(false, false, "p2");

		for (int i = 1; i <= (2 * cInt - 2); i++) {
			automaton.addState(false, false, "c" + i);
			if (i > 1)
				automaton.addInternalTransition("c" + (i - 1), xy00, "c" + i);
			if (i % 2 == 0)
				automaton.addInternalTransition("c" + i, second, "final");
		}

		automaton.addInternalTransition("p1", xy00, "p2");
		automaton.addInternalTransition("p2", xy00, "p1");
		automaton.addInternalTransition("p1", first, "c1");
	}

	/**
	 * Some repeating part in the automaton
	 */
	private static void repeatingPart(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
			final MoNatDiffAlphabetSymbol first, final MoNatDiffAlphabetSymbol second,
			final MoNatDiffAlphabetSymbol xy00, final MoNatDiffAlphabetSymbol xy11, final boolean concurrent) {

		for (int i = 1; i <= 5; i++) {
			automaton.addState(false, false, "q" + i);
		}
		automaton.addInternalTransition("q1", xy00, "q2");
		automaton.addInternalTransition("q2", xy00, "q1");
		automaton.addInternalTransition("q1", first, "q3");
		automaton.addInternalTransition("q3", xy00, "q4");
		automaton.addInternalTransition("q4", xy00, "q5");
		automaton.addInternalTransition("q5", xy00, "q4");
		automaton.addInternalTransition("q4", second, "final");

		if (concurrent)
			automaton.addInternalTransition("q1", xy11, "final");
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

				final Iterator<MoNatDiffAlphabetSymbol> itMatches =
						isExtended ? alphabet.stream().filter(e -> e.contains(transition.getLetter())).iterator()
								: alphabet.stream().filter(e -> transition.getLetter().contains(e)).iterator();

				while (itMatches.hasNext()) {
					result.addInternalTransition(state, itMatches.next(), transition.getSucc());
				}
			}
		}

		return result;
	}

	/**
	 * TODO: Move to MoNatDiffAlphabetSymbol
	 */
	public static Map<String, MoNatDiffAlphabetSymbol>
			createAlphabet(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final Term... terms) {
		Map<String, MoNatDiffAlphabetSymbol> alphabetSymbols = new HashMap<String, MoNatDiffAlphabetSymbol>();

		// Deal with all other term length

		if (terms.length == 1) {
			final MoNatDiffAlphabetSymbol x0, x1;
			x0 = new MoNatDiffAlphabetSymbol(terms[0], false);
			x1 = new MoNatDiffAlphabetSymbol(terms[0], true);
			alphabetSymbols.put("x0", x0);
			alphabetSymbols.put("x1", x1);
			automaton.getAlphabet().addAll(Arrays.asList(x0, x1));
		}

		if (terms.length == 2) {
			final MoNatDiffAlphabetSymbol xy00, xy01, xy10, xy11;
			xy00 = new MoNatDiffAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, false });
			xy01 = new MoNatDiffAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, true });
			xy10 = new MoNatDiffAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, false });
			xy11 = new MoNatDiffAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, true });
			alphabetSymbols.put("xy00", xy00);
			alphabetSymbols.put("xy01", xy01);
			alphabetSymbols.put("xy10", xy10);
			alphabetSymbols.put("xy11", xy11);
			automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));
		}

		return alphabetSymbols;
	}
}

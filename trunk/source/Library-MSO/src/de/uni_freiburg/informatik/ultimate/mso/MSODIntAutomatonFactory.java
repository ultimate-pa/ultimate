/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
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
 * 1. Find meaningful names for the automata representing only one case of the
 * complete automaton. 2. Test all (new) Int automata. 3. Note: Some methods are
 * redundant to the ones in MoNatDiffAutomatonFactory (even though some are
 * shortened by the use of createAlphabet) including: emptyAutomaton,
 * trueAutomaton, falseAutomaton, intVariableAutomaton, reconstruct,
 * createAlphabet, strictSubsetAutomaton, nonStrictSubsetAutomaton 4.
 * nonStrictSubset changed such that actually no transition is needed to be
 * accepting.
 * 
 */

final class Counter {

	public int prev() {
		assert value > 1 : "Counter value < 2.";
		return value - 1;
	}

	public String prevState() {
		return "s" + (prev() - 1);
	}

	public int value() {
		assert value > 0 : "Counter value < 1.";
		return value;
	}

	public String state() {
		return "s" + (value() - 1);
	}

	public int next() {
		return ++value;
	}

	public String nextState() {
		return "s" + (next() - 1);
	}

	private int value = 0;
};

public class MSODIntAutomatonFactory extends MSODAutomatonFactory {
	
	/**
	 * Constructs an automaton that represents "x < c".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type Int.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational constant) {

		if (!MSODUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be an Int variable.");

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
			for (int i = 0; i < 2 * Math.abs(c); i++)
			{
				final String state = "c" + i;
				automaton.addState(false, false, state);
				automaton.addInternalTransition(pred, x0, state);
				pred = state;
			}
			
			automaton.addState(false, false, "s1");
			automaton.addInternalTransition(pred, x0, "s1");
			automaton.addInternalTransition("s1", x1, "final");
			
			automaton.addState(false, false, "s2");
			automaton.addInternalTransition("s1", x0, "s2");
			automaton.addInternalTransition("s2", x0, "s1");
		}
		
		if (c > 0)
		{
			automaton.addInternalTransition("init", x1, "final");
			
			String pred = "init";
			for (int i = 0; i < 2 * (Math.abs(c) - 1); i++)
			{
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
	 * Creates an automaton that represents "x+c element Y".
	 * 
	 * @throws AutomataLibraryException
	 * 
	 * @throws IllegalArgumentException
	 *             if x, y are not of type Int respectively SetOfInt.
	 */
	public static INestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational constant, final Term y)
			throws AutomataLibraryException {

		if (!MSODUtils.isIntVariable(x) || !MSODUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be Int respectively SetOfInt variables.");

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

		if (c >= 0)
			return automaton;

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

		if (c <= 0)
			return automaton;

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
	 * Create automaton for x - y < c. The automaton consists of four parts, one for
	 * each of the following case distinctions: x,y < 0; x,y >= 0; x < 0, y >= 0 and
	 * x >= 0, y < 0.
	 * 
	 * @throws AutomataLibraryException
	 */
	public static INestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
			throws AutomataLibraryException {

		Set<MSODAlphabetSymbol> symbols;
		final List<INestedWordAutomaton<MSODAlphabetSymbol, String>> automata = new ArrayList<INestedWordAutomaton<MSODAlphabetSymbol, String>>();
		automata.add(strictIneqAtomatonCase1(services, x, y, c));
		automata.add(strictIneqAutomatonCase2(services, x, y, c));
		automata.add(strictIneqAutomatonCase3(services, x, y, c));
		automata.add(strictIneqAutomatonCase4(services, x, y, c));

		INestedWordAutomaton<MSODAlphabetSymbol, String> result;
		INestedWordAutomaton<MSODAlphabetSymbol, String> tmp;

		result = automata.get(0);
		for (int i = 1; i < 4; i++) {
			symbols = MSODUtils.mergeAlphabets(result.getAlphabet(), automata.get(i).getAlphabet());
			result = reconstruct(services, result, symbols, true);
			tmp = reconstruct(services, automata.get(i), symbols, true);
			result = new Union<>(services, new MSODStringFactory(), result, tmp).getResult();
		}

		result = new MinimizeSevpa<>(services, new MSODStringFactory(), result).getResult();

		return result;
	}

	/**
	 * Create automaton for x - y < c, case distinction: x, y < 0.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAtomatonCase1(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final int cIntAbs = Math.abs(cInt);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomatonCase2(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final int cIntAbs = Math.abs(cInt);

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		if (cInt > 0) {
			// x <= y
			repeatingPart(automaton, symbol.get("xy10"), symbol.get("xy01"), symbol.get("xy00"), symbol.get("xy11"),
					true);
			automaton.addInternalTransition("init", symbol.get("xy00"), "q1");
			automaton.addInternalTransition("init", symbol.get("xy10"), "q4");
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
				if (i == 2)
					automaton.addInternalTransition("init", symbol.get("xy10"), "c" + i);

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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomatonCase3(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);
		final int cInt = SmtUtils.toInt(c).intValueExact();
		final int cIntAbs = Math.abs(cInt);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("xy00"), "final");

		if (cInt > 0) {
			for (int i = 1; i <= 7; i++)
				automaton.addState(false, false, "s" + i);

			// |x| <= y
			automaton.addInternalTransition("init", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s2");
			automaton.addInternalTransition("s2", symbol.get("xy00"), "s1");
			automaton.addInternalTransition("s1", symbol.get("xy00"), "s3");
			automaton.addInternalTransition("s3", symbol.get("xy10"), "s4");
			automaton.addInternalTransition("s4", symbol.get("xy00"), "s5");
			automaton.addInternalTransition("s5", symbol.get("xy00"), "s4");
			automaton.addInternalTransition("s4", symbol.get("xy01"), "final");

			// |x| > y
			automaton.addInternalTransition("init", symbol.get("xy01"), "s3");
			automaton.addInternalTransition("s6", symbol.get("xy00"), "s7");
			automaton.addInternalTransition("s7", symbol.get("xy00"), "s6");
			automaton.addInternalTransition("s1", symbol.get("xy01"), "s7");
			automaton.addInternalTransition("s7", symbol.get("xy10"), "final");

		} else {
			// Add branching states
			for (int i = 1; i <= Math.max(0, cIntAbs - 1) + 2; i++) {
				String prevState = "s" + (i - 1);
				final String state = "s" + i;

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
					final String prevState = "c" + i + "_" + (j - 1);
					final String state = "c" + i + "_" + j;
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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomatonCase4(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c) {

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

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
			final String prevState = "c" + (i - 1);
			final String state = "c" + i;
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
			final String state = "s" + i;

			if (i == 1)
				prevState = "init";

			automaton.addState(false, false, state);
			automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
		}

		// Add "x-states" and transitions
		for (int i = 1; i <= (cInt - 2); i++) {
			for (int j = 1; j <= 2 * cInt - 4 * i - 1; j++) {
				final String prevStateX = "x" + i + "_" + (j - 1);
				final String stateX = "x" + i + "_" + j;
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
				final String prevStateY = "y" + i + "_" + (j - 1);
				final String stateY = "y" + i + "_" + j;
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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictNegIneqAutomaton(
			final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MSODUtils.isIntVariable(x))
			throw new IllegalArgumentException("Input x must be Int variable.");

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final int cIntAbs = Math.abs(cInt);
		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x);

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
				final String prevState = (i == 1) ? "init" : "c" + (i - 1);
				final String state = "c" + i;

				automaton.addState(false, false, state);
				automaton.addInternalTransition(prevState, symbol.get("x0"), state);

				if (i % 2 == 1)
					automaton.addInternalTransition(state, symbol.get("x1"), "final");

				if (i == 2 * cInt - 1) {
					automaton.addState(false, false, "l0");
					automaton.addInternalTransition(state, symbol.get("x0"), "l0");
					automaton.addInternalTransition("l0", symbol.get("x0"), state);
				}
			}
		}

		if (cInt < 0) {
			for (int i = 1; i <= 2 * cIntAbs + 1; i++) {
				final String prevState = (i == 1) ? "init" : "c" + (i - 1);
				final String state = "c" + i;

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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> strictSubsetAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntVariable(x) || !MSODUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

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
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> subsetAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y) {

		if (!MSODUtils.isSetOfIntVariable(x) || !MSODUtils.isSetOfIntVariable(y))
			throw new IllegalArgumentException("Input x, y must be SetOfInt variables.");

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x, y);

		automaton.addState(true, true, "init");
		automaton.addInternalTransition("init", symbol.get("xy00"), "init");
		automaton.addInternalTransition("init", symbol.get("xy01"), "init");
		automaton.addInternalTransition("init", symbol.get("xy11"), "init");

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "c element X".
	 * 
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> constElementAutomaton(
			final AutomataLibraryServices services, final Rational c, final Term x) {

		if (!MSODUtils.isSetOfIntVariable(x))
			throw new IllegalArgumentException("Input x must be a SetOfInt variable.");

		final int cInt = SmtUtils.toInt(c).intValueExact();
		final int cIntAbs = Math.abs(cInt);
		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final Map<String, MSODAlphabetSymbol> symbol = createAlphabet(automaton, x);

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", symbol.get("x0"), "final");
		automaton.addInternalTransition("final", symbol.get("x1"), "final");

		if (cInt == 0)
			automaton.addInternalTransition("init", symbol.get("x1"), "final");

		final int loopCond = cInt > 0 ? 2 * cInt - 1 : 2 * cIntAbs;

		for (int i = 1; i <= loopCond; i++) {
			String prevState = "c" + (i - 1);
			final String state = "c" + i;

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
	private static void repeatingPartConst(final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton,
			final MSODAlphabetSymbol first, final MSODAlphabetSymbol second, final MSODAlphabetSymbol xy00,
			final MSODAlphabetSymbol xy11, final Rational c) {

		final int cInt = SmtUtils.toInt(c).intValueExact();

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
	private static void repeatingPart(final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton,
			final MSODAlphabetSymbol first, final MSODAlphabetSymbol second, final MSODAlphabetSymbol xy00,
			final MSODAlphabetSymbol xy11, final boolean concurrent) {

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
	 * Constructs a copy of the given automaton with the extended or reduced
	 * alphabet.
	 */
	public static NestedWordAutomaton<MSODAlphabetSymbol, String> reconstruct(final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Set<MSODAlphabetSymbol> alphabet,
			final boolean isExtended) {

		final NestedWordAutomaton<MSODAlphabetSymbol, String> result;

		result = MSODNatAutomatonFactory.emptyAutomaton(services);
		result.getAlphabet().addAll(alphabet);

		for (final String state : automaton.getStates())
			result.addState(automaton.isInitial(state), automaton.isFinal(state), state);

		for (final String state : automaton.getStates()) {

			for (final OutgoingInternalTransition<MSODAlphabetSymbol, String> transition : automaton
					.internalSuccessors(state)) {

				final Iterator<MSODAlphabetSymbol> itMatches = isExtended
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
	 * TODO: Move to MoNatDiffAlphabetSymbol
	 */
	public static Map<String, MSODAlphabetSymbol> createAlphabet(
			final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Term... terms) {
		final Map<String, MSODAlphabetSymbol> alphabetSymbols = new HashMap<String, MSODAlphabetSymbol>();

		// Deal with all other term length

		if (terms.length == 1) {
			final MSODAlphabetSymbol x0, x1;
			x0 = new MSODAlphabetSymbol(terms[0], false);
			x1 = new MSODAlphabetSymbol(terms[0], true);
			alphabetSymbols.put("x0", x0);
			alphabetSymbols.put("x1", x1);
			automaton.getAlphabet().addAll(Arrays.asList(x0, x1));
		}

		if (terms.length == 2) {
			final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
			xy00 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, false });
			xy01 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, true });
			xy10 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, false });
			xy11 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, true });
			alphabetSymbols.put("xy00", xy00);
			alphabetSymbols.put("xy01", xy01);
			alphabetSymbols.put("xy10", xy10);
			alphabetSymbols.put("xy11", xy11);
			automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));
		}

		return alphabetSymbols;
	}
}

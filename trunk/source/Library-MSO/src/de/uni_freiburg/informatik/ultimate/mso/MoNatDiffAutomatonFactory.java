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
	 * Constructs a copy of the given automaton with the extended or reduced
	 * alphabet.
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
	
	// Test automaton fot int numbers
	
	/**
	 * TODO: Create automaton for x - y < c, x,y Int
	 * 
	 * @throws AutomataLibraryException
	 */

	public static INestedWordAutomaton<MoNatDiffAlphabetSymbol, String> testCompleteAutomaton(
			final AutomataLibraryServices services, final Term x, final Term y, final Rational c)
			throws AutomataLibraryException {

		Set<MoNatDiffAlphabetSymbol> symbols;
		List<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>> automata = new ArrayList<INestedWordAutomaton<MoNatDiffAlphabetSymbol, String>>();
		automata.add(testAutomaton(services, x, y, c));
		automata.add(testAutomaton1(services, x, y, c));
		automata.add(testAutomaton2(services, x, y, c));
		automata.add(testAutomaton3(services, x, y, c));

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
	 * TODO: Test Automaton for x - y < c, for x >= 0, y < 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> testAutomaton(
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
	 * TODO: Test Automaton for x - y < c, x, y < 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> testAutomaton1(
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
			testRepeatingPart(automaton, symbol.get("xy01"), symbol.get("xy10"), symbol.get("xy00"), symbol.get("xy11"),
					true);
			automaton.addInternalTransition("s1", symbol.get("xy00"), "q1");
	
			// |y| > |x|
			if (cInt > 1) {
				testRepeatingPartConst(automaton, symbol.get("xy10"), symbol.get("xy01"), symbol.get("xy00"),
						symbol.get("xy11"), c);
				automaton.addInternalTransition("s1", symbol.get("xy00"), "p1");
			}
		}
		else {
			for (int i = 0; i <= 3; i++)
				automaton.addState(false, false, "s" + i);
				
			for (int i = 1; i <= (2*cIntAbs+2); i++) {
				automaton.addState(false, false, "c" + i);
				
				if (i == 1)
					automaton.addInternalTransition("s1", symbol.get("xy01"), "c" + i);
				else
					automaton.addInternalTransition("c" + (i-1), symbol.get("xy00"), "c" + i);
				
				if (i == (2*cIntAbs+2)) {
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
	 * TODO: Test Automaton for x - y < c, x, y >= 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> testAutomaton2(
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
			testRepeatingPart(automaton, symbol.get("xy10"), symbol.get("xy01"), symbol.get("xy00"), symbol.get("xy11"),
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
				testRepeatingPartConst(automaton, symbol.get("xy01"), symbol.get("xy10"), symbol.get("xy00"),
						symbol.get("xy11"), c);
				automaton.addInternalTransition("init", symbol.get("xy00"), "p1");
				automaton.addInternalTransition("s2", symbol.get("xy00"), "c1");
			}
		}
		
		else {
			for (int i = 0; i <= 2; i++)
				automaton.addState(false, false, "s" + i);
				
			for (int i = 1; i <= (2*cIntAbs+2); i++) {
				automaton.addState(false, false, "c" + i);
				
				if (i == 1)
					automaton.addInternalTransition("s0", symbol.get("xy10"), "c" + i);
				else
					automaton.addInternalTransition("c" + (i-1), symbol.get("xy00"), "c" + i);
				
				if (i == (2*cIntAbs+2)) {
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
	 * TODO: Test Automaton for x - y < c, x < 0, y >= 0.
	 */
	public static NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> testAutomaton3(
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
		}
		else {
			// Add branching states
			for (int i = 1; i <= Math.max(0, cIntAbs-1)+2; i++) {
				String prevState = "s" + (i - 1);
				String state = "s" + i;

				if (i == 1)
					prevState = "init";

				automaton.addState(false, false, state);
				automaton.addInternalTransition(prevState, symbol.get("xy00"), state);
				
				if (i == Math.max(0, cIntAbs-1)+1) {
					automaton.addState(false, false, "l");
					automaton.addInternalTransition(state, symbol.get("xy00"), "l" );
					automaton.addInternalTransition("l", symbol.get("xy00"), state);
				}
			}
			
			// Add x and y states
			for (int i = 0; i <= Math.max(0, cIntAbs-1)+2; i++) {
				int loopCond = Math.max(1, (2*cIntAbs-2*i+1));
				
				if (i == 0) {
					loopCond = 2*(cIntAbs+1);
					if (cIntAbs == 0)
						loopCond = 2;
				}
				
				for (int j = 1; j <= loopCond; j++) {
					String prevState = "c" + i + (j-1);
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
					}
					else
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
	 * TODO: Some repeating part with constant in the automaton
	 */
	private static void testRepeatingPartConst(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
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
	 * TODO: Some repeating part in the automaton
	 */
	private static void testRepeatingPart(final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton,
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
	 * TODO: Move to MoNatDiffAlphabetSymbol
	 */
	public static Map<String, MoNatDiffAlphabetSymbol> createAlphabet(
			final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> automaton, final Term... terms) {
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

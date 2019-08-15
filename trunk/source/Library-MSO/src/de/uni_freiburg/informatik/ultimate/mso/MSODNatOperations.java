/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * TODO: Comment.
 *
 * TODO: Check inputs.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODNatOperations extends MSODOperations {

	/**
	 * Constructs an automaton that represents "x < c".
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c) {

		if (!MSODUtils.isIntVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);
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
	 *             if x, y are not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> strictIneqAutomaton(final AutomataLibraryServices services,
			final Term x, final Term y, final Rational c) {

		if (!MSODUtils.isIntVariable(x) || !MSODUtils.isIntVariable(y) || c.isNegative()) {
			throw new IllegalArgumentException("Input x, y must be Int variables and c must be >= 0.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
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
	 *             if x is not of type Int or c is less than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String>
			strictNegIneqAutomaton(final AutomataLibraryServices services, final Term x, final Rational c) {

		if (!MSODUtils.isIntVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be an Int variable and c must be >= 0.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);
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

		if (c.signum() == 1) {
			automaton.addInternalTransition("init", x1, "final");
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

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
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

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
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
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> elementAutomaton(final AutomataLibraryServices services,
			final Term x, final Rational c, final Term y) {

		if (!MSODUtils.isIntVariable(x) || !MSODUtils.isSetOfIntVariable(y) || c.isNegative()) {
			throw new IllegalArgumentException("Input x, y must be Int, SetOfInt variables and c must be >= 0.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
		xy00 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, false });
		xy01 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { false, true });
		xy10 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, false });
		xy11 = new MSODAlphabetSymbol(new Term[] { x, y }, new boolean[] { true, true });
		automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("init", xy00, "init");
		automaton.addInternalTransition("init", xy01, "init");
		automaton.addInternalTransition("final", xy00, "final");
		automaton.addInternalTransition("final", xy01, "final");

		if (c.signum() == 0) {
			automaton.addInternalTransition("init", xy11, "final");
		}

		addConstPart(automaton, c, xy10, xy11, xy00, xy01, xy01);

		return automaton;
	}

	/**
	 * Constructs an automaton that represents "c element X".
	 *
	 * @throws IllegalArgumentException
	 *             if x is not of type SetOfInt or c is smaller than 0.
	 */
	@Override
	public NestedWordAutomaton<MSODAlphabetSymbol, String> constElementAutomaton(final AutomataLibraryServices services,
			final Rational c, final Term x) {

		if (!MSODUtils.isSetOfIntVariable(x) || c.isNegative()) {
			throw new IllegalArgumentException("Input x must be a SetOfInt variable and c must be >= 0.");
		}

		final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton = emptyAutomaton(services);
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);
		automaton.getAlphabet().addAll(Arrays.asList(x0, x1));

		automaton.addState(true, false, "init");
		automaton.addState(false, true, "final");
		automaton.addInternalTransition("final", x0, "final");
		automaton.addInternalTransition("final", x1, "final");

		if (c.signum() == 0) {
			automaton.addInternalTransition("init", x1, "final");
		}

		addConstPart(automaton, c, x0, x1, x0, x1, x1);

		return automaton;
	}

	/**
	 * Adds a part to the given automaton that represents the value of constant c.
	 */
	private static void addConstPart(final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Rational c,
			final MSODAlphabetSymbol initToState1, final MSODAlphabetSymbol initToState2,
			final MSODAlphabetSymbol predToState1, final MSODAlphabetSymbol predToState2,
			final MSODAlphabetSymbol stateToFinal) {

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

			if (i == cInt - 1) {
				automaton.addInternalTransition(state, stateToFinal, "final");
			}
		}
	}

	/**
	 * Adds a part to the given automaton that represents values from 0 up to constant c.
	 */
	private static void addUpToConstPart(final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton,
			final Rational c, final MSODAlphabetSymbol initToState, final MSODAlphabetSymbol predToState,
			final MSODAlphabetSymbol stateToFinal) {

		final int cInt = SmtUtils.toInt(c).intValueExact();

		for (int i = 0; i < cInt; i++) {
			final String state = "c" + String.valueOf(i + 1);
			automaton.addState(false, false, state);

			if (i == 0) {
				automaton.addInternalTransition("init", initToState, state);
			}

			if (i > 0) {
				final String pred = "c" + String.valueOf(i);
				automaton.addInternalTransition(pred, predToState, state);
			}

			automaton.addInternalTransition(state, stateToFinal, "final");
		}
	}

	/**
	 * TODO Comment.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	@Override
	public Map<Term, Term> getResult(final Script script, final AutomataLibraryServices services,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		Map<Term, Term> result = new HashMap<>();

		final IsEmpty<MSODAlphabetSymbol, String> isEmpty = new IsEmpty<>(services, automaton);

		if (!isEmpty.getResult()) {
			final NestedRun<MSODAlphabetSymbol, String> run = isEmpty.getNestedRun();
			final NestedWord<MSODAlphabetSymbol> word = run.getWord();

			final Term[] terms = automaton.getAlphabet().iterator().next().getTerms();
			result = MSODUtils.parseMSODNatToTerm(script, word, terms);
		}

		return result;
	}

}

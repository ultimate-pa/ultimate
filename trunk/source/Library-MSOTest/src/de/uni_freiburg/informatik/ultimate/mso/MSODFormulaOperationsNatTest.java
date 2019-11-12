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

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODFormulaOperationsNatTest {
	private IUltimateServiceProvider mServiceProvider;
	private AutomataLibraryServices mALS;
	private Script mScript;
	private ILogger mLogger;

	private final MSODFormulaOperationsNat mOperations = new MSODFormulaOperationsNat();
	private static final String WORD_SEP = " ";

	@Before
	public void setUp() {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mALS = new AutomataLibraryServices(mServiceProvider);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("lol");

		mScript.setLogic(Logics.UFLIA);
		mScript.declareSort("SetOfInt", 0);
	}

	/**
	 * Returns a {@link NestedWord} parsed from the given string.
	 */
	private static NestedWord<MSODAlphabetSymbol> parseWord(final Term term, final String values) {
		final MSODAlphabetSymbol[] symbols = new MSODAlphabetSymbol[values.length()];
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		for (int i = 0; i < values.length(); i++) {

			if ('0' == values.charAt(i)) {
				symbols[i] = x0;
				continue;
			}
			if ('1' == values.charAt(i)) {
				symbols[i] = x1;
				continue;
			}
			throw new IllegalArgumentException("Failure during parsing: " + values);
		}

		return NestedWord.nestedWord(new Word<>(symbols));
	}

	/**
	 * Returns a {@link NestedWord} parsed from the given strings.
	 */
	private static NestedWord<MSODAlphabetSymbol> parseWord(final Term term1, final Term term2, final String values1,
			final String values2) {

		assert (values1.length() == values2.length());

		final MSODAlphabetSymbol[] symbols = new MSODAlphabetSymbol[values1.length()];
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(term1, term2, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(term1, term2, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(term1, term2, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(term1, term2, true, true);

		for (int i = 0; i < values1.length(); i++) {

			if ('0' == values1.charAt(i) && '0' == values2.charAt(i)) {
				symbols[i] = xy00;
				continue;
			}
			if ('1' == values1.charAt(i) && '0' == values2.charAt(i)) {
				symbols[i] = xy10;
				continue;
			}
			if ('0' == values1.charAt(i) && '1' == values2.charAt(i)) {
				symbols[i] = xy01;
				continue;
			}
			if ('1' == values1.charAt(i) && '1' == values2.charAt(i)) {
				symbols[i] = xy11;
				continue;
			}
			throw new IllegalArgumentException("Failure during parsing: " + values1 + ", " + values2);
		}

		return NestedWord.nestedWord(new Word<>(symbols));
	}

	/**
	 * Returns a {@link NestedLassoWord} parsed from the given string.
	 */
	private static NestedLassoWord<MSODAlphabetSymbol> parseLassoWord(final Term term, final String values) {
		final String[] v = values.split(WORD_SEP);
		assert (v.length == 2);

		return new NestedLassoWord<>(parseWord(term, v[0]), parseWord(term, v[1]));
	}

	/**
	 * Returns a {@link NestedLassoWord} parsed from the given strings.
	 */
	private static NestedLassoWord<MSODAlphabetSymbol> parseLassoWord(final Term term1, final Term term2,
			final String values1, final String values2) {

		final String[] v1 = values1.split(WORD_SEP);
		final String[] v2 = values2.split(WORD_SEP);
		assert (v1.length == 2 && v2.length == 2);

		return new NestedLassoWord<>(parseWord(term1, term2, v1[0], v2[0]), parseWord(term1, term2, v1[1], v2[1]));
	}

	/**
	 * Tests if a given {@link NestedWord} is or is not accepted by the given {@link INestedWordAutomaton}.
	 */
	private void test(final Boolean result, final NestedWord<MSODAlphabetSymbol> word,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final Accepts<MSODAlphabetSymbol, String> accepts = new Accepts<>(mALS, automaton, word);

		mLogger.info("Word: " + word);
		mLogger.info("Expected: " + result + " / Result: " + accepts.getResult());
		Assert.assertEquals(result, accepts.getResult());
	}

	/**
	 * Tests if a given {@link NestedLassoWord} is or is not accepted by the given {@link INestedWordAutomaton}.
	 */
	private void test(final Boolean result, final NestedLassoWord<MSODAlphabetSymbol> word,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final BuchiAccepts<MSODAlphabetSymbol, String> accepts = new BuchiAccepts<>(mALS, automaton, word);

		mLogger.info("Word: " + word);
		mLogger.info("Expected: " + result + " / Result: " + accepts.getResult());
		Assert.assertEquals(result, accepts.getResult());
	}

	/**
	 * Test Cases for x < c.
	 */
	@Test
	public void strictIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Test strictIneqAutomaton x < c ...");

		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// false: 0 < 0
		c = Rational.valueOf(0, 1);
		test(false, parseWord(x, "1"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(false, parseWord(x, "100"), mOperations.strictIneqAutomaton(mALS, x, c));

		test(false, parseLassoWord(x, "1 0"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(false, parseLassoWord(x, "100 000"), mOperations.strictIneqAutomaton(mALS, x, c));

		// true: 0 < 1
		c = Rational.valueOf(1, 1);
		test(true, parseWord(x, "1"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(true, parseWord(x, "100"), mOperations.strictIneqAutomaton(mALS, x, c));

		test(true, parseLassoWord(x, "1 0"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(true, parseLassoWord(x, "100 000"), mOperations.strictIneqAutomaton(mALS, x, c));

		// true: 4 < 7
		c = Rational.valueOf(7, 1);
		test(true, parseWord(x, "00001"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(true, parseWord(x, "000010"), mOperations.strictIneqAutomaton(mALS, x, c));

		test(true, parseLassoWord(x, "00001 0"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(true, parseLassoWord(x, "0000100 00"), mOperations.strictIneqAutomaton(mALS, x, c));

		// false: 5 < 2
		c = Rational.valueOf(2, 1);
		test(false, parseWord(x, "000001"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(false, parseWord(x, "000001000"), mOperations.strictIneqAutomaton(mALS, x, c));

		test(false, parseLassoWord(x, "0000010 0"), mOperations.strictIneqAutomaton(mALS, x, c));
		test(false, parseLassoWord(x, "000001 00"), mOperations.strictIneqAutomaton(mALS, x, c));
	}

	/**
	 * Test Cases for x-y < c
	 */
	@Test
	public void strictIneqAutomatonXYC() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Test strictIneqAutomaton x-y < c...");

		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", SmtSortUtils.getIntSort(mScript));

		// false: 0-0 < 0
		c = Rational.valueOf(0, 1);
		test(false, parseWord(x, y, "10", "10"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(false, parseWord(x, y, "1", "1"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		test(false, parseLassoWord(x, y, "10 0", "10 0"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(false, parseLassoWord(x, y, "1 00", "1 00"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		// true: 1-2 < 0
		c = Rational.valueOf(0, 1);
		test(true, parseWord(x, y, "010", "001"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(true, parseWord(x, y, "0100", "0010"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		test(true, parseLassoWord(x, y, "010 0", "001 0"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(true, parseLassoWord(x, y, "0100 00", "0010 00"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		// false: 5-3 < 2
		c = Rational.valueOf(2, 1);
		test(false, parseWord(x, y, "0000010", "0001000"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(false, parseWord(x, y, "000001", "000100"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		test(false, parseLassoWord(x, y, "000001 0", "000100 0"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(false, parseLassoWord(x, y, "000001 00", "000100 00"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		// true: 5-4 < 2
		c = Rational.valueOf(2, 1);
		test(true, parseWord(x, y, "0000010", "0000100"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(true, parseWord(x, y, "000001", "000010"), mOperations.strictIneqAutomaton(mALS, x, y, c));

		test(true, parseLassoWord(x, y, "000001 0", "000010 0"), mOperations.strictIneqAutomaton(mALS, x, y, c));
		test(true, parseLassoWord(x, y, "0000010 00", "0000100 00"), mOperations.strictIneqAutomaton(mALS, x, y, c));
	}
}

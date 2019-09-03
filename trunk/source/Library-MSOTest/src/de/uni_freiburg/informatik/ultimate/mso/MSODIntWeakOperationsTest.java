/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
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
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODIntWeakOperationsTest {

	private IUltimateServiceProvider mServiceProvider;
	private AutomataLibraryServices mServices;
	private Script mScript;
	private ILogger mLogger;

	MSODOperations mMSODOperations =
			new MSODOperations(new MSODFormulaOperationsInt(), new MSODAutomataOperationsWeak());

	@Rule
	public final ExpectedException mNoException = ExpectedException.none();

	@Before
	public void setUp() {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mServices = new AutomataLibraryServices(mServiceProvider);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("lol");

		mScript.setLogic(Logics.UFLIA);
		mScript.declareSort("SetOfInt", 0);
	}

	private void test(final Boolean result, final NestedWord<MSODAlphabetSymbol> word,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final Accepts<MSODAlphabetSymbol, String> accepts = new Accepts<>(mServices, automaton, word);

		mLogger.info("Word: " + word);
		mLogger.info("Result: " + result + " / " + accepts.getResult());

		Assert.assertEquals(result, accepts.getResult());
	}

	private int intToIndex(final int n) {

		return n <= 0 ? 2 * Math.abs(n) : 2 * n - 1;
	}

	private NestedWord<MSODAlphabetSymbol> getWord(final Term term, final int[] values) {
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		int size = 0;
		for (int i = 0; i < values.length; i++) {
			final int index = intToIndex(values[i]);
			size = index + 1 > size ? index + 1 : size;
		}

		final MSODAlphabetSymbol[] symbols = new MSODAlphabetSymbol[size];
		Arrays.fill(symbols, x0);

		for (int i = 0; i < values.length; i++) {
			final int index = intToIndex(values[i]);
			symbols[index] = x1;
		}

		return NestedWord.nestedWord(new Word<>(symbols));
	}

	private NestedWord<MSODAlphabetSymbol> getWord(final Term term1, final int[] values1, final Term term2,
			final int[] values2) {

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(term1, term2, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(term1, term2, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(term1, term2, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(term1, term2, true, true);

		int size = 0;
		for (int i = 0; i < values1.length; i++) {
			final int index = intToIndex(values1[i]);
			size = index + 1 > size ? index + 1 : size;
		}

		for (int i = 0; i < values2.length; i++) {
			final int index = intToIndex(values2[i]);
			size = index + 1 > size ? index + 1 : size;
		}

		final MSODAlphabetSymbol[] symbols = new MSODAlphabetSymbol[size];
		Arrays.fill(symbols, xy00);

		for (int i = 0; i < values1.length; i++) {
			final int index = intToIndex(values1[i]);
			symbols[index] = xy10;
		}

		for (int i = 0; i < values2.length; i++) {
			final int index = intToIndex(values2[i]);
			symbols[index] = symbols[index] == xy10 ? xy11 : xy01;
		}

		return NestedWord.nestedWord(new Word<>(symbols));
	}

	@Test
	public void strictIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");
		int[] xValues;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x < c AND c <= 0

		// -1 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -1 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -3 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -3 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -3 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { -3 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 0 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		test(false, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -1 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { -1 };
		test(false, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// Test Cases for: x < c AND c > 0

		// 0 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 0 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -3 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -3 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 2 < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 2 };
		test(true, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 1 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		test(false, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 3 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 3 };
		test(false, getWord(x, xValues), mMSODOperations.strictIneqAutomaton(mServices, x, c));

	}

	@Test
	public void strictIneqAutomatonXYC() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");

		int[] xValues, yValues;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x - y < c AND x > 0 AND y > 0 AND c <= 0

		// 1 - 2 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 4 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { 4 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 4 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 4 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 1 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 1 < -3
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// Test Cases for x - y < c AND x > 0 AND y > 0 AND c > 0

		// 1 - 1 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 2 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 3 - 2 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 3 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 1 < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 1 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 4 - 1 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 4 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 7 - 6 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 7 };
		yValues = new int[] { 6 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// Test Cases for x - y < c AND x <= 0 AND y <= 0 AND c <= 0

		// -1 - 0 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// - 2 - (-1) < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -5 - (-2) < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { -5 };
		yValues = new int[] { -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -1 - (-2) < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { -2 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - (-2) < -3
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { -2 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -8 - (-4) < -3
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { -8 };
		yValues = new int[] { -4 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// Test cases for x - y < c AND x <= 0 AND y <= 0 AND c > 0

		// 0 - 0 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -1 - (-1) < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -3 - (-2) < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -3 };
		yValues = new int[] { -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 0 - (-1) < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - (-4) < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { -4 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - (-3) < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { -3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 0 - (-3) < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { -3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -9 - (-5) < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -9 };
		yValues = new int[] { -5 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// Test Cases for x - y < c AND x > 0 AND y <= 0 AND c > 0

		// 1 - 0 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - (-2) < 4
		c = Rational.valueOf(4, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - (-1) < 4
		c = Rational.valueOf(4, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - (-1) < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { -1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 0 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 0 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - (-2) < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { -2 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 5 - (-4) < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 5 };
		yValues = new int[] { -4 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// Test Cases for x - y < c AND x <= 0 AND y > 0 AND c <= 0

		// -1 - 1 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 0 - 1 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 0 - 3 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -3 - 1 < -3
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { -3 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - 2 < -3
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 0 - 1 < -1
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -7 - 8 < -5
		c = Rational.valueOf(-5, 1);
		xValues = new int[] { -7 };
		yValues = new int[] { 8 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -6 - 5 < -1
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { -6 };
		yValues = new int[] { 5 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -6 - 6 < -1
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { -6 };
		yValues = new int[] { 6 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictIneqAutomaton(mServices, x, y, c));
	}

	@Test
	public void strictNegIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictNegIneqAutomaton ...");
		Rational c;
		int[] xValues;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for -x < c AND c <= 0

		// -1 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 1 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 3 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -3 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { 3 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 0 < 0
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		test(false, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -1 < -2
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { 1 };
		test(false, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// Test Cases for -x < c AND c > 0

		// 0 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 0 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 3 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 2 < 3
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -2 };
		test(true, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 1 < 1
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -1 };
		test(false, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 3 < 2
		c = Rational.valueOf(2, 1);
		xValues = new int[] { -3 };
		test(false, getWord(x, xValues), mMSODOperations.strictNegIneqAutomaton(mServices, x, c));
	}

	@Test
	public void strictSubsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictSubsetAutomaton ...");

		int[] xValues;
		int[] yValues;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x strictSubsetInt y

		// { } strictSubsetInt { 0 }
		xValues = new int[] {};
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 0 } strictSubsetInt { 0, 1 }
		xValues = new int[] { 0 };
		yValues = new int[] { 0, 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { -1, 2 } strictSubsetInt { -2, -1, 0, 2 }
		xValues = new int[] { -1, 2 };
		yValues = new int[] { 0, -1, 2, -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 0, 1 } strictSubsetInt { 0 }
		xValues = new int[] { 0, 1 };
		yValues = new int[] { 0 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { } strictSubsetInt { }
		xValues = new int[] {};
		yValues = new int[] {};
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { -1, 3 } strictSubsetInt { -1, 3 }
		xValues = new int[] { -1, 3 };
		yValues = new int[] { -1, 3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { -2, 3 } strictSubsetInt { 2, 3 }
		xValues = new int[] { -2, 3 };
		yValues = new int[] { 2, 3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.strictSubsetAutomaton(mServices, x, y));
	}

	@Test
	public void subsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing subsetAutomaton ...");

		int[] xValues;
		int[] yValues;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x nonStrictSubsetInt y

		// { } nonStrictSubsetInt { }
		xValues = new int[] {};
		yValues = new int[] {};
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { } nonStrictSubsetInt { 0 }
		xValues = new int[] {};
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 0 } nonStrictSubsetInt { 0 }
		xValues = new int[] { 0 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 0 } nonStrictSubsetInt { 0, 1 }
		xValues = new int[] { 0 };
		yValues = new int[] { 0, 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { -1, 3 } nonStrictSubsetInt { -1, 3 }
		xValues = new int[] { -1, 3 };
		yValues = new int[] { -1, 3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { -1, 2 } nonStrictSubsetInt { -2, -1, 0, 2 }
		xValues = new int[] { -1, 2 };
		yValues = new int[] { 0, -1, 2, -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 0, 1 } nonStrictSubsetInt { 0 }
		xValues = new int[] { 0, 1 };
		yValues = new int[] { 0 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { -2 } nonStrictSubsetInt { }
		xValues = new int[] { -2 };
		yValues = new int[] {};
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));

		// { -2, 3 } nonStrictSubsetInt { 2, 3 }
		xValues = new int[] { -2, 3 };
		yValues = new int[] { 2, 3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.subsetAutomaton(mServices, x, y));
	}

	@Test
	public void elementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing elementAutomaton ...");

		Rational c;
		int[] xValues;
		int[] yValues;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x + c element y AND x + c <= 0 AND x <= 0

		// 0 + 0 element { 0 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 0 + (-1) element { -1 }
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -1 + 1 element { 0 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -3 + 0 element { -3 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { -3 };
		yValues = new int[] { -3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 0 + (-3) element { -3 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { -3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -3 + 3 element { 0 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -3 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -4 + 3 element { 0, 1, 2 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -4 };
		yValues = new int[] { 0, 1, 2 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -5 + 4 element { }
		c = Rational.valueOf(4, 1);
		xValues = new int[] { -5 };
		yValues = new int[] {};
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// Test Cases for x + c element y AND x + c > 0 AND x > 0

		// 1 + 0 element { 1 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 2 + (-1) element { 1 }
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + 1 element { 2 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 3 + 0 element { 3 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 3 };
		yValues = new int[] { 3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 4 + (-3) element { 1 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 4 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + 3 element { 4 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 4 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + 3 element { -4 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { -4 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 5 + (-4) element { 2, 4, -4 }
		c = Rational.valueOf(-4, 1);
		xValues = new int[] { 5 };
		yValues = new int[] { 2, 4, -4 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// Test Cases for x + c element y AND x + c <= 0 AND x > 0

		// 1 + (-1) element { 0 }
		c = Rational.valueOf(-1, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 3 + (-3) element { 0 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 3 };
		yValues = new int[] { 0 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 2 + (-3) element { -1 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 2 };
		yValues = new int[] { -1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + (-3) element { -2 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { -2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 3 + (-4) element { 0, 1 }
		c = Rational.valueOf(-4, 1);
		xValues = new int[] { 3 };
		yValues = new int[] { 0, 1 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + (-3) element { 2 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 1 };
		yValues = new int[] { 2 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// Test Cases for x + c element y AND x + c > 0 AND x <= 0

		// 0 + 1 element { 1 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -2 + 3 element { 1 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -2 };
		yValues = new int[] { 1 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -1 + 3 element { 2 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { 2 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 0 + 3 element { 3 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 0 };
		yValues = new int[] { 3 };
		test(true, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -4 + 6 element { 1, -1, -2, 3 }
		c = Rational.valueOf(6, 1);
		xValues = new int[] { -4 };
		yValues = new int[] { 1, -1, -2, 3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));

		// -1 + 3 element { -3 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { -1 };
		yValues = new int[] { -3 };
		test(false, getWord(x, xValues, y, yValues), mMSODOperations.elementAutomaton(mServices, x, c, y));
	}

	@Test
	public void constElementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing constElementAutomaton ...");

		Rational c;
		int[] xValues;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for c element x AND c <= 0

		// 0 element { 0 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 0 element { 0, 3 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 0, 3 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// -3 element { -3 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { -3 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// -3 element { -3, 0, 4 }
		c = Rational.valueOf(-3, 1);
		xValues = new int[] { 0, -3, 4 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 0 element { }
		c = Rational.valueOf(0, 1);
		xValues = new int[] {};
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 0 element { -1, 1 }
		c = Rational.valueOf(0, 1);
		xValues = new int[] { 1, -1 };
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// -2 element { -1, 1 }
		c = Rational.valueOf(-2, 1);
		xValues = new int[] { 1, -1 };
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// Test Cases for c element x AND c > 0

		// 1 element { 1 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 1 element { 1, 3 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { 1, 3 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 3 element { 3 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 3 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 3 element { 0, 3, 4 }
		c = Rational.valueOf(3, 1);
		xValues = new int[] { 0, 3, 4 };
		test(true, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 1 element { }
		c = Rational.valueOf(1, 1);
		xValues = new int[] {};
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 1 element { -1, 2 }
		c = Rational.valueOf(1, 1);
		xValues = new int[] { -1, 2 };
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));

		// 2 element { -1, 1 }
		c = Rational.valueOf(2, 1);
		xValues = new int[] { 1, -1 };
		test(false, getWord(x, xValues), mMSODOperations.constElementAutomaton(mServices, c, x));
	}
}

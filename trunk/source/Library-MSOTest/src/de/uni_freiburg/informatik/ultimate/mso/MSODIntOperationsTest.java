/*
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
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
public final class MSODIntOperationsTest {
	private IUltimateServiceProvider mServiceProvider;
	private AutomataLibraryServices mServices;
	private Script mScript;
	private ILogger mLogger;

	MSODOperations mMSODOperations =
			new MSODOperations(new MSODFormulaOperationsInt(), new MSODAutomataOperationsBuchi());

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

	private void test(final Boolean result, final NestedLassoWord<MSODAlphabetSymbol> word,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final BuchiAccepts<MSODAlphabetSymbol, String> accepts = new BuchiAccepts<>(mServices, automaton, word);

		mLogger.info("Word: " + word);
		mLogger.info("Result: " + result + " / " + accepts.getResult());

		Assert.assertEquals(result, accepts.getResult());
	}

	private int intToIndex(final int n) {

		return n <= 0 ? 2 * Math.abs(n) : 2 * n - 1;
	}

	private NestedLassoWord<MSODAlphabetSymbol> getWord(final Term term, final int[] stemValues,
			final int lastStemIndex, final int[] loopValues, final int lastLoopIndex) {

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		// Construct stem.
		final MSODAlphabetSymbol[] stemSymbols = new MSODAlphabetSymbol[lastStemIndex + 1];
		Arrays.fill(stemSymbols, x0);

		for (int i = 0; i < stemValues.length; i++) {
			final int index = intToIndex(stemValues[i]);
			stemSymbols[index] = x1;
		}
		final NestedWord<MSODAlphabetSymbol> stem = NestedWord.nestedWord(new Word<>(stemSymbols));

		// Construct loop (Note: Loop is given by enumerating the indices with value = 1, as the order of positive resp.
		// negative numbers changes depending on the stem length).
		final MSODAlphabetSymbol[] loopSymbols = new MSODAlphabetSymbol[lastLoopIndex + 1];
		Arrays.fill(loopSymbols, x0);

		for (int i = 0; i < loopValues.length; i++) {
			loopSymbols[loopValues[i]] = x1;
		}
		final NestedWord<MSODAlphabetSymbol> loop = NestedWord.nestedWord(new Word<>(loopSymbols));

		// Construct NestedLassoWord.
		final NestedLassoWord<MSODAlphabetSymbol> word = new NestedLassoWord<>(stem, loop);

		return word;
	}

	private NestedLassoWord<MSODAlphabetSymbol> getWord(final Term term1, final int[] stemValues1,
			final int[] loopValues1, final Term term2, final int[] stemValues2, final int[] loopValues2,
			final int lastStemIndex, final int lastLoopIndex) {

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(term1, term2, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(term1, term2, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(term1, term2, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(term1, term2, true, true);

		// Construct stem.

		final MSODAlphabetSymbol[] stemSymbols = new MSODAlphabetSymbol[lastStemIndex + 1];
		Arrays.fill(stemSymbols, xy00);

		for (int i = 0; i < stemValues1.length; i++) {
			final int index = intToIndex(stemValues1[i]);
			stemSymbols[index] = xy10;
		}

		for (int i = 0; i < stemValues2.length; i++) {
			final int index = intToIndex(stemValues2[i]);
			stemSymbols[index] = stemSymbols[index] == xy10 ? xy11 : xy01;
		}
		final NestedWord<MSODAlphabetSymbol> stem = NestedWord.nestedWord(new Word<>(stemSymbols));

		// Construct loop
		final MSODAlphabetSymbol[] loopSymbols = new MSODAlphabetSymbol[lastLoopIndex + 1];
		Arrays.fill(loopSymbols, xy00);

		for (int i = 0; i < loopValues1.length; i++) {
			loopSymbols[loopValues1[i]] = xy10;
		}

		for (int i = 0; i < loopValues2.length; i++) {
			loopSymbols[loopValues2[i]] = loopSymbols[loopValues2[i]] == xy10 ? xy11 : xy01;
		}
		final NestedWord<MSODAlphabetSymbol> loop = NestedWord.nestedWord(new Word<>(loopSymbols));

		// Construct NestedLassoWord.
		final NestedLassoWord<MSODAlphabetSymbol> word = new NestedLassoWord<>(stem, loop);

		return word;
	}

	@Test
	public void strictIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");

		int[] xValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int lastLoopIndex;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x < c

		// 0 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] {};
		lastLoopIndex = 10;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -1 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { -1 };
		lastStemIndex = 4;
		xValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -5 < -6
		c = Rational.valueOf(-6, 1);
		xValuesStem = new int[] { -5 };
		lastStemIndex = 15;
		xValuesLoop = new int[] {};
		lastLoopIndex = 3;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 3 < -2
		c = Rational.valueOf(-2, 1);
		xValuesStem = new int[] { 3 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// -4 < 3
		c = Rational.valueOf(3, 1);
		xValuesStem = new int[] { -4 };
		lastStemIndex = 9;
		xValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));
	}

	@Test
	public void strictIneqAutomatonXYC() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");

		int[] xValuesStem;
		int[] yValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int[] yValuesLoop;
		int lastLoopIndex;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x - y < c

		// 1 - 2 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 1 };
		yValuesStem = new int[] { 2 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 1 < -3
		c = Rational.valueOf(-3, 1);
		xValuesStem = new int[] { 1 };
		yValuesStem = new int[] { 1 };
		lastStemIndex = 4;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 3;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 1 < 3
		c = Rational.valueOf(3, 1);
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 1 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 2 - 1 < 1
		c = Rational.valueOf(1, 1);
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -5 - (-2) < -2
		c = Rational.valueOf(-2, 1);
		xValuesStem = new int[] { -5 };
		yValuesStem = new int[] { -2 };
		lastStemIndex = 10;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -1 - (-2) < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { -1 };
		yValuesStem = new int[] { -2 };
		lastStemIndex = 4;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 7;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - (-4) < 3
		c = Rational.valueOf(3, 1);
		xValuesStem = new int[] { -2 };
		yValuesStem = new int[] { -4 };
		lastStemIndex = 8;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// -2 - (-3) < 1
		c = Rational.valueOf(1, 1);
		xValuesStem = new int[] { -2 };
		yValuesStem = new int[] { -3 };
		lastStemIndex = 7;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

	}

	@Test
	public void strictNegIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictNegIneqAutomaton ...");
		int[] xValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int lastLoopIndex;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for -x < c

		// -1 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 3 };
		lastStemIndex = 6;
		xValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -1 < -2
		c = Rational.valueOf(-2, 1);
		xValuesStem = new int[] { 1 };
		lastStemIndex = 4;
		xValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 2 < 3
		c = Rational.valueOf(3, 1);
		xValuesStem = new int[] { -2 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// 3 < 2
		c = Rational.valueOf(2, 1);
		xValuesStem = new int[] { -3 };
		lastStemIndex = 6;
		xValuesLoop = new int[] {};
		lastLoopIndex = 5;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

	}

	@Test
	public void strictSubsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictSubsetAutomaton ...");

		int[] xValuesStem;
		int[] yValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int[] yValuesLoop;
		int lastLoopIndex;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x strictSubsetInt y

		// { } strictSubsetInt { 0 }
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 4 } strictSubsetInt { 0 , 2, 4, 6, ..}
		xValuesStem = new int[] { 4 };
		yValuesStem = new int[] { 0, 2, 4 };
		lastStemIndex = 7;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { -1, -2, -3, ... } strictSubsetInt {0, 1, -1, 2, -2, ...}
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] { 01 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 0, -1 } strictSubsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { 0, -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// {-1 } strictSubsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// {-1, -2, -3, ... } strictSubsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));
	}

	@Test
	public void subsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing subsetAutomaton ...");

		int[] xValuesStem;
		int[] yValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int[] yValuesLoop;
		int lastLoopIndex;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x subsetInt y

		// { } subsetInt { 0 }
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 2;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 4 } subsetInt { 0 , 2, 4, 6, ..}
		xValuesStem = new int[] { 4 };
		yValuesStem = new int[] { 0, 2, 4 };
		lastStemIndex = 7;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { -1, -2, -3, ... } subsetInt {0, 1, -1, 2, -2, ...}
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] { 01 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 0, -1 } subsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { 0, -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// {-1 } subsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// {-1, -2, -3, ... } subsetInt {-1, -2, -3, ...}
		xValuesStem = new int[] { -1 };
		yValuesStem = new int[] { -1 };
		lastStemIndex = 3;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0 };
		lastLoopIndex = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.subsetAutomaton(mServices, x, y));
	}

	@Test
	public void elementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing elementAutomaton ...");

		int[] xValuesStem;
		int[] yValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int[] yValuesLoop;
		int lastLoopIndex;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x + c element Y.

		// 0 + 0 element { 0 }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		yValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 3 + 2 element { 1, -1, 3, -3,.. }
		c = Rational.valueOf(2, 1);
		xValuesStem = new int[] { 3 };
		yValuesStem = new int[] { 1, -1, 3 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0, 3 };
		lastLoopIndex = 3;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 3 + -2 element { 1, -1, 3, -3,.. }
		c = Rational.valueOf(-2, 1);
		xValuesStem = new int[] { 3 };
		yValuesStem = new int[] { 1, -1, 3 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0, 3 };
		lastLoopIndex = 3;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 2 + 2 element { 1, -1, 3, -3,.. }
		c = Rational.valueOf(2, 1);
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 1, -1, 3 };
		lastStemIndex = 5;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0, 3 };
		lastLoopIndex = 3;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemIndex, lastLoopIndex),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

	}

	@Test
	public void constElementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing constElementAutomaton ...");

		int[] xValuesStem;
		int lastStemIndex;
		int[] xValuesLoop;
		int lastLoopIndex;
		Rational c;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for c element X

		// 0 element { 0 }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] {};
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 5 element { 0, 1, -1, 2, -2, ... }
		c = Rational.valueOf(5, 1);
		xValuesStem = new int[] { 0 };
		lastStemIndex = 0;
		xValuesLoop = new int[] { 0 };
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// -6 element { 0, 1, 2, 3, ... }
		c = Rational.valueOf(-6, 1);
		xValuesStem = new int[] { 1 };
		lastStemIndex = 1;
		xValuesLoop = new int[] { 1 };
		lastLoopIndex = 1;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// -3 element { -3 }
		c = Rational.valueOf(-3, 1);
		xValuesStem = new int[] { -3 };
		lastStemIndex = 8;
		xValuesLoop = new int[] {};
		lastLoopIndex = 4;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// -3 element { -3, 0, 4, -4, 5, -5 }
		c = Rational.valueOf(-3, 1);
		xValuesStem = new int[] { 0, -3, 4 };
		lastStemIndex = 8;
		xValuesLoop = new int[] { 0 };
		lastLoopIndex = 0;
		test(true, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// -1 element { -3, 0, 4, -4, 5, -5 }
		c = Rational.valueOf(-1, 1);
		xValuesStem = new int[] { 0, -3, 4 };
		lastStemIndex = 8;
		xValuesLoop = new int[] { 0 };
		lastLoopIndex = 0;
		test(false, getWord(x, xValuesStem, lastStemIndex, xValuesLoop, lastLoopIndex),
				mMSODOperations.constElementAutomaton(mServices, c, x));
	}
}

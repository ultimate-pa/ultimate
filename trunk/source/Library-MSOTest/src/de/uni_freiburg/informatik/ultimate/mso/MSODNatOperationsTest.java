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
public final class MSODNatOperationsTest {

	private IUltimateServiceProvider mServiceProvider;
	private AutomataLibraryServices mServices;
	private Script mScript;
	private ILogger mLogger;

	MSODOperations mMSODOperations =
			new MSODOperations(new MSODFormulaOperationsNat(), new MSODAutomataOperationsBuchi());

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

	private NestedLassoWord<MSODAlphabetSymbol> getWord(final Term term, final int[] stemValues,
			final int lastNumberStem, final int[] loopValues, final int lastNumberLoop) {

		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(term, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(term, true);

		// Construct stem.
		final MSODAlphabetSymbol[] stemSymbols = new MSODAlphabetSymbol[lastNumberStem + 1];
		Arrays.fill(stemSymbols, x0);

		for (int i = 0; i < stemValues.length; i++) {
			stemSymbols[stemValues[i]] = x1;
		}
		final NestedWord<MSODAlphabetSymbol> stem = NestedWord.nestedWord(new Word<>(stemSymbols));

		// Construct loop.
		final MSODAlphabetSymbol[] loopSymbols = new MSODAlphabetSymbol[lastNumberLoop + 1];
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
			final int lastNumberStem, final int lastNumberLoop) {

		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(term1, term2, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(term1, term2, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(term1, term2, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(term1, term2, true, true);

		// Construct stem.

		final MSODAlphabetSymbol[] stemSymbols = new MSODAlphabetSymbol[lastNumberStem + 1];
		Arrays.fill(stemSymbols, xy00);

		for (int i = 0; i < stemValues1.length; i++) {
			stemSymbols[stemValues1[i]] = xy10;
		}

		for (int i = 0; i < stemValues2.length; i++) {
			stemSymbols[stemValues2[i]] = stemSymbols[stemValues2[i]] == xy10 ? xy11 : xy01;
		}
		final NestedWord<MSODAlphabetSymbol> stem = NestedWord.nestedWord(new Word<>(stemSymbols));

		// Construct loop
		final MSODAlphabetSymbol[] loopSymbols = new MSODAlphabetSymbol[lastNumberLoop + 1];
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
		int lastStemNumber;
		int[] xValuesLoop;
		int lastLoopNumber;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x < c

		// 0 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		lastLoopNumber = 10;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 0 < 1
		c = Rational.valueOf(1, 1);
		xValuesStem = new int[] { 0 };
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		lastLoopNumber = 4;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 6 < 9
		c = Rational.valueOf(9, 1);
		xValuesStem = new int[] { 6 };
		lastStemNumber = 7;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));

		// 8 < 4
		c = Rational.valueOf(4, 1);
		xValuesStem = new int[] { 8 };
		lastStemNumber = 8;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, c));
	}

	@Test
	public void strictIneqAutomatonXYC() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");

		int[] xValuesStem;
		int[] xValuesLoop;
		int[] yValuesStem;
		int[] yValuesLoop;
		int lastStemNumber;
		int lastLoopNumber;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", SmtSortUtils.getIntSort(mScript));

		// Test Cases for x - y < c

		// 0 - 0 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 3;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 1 - 2 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 1 };
		yValuesStem = new int[] { 2 };
		lastStemNumber = 3;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 8 - 2 < 6
		c = Rational.valueOf(6, 1);
		xValuesStem = new int[] { 8 };
		yValuesStem = new int[] { 2 };
		lastStemNumber = 9;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 2;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));

		// 8 - 3 < 6
		c = Rational.valueOf(6, 1);
		xValuesStem = new int[] { 8 };
		yValuesStem = new int[] { 3 };
		lastStemNumber = 8;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictIneqAutomaton(mServices, x, y, c));
	}

	@Test
	public void strictNegIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictNegIneqAutomaton ...");
		Rational c;
		int[] xValuesStem;
		int lastStemNumber;
		int[] xValuesLoop;
		int lastLoopNumber;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));

		// Test Cases for -x < c

		// -0 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -1 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 1 };
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		lastLoopNumber = 2;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -6 < 0
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 6 };
		lastStemNumber = 6;
		xValuesLoop = new int[] {};
		lastLoopNumber = 5;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -8 < 7
		c = Rational.valueOf(7, 1);
		xValuesStem = new int[] { 8 };
		lastStemNumber = 8;
		xValuesLoop = new int[] {};
		lastLoopNumber = 4;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 4
		c = Rational.valueOf(4, 3);
		xValuesStem = new int[] { 3 };
		lastStemNumber = 4;
		xValuesLoop = new int[] {};
		lastLoopNumber = 4;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.strictNegIneqAutomaton(mServices, x, c));
	}

	@Test
	public void strictSubsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictSubsetAutomaton ...");

		int[] xValuesStem;
		int[] xValuesLoop;
		int[] yValuesStem;
		int[] yValuesLoop;
		int lastStemNumber;
		int lastLoopNumber;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x strictSubsetInt y

		// { } subsetInt { 0 }
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 0, 1, 2, 3, 4, ... }
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 0, 1, 2 };
		lastStemNumber = 2;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] { 0, 1 };
		lastLoopNumber = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 0, 1, 2, 3, 4, ...} subsetInt { 0, 1, 2, 3, 4, ... }
		xValuesStem = new int[] { 0 };
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0 };
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 3, 4, 5, ... }
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 3 };
		lastStemNumber = 3;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0, 1 };
		lastLoopNumber = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 2, 4, 6 }
		xValuesStem = new int[] { 2, 4, 6 };
		yValuesStem = new int[] { 2, 4, 6 };
		lastStemNumber = 6;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] {};
		lastLoopNumber = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));

		// { 2, 4, 6} subsetInt { 2, 4, 6, ...}
		xValuesStem = new int[] { 2, 4, 6 };
		yValuesStem = new int[] { 2, 4, 6 };
		lastStemNumber = 6;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopNumber = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.strictSubsetAutomaton(mServices, x, y));
	}

	@Test
	public void subsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing subsetAutomaton ...");

		int[] xValuesStem;
		int[] xValuesLoop;
		int[] yValuesStem;
		int[] yValuesLoop;
		int lastStemNumber;
		int lastLoopNumber;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x subsetInt y

		// { } subsetInt { 0 }
		xValuesStem = new int[] {};
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 0, 1, 2, 3, 4, ... }
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 0, 1, 2 };
		lastStemNumber = 2;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] { 0, 1 };
		lastLoopNumber = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 0, 1, 2, 3, 4, ...} subsetInt { 0, 1, 2, 3, 4, ... }
		xValuesStem = new int[] { 0 };
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0 };
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 3, 4, 5, ... }
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] { 3 };
		lastStemNumber = 3;
		xValuesLoop = new int[] { 0 };
		yValuesLoop = new int[] { 0, 1 };
		lastLoopNumber = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 2, 4, 6, ...} subsetInt { 2, 4, 6 }
		xValuesStem = new int[] { 2, 4, 6 };
		yValuesStem = new int[] { 2, 4, 6 };
		lastStemNumber = 6;
		xValuesLoop = new int[] { 1 };
		yValuesLoop = new int[] {};
		lastLoopNumber = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));

		// { 2, 4, 6} subsetInt { 2, 4, 6, ...}
		xValuesStem = new int[] { 2, 4, 6 };
		yValuesStem = new int[] { 2, 4, 6 };
		lastStemNumber = 6;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopNumber = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.subsetAutomaton(mServices, x, y));
	}

	@Test
	public void elementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing elementAutomaton ...");

		int[] xValuesStem;
		int[] xValuesLoop;
		int[] yValuesStem;
		int[] yValuesLoop;
		int lastStemNumber;
		int lastLoopNumber;
		Rational c;
		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for x + c element Y.

		// 0 + 0 element { 0, 1, 2, ... }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		yValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 0 };
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + 7 element { 2, 4, 6, ... }
		c = Rational.valueOf(7, 1);
		xValuesStem = new int[] { 1 };
		yValuesStem = new int[] { 2 };
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopNumber = 1;
		test(true, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 1 + 8 element { 2, 4, 6, ... }
		c = Rational.valueOf(8, 1);
		xValuesStem = new int[] { 1 };
		yValuesStem = new int[] { 2 };
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] { 1 };
		lastLoopNumber = 1;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.elementAutomaton(mServices, x, c, y));

		// 2 + 4 element { }
		c = Rational.valueOf(4, 1);
		xValuesStem = new int[] { 2 };
		yValuesStem = new int[] {};
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		yValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, xValuesLoop, y, yValuesStem, yValuesLoop, lastStemNumber, lastLoopNumber),
				mMSODOperations.elementAutomaton(mServices, x, c, y));
	}

	@Test
	public void constElementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing constElementAutomaton ...");

		Rational c;
		int[] xValuesStem;
		int lastStemNumber;
		int[] xValuesLoop;
		int lastLoopNumber;
		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));

		// Test Cases for c element X

		// 0 element { 0 }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 0 };
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 0 element { }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] {};
		lastStemNumber = 0;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 1 element { }
		c = Rational.valueOf(1, 1);
		xValuesStem = new int[] {};
		lastStemNumber = 1;
		xValuesLoop = new int[] {};
		lastLoopNumber = 2;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 0 element { 1 }
		c = Rational.valueOf(0, 1);
		xValuesStem = new int[] { 1 };
		lastStemNumber = 2;
		xValuesLoop = new int[] {};
		lastLoopNumber = 0;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 1 element { 1 }
		c = Rational.valueOf(1, 1);
		xValuesStem = new int[] { 1 };
		lastStemNumber = 1;
		xValuesLoop = new int[] {};
		lastLoopNumber = 3;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 10 element { 0, 5, 10, ...}
		c = Rational.valueOf(10, 1);
		xValuesStem = new int[] { 0, 5 };
		lastStemNumber = 5;
		xValuesLoop = new int[] { 4 };
		lastLoopNumber = 4;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 2 element { 1, 3 }
		c = Rational.valueOf(2, 1);
		xValuesStem = new int[] { 1, 3 };
		lastStemNumber = 3;
		xValuesLoop = new int[] {};
		lastLoopNumber = 3;
		test(false, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));

		// 4 element { 0, 1, 2, 4, 5 , ...}
		c = Rational.valueOf(4, 1);
		xValuesStem = new int[] { 0, 1, 2, 4, 5 };
		lastStemNumber = 5;
		xValuesLoop = new int[] { 0 };
		lastLoopNumber = 0;
		test(true, getWord(x, xValuesStem, lastStemNumber, xValuesLoop, lastLoopNumber),
				mMSODOperations.constElementAutomaton(mServices, c, x));
	}
}

/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODIntAutomataTest {

	private IUltimateServiceProvider mServiceProvider;
	private AutomataLibraryServices mServices;
	private Script mScript;
	private ILogger mLogger;

	MSODAutomatonFactory factory;

	@Rule
	public final ExpectedException mNoException = ExpectedException.none();

	@Before
	public void setUp() {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mServices = new AutomataLibraryServices(mServiceProvider);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("lol");

		mScript.setLogic(Logics.ALL);
		mScript.declareSort("SetOfInt", 0);
	}

	private void test(final Boolean result, final MSODAlphabetSymbol[] symbols,
			final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton) throws AutomataLibraryException {

		final NestedWord<MSODAlphabetSymbol> word = NestedWord.nestedWord(new Word<MSODAlphabetSymbol>(symbols));
		final Accepts<MSODAlphabetSymbol, String> accepts = new Accepts<>(mServices, automaton, word);

		mLogger.info("Word: " + word);
		mLogger.info("Result: " + result + " / " + accepts.getResult());

		Assert.assertEquals(result, accepts.getResult());
	}

	@Test
	public void strictIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");
		MSODAlphabetSymbol[] symbols;
		Rational c;

		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		// x < c AND c <= 0

		// -1 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// -3 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// -3 < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// 0 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// -1 < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// x < c AND c > 0

		// 0 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// -3 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// 2 < 3
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// 1 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));

		// 3 < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, c));
	}

	@Test
	public void strictIneqAutomatonXYC() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictIneqAutomaton ...");
		MSODAlphabetSymbol[] symbols;
		Rational c;

		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", SmtSortUtils.getIntSort(mScript));
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		// x - y < c AND x > 0 AND y > 0 AND c <= 0

		// 1 - 2 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 2 - 4 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy10, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - 4 < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 2 - 1 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - 1 < -3
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy11 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		
		// x - y < c AND x > 0 AND y > 0 AND c > 0

		// 1 - 1 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - 2 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 3 - 2 < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 2 - 1 < 3
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 2 - 1 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 4 - 1 < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		
		// x - y < c AND x <= 0 AND y <= 0 AND c <= 0

		// -1 - 0 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
				
		// - 2 - (-1) < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
				
		// -5 - (-2) < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
				
		// -1 - (-2) < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy10, xy00, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
				
		// -2 - (-2) < -3
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy11 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// x - y < c AND x <= 0 AND y <= 0 AND c > 0

		// 0 - 0 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy11 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -1 - (-1) < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -3 - (-2) < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 0 - (-1) < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -2 - (-4) < 3
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy10, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -2 - (-3) < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy10, xy00, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 0 - (-3) < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// x - y < c AND x > 0 AND y <= 0 AND c > 0
		
		// 1 - 0 < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - (-2) < 4
		c = Rational.valueOf(4, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 2 - (-1) < 4
		c = Rational.valueOf(4, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy01, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - (-1) < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - 0 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 1 - (-2) < 3
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// x - y < c AND x <= 0 AND y > 0 AND c <= 0
				
		// 0 - 1 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 0 - 3 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -3 - 1 < -3
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// -2 - 2 < -3
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy01, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
		// 0 - 1 < -1
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy01 };
		test(false, symbols, MSODIntAutomatonFactory.strictIneqAutomaton(mServices, x, y, c));
		
	}
	
	@Test
	public void strictNegIneqAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictNegIneqAutomaton ...");
		MSODAlphabetSymbol[] symbols;
		Rational c;

		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		// -x < c AND c <= 0

		// -1 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// -3 < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// 0 < 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// -1 < -2
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// -x < c AND c > 0

		// 0 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// -3 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// 2 < 3
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// 1 < 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));

		// 3 < 2
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		test(false, symbols, MSODIntAutomatonFactory.strictNegIneqAutomaton(mServices, x, c));
	}
	
	@Test
	public void constElementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing constElementAutomaton ...");
		MSODAlphabetSymbol[] symbols;
		Rational c;

		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final MSODAlphabetSymbol x0 = new MSODAlphabetSymbol(x, false);
		final MSODAlphabetSymbol x1 = new MSODAlphabetSymbol(x, true);

		// c element x AND c <= 0

		// 0 element { 0 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 0 element { 0, 3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x1, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// -3 element { -3 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// -3 element { -3, 0, 4 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { x1, x0, x0, x0, x0, x0, x1, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 0 element { }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] {};
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 0 element { -1, 1 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1, x1 };
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// -2 element { -1, 1 }
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1, x1 };
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// c element x AND c > 0

		// 1 element { 1 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 1 element { 1, 3 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 3 element { 3 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 3 element { 0, 3, 4 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { x1, x0, x0, x0, x0, x1, x0, x1 };
		test(true, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 1 element { }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] {};
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 1 element { -1, 2 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1, x1 };
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));

		// 2 element { -1, 1 }
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1, x1 };
		test(false, symbols, MSODIntAutomatonFactory.constElementAutomaton(mServices, c, x));
	}

	@Test
	public void elementAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing elementAutomaton ...");
		MSODAlphabetSymbol[] symbols;
		Rational c;

		final Term x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		// x + c element y AND x + c <= 0 AND x <= 0

		// 0 + 0 element { 0 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy11 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 0 + (-1) element { -1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// -1 + 1 element { 0 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// -3 + 0 element { -3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 0 + (-3) element { -3 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// -3 + 3 element { 0 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// x + c element y AND x + c > 0 AND x > 0

		// 1 + 0 element { 1 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 2 + (-1) element { 1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 1 + 1 element { 2 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 3 + 0 element { 3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 4 + (-3) element { 1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 1 + 3 element { 4 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// x + c element y AND x + c <= 0 AND x > 0

		// 1 + (-1) element { 0 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 3 + (-3) element { 0 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 2 + (-3) element { -1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy01, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 1 + (-3) element { -2 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// x + c element y AND x + c > 0 AND x <= 0

		// 0 + 1 element { 1 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// -2 + 3 element { 1 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy10 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// -1 + 3 element { 2 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy10, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));

		// 0 + 3 element { 3 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.elementAutomaton(mServices, x, c, y));
	}

	@Test
	public void strictSubsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing strictSubsetAutomaton ...");
		MSODAlphabetSymbol[] symbols;

		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		// x strictSubsetInt y

		// { } strictSubsetInt { 0 }
		symbols = new MSODAlphabetSymbol[] { xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { 0 } strictSubsetInt { 0, 1 }
		symbols = new MSODAlphabetSymbol[] { xy11, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { -1, 2 } strictSubsetInt { -2, -1, 0, 2 }
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy11, xy11, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { 0, 1 } strictSubsetInt { 0 }
		symbols = new MSODAlphabetSymbol[] { xy11, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { } strictSubsetInt { }
		symbols = new MSODAlphabetSymbol[] { xy00 };
		test(false, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { -1, 3 } strictSubsetInt { -1, 3 }
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy11, xy00, xy00, xy11 };
		test(false, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));

		// { -2, 3 } strictSubsetInt { 2, 3 }
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy01, xy10, xy11 };
		test(false, symbols, MSODIntAutomatonFactory.strictSubsetAutomaton(mServices, x, y));
	}

	@Test
	public void subsetAutomaton() throws AutomataLibraryException {
		mLogger.info("--------------------------------------------------");
		mLogger.info("Testing subsetAutomaton ...");
		MSODAlphabetSymbol[] symbols;

		final Term x = mScript.variable("x", MSODUtils.getSetOfIntSort(mScript));
		final Term y = mScript.variable("y", MSODUtils.getSetOfIntSort(mScript));
		final MSODAlphabetSymbol xy00 = new MSODAlphabetSymbol(x, y, false, false);
		final MSODAlphabetSymbol xy10 = new MSODAlphabetSymbol(x, y, true, false);
		final MSODAlphabetSymbol xy01 = new MSODAlphabetSymbol(x, y, false, true);
		final MSODAlphabetSymbol xy11 = new MSODAlphabetSymbol(x, y, true, true);

		// x nonStrictSubsetInt y

		// { } nonStrictSubsetInt { }
		symbols = new MSODAlphabetSymbol[] {};
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { } nonStrictSubsetInt { 0 }
		symbols = new MSODAlphabetSymbol[] { xy01 };
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { 0 } nonStrictSubsetInt { 0 }
		symbols = new MSODAlphabetSymbol[] { xy11 };
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { 0 } nonStrictSubsetInt { 0, 1 }
		symbols = new MSODAlphabetSymbol[] { xy11, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { -1, 3 } nonStrictSubsetInt { -1, 3 }
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy11, xy00, xy00, xy11 };
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { -1, 2 } nonStrictSubsetInt { -2, -1, 0, 2 }
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy11, xy11, xy01 };
		test(true, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { 0, 1 } nonStrictSubsetInt { 0 }
		symbols = new MSODAlphabetSymbol[] { xy11, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { -2 } nonStrictSubsetInt { }
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy10 };
		test(false, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));

		// { -2, 3 } nonStrictSubsetInt { 2, 3 }
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy01, xy10, xy11 };
		test(false, symbols, MSODIntAutomatonFactory.subsetAutomaton(mServices, x, y));
	}
}

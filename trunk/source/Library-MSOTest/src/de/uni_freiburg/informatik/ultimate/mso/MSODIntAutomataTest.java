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

	protected IUltimateServiceProvider mServiceProvider;
	protected AutomataLibraryServices mServices;
	protected Script mScript;
	protected ILogger mLogger;

	protected Term x;
	protected Term y;
	protected MSODAlphabetSymbol x0;
	protected MSODAlphabetSymbol x1;
	protected MSODAlphabetSymbol xy00;
	protected MSODAlphabetSymbol xy01;
	protected MSODAlphabetSymbol xy10;
	protected MSODAlphabetSymbol xy11;

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

		x = mScript.variable("x", SmtSortUtils.getIntSort(mScript));
		y = mScript.variable("y", MoNatDiffUtils.getSetOfIntSort(mScript));

		x0 = new MSODAlphabetSymbol(x, false);
		x1 = new MSODAlphabetSymbol(x, true);
		xy00 = new MSODAlphabetSymbol(x, y, false, false);
		xy10 = new MSODAlphabetSymbol(x, y, true, false);
		xy01 = new MSODAlphabetSymbol(x, y, false, true);
		xy11 = new MSODAlphabetSymbol(x, y, true, true);
	}

	private void strictIneqAutomatonTest(final Boolean result, final Rational c, final MSODAlphabetSymbol... symbols)
			throws AutomataLibraryException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton = MSODIntAutomatonFactory
				.strictIneqAutomaton(mServices, x, c);

		final NestedWord<MSODAlphabetSymbol> word = NestedWord.nestedWord(new Word<MSODAlphabetSymbol>(symbols));
		final Accepts<MSODAlphabetSymbol, String> accepts = new Accepts<>(mServices, automaton, word);

		mLogger.info("Test: x < c | c = " + c + " | word = " + word);
		mLogger.info("Result: " + accepts.getResult());

		Assert.assertEquals(result, accepts.getResult());
	}

	@Test
	public void strictIneqAutomaton() throws AutomataLibraryException {
		MSODAlphabetSymbol[] symbols;
		Rational c;

		// x < c and c <= 0

		// x < 0 | x = -1
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1 };
		strictIneqAutomatonTest(true, c, symbols);

		// x < 0 | x = -3
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		strictIneqAutomatonTest(true, c, symbols);

		// x < -2 | x = -3
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		strictIneqAutomatonTest(true, c, symbols);

		// x < 0 | x = 0
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		strictIneqAutomatonTest(false, c, symbols);

		// x < -2 | x = -1
		c = Rational.valueOf(-2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x1 };
		strictIneqAutomatonTest(false, c, symbols);

		// x < c and c > 0
		
		// x < 1 | x = 0
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x1 };
		strictIneqAutomatonTest(true, c, symbols);

		// x < 1 | x = -3
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x0, x1 };
		strictIneqAutomatonTest(true, c, symbols);

		// x < 3 | x = 2
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x1 };
		strictIneqAutomatonTest(true, c, symbols);
		
		// x < 1 | x = 1
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x1 };
		strictIneqAutomatonTest(false, c, symbols);

		// x < 2 | x = 3
		c = Rational.valueOf(2, 1);
		symbols = new MSODAlphabetSymbol[] { x0, x0, x0, x0, x0, x1 };
		strictIneqAutomatonTest(false, c, symbols);
	}

	private void elementAutomatonTest(final Boolean result, final Rational c, final MSODAlphabetSymbol... symbols)
			throws AutomataLibraryException {

		final INestedWordAutomaton<MSODAlphabetSymbol, String> automaton = MSODIntAutomatonFactory
				.elementAutomaton(mServices, x, c, y);

		final NestedWord<MSODAlphabetSymbol> word = NestedWord.nestedWord(new Word<MSODAlphabetSymbol>(symbols));
		final Accepts<MSODAlphabetSymbol, String> accepts = new Accepts<>(mServices, automaton, word);

		mLogger.info("Test: x + c element y | c = " + c + " | word = " + word);
		mLogger.info("Result: " + accepts.getResult());

		Assert.assertEquals(result, accepts.getResult());
	}

	@Test
	public void elementAutomaton() throws AutomataLibraryException {
		MSODAlphabetSymbol[] symbols;
		Rational c;

		// x + c <= 0 and x <= 0

		// x + 0 element y | x = 0 and y = { 0 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy11 };
		elementAutomatonTest(true, c, symbols);

		// x + (-1) element y | x = 0 and y = { -1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + 1 element y | x = -1 and y = { 0 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + 0 element y | x = -3 and y = { -3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy00, xy11 };
		elementAutomatonTest(true, c, symbols);

		// x + (-3) element y | x = 0 and y = { -3 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + 3 element y | x = -3 and y = { 0 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + c > 0 and x > 0

		// x + 0 element y | x = 1 and y = { 1 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy11 };
		elementAutomatonTest(true, c, symbols);

		// x + (-1) element y | x = 2 and y = { 1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + 1 element y | x = 1 and y = { 2 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + 0 element y | x = 3 and y = { 3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy11 };
		elementAutomatonTest(true, c, symbols);

		// x + (-3) element y | x = 4 and y = { 1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + 3 element y | x = 1 and y = { 4 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + c <= 0 and x > 0

		// x + (-1) element y | x = 1 and y = { 0 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + (-3) element y | x = 3 and y = { 0 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + (-3) element y | x = 2 and y = { -1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy01, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + (-3) element y | x = 1 and y = { -2 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + c > 0 and x <= 0

		// x + 1 element y | x = 0 and y = { 1 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + 3 element y | x = -2 and y = { 1 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy10 };
		elementAutomatonTest(true, c, symbols);

		// x + 3 element y | x = -1 and y = { 2 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy10, xy01 };
		elementAutomatonTest(true, c, symbols);

		// x + 3 element y | x = 0 and y = { 3 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy01 };
		elementAutomatonTest(true, c, symbols);
	}
}

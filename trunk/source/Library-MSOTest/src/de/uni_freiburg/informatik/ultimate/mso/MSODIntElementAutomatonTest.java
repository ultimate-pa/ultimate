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
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODIntElementAutomatonTest extends MSODTest {

	private void test(final Boolean result, final Rational c, final MSODAlphabetSymbol... symbols)
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
		test(true, c, symbols);

		// x + (-1) element y | x = 0 and y = { -1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy01 };
		test(true, c, symbols);

		// x + 1 element y | x = -1 and y = { 0 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy10 };
		test(true, c, symbols);

		// x + 0 element y | x = -3 and y = { -3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy00, xy11 };
		test(true, c, symbols);

		// x + (-3) element y | x = 0 and y = { -3 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(true, c, symbols);

		// x + 3 element y | x = -3 and y = { 0 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(true, c, symbols);

		// x + c > 0 and x > 0

		// x + 0 element y | x = 1 and y = { 1 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy11 };
		test(true, c, symbols);

		// x + (-1) element y | x = 2 and y = { 1 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy10 };
		test(true, c, symbols);

		// x + 1 element y | x = 1 and y = { 2 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy01 };
		test(true, c, symbols);

		// x + 0 element y | x = 3 and y = { 3 }
		c = Rational.valueOf(0, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy00, xy00, xy00, xy11 };
		test(true, c, symbols);

		// x + (-3) element y | x = 4 and y = { 1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy00, xy00, xy00, xy10 };
		test(true, c, symbols);

		// x + 3 element y | x = 1 and y = { 4 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy00, xy00, xy00, xy01 };
		test(true, c, symbols);

		// x + c <= 0 and x > 0

		// x + (-1) element y | x = 1 and y = { 0 }
		c = Rational.valueOf(-1, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy10 };
		test(true, c, symbols);

		// x + (-3) element y | x = 3 and y = { 0 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy01, xy00, xy00, xy00, xy00, xy10 };
		test(true, c, symbols);

		// x + (-3) element y | x = 2 and y = { -1 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy01, xy10 };
		test(true, c, symbols);

		// x + (-3) element y | x = 1 and y = { -2 }
		c = Rational.valueOf(-3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy10, xy00, xy00, xy01 };
		test(true, c, symbols);

		// x + c > 0 and x <= 0

		// x + 1 element y | x = 0 and y = { 1 }
		c = Rational.valueOf(1, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy01 };
		test(true, c, symbols);

		// x + 3 element y | x = -2 and y = { 1 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy01, xy00, xy00, xy10 };
		test(true, c, symbols);

		// x + 3 element y | x = -1 and y = { 2 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy00, xy00, xy10, xy01 };
		test(true, c, symbols);

		// x + 3 element y | x = 0 and y = { 3 }
		c = Rational.valueOf(3, 1);
		symbols = new MSODAlphabetSymbol[] { xy10, xy00, xy00, xy00, xy00, xy01 };
		test(true, c, symbols);
	}
}

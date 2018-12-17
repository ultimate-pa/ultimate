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

import java.math.BigInteger;
import java.util.Optional;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MSOTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Term mTrue;
	private Term mFalse;
	private AutomataLibraryServices mAuLibServices;
	private Sort mIntSort;

	@Rule
	public final ExpectedException mNoException = ExpectedException.none();

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mAuLibServices = new AutomataLibraryServices(mServices);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger("lol");
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);
	}

	@Test
	public void bla() throws AutomataLibraryException {
		final Term x = mScript.variable("x", mIntSort);
		final Term y = mScript.variable("y", mIntSort);
		final Rational c = Rational.ONE;

		final NestedWordAutomaton<MoNatDiffAlphabetSymbol, String> aut =
				MoNatDiffAutomatonFactory.strictIneqAutomaton(mAuLibServices, x, y, c);

		mLogger.info("Alphabet: " + aut.getAlphabet());

		final Optional<MoNatDiffAlphabetSymbol> firstSymOpt =
				aut.getAlphabet().stream().filter(a -> a.getTerms()[0].toStringDirect().equals("x")).findFirst();
		final MoNatDiffAlphabetSymbol firstSym = firstSymOpt.get();

		mLogger.info("First: " + firstSym);

		final Term one = mScript.numeral(BigInteger.ONE);
		final Term zero = mScript.numeral(BigInteger.ZERO);

		final Term xEqZero = mScript.term("=", x, zero);

		final MoNatDiffAlphabetSymbol sym = new MoNatDiffAlphabetSymbol(x, true);
		sym.add(y, true);
		mLogger.info("Trying " + sym);
		final Word<MoNatDiffAlphabetSymbol> word = new Word<>(sym);
		final NestedWord<MoNatDiffAlphabetSymbol> nWord = NestedWord.nestedWord(word);

		// mNoException.expect(AutomataLibraryException.class);
		final Accepts<MoNatDiffAlphabetSymbol, String> accept = new Accepts<>(mAuLibServices, aut, nWord);
		mLogger.info("Result: " + accept.getResult());
	}

	// @Test
	// public void testSubstitutionWithLocalSimplification1() {
	//
	// final Sort intSort = SmtSortUtils.getIntSort(mScript);
	//
	// final String names = "ABCDE";
	// final Term[] values = new Term[] { mScript.term("-", mScript.numeral("1")), mScript.numeral("0"),
	// mScript.numeral("2"), mScript.numeral("0"), mScript.numeral("0"), };
	// final Map<Term, Term> substitutionMapping = new HashMap<>();
	// for (int i = 0; i < names.length(); ++i) {
	// final Term term = declareVar(String.valueOf(names.charAt(i)), intSort);
	// if (i < values.length) {
	// final Term value = values[i];
	// final Term newValue = new UnfTransformer(mScript).transform(value);
	// substitutionMapping.put(term, newValue);
	// }
	// }
	//
	// final Term input = TermParseUtils.parseTerm(mScript,
	// "(and (<= A E) (or (and (= C 2) (<= D E) (<= B D) (not (= A D))) (= C 1) (and (<= C 1) (not (= C 2)) (not (= C
	// 1)) (= C 3))))");
	//
	// final SubstitutionWithLocalSimplification swls =
	// new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
	// final Term result = swls.transform(input);
	// final LBool isDistinct = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", mTrue, result));
	// final boolean isEqualToTrue = result.equals(mTrue);
	//
	// mLogger.info("Original: " + input.toStringDirect());
	// mLogger.info("Witness: " + substitutionMapping.toString());
	// mLogger.info("After Substitution: " + result.toStringDirect());
	// mLogger.info("(distinct true result): " + isDistinct);
	// mLogger.info("isEqualToTrue: " + isEqualToTrue);
	// Assert.isTrue(isDistinct == LBool.UNSAT && isEqualToTrue);
	// }
	//
	// private Term declareVar(final String name, final Sort sort) {
	// mScript.declareFun(name, new Sort[0], sort);
	// return mScript.term(name);
	// }

}

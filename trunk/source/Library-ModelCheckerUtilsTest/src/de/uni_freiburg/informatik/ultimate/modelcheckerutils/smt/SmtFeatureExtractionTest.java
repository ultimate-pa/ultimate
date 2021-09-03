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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Julian Löffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class SmtFeatureExtractionTest {

	private static final String ABCDE = "ABCDE";
	private Script mScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mLogger = services.getLoggingService().getLogger("lol");
		mScript.setLogic(Logics.ALL);
	}

	@Test
	public void checkSingleTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		for (int i = 0; i < ABCDE.length(); ++i) {
			declareVar(String.valueOf(ABCDE.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(= A 0)");
		check(input, Set.of(Set.of("A")), 1, Map.of("=", 1), Map.of("Int", 1), 0, Collections.emptyMap());
	}

	@Test
	public void checkAdditionTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		for (int i = 0; i < ABCDE.length(); ++i) {
			declareVar(String.valueOf(ABCDE.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(= A (+ B 1))");
		check(input, Set.of(Set.of("A", "B")), 2, Map.of("=", 1, "+", 1), Map.of("Int", 2), 0, Collections.emptyMap());
	}

	@Test
	public void checkSubtractionTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(= A (- B 1))");
		check(input, Set.of(Set.of("A", "B")), 2, Map.of("=", 1, "-", 1), Map.of("Int", 2), 0, Collections.emptyMap());
	}

	@Test
	public void checkMultiplicationTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(= A (* B 1))");
		check(input, Set.of(Set.of("A", "B")), 2, Map.of("=", 1, "*", 1), Map.of("Int", 2), 0, Collections.emptyMap());
	}

	@Test
	public void checkAndTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(and (= A (+ B 1)) (= C 0))");
		check(input, Set.of(Set.of("A", "B", "C")), 3, Map.of("and", 1, "+", 1, "=", 2), Map.of("Int", 3), 0,
				Collections.emptyMap());
	}

	@Test
	public void checkOrTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(or (= A (+ B 1)) (= C 0))");
		check(input, Set.of(Set.of("A", "B"), Set.of("C")), 3, Map.of("=", 2, "+", 1, "or", 1), Map.of("Int", 3), 0,
				Collections.emptyMap());
	}

	@Test
	public void checkOrAndTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(or (and (= A (+ B 1)) (= D 1)) (= C 0))");
		check(input, Set.of(Set.of("A", "B", "D"), Set.of("C")), 4, Map.of("=", 3, "+", 1, "or", 1, "and", 1),
				Map.of("Int", 4), 0, Collections.emptyMap());
	}

	@Test
	public void checkOrOrTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(or (or (= A (+ B 1)) (= D 1)) (= C 0))");
		check(input, Set.of(Set.of("A", "B"), Set.of("D"), Set.of("C")), 4, Map.of("=", 3, "+", 1, "or", 2),
				Map.of("Int", 4), 0, Collections.emptyMap());
	}

	@Test
	public void checkOrOrAndTerm() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);

		final String names = ABCDE;
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(or (or (and (= A 0) (= D 1)) (= E 0)) (= C 0))");
		check(input, Set.of(Set.of("A", "D"), Set.of("E"), Set.of("C")), 4, Map.of("=", 4, "and", 1, "or", 2),
				Map.of("Int", 4), 0, Collections.emptyMap());
	}

	@Test
	public void checkCountSorts() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort realSort = SmtSortUtils.getRealSort(mScript);
		final Sort boolSort = SmtSortUtils.getBoolSort(mScript);

		String names = "AB";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}
		names = "CD";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), realSort);
		}
		names = "EF";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), boolSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(and (= A 1) (= B A) (= C 1.0) (= D 1.5) E F)");
		check(input, Set.of(Set.of("A", "B", "C", "D", "E", "F")), 6, Map.of("=", 4, "and", 1),
				Map.of("Int", 2, "Bool", 2, "Real", 2), 0, Collections.emptyMap());
	}

	@Test
	public void checkCountFunctions() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort realSort = SmtSortUtils.getRealSort(mScript);
		final Sort boolSort = SmtSortUtils.getBoolSort(mScript);

		String names = "AB";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}
		names = "CD";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), realSort);
		}
		names = "EF";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), boolSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript,
				"(and (= A (+ A 1)) (= B (- A 1)) (= C (* 1.0 D)) (= D (* 1.5 4.0)) E F)");
		check(input, Set.of(Set.of("A", "B", "C", "D", "E", "F")), 6, Map.of("=", 4, "and", 1, "-", 1, "*", 2, "+", 1),
				Map.of("Int", 2, "Bool", 2, "Real", 2), 0, Collections.emptyMap());
	}

	@Test
	public void checkNot() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort realSort = SmtSortUtils.getRealSort(mScript);
		final Sort boolSort = SmtSortUtils.getBoolSort(mScript);

		String names = "AB";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}
		names = "CD";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), realSort);
		}
		names = "EF";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), boolSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript, "(and (not E) F)");
		check(input, Set.of(Set.of("E", "F")), 2, Map.of("and", 1, "not", 1), Map.of("Bool", 2), 0,
				Collections.emptyMap());
	}

	@Test
	public void checkCountQuantifiers() {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort realSort = SmtSortUtils.getRealSort(mScript);
		final Sort boolSort = SmtSortUtils.getBoolSort(mScript);

		String names = "AB";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), intSort);
		}
		names = "CD";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), realSort);
		}
		names = "EF";
		for (int i = 0; i < names.length(); ++i) {
			declareVar(String.valueOf(names.charAt(i)), boolSort);
		}

		final Term input = TermParseUtils.parseTerm(mScript,
				"(exists ((A Int))(and (= A (+ A 1)) (= B (- A 1)) (= C (* 1.0 D)) (= D (* 1.5 4.0)) E F))");
		check(input, Set.of(Set.of("A", "B", "C", "D", "E", "F")), 6, Map.of("=", 4, "and", 1, "-", 1, "*", 2, "+", 1),
				Map.of("Int", 4, "Bool", 2, "Real", 2), 1, Map.of(0, 1));

	}

	private void check(final Term input, final Set<Set<String>> expectedEquivClasses, final int expectedNumberOfVars,
			final Map<String, Integer> expectedFunctions, final Map<String, Integer> expectedSorts,
			final int expectedNumberOfQuantifiers, final Map<Integer, Integer> expectedQuantifiers) {
		final LBool isSat = SmtUtils.checkSatTerm(mScript, input);
		final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
		tc.checkTerm(input);

		mLogger.info("Original:               " + input.toStringDirect());
		mLogger.info("Original isSat:         " + isSat);
		mLogger.info("Original equiv classes: " + tc.getEquivalenceClasses());
		mLogger.info("Original #Vars:         " + tc.getNumberOfVariables());
		mLogger.info("Original Functions:     " + tc.getOccuringFunctionNames());
		mLogger.info("Original Sorts:         " + tc.getOccuringSortNames());
		mLogger.info("Original Quantifiers:   " + tc.getNumberOfQuantifiers());

		final Set<Set<String>> equivClasses = tc.getEquivalenceClasses().getAllEquivalenceClasses().stream()
				.map(a -> a.stream().map(Term::toString).collect(Collectors.toSet())).collect(Collectors.toSet());
		MatcherAssert.assertThat("equiv classes", equivClasses, IsEqual.equalTo(expectedEquivClasses));

		MatcherAssert.assertThat("#Vars", tc.getNumberOfVariables(), IsEqual.equalTo(expectedNumberOfVars));

		MatcherAssert.assertThat("Functions", tc.getOccuringFunctionNames(), IsEqual.equalTo(expectedFunctions));
		MatcherAssert.assertThat("Sorts", tc.getOccuringSortNames(), IsEqual.equalTo(expectedSorts));
		MatcherAssert.assertThat("#Quantifier", tc.getNumberOfQuantifiers(),
				IsEqual.equalTo(expectedNumberOfQuantifiers));
		MatcherAssert.assertThat("#Quantifier", tc.getOccuringQuantifiers(), IsEqual.equalTo(expectedQuantifiers));
	}

	private Term declareVar(final String name, final Sort sort) {
		mScript.declareFun(name, new Sort[0], sort);
		return mScript.term(name);
	}
}

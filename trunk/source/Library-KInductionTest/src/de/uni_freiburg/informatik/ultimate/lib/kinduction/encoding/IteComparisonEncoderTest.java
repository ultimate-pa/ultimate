/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * @author Max Barth (max.barth@lmu.de)
 */
public class IteComparisonEncoderTest {
	private static final String ONE = "(_ bv1 32)";
	private static final String ZERO = "(_ bv0 32)";
	private static final long TIMEOUT_MS = 60_000;

	private Script mScript;
	private ManagedScript mMgdScript;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(services, mScript);
		mScript.setLogic(Logics.ALL);
		final Sort bool = SmtSortUtils.getBoolSort(mScript);
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, 32);
		final Sort integer = SmtSortUtils.getIntSort(mScript);
		for (final String name : List.of("p", "q", "r")) {
			mScript.declareFun(name, new Sort[0], bool);
		}
		for (final String name : List.of("x", "y", "z")) {
			mScript.declareFun(name, new Sort[0], bv32);
		}
		mScript.declareFun("i", new Sort[0], integer);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void conditionIsNegatedIfThenBranchDiffers() {
		assertEncodedTo(String.format("(= (ite p %s %s) %s)", ONE, ZERO, ZERO), "(not p)");
	}

	@Test
	public void conditionStaysIfThenBranchIsEqual() {
		assertEncodedTo(String.format("(= (ite p %s %s) %s)", ONE, ZERO, ONE), "p");
	}

	@Test
	public void swappedBranches() {
		assertEncodedTo(String.format("(= (ite p %s %s) %s)", ZERO, ONE, ZERO), "p");
	}

	@Test
	public void iteOnTheRightHandSide() {
		assertEncodedTo(String.format("(= %s (ite p %s %s))", ZERO, ONE, ZERO), "(not p)");
	}

	@Test
	public void integers() {
		assertEncodedTo("(= (ite (= i 5) 1 0) 0)", "(not (= i 5))");
	}

	@Test
	public void nestedIteBecomesConjunction() {
		final Term encoded =
				assertEquivalentWithoutIte(String.format("(= %s (ite p (ite q %s %s) %s))", ZERO, ONE, ZERO, ONE));
		Assert.assertEquals(SmtUtils.and(mScript, parse("p"), parse("(not q)")), encoded);
	}

	@Test
	public void conditionIsEncodedToo() {
		assertEquivalentWithoutIte(
				String.format("(= (ite (= (ite p %s %s) %s) %s %s) %s)", ONE, ZERO, ZERO, ONE, ZERO, ZERO));
	}

	@Test
	public void insideBooleanStructure() {
		assertEquivalentWithoutIte(String.format("(or q (not (= (ite p %s %s) %s)))", ONE, ZERO, ZERO));
	}

	@Test
	public void leafThatDoesNotDecideKeepsTheEquality() {
		final Term input = parse("(= (ite p x y) z)");
		Assert.assertSame(input, IteComparisonEncoder.apply(mScript, input));
	}

	@Test
	public void leafThatDoesNotDecideInANestedIteKeepsTheEquality() {
		final Term input = parse(String.format("(= (ite p (ite q x %s) %s) %s)", ONE, ZERO, ZERO));
		Assert.assertSame(input, IteComparisonEncoder.apply(mScript, input));
	}

	/** Unfolded, the ite has more than 2^40 leaves. */
	@Test(timeout = TIMEOUT_MS)
	public void sharedSubtermsAreNotVisitedAgain() {
		final Sort bool = SmtSortUtils.getBoolSort(mScript);
		Term ite = parse(ONE);
		for (int i = 0; i < 40; i++) {
			mScript.declareFun("c" + i, new Sort[0], bool);
			mScript.declareFun("d" + i, new Sort[0], bool);
			final Term branch = mScript.term("ite", mScript.term("d" + i), ite, parse(ZERO));
			ite = mScript.term("ite", mScript.term("c" + i), ite, branch);
		}
		final Term encoded = IteComparisonEncoder.apply(mScript, mScript.term("=", ite, parse(ZERO)));
		Assert.assertTrue(SmtUtils.extractApplicationTerms("ite", encoded, false).isEmpty());
	}

	/**
	 * A C condition with 60 ites inside one equality. IteRemover would double the equality per ite, so it only finishes
	 * if the encoding has split it into its conjuncts first. The second ite of each conjunct does not decide its
	 * equality, so it is still there for IteRemover.
	 */
	@Test(timeout = TIMEOUT_MS)
	public void iteRemoverFinishesOnEncodedCondition() {
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, 32);
		final List<String> conjuncts = new ArrayList<>();
		for (int i = 0; i < 30; i++) {
			mScript.declareFun("v" + i, new Sort[0], bv32);
			final String max = String.format("(ite (bvsgt v%d y) v%d y)", i, i);
			conjuncts.add(String.format("(not (= %s (ite (= x %s) %s %s)))", ZERO, max, ONE, ZERO));
		}
		final Term input =
				parse(String.format("(= (ite (and %s) %s %s) %s)", String.join(" ", conjuncts), ONE, ZERO, ZERO));
		final Term encoded = IteComparisonEncoder.apply(mScript, input);
		final Term withoutIte = IteRemover.apply(mMgdScript, encoded);
		Assert.assertTrue(SmtUtils.extractApplicationTerms("ite", withoutIte, false).isEmpty());
	}

	private void assertEncodedTo(final String input, final String expected) {
		Assert.assertEquals(parse(expected), assertEquivalentWithoutIte(input));
	}

	private Term assertEquivalentWithoutIte(final String input) {
		final Term term = parse(input);
		final Term encoded = IteComparisonEncoder.apply(mScript, term);
		Assert.assertTrue(encoded.toString(), SmtUtils.extractApplicationTerms("ite", encoded, false).isEmpty());
		Assert.assertTrue(encoded.toString(), SmtUtils.areFormulasEquivalent(term, encoded, mScript));
		return encoded;
	}

	private Term parse(final String term) {
		return TermParseUtils.parseTerm(mScript, term);
	}
}

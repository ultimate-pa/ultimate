/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.io.IOException;
import java.util.List;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.Junction;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.FunDecl;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.QuantifierEliminationTest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Unit tests for {@link PolyPoNe}'s Phase B handling of {@link BitvectorInequalityRelation} (see
 * bitvector-inequality-relation-idea memory / the "pure-launching-barto" plan). Lives in the same package as
 * {@link PolyPoNe} deliberately - {@link PolyPoNe#addPolyRel} is protected and its constructor is package-visible,
 * neither reachable from a test in a different package.
 * <p>
 * Most tests below are exercised directly via {@link PolyPoNe#addPolyRel} rather than via {@link PolyPoNeUtils},
 * since {@link PolynomialRelation#of} (the shared factory used by ~15 other callers across the codebase) still
 * never returns a {@link BitvectorInequalityRelation} - see the "public entry point" tests near the end of this
 * file for the one place PolyPoNe itself is actually wired live (its own {@code add(...)}, via
 * {@link BitvectorInequalityRelation#ofIfApplicable}), which those tests exercise through {@link PolyPoNeUtils}.
 *
 * @author Roman Vintonyak
 */
public class PolyPoNeTwoSidedTest {

	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	private static final long TEST_TIMEOUT_MILLISECONDS = 20_000;

	private IUltimateServiceProvider mServices;
	private Script mScript;

	@Before
	public void setUp() throws IOException {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		mScript = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	private void declare(final FunDecl[] funDecls) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mScript);
		}
	}

	private Term parse(final String formulaAsString) {
		return TermParseUtils.parseTerm(mScript, formulaAsString);
	}

	private BitvectorInequalityRelation twoSided(final String formulaAsString) {
		return BitvectorInequalityRelation.of(mScript, parse(formulaAsString));
	}

	@Test
	public void tighterUpperBoundDropsLooserOne() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv5 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv3 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(bvule x (_ bv3 8))")));
	}

	@Test
	public void tighterUpperBoundDropsLooserOneRegardlessOfOrder() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv3 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv5 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(bvule x (_ bv3 8))")));
	}

	@Test
	public void crossStrictnessLooserBoundGetsDropped() {
		// x <=u 7 implies x <u 9 (Heizmann's example) - the looser, strict one should be dropped
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv7 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv9 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(bvule x (_ bv7 8))")));
	}

	@Test
	public void crossStrictnessTighterBoundReplacesLooserRegardlessOfOrder() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv9 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv7 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(bvule x (_ bv7 8))")));
	}

	@Test
	public void crossStrictnessEquivalentBoundsCollapseToOne() {
		// x <=u 7 and x <u 8 describe exactly the same set - the second one is redundant
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv7 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv8 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(bvule x (_ bv7 8))")));
	}

	@Test
	public void crossStrictnessAtUnderflowBoundaryDoesNotCrash() {
		// x <u 0 can't be normalized to a non-strict boundary (0 - 1 would underflow) - must decline, not crash
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv0 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv5 8))"), true);
		final Term result = polyPoNe.and();
		final Term expected = parse("(and (bvult x (_ bv0 8)) (bvule x (_ bv5 8)))");
		Assert.assertNotEquals(LBool.SAT, SmtUtils.checkEquivalence(result, expected, mScript));
	}

	@Test
	public void knownEqualityMakesSatisfyingInequalityRedundant() {
		// x = 5, then x <u 9 arrives - 5 <u 9 holds, so the inequality is redundant
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, PolynomialRelation.of(mScript, parse("(= x (_ bv5 8))")), true);
		final boolean inconsistent = polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv9 8))"), true);
		Assert.assertFalse(inconsistent);
		// toTerm() rebuilds "=" from the internal representation, which canonically orders it constant-first -
		// same pattern observed for upperAndLowerBoundWithSameConstantFuseIntoEquality below
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(= (_ bv5 8) x)")));
	}

	@Test
	public void knownEqualityViolatingInequalityIsInconsistent() {
		// x = 42, then x <s 7 arrives - 42 is not <s 7, so this is a contradiction
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, PolynomialRelation.of(mScript, parse("(= x (_ bv42 8))")), true);
		final boolean inconsistent = polyPoNe.addPolyRel(mScript, twoSided("(bvslt x (_ bv7 8))"), true);
		Assert.assertTrue(inconsistent);
	}

	@Test
	public void inequalityAddedBeforeEqualityIsNotCheckedAgainstIt() {
		// documents the scope boundary: only "new inequality vs. existing equality" is checked, not the reverse
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvult x (_ bv9 8))"), true);
		final boolean inconsistent =
				polyPoNe.addPolyRel(mScript, PolynomialRelation.of(mScript, parse("(= x (_ bv5 8))")), true);
		Assert.assertFalse(inconsistent);
		final Term result = polyPoNe.and();
		final Term expected = parse("(and (bvult x (_ bv9 8)) (= x (_ bv5 8)))");
		Assert.assertNotEquals(LBool.SAT, SmtUtils.checkEquivalence(result, expected, mScript));
	}

	@Test
	public void upperAndLowerBoundWithSameConstantFuseIntoEquality() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		polyPoNe.addPolyRel(mScript, twoSided("(bvule x (_ bv5 8))"), true);
		polyPoNe.addPolyRel(mScript, twoSided("(bvuge x (_ bv5 8))"), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(parse("(= (_ bv5 8) x)")));
	}

	@Test
	public void compoundRelationIsKeptAsIsWithoutCrashing() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final PolyPoNe polyPoNe = new PolyPoNe(mScript, Junction.AND);
		final Term compound = parse("(bvult (bvadd x y) (_ bv5 8))");
		polyPoNe.addPolyRel(mScript, BitvectorInequalityRelation.of(mScript, compound), true);
		MatcherAssert.assertThat(polyPoNe.and(), IsEqual.equalTo(compound));
	}

	@Test
	public void numericFusionStillWorksUnaffectedByTwoSidedBranch() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x") };
		declare(funDecls);
		final List<Term> params = List.of(parse("(<= x 5)"), parse("(>= x 5)"));
		final Term result = new PolyPoNe(mScript, Junction.AND).and(params);
		MatcherAssert.assertThat(result, IsEqual.equalTo(parse("(= 5 x)")));
	}

	// --- public entry point (PolyPoNeUtils) - the one live, wired-up path, see BitvectorInequalityRelation#ofIfApplicable ---

	@Test
	public void publicEntryPointDropsRedundantBoundForBitvectors() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final List<Term> params = List.of(parse("(bvule x (_ bv5 8))"), parse("(bvule x (_ bv3 8))"));
		final Term result = PolyPoNeUtils.and(mScript, params);
		MatcherAssert.assertThat(result, IsEqual.equalTo(parse("(bvule x (_ bv3 8))")));
	}

	@Test
	public void publicEntryPointFusesIntoEqualityForBitvectors() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final List<Term> params = List.of(parse("(bvule x (_ bv5 8))"), parse("(bvuge x (_ bv5 8))"));
		final Term result = PolyPoNeUtils.and(mScript, params);
		MatcherAssert.assertThat(result, IsEqual.equalTo(parse("(= (_ bv5 8) x)")));
	}

	@Test
	public void publicEntryPointStillHandlesNonRelationalAtomsSafely() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "p") };
		declare(funDecls);
		// "p" is not a binary relation at all - must not trip BitvectorInequalityRelation.ofIfApplicable
		final List<Term> params = List.of(parse("(bvule x (_ bv5 8))"), parse("p"));
		final Term result = PolyPoNeUtils.and(mScript, params);
		// "and" is commutative and may reorder its arguments, so compare by equivalence rather than exact term
		final Term expected = parse("(and (bvule x (_ bv5 8)) p)");
		Assert.assertNotEquals(LBool.SAT, SmtUtils.checkEquivalence(result, expected, mScript));
	}
}

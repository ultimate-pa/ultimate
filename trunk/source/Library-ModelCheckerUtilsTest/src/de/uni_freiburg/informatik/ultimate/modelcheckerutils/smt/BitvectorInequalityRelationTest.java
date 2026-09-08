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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.BitvectorInequalityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Unit tests for {@link BitvectorInequalityRelation}, exercised directly via its own {@code of(Script, Term)} entry
 * point since it is not yet wired into {@code PolynomialRelation.of(...)} - see the TODOs on that interface's static
 * factories. Follows the same solver/script setup as {@link BitvectorUtilsTest}.
 *
 * @author Roman Vintonyak
 */
public class BitvectorInequalityRelationTest {

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

	private void assertToTermEquals(final BitvectorInequalityRelation relation, final String expectedAsString) {
		final Term expected = parse(expectedAsString);
		MatcherAssert.assertThat(relation.toTerm(mScript), IsEqual.equalTo(expected));
	}

	@Test
	public void bvugeMirroredToBvule() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvuge x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		assertToTermEquals(relation, "(bvule y x)");
	}

	@Test
	public void bvugtMirroredToBvult() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvugt x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		assertToTermEquals(relation, "(bvult y x)");
	}

	@Test
	public void bvsgeMirroredToBvsle() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvsge x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		assertToTermEquals(relation, "(bvsle y x)");
	}

	@Test
	public void bvsgtMirroredToBvslt() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvsgt x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		assertToTermEquals(relation, "(bvslt y x)");
	}

	@Test
	public void bvultStaysUnmirrored() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvult x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		assertToTermEquals(relation, "(bvult x y)");
	}

	@Test
	public void isAffineForBareVariables() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvult x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		Assert.assertTrue(relation.isAffine());
	}

	@Test
	public void isVariableDistinguishesOccurringFromForeignVariables() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y", "z") };
		declare(funDecls);
		final Term input = parse("(bvult x y)");
		final Term foreignVar = parse("z");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		Assert.assertTrue(relation.isVariable(parse("x")));
		Assert.assertTrue(relation.isVariable(parse("y")));
		Assert.assertFalse(relation.isVariable(foreignVar));
	}

	@Test
	public void negateTwiceReturnsToCanonicalForm() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvuge x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		final BitvectorInequalityRelation doubleNegated = relation.negate().negate();
		MatcherAssert.assertThat(doubleNegated.toTerm(mScript), IsEqual.equalTo(relation.toTerm(mScript)));
	}

	@Test
	public void isSimpleEqualityIsAlwaysNull() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvult x y)");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		Assert.assertNull(relation.isSimpleEquality(mScript));
	}

	@Test
	public void solveForSubjectSolvesBareVariableUpperBound() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final Term input = parse("(bvult x (_ bv5 8))");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		final SolvedBinaryRelation solved = relation.solveForSubject(mScript, parse("x"));
		Assert.assertNotNull(solved);
		MatcherAssert.assertThat(solved.getLeftHandSide(), IsEqual.equalTo(parse("x")));
		MatcherAssert.assertThat(solved.getRightHandSide(), IsEqual.equalTo(parse("(_ bv5 8)")));
		Assert.assertEquals(RelationSymbol.BVULT, solved.getRelationSymbol());
	}

	@Test
	public void solveForSubjectSolvesBareVariableLowerBoundAfterMirroring() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		// canonicalizes to "(_ bv5 8) bvule x", i.e. the variable ends up on the right-hand side
		final Term input = parse("(bvuge x (_ bv5 8))");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		final SolvedBinaryRelation solved = relation.solveForSubject(mScript, parse("x"));
		Assert.assertNotNull(solved);
		MatcherAssert.assertThat(solved.getLeftHandSide(), IsEqual.equalTo(parse("x")));
		MatcherAssert.assertThat(solved.getRightHandSide(), IsEqual.equalTo(parse("(_ bv5 8)")));
		Assert.assertEquals(RelationSymbol.BVULE, solved.getRelationSymbol());
	}

	@Test
	public void solveForSubjectReturnsNullForWrongVariable() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvult x (_ bv5 8))");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		Assert.assertNull(relation.solveForSubject(mScript, parse("y")));
	}

	@Test
	public void solveForSubjectReturnsNullForCompoundSide() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final Term input = parse("(bvult (bvadd x y) (_ bv5 8))");
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, input);
		Assert.assertNull(relation.solveForSubject(mScript, parse("x")));
	}

	@Test
	public void mulByOneIsNoOp() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, parse("(bvult x y)"));
		Assert.assertSame(relation, relation.mul(mScript, Rational.ONE));
	}

	@Test
	public void mulByNegativeOneOnSignedRelationReversesOrder() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, parse("(bvslt x y)"));
		final PolynomialRelation result = relation.mul(mScript, Rational.MONE);
		final Term expected = parse("(bvslt (bvneg y) (bvneg x))");
		Assert.assertNotEquals(LBool.SAT, SmtUtils.checkEquivalence(result.toTerm(mScript), expected, mScript));
	}

	@Test(expected = UnsupportedOperationException.class)
	public void mulByNegativeOneRejectsUnsignedRelation() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, parse("(bvult x y)"));
		relation.mul(mScript, Rational.MONE);
	}

	@Test(expected = UnsupportedOperationException.class)
	public void mulByOtherValuesIsUnsupported() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x", "y") };
		declare(funDecls);
		final BitvectorInequalityRelation relation = BitvectorInequalityRelation.of(mScript, parse("(bvslt x y)"));
		relation.mul(mScript, Rational.valueOf(2, 1));
	}

	@Test
	public void strictlyBelowUnsignedMinimumCollapsesToFalse() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvult x (_ bv0 8))"));
		assertToTermEquals(relation, "false");
	}

	@Test
	public void atMostUnsignedMinimumCollapsesToEquality() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvule x (_ bv0 8))"));
		assertToTermEquals(relation, "(= (_ bv0 8) x)");
	}

	@Test
	public void atMostUnsignedMaximumCollapsesToTrue() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvule x (_ bv255 8))"));
		assertToTermEquals(relation, "true");
	}

	@Test
	public void atLeastUnsignedMinimumCollapsesToTrue() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvule (_ bv0 8) x)"));
		assertToTermEquals(relation, "true");
	}

	@Test
	public void strictlyAboveUnsignedMaximumCollapsesToFalse() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvult (_ bv255 8) x)"));
		assertToTermEquals(relation, "false");
	}

	@Test
	public void atLeastUnsignedMaximumCollapsesToEquality() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvule (_ bv255 8) x)"));
		assertToTermEquals(relation, "(= (_ bv255 8) x)");
	}

	@Test
	public void strictlyBelowUnsignedMaximumDoesNotCollapse() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvult x (_ bv255 8))"));
		assertToTermEquals(relation, "(bvult x (_ bv255 8))");
	}

	@Test
	public void strictlyBelowSignedMinimumCollapsesToFalse() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		declare(funDecls);
		// (_ bv128 8) is the most-negative signed 8-bit value (-128)
		final BitvectorInequalityRelation relation =
				BitvectorInequalityRelation.of(mScript, parse("(bvslt x (_ bv128 8))"));
		assertToTermEquals(relation, "false");
	}
}

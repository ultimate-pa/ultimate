/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.io.IOException;
import java.math.BigInteger;
import java.util.HashSet;
import java.util.Set;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PredicateTreeTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServices.getLoggingService().getLogger(getClass());
		try {
			mScript = new Scriptor("z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in", mLogger, mServices,
					new ToolchainStorage(), "z3");
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);

	}

	@Test
	public void test() {

		final PredicateTree<TestPredicate> ptree = new PredicateTree<>(mMgdScript);
		mMgdScript.lock(this);
		final Set<IProgramVar> vars = new HashSet<>();
		final BoogieNonOldVar a = constructProgramVar("a");
		final BoogieNonOldVar b = constructProgramVar("b");
		vars.add(a);
		vars.add(b);
		final TestPredicate pred1 =
				new TestPredicate(mScript.term("=", a.getTermVariable(), mScript.numeral("1")), vars, mScript);
		final TestPredicate pred2 =
				new TestPredicate(mScript.term("=", a.getTermVariable(), mScript.numeral("1")), vars, mScript);
		final TestPredicate pred3 =
				new TestPredicate(mScript.term("=", a.getTermVariable(), mScript.numeral("2")), vars, mScript);
		final TestPredicate pred4 =
				new TestPredicate(mScript.term(">", a.getTermVariable(), mScript.numeral("0")), vars, mScript);
		final TestPredicate pred5 =
				new TestPredicate(mScript.term(">", a.getTermVariable(), mScript.numeral("1")), vars, mScript);
		final TestPredicate pred6 =
				new TestPredicate(mScript.term("=", b.getTermVariable(), mScript.numeral("0")), vars, mScript);
		final TestPredicate pred7 =
				new TestPredicate(SmtUtils.and(mScript, pred1.getFormula(), pred6.getFormula()), vars, mScript);
		mMgdScript.unlock(this);

		Assert.assertTrue(pred1 != pred2);
		final TestPredicate upred1 = ptree.unifyPredicate(pred1);
		Assert.assertTrue(upred1 == pred1);
		final TestPredicate upred2 = ptree.unifyPredicate(pred2);
		Assert.assertTrue(upred2 == pred1);
		final TestPredicate upred3 = ptree.unifyPredicate(pred3);
		Assert.assertTrue(upred3 == pred3);
		final TestPredicate upred4 = ptree.unifyPredicate(pred4);
		Assert.assertTrue(upred4 == pred4);
		final TestPredicate upred5 = ptree.unifyPredicate(pred5);
		Assert.assertTrue(upred5 == pred5);
		final TestPredicate upred7 = ptree.unifyPredicate(pred7);
		Assert.assertTrue(upred7 == pred7);
		final TestPredicate upred6 = ptree.unifyPredicate(pred6);
		Assert.assertTrue(upred6 == pred6);
		mLogger.info("\n" + ptree.toLogString());
	}

	/**
	 * Old quantifier elimination needs seconds, new quantifier elimination needs minutes and produces more than 500
	 * conjuncts
	 */
	public void rajdeepIteration5wp() {

		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(8) });
		final Sort bv32 = SmtSortUtils.getBitvectorSort(mScript, new BigInteger[] { BigInteger.valueOf(32) });
		final Sort array = SmtSortUtils.getArraySort(mScript, bv32, bv8);

		mScript.declareFun("ULTIMATE.start_design_~nack.base", new Sort[0], bv32);
		mScript.declareFun("ULTIMATE.start_design_~nack.offset", new Sort[0], bv32);
		mScript.declareFun("ULTIMATE.start_design_~alloc_addr.base", new Sort[0], bv32);
		mScript.declareFun("ULTIMATE.start_main_~#nack~7.base", new Sort[0], bv32);
		mScript.declareFun("ULTIMATE.start_main_~#nack~7.offset", new Sort[0], bv32);

		mScript.declareFun("~smain.count", new Sort[0], bv8);
		mScript.declareFun("~smain.busy", new Sort[0], array);

		final String formulaAsString =
				"(forall ((|#memory_INTTYPE1| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8)))) (v_bitvector_28 (_ BitVec 32)) (v_bitvector_27 (_ BitVec 32)) (~smain.free_addr (_ BitVec 8)) (v_bitvector_20 (_ BitVec 8)) (~smain.alloc (_ BitVec 8)) (v_bitvector_32 (_ BitVec 32)) (v_bitvector_31 (_ BitVec 32)) (v_bitvector_30 (_ BitVec 32)) (v_bitvector_29 (_ BitVec 32)) (v_bitvector_36 (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8)))) (ULTIMATE.start_design_~alloc_addr.offset (_ BitVec 32)) (|ULTIMATE.start_design_#t~ite18| (_ BitVec 32)) (v_bitvector_24 (_ BitVec 8)) (v_bitvector_19 (_ BitVec 8)) (v_bitvector_35 (_ BitVec 8)) (v_bitvector_25 (_ BitVec 32)) (v_bitvector_26 (_ BitVec 32)) (v_bitvector_33 (_ BitVec 32)) (v_bitvector_34 (_ BitVec 32))) (and (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_28 ((_ extract 7 0) v_bitvector_27))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8)) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_28 ((_ extract 7 0) v_bitvector_27))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_32 ((_ extract 7 0) v_bitvector_31))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8)) (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_30 ((_ extract 7 0) v_bitvector_29))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) ULTIMATE.start_design_~alloc_addr.offset ((_ extract 7 0) |ULTIMATE.start_design_#t~ite18|))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (or (not (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (_ bv0 8) ~smain.alloc) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_25 ((_ extract 7 0) v_bitvector_26))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (not (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_33 ((_ extract 7 0) v_bitvector_34))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32)) (_ bv0 32)) (= (_ bv0 8) v_bitvector_35)) (or (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) ULTIMATE.start_design_~alloc_addr.offset ((_ extract 7 0) |ULTIMATE.start_design_#t~ite18|))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))))))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mLogger.info(result);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	private BoogieNonOldVar constructProgramVar(final String identifier) {
		BoogieOldVar oldVar;
		final Sort sort = SmtSortUtils.getIntSort(mMgdScript);
		{
			final boolean isOldVar = true;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = mMgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, this, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, this, sort, name);

			oldVar = new BoogieOldVar(identifier, null, termVariable, defaultConstant, primedConstant);
		}
		BoogieNonOldVar nonOldVar;
		{
			final boolean isOldVar = false;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = mMgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, this, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, this, sort, name);

			nonOldVar = new BoogieNonOldVar(identifier, null, termVariable, defaultConstant, primedConstant, oldVar);
		}
		oldVar.setNonOldVar(nonOldVar);
		return nonOldVar;
	}

	private static final class TestPredicate implements IPredicate {

		private final Set<IProgramVar> mVars;
		private final Term mClosedFormula;
		private final Term mFormula;

		public TestPredicate(final Term formula, final Set<IProgramVar> vars, final Script script) {
			mVars = vars;
			mFormula = formula;
			mClosedFormula = PredicateUtils.computeClosedFormula(formula, vars, script);
		}

		@Override
		public String[] getProcedures() {
			return new String[0];
		}

		@Override
		public Set<IProgramVar> getVars() {
			return mVars;
		}

		@Override
		public Term getFormula() {
			return mFormula;
		}

		@Override
		public Term getClosedFormula() {
			return mClosedFormula;
		}

		@Override
		public String toString() {
			return getFormula().toStringDirect();
		}

	}
}

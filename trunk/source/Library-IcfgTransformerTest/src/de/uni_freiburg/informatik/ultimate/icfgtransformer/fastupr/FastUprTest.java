/*
 * Copyright (C) 2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.fastupr;

import java.util.Collections;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRCore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FastUprTest {

	private static final boolean DUMP = false;
	private static final String DUMP_PATH = "C:\\Users\\firefox\\Desktop\\dump";
	private static final boolean PQE_AND_SIMPLIFY = false;

	private IUltimateServiceProvider mServices;
	private Script mZ3;
	private ManagedScript mMgdZ3;
	private ILogger mLogger;
	private Script mSmtInterpol;
	private ManagedScript mMgdSmtInterpol;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = new ConsoleLogger(LogLevel.DEBUG);

		final SolverSettings solverSettingsZ3 =
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setSolverLogics(Logics.ALL).setUseExternalSolver(ExternalSolver.Z3)
						.setSolverLogger(UltimateMocks.createUltimateServiceProviderMock(LogLevel.WARN)
								.getLoggingService().getLogger(getClass()))
						.setDumpSmtScriptToFile(DUMP, DUMP_PATH, getClass().getSimpleName() + "_z3", false);

		mZ3 = SolverBuilder.buildAndInitializeSolver(mServices, solverSettingsZ3, "Z3");
		mMgdZ3 = new ManagedScript(mServices, mZ3);

		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.Internal_SMTInterpol).setSolverLogics(Logics.ALL)
				.setSolverLogger(UltimateMocks.createUltimateServiceProviderMock(LogLevel.WARN).getLoggingService()
						.getLogger(getClass()))
				.setDumpSmtScriptToFile(DUMP, DUMP_PATH, getClass().getSimpleName() + "_smtinterpol", false);
		mSmtInterpol = SolverBuilder.buildAndInitializeSolver(mServices, solverSettings, "SmtInterpol");
		mMgdSmtInterpol = new ManagedScript(mServices, mSmtInterpol);

		mLogger.info("setUp() finished");
	}

	/**
	 * The expected formulas for {@link #tfEx01_Z3()} and {@link #tfEx01_SmtInterpol()} are equivalent according to
	 * SmtInterpol (Z3 says unknown)
	 */
	// @Test disable because it also takes ~4h on jenkins
	public void tfEx01_Z3() {
		runAndTestAcceleration(this::getTfEx01LoopBody,
				"(or (and (<= (+ (* (- 1) c_x_primed) c_x) (- 1)) (<= (+ (* (- 1) c_x) c_x_primed) 1)) "
						+ "(exists ((v_k_1 Int)) (and (>= v_k_1 0) (and (<= (+ (* (- 1) c_x_primed) c_x) "
						+ "(+ (* (- 1) v_k_1) (- 2))) (<= (+ c_x_primed (* (- 1) c_x)) (+ (* 1 v_k_1) 2))))))",
				mMgdZ3);
	}

	/**
	 * @see #tfEx01_Z3()
	 */
	@Test
	public void tfEx01_SmtInterpol() {
		runAndTestAcceleration(this::getTfEx01LoopBody, "(<= (+ c_x 1) c_x_primed)", mMgdSmtInterpol);
	}

	// @Test disable because it does not succeed
	public void tfEx02_SmtInterpol() {
		// smtinterpol sometimes shows equivalence, sometimes answers with unknown
		final String simplified = "(or (and (<= (div (+ (* c_x_primed (- 1)) c_x 6) (- 3)) "
				+ "(div (+ c_x_primed (* c_x (- 1)) (- 6)) 3)) (<= 0 (div (+ c_x_primed (* c_x (- 1)) (- 6)) 3)) "
				+ "(<= (div (+ (* c_x_primed (- 1)) c_x 6) (- 3)) (div (+ (* c_x (- 2)) 992) 6))) "
				+ "(and (<= (+ c_x 3) c_x_primed) (<= (* 2 c_x) 998) (<= c_x_primed (+ c_x 3))))";
		final String actual = "(or (and (<= (* 2 c_x) 998) (<= (+ (* (- 1) c_x_primed) c_x) (- 3)) "
				+ "(<= (+ (* (- 1) c_x) c_x_primed) 3)) " + "(exists ((v_k_1 Int)) " + "(and (>= v_k_1 0) " + "(and "
				+ "(<= (+ c_x_primed (* (- 1) c_x)) (+ (* 3 v_k_1) 6)) " + "(<= (* 2 c_x) (+ (* (- 6) v_k_1) 992)) "
				+ "(<= (+ (* (- 1) c_x_primed) c_x) (+ (* (- 3) v_k_1) (- 6))) "
				+ "(<= (* 2 c_x) (+ (* (- 6) v_k_1) 998))))))";

		runAndTestAcceleration(this::getTfEx02LoopBody, actual, mMgdSmtInterpol);
	}

	// @Test disable because it does not succeed
	public void tfEx03_SmtInterpol() {
		runAndTestAcceleration(this::getTfEx03LoopBody,
				"(or (and (<= (+ c_x 2) c_x_primed) (<= (* 2 c_x) 20) (<= c_x_primed (+ c_x 2))) (and (<= 0 (div (+ c_x_primed (* c_x (- 1)) (- 4)) 2)) (<= (div (+ (* c_x_primed (- 1)) c_x 4) (- 2)) (div (+ c_x_primed (* c_x (- 1)) (- 4)) 2)) (<= (div (+ (* c_x_primed (- 1)) c_x 4) (- 2)) (div (+ (* c_x (- 2)) 16) 4))))",
				mMgdSmtInterpol);
	}

	// @Test disable because it does not succeed
	public void tfEx04_Z3() {
		runAndTestAcceleration(this::getTfEx04LoopBody,
				"(and (<= (+ c_x 2) c_x_primed) (<= 6 (* 2 c_x)) (<= (* 2 c_x) 20) (<= c_x_primed (+ c_x 2)))", mMgdZ3);
	}

	// @Test disable because it runs reeeeally long
	public void tfEx05_Z3() {
		runAndTestAcceleration(this::getTfEx05LoopBody, "false", mMgdZ3);
	}

	// @Test disable because it does not succeed
	public void tfEx05_SmtInterpol() {
		runAndTestAcceleration(this::getTfEx05LoopBody, "false", mMgdSmtInterpol);
	}

	// @Test disabled because Z3 runs out of resources during acceleration
	public void tfEx02_Z3() {
		runAndTestAcceleration(this::getTfEx02LoopBody, "???", mMgdZ3);
	}

	// @Test test disabled because Z3 runs out of resources during acceleration
	public void compareTfEx01() {
		compareAccelerations(this::getTfEx01LoopBody);
	}

	private void compareAccelerations(final TestData funData) {
		final UnmodifiableTransFormula loopBodyZ3 = funData.getLoopBody(mMgdZ3);

		// create decls for smtinterpol as well
		final UnmodifiableTransFormula loopBodySmtInterpol = funData.getLoopBody(mMgdSmtInterpol);

		final UnmodifiableTransFormula acceleratedZ3 =
				new FastUPRCore(loopBodyZ3, mMgdZ3, mLogger, mServices).getResult();
		final UnmodifiableTransFormula acceleratedSmtInterpol =
				new FastUPRCore(loopBodySmtInterpol, mMgdSmtInterpol, mLogger, mServices).getResult();
		mLogger.info("Input                : %s", loopBodyZ3);
		mLogger.info("Output Z3            : %s", acceleratedZ3);
		mLogger.info("Output SmtInterpol   : %s", acceleratedSmtInterpol);

		final Script z3 = mMgdZ3.getScript();
		final Script smtInterpol = mMgdSmtInterpol.getScript();
		final IUltimateServiceProvider services = mServices;
		final ILogger logger = mLogger;
		final ManagedScript mgdScript = mMgdZ3;

		final Term pqeZ3 = PartialQuantifierElimination.eliminateCompat(services, mgdScript, SimplificationTechnique.SIMPLIFY_DDA, acceleratedZ3.getClosedFormula());
		final Term z3SimpTerm = SmtUtils.simplify(mMgdZ3, pqeZ3, mServices, SimplificationTechnique.SIMPLIFY_DDA);
		final Term smtInterpolSimpTerm = SmtUtils.simplify(mMgdSmtInterpol, acceleratedSmtInterpol.getClosedFormula(),
				mServices, SimplificationTechnique.SIMPLIFY_DDA);

		mLogger.info("Output Z3 S          : %s", z3SimpTerm);
		mLogger.info("Output SmtInterpol S : %s", smtInterpolSimpTerm);

		final TermTransferrer tt = new TermTransferrer(smtInterpol, z3, Collections.emptyMap(), false);

		z3.assertTerm(z3.term("distinct", z3SimpTerm, tt.transform(smtInterpolSimpTerm)));
		final LBool result = z3.checkSat();

		mLogger.info("Is distinct        : %s", result);
		Assert.assertEquals(result, LBool.UNSAT);
	}

	/**
	 * Create loop body x' = x + 1
	 */
	private UnmodifiableTransFormula getTfEx01LoopBody(final ManagedScript managedScript) {
		final Script script = managedScript.getScript();
		managedScript.lock(this);
		final ProgramNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
				managedScript, this);
		managedScript.unlock(this);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final TermVariable in = managedScript.constructFreshCopy(varX.getTermVariable());
		final TermVariable out = managedScript.constructFreshCopy(varX.getTermVariable());

		tfb.addInVar(varX, in);
		tfb.addOutVar(varX, out);

		final Term term = script.term("=", script.term("+", in, script.numeral("1")), out);

		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Create loop body x < 500 /\ x' = x + 3 (from presentation)
	 */
	private UnmodifiableTransFormula getTfEx02LoopBody(final ManagedScript managedScript) {
		final Script script = managedScript.getScript();
		managedScript.lock(this);
		final ProgramNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
				managedScript, this);
		managedScript.unlock(this);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final TermVariable in = managedScript.constructFreshCopy(varX.getTermVariable());
		final TermVariable out = managedScript.constructFreshCopy(varX.getTermVariable());

		tfb.addInVar(varX, in);
		tfb.addOutVar(varX, out);

		final Term term = script.term("and", script.term("<", in, script.numeral("500")),
				script.term("=", script.term("+", in, script.numeral("3")), out));

		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Create loop body for
	 *
	 * [assume x <= 10;, assume !(x > 2);, x := x + 1;, x := x + 1;],
	 *
	 * by simplifying to
	 *
	 * x <= 10 && x' = x+2
	 *
	 * (accelerated interpolation 1)
	 */
	private UnmodifiableTransFormula getTfEx03LoopBody(final ManagedScript managedScript) {
		final Script script = managedScript.getScript();
		managedScript.lock(this);
		final ProgramNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
				managedScript, this);
		managedScript.unlock(this);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final TermVariable in = managedScript.constructFreshCopy(varX.getTermVariable());
		final TermVariable out = managedScript.constructFreshCopy(varX.getTermVariable());

		tfb.addInVar(varX, in);
		tfb.addOutVar(varX, out);

		final Term term = script.term("and", script.term("<=", in, script.numeral("10")),
				script.term("=", script.term("+", in, script.numeral("2")), out));

		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Create loop body for
	 *
	 * [assume x <= 10;, assume x > 2;, x := x + 1;, x := x + 1;]
	 *
	 * by simplifying to
	 *
	 * x <= 10 && x > 2 && x' = x+2
	 *
	 * (accelerated interpolation 2)
	 */
	private UnmodifiableTransFormula getTfEx04LoopBody(final ManagedScript managedScript) {
		final Script script = managedScript.getScript();
		managedScript.lock(this);
		final ProgramNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
				managedScript, this);
		managedScript.unlock(this);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final TermVariable in = managedScript.constructFreshCopy(varX.getTermVariable());
		final TermVariable out = managedScript.constructFreshCopy(varX.getTermVariable());

		tfb.addInVar(varX, in);
		tfb.addOutVar(varX, out);

		final Term guard1 = script.term("<=", in, script.numeral("10"));
		final Term guard2 = script.term(">", in, script.numeral("2"));
		final Term body = script.term("=", script.term("+", in, script.numeral("2")), out);

		final Term term = script.term("and", guard1, guard2, body);

		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	/**
	 * Create loop body for
	 *
	 * (and (< (+ c_x 4026531841) 0) (= c_x_primed (+ c_x 2)) (<= 0 (+ c_x 4294967296)))
	 *
	 * x + 4026531841 < 0 && x' = x +2 && 0 <= x + 4294967296
	 *
	 * (accelerated interpolation 3)
	 *
	 * Formula:
	 *
	 * (and (< (+ c_x 4026531841) 0) (= c_x_primed (+ c_x 2)) (<= 0 (+ c_x 4294967296))) InVars {main_~x~0=c_x}
	 * OutVars{main_~x~0=c_x_primed} AuxVars[] AssignedVars[main_~x~0]
	 *
	 */
	private UnmodifiableTransFormula getTfEx05LoopBody(final ManagedScript managedScript) {
		final Script script = managedScript.getScript();
		managedScript.lock(this);
		final ProgramNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
				managedScript, this);
		managedScript.unlock(this);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final TermVariable in = managedScript.constructFreshCopy(varX.getTermVariable());
		final TermVariable out = managedScript.constructFreshCopy(varX.getTermVariable());

		tfb.addInVar(varX, in);
		tfb.addOutVar(varX, out);

		final Term zero = script.numeral("0");
		final Term guard1 = script.term("<", script.term("+", in, script.numeral("4026531841")), zero);
		final Term guard2 = script.term("<=", zero, script.term("+", in, script.numeral("4294967296")));
		final Term body = script.term("=", out, script.term("+", in, script.numeral("2")));

		final Term term = script.term("and", guard1, body, guard2);

		tfb.setFormula(term);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}

	private void runAndTestAcceleration(final TestData input, final String expected,
			final ManagedScript managedScript) {
		final UnmodifiableTransFormula loopBody = input.getLoopBody(managedScript);
		testAcceleration(managedScript, loopBody, expected);
	}

	@Test
	public void noLoopAcceleration() {
		testAcceleration(mMgdZ3, TransFormulaBuilder.getTrivialTransFormula(mMgdZ3), "true");
	}

	private void testAcceleration(final ManagedScript managedScript, final UnmodifiableTransFormula input,
			final String expected) {
		final UnmodifiableTransFormula accelerated =
				new FastUPRCore(input, managedScript, mLogger, mServices).getResult();
		final Term actualT = accelerated.getClosedFormula();
		mLogger.info("Input            : %s", input.getClosedFormula().toStringDirect());
		mLogger.info("Output           : %s", actualT.toStringDirect());
		mLogger.info("Expected formula : %s", expected);

		final Script script = managedScript.getScript();
		if (PQE_AND_SIMPLIFY) {
			mLogger.info("Running PQE");
			final IUltimateServiceProvider services = mServices;
			final ILogger logger = mLogger;
			final Term pqe = PartialQuantifierElimination.eliminateCompat(services, managedScript, SimplificationTechnique.SIMPLIFY_DDA, actualT);
			mLogger.info("Running simplify");
			final Term simpTerm =
					SmtUtils.simplify(managedScript, pqe, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			mLogger.info("Output Simplified: %s", simpTerm.toStringDirect());

			script.echo(new QuotedObject("check (distinct simplified acceleration)"));
			script.push(1);
			script.assertTerm(script.term("distinct", simpTerm, actualT));
			final LBool isDistinct = script.checkSat();
			script.pop(1);
			mLogger.info("isDistinct %s", isDistinct);
			Assert.assertEquals("Simplification and actual term are not equal", LBool.UNSAT, isDistinct);
		}

		final Term expectedT = TermParseUtils.parseTerm(script, expected);
		final LBool isDistinct = SmtUtils.checkSatTerm(script, script.term("distinct", expectedT, actualT));
		Assert.assertEquals(String.format("(E)xpected result %s and (A)ctual result %s are not equal. (distict E A): ",
				expectedT, actualT), LBool.UNSAT, isDistinct);

	}

	// @Test not necessary, was just trying to look at possible error sources
	public void quantifierElim1() {
		final ManagedScript managedScript = mMgdZ3;
		final Script script = managedScript.getScript();

		final TermVariable x = script.variable("x", SmtSortUtils.getIntSort(managedScript));
		final TermVariable k = script.variable("k", SmtSortUtils.getIntSort(managedScript));

		/**
		 * (exists ((k Int)) (and (>= k 0) (k <= 496 / 3) (out = 3k + 6 )
		 */

		final Term con1 = script.term(">=", k, script.numeral("0"));
		final Term con2 = script.term("<=", k, script.term("div", script.numeral("496"), script.numeral("3")));
		final Term con3 =
				script.term("=", x, script.term("+", script.term("*", k, script.numeral("3")), script.numeral("6")));
		final Term quantified =
				script.quantifier(Script.EXISTS, new TermVariable[] { k }, script.term("and", con1, con2, con3));
		final IUltimateServiceProvider services = mServices;
		final ILogger logger = mLogger;
		final Term eliminated = PartialQuantifierElimination.eliminateCompat(services, managedScript, SimplificationTechnique.SIMPLIFY_DDA, quantified);

		final LBool isDistinct = SmtUtils.checkSatTerm(script, script.term("distinct", quantified, eliminated));
		mLogger.info("Term     : %s", quantified.toStringDirect());
		mLogger.info("Elim     : %s", eliminated.toStringDirect());
		mLogger.info("Distinct?: %s", isDistinct);

		Assert.assertEquals(LBool.UNSAT, isDistinct);
	}

	// @Test not necessary, was just trying to look at possible error sources
	public void quantifierElim2() {
		final ManagedScript managedScript = mMgdZ3;
		final Script script = managedScript.getScript();

		final TermVariable in = script.variable("in", SmtSortUtils.getIntSort(managedScript));
		final TermVariable out = script.variable("out", SmtSortUtils.getIntSort(managedScript));
		final TermVariable k = script.variable("k", SmtSortUtils.getIntSort(managedScript));

		/**
		 * (or (and (<= in 499) (= (+ (* (- 1) out) in) (- 3))
		 *
		 * (exists ((k Int)) (and (>= k 0) (k <= 496 / 3) (out = 3k + 6 )
		 */

		final Term d1c1 = script.term("<=", in, script.numeral("499"));
		final Term d1c2 = script.term("=", script.term("+", script.term("*", script.numeral("-1"), out), in),
				script.numeral("-3"));
		final Term disj1 = script.term("and", d1c1, d1c2);

		final Term qcon1 = script.term(">=", k, script.numeral("0"));
		final Term qcon2 = script.term("<=", k, script.term("div", script.numeral("496"), script.numeral("3")));
		final Term qcon3 =
				script.term("=", out, script.term("+", script.term("*", k, script.numeral("3")), script.numeral("6")));
		final Term disj2 =
				script.quantifier(Script.EXISTS, new TermVariable[] { k }, script.term("and", qcon1, qcon2, qcon3));

		final Term term = script.term("or", disj1, disj2);
		final IUltimateServiceProvider services = mServices;
		final ILogger logger = mLogger;

		final Term eliminated = PartialQuantifierElimination.eliminateCompat(services, managedScript, SimplificationTechnique.SIMPLIFY_DDA, term);

		final LBool isDistinct = SmtUtils.checkSatTerm(script, script.term("distinct", term, eliminated));
		mLogger.info("Term     : %s", term.toStringDirect());
		mLogger.info("Elim     : %s", eliminated.toStringDirect());
		mLogger.info("Distinct?: %s", isDistinct);

		Assert.assertEquals(LBool.UNSAT, isDistinct);
	}

	@After
	public void executeAfterEachTest() {
		mZ3.exit();
		mSmtInterpol.exit();
		mLogger.info("--");
	}

	@FunctionalInterface
	private interface TestAcceleration {
		void testAcceleration(final ManagedScript script, final UnmodifiableTransFormula input, final String expected);
	}

	@FunctionalInterface
	private interface TestData {
		UnmodifiableTransFormula getLoopBody(final ManagedScript script);
	}

}

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FastUprTest {

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

		final SolverSettings solverSettingsZ3 = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setSolverLogics(Logics.ALL)
				.setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, Logics.ALL)
				.setSolverLogger(UltimateMocks.createUltimateServiceProviderMock(LogLevel.WARN).getLoggingService()
						.getLogger(getClass()));

		mZ3 = SolverBuilder.buildAndInitializeSolver(mServices, solverSettingsZ3, "Z3");
		mMgdZ3 = new ManagedScript(mServices, mZ3);

		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.Internal_SMTInterpol).setSolverLogics(Logics.ALL)
				.setSolverLogger(UltimateMocks.createUltimateServiceProviderMock(LogLevel.WARN).getLoggingService()
						.getLogger(getClass()));
		mSmtInterpol = SolverBuilder.buildAndInitializeSolver(mServices, solverSettings, "SmtInterpol");
		mMgdSmtInterpol = new ManagedScript(mServices, mSmtInterpol);

		mLogger.info("setUp() finished");
	}

	@Test
	public void tfEx01_Z3() {
		iterationAcceleration(this::getTfEx01LoopBody, "???", this::testAccelerationZ3, mMgdZ3);
	}

	@Test
	public void tfEx01_SmtInterpol() {
		iterationAcceleration(this::getTfEx01LoopBody, "???", this::testAccelerationSmtInterpol, mMgdSmtInterpol);
	}

	@Test
	public void tfEx02_SmtInterpol() {
		iterationAcceleration(this::getTfEx02LoopBody, "???", this::testAccelerationSmtInterpol, mMgdSmtInterpol);
	}

	@Test
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

		final Term pqeZ3 = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdZ3,
				acceleratedZ3.getClosedFormula(), SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
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
		final BoogieNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
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
		final BoogieNonOldVar varX = ProgramVarUtils.constructGlobalProgramVarPair("x", SmtSortUtils.getIntSort(script),
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

	private static void iterationAcceleration(final TestData input, final String expected,
			final TestAcceleration funTest, final ManagedScript managedScript) {
		final UnmodifiableTransFormula loopBody = input.getLoopBody(managedScript);
		funTest.testAcceleration(loopBody, expected);
	}

	@Test
	public void noLoopAcceleration() {
		testAccelerationZ3(TransFormulaBuilder.getTrivialTransFormula(mMgdZ3), "true");
	}

	private void testAccelerationZ3(final UnmodifiableTransFormula input, final String expected) {
		testAcceleration(mMgdZ3, input, expected);
	}

	private void testAccelerationSmtInterpol(final UnmodifiableTransFormula input, final String expected) {
		testAcceleration(mMgdSmtInterpol, input, expected);
	}

	private void testAcceleration(final ManagedScript script, final UnmodifiableTransFormula input,
			final String expected) {
		final UnmodifiableTransFormula accelerated = new FastUPRCore(input, script, mLogger, mServices).getResult();
		mLogger.info("Input           : %s", input);
		mLogger.info("Output          : %s", accelerated);
		mLogger.info("Expected formula: %s", expected);
		Assert.assertEquals(accelerated.getFormula().toStringDirect(), expected);
	}

	@After
	public void executeAfterEachTest() {
		mZ3.exit();
		mSmtInterpol.exit();
		mLogger.info("--");
	}

	@FunctionalInterface
	private interface TestAcceleration {
		public void testAcceleration(final UnmodifiableTransFormula input, final String expected);
	}

	@FunctionalInterface
	private interface TestData {
		public UnmodifiableTransFormula getLoopBody(final ManagedScript script);
	}

}

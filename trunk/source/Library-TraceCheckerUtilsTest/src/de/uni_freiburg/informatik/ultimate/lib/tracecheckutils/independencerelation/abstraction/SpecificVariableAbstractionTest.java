/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class SpecificVariableAbstractionTest {

	private static final long TEST_TIMEOUT_MILLISECONDS = 10000000000000L;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	private static final String PROCEDURE = "SpecificVariableAbstractionTest";

	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private Script mScript;
	private ManagedScript mMgdScript;
	private final DefaultIcfgSymbolTable mSymbolTable = new DefaultIcfgSymbolTable();

	CfgSmtToolkit mToolkit;
	private SpecificVariableAbstraction<BasicInternalAction> mSpVaAbs;
	private Sort mIntSort;

	// variables for SimpleSet example
	private IProgramVar x, y, a, b, sz, r1, r2, s1, s2;

	// variables for ArrayStack example
	private IProgramVar arr, max, top, e1, e2;

	

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		mLogger = mServices.getLoggingService().getLogger(VariableAbstractionTest.class);

		mScript = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mIntSort = SmtSortUtils.getIntSort(mScript);

		setupSimpleSet();
		setupArrayStack();

		mToolkit = new CfgSmtToolkit(null, mMgdScript, mSymbolTable, null, null, null, null, null, null);
		final Set<IProgramVar> mAllVariables = new HashSet<>();
		for (final IProgramNonOldVar nOV : mSymbolTable.getGlobals()) {
			mAllVariables.add(nOV);
		}
		mSpVaAbs = new SpecificVariableAbstraction<>(SpecificVariableAbstractionTest::copyAction, mMgdScript,
				mAllVariables, Collections.emptySet());
	}

	private static BasicInternalAction copyAction(final BasicInternalAction old,
			final UnmodifiableTransFormula newTransformula, final UnmodifiableTransFormula newTransformulaWithBE) {
		assert newTransformulaWithBE == null : "TF with branch encoders should be null";
		return createAction(newTransformula);
	}

	private static BasicInternalAction createAction(final UnmodifiableTransFormula newTransformula) {
		return new BasicInternalAction(PROCEDURE, PROCEDURE, newTransformula);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	public UnmodifiableTransFormula yIsXPlusY() {
		return TransFormulaBuilder.constructAssignment(List.of(y),
				List.of(SmtUtils.sum(mScript, mIntSort, x.getTerm(), y.getTerm())), mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula yIsXTimesTwo() {
		return TransFormulaBuilder.constructAssignment(List.of(y), List
				.of(SmtUtils.mul(mScript, mIntSort, x.getTerm(), SmtUtils.constructIntValue(mScript, BigInteger.TWO))),
				mSymbolTable, mMgdScript);
	}

	public UnmodifiableTransFormula xIsXPlusOne() {
		return TransFormulaBuilder.constructAssignment(List.of(x), List
				.of(SmtUtils.sum(mScript, mIntSort, x.getTerm(), SmtUtils.constructIntValue(mScript, BigInteger.ONE))),
				mSymbolTable, mMgdScript);
	}

	private VarAbsConstraints<BasicInternalAction> makeSimpleVarAbConstaraint(final BasicInternalAction letter,
			final Set<IProgramVar> in, final Set<IProgramVar> out) {
		final Map<BasicInternalAction, Set<IProgramVar>> inConstr = new HashMap<>();
		final Map<BasicInternalAction, Set<IProgramVar>> outConstr = new HashMap<>();
		if (!in.isEmpty()) {
			inConstr.put(letter, in);
		}
		if (!out.isEmpty()) {
			outConstr.put(letter, out);
		}
		return new VarAbsConstraints<>(inConstr, outConstr);
	}

	@Test
	public void sharedInOutVar() {
		runTestAbstraction(yIsXPlusY(), Set.of(y), Set.of(y));
	}

	@Test
	public void rightSideAbstracted() {
		// abstract variable on right side, but not left side
		final Set<IProgramVar> constrInVars = new HashSet<>();
		final Set<IProgramVar> constrOutVars = new HashSet<>();
		constrInVars.add(y);
		runTestAbstraction(yIsXTimesTwo(), constrInVars, constrOutVars);
	}

	@Test
	public void leftSideAbstracton() {
		final Set<IProgramVar> constrVars = new HashSet<>();
		constrVars.add(x);
		runTestAbstraction(yIsXTimesTwo(), constrVars, constrVars);
	}

	@Test
	public void bothSidesDifferentVariablesEmptyConstrVars() {
		final Set<IProgramVar> constrVars = new HashSet<>();
		runTestAbstraction(yIsXTimesTwo(), constrVars, constrVars);
	}

	@Test
	public void withAuxVar() {
		runTestAbstraction(jointHavocXandY(), Set.of(x), Set.of(x));
	}

	public UnmodifiableTransFormula jointHavocXandY() {
		final TermVariable aux = mMgdScript.variable("aux", mIntSort);
		final TermVariable xOut = mMgdScript.variable("x_out", mIntSort);
		final TermVariable yOut = mMgdScript.variable("y_out", mIntSort);

		final Term formula = parseWithVariables("(and (= x_out aux) (= y_out aux))");
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, false);
		tfb.addOutVar(x, xOut);
		tfb.addOutVar(y, yOut);
		tfb.addAuxVar(aux);
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mMgdScript);
	}

	@Test
	public void doNothingFullConstrVars() {
		final Set<IProgramVar> constrVars = new HashSet<>();
		constrVars.add(x);
		constrVars.add(y);
		runTestAbstractionDoesNothing(yIsXTimesTwo(), constrVars);
		runTestAbstractionDoesNothing(xIsXPlusOne(), constrVars);
	}

	@Test
	public void bothSidesSameVariable() {
		final Set<IProgramVar> constrVars = new HashSet<>();
		runTestAbstraction(xIsXPlusOne(), constrVars, constrVars);
	}

	private void runTestAbstraction(final UnmodifiableTransFormula utf, final Set<IProgramVar> inConstr,
			final Set<IProgramVar> outConstr) {
		final BasicInternalAction action = createAction(utf);
		final UnmodifiableTransFormula abstractedTF = mSpVaAbs
				.abstractLetter(action, makeSimpleVarAbConstaraint(action, inConstr, outConstr)).getTransformula();

		for (final IProgramVar iv : abstractedTF.getInVars().keySet()) {
			assert !abstractedTF.getAuxVars().contains(iv.getTermVariable()) : "auxVar in InVar ";
		}

		for (final IProgramVar iv : abstractedTF.getOutVars().keySet()) {
			assert !abstractedTF.getAuxVars().contains(abstractedTF.getOutVars().get(iv)) : "auxVar in OutVar "
					+ iv.getTermVariable().toString();
		}
		LBool working = TransFormulaUtils.checkImplication(utf, abstractedTF, mMgdScript);
		assert working != LBool.SAT : "IS SAT";
		working = TransFormulaUtils.checkImplication(abstractedTF, utf, mMgdScript);
		assert working != LBool.UNSAT : "IS UNSAT";

	}

	private void runTestAbstractionDoesNothing(final UnmodifiableTransFormula utf,
			final Set<IProgramVar> constrainingVars) {
		final BasicInternalAction action = createAction(utf);
		final UnmodifiableTransFormula abstractedTF =
				mSpVaAbs.abstractLetter(action, makeSimpleVarAbConstaraint(action, constrainingVars, constrainingVars))
						.getTransformula();

		for (final IProgramVar iv : abstractedTF.getInVars().keySet()) {
			assert !abstractedTF.getAuxVars().contains(iv.getTermVariable()) : "auxVar in InVar ";
		}

		for (final IProgramVar iv : abstractedTF.getOutVars().keySet()) {
			assert !abstractedTF.getAuxVars().contains(abstractedTF.getOutVars().get(iv)) : "auxVar in OutVar "
					+ iv.getTermVariable().toString();
		}
		final LBool working = TransFormulaUtils.checkImplication(utf, abstractedTF, mMgdScript);
		assert working != LBool.SAT : "IS SAT";

	}

	private void setupSimpleSet() {
		// generic inputs
		x = constructVar("x", "Int");
		y = constructVar("y", "Int");

		// data structure
		a = constructVar("a", "Int");
		b = constructVar("b", "Int");
		sz = constructVar("sz", "Int");

		// generic return values
		r1 = constructVar("r1", "Bool");
		r2 = constructVar("r2", "Bool");
		s1 = constructVar("s1", "Int");
		s2 = constructVar("s2", "Int");

	}

	private void setupArrayStack() {
		arr = ProgramVarUtils.constructGlobalProgramVarPair("arr",
				mScript.sort("Array", mScript.sort("Int"), mScript.sort("Int")), mMgdScript, null);
		mSymbolTable.add(arr);

		max = constructVar("max", "Int");
		top = constructVar("top", "Int");
		e1 = constructVar("e1", "Int");
		e2 = constructVar("e2", "Int");
	}

	private IProgramVar constructVar(final String name, final String sort) {
		final IProgramVar variable =
				ProgramVarUtils.constructGlobalProgramVarPair(name, mScript.sort(sort), mMgdScript, null);
		mSymbolTable.add(variable);
		return variable;
	}
	
	private Term parseWithVariables(final String syntax) {
		final String declarations = mSymbolTable.getGlobals().stream()
				.map(pv -> "(" + pv.getTermVariable().getName() + "_in " + pv.getSort() + ") ("
						+ pv.getTermVariable().getName() + "_out " + pv.getSort() + ") ")
				.collect(Collectors.joining(" ")) + " (aux Int)";
		final String fullSyntax = "(forall (" + declarations + ") " + syntax + ")";
		final QuantifiedFormula quant = (QuantifiedFormula) TermParseUtils.parseTerm(mScript, fullSyntax);
		return new CommuhashNormalForm(mServices, mScript).transform(quant.getSubformula());
	}

}

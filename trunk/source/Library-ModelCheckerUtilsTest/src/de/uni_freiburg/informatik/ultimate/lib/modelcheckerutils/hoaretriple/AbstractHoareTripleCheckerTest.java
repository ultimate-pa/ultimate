/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicCallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public abstract class AbstractHoareTripleCheckerTest {

	private static final String PROCEDURE = AbstractHoareTripleCheckerTest.class.getSimpleName();
	private static final String CALLER = "caller";
	private static final String CALLEE = "callee";

	protected IUltimateServiceProvider mServices;
	protected Script mScript;
	protected ManagedScript mMgdScript;
	protected ILogger mLogger;
	protected PredicateUnifier mPredicateUnifier;
	protected CfgSmtToolkit mCsToolkit;
	protected final DefaultIcfgSymbolTable mSymbolTable = new DefaultIcfgSymbolTable();

	private IProgramConst c, d;
	private IProgramNonOldVar x, y, z;

	protected abstract IHoareTripleChecker getHtc();

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mScript = new HistoryRecordingScript(UltimateMocks.createZ3Script(LogLevel.INFO));
		mLogger = mServices.getLoggingService().getLogger(AbstractHoareTripleCheckerTest.class);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);

		c = constructConst("c", SmtSortUtils.getIntSort(mScript));
		d = constructConst("d", SmtSortUtils.getIntSort(mScript));
		x = constructVar("x", SmtSortUtils.getIntSort(mScript));
		y = constructVar("y", SmtSortUtils.getIntSort(mScript));
		z = constructVar("z", SmtSortUtils.getIntSort(mScript));
		final BasicPredicateFactory predicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);
		mPredicateUnifier = new PredicateUnifier(mLogger, mServices, mMgdScript, predicateFactory, mSymbolTable,
				SimplificationTechnique.SIMPLIFY_DDA);

		final var modifiable = new HashRelation<String, IProgramNonOldVar>();
		modifiable.addPair(PROCEDURE, x);
		modifiable.addPair(CALLER, x);
		modifiable.addPair(CALLEE, x);
		modifiable.addPair(CALLER, z);
		final ModifiableGlobalsTable modGlobTab = new ModifiableGlobalsTable(modifiable);

		final IcfgEdgeFactory icfgEdgeFactory = new IcfgEdgeFactory(new SerialProvider());
		final ConcurrencyInformation ci =
				new ConcurrencyInformation(Collections.emptyMap(), Collections.emptyMap(), Collections.emptySet());
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms = new SmtFunctionsAndAxioms(mMgdScript);
		mCsToolkit = new CfgSmtToolkit(modGlobTab, mMgdScript, mSymbolTable, Collections.emptySet(),
				Collections.emptyMap(), Collections.emptyMap(), icfgEdgeFactory, ci, smtFunctionsAndAxioms);
	}

	private void testInternal(final Validity validity, final Validity expected, final String pre,
			final UnmodifiableTransFormula act, final String post) {
		assert validity == Validity.VALID || validity == Validity.INVALID : "Triple must be either valid or invalid";
		assert validity == expected || expected == Validity.UNKNOWN : "Inconsistent expected validity";

		final IPredicate precond = pred(pre);
		final IPredicate postcond = pred(post);
		final IHoareTripleChecker htc = getHtc();
		final Validity actual =
				htc.checkInternal(precond, new BasicInternalAction(PROCEDURE, PROCEDURE, act), postcond);
		Assert.assertEquals("Unexpected validity for " + validity + " Hoare triple:", expected, actual);
	}

	private void testCall(final Validity validity, final Validity expected, final String pre,
			final UnmodifiableTransFormula act, final String post) {
		assert validity == Validity.VALID || validity == Validity.INVALID : "Triple must be either valid or invalid";
		assert validity == expected || expected == Validity.UNKNOWN : "Inconsistent expected validity";

		final IPredicate precond = pred(pre);
		final IPredicate postcond = pred(post);
		final IHoareTripleChecker htc = getHtc();
		final Validity actual = htc.checkCall(precond, new BasicCallAction(CALLER, CALLEE, act), postcond);
		Assert.assertEquals("Unexpected validity for " + validity + " Hoare triple:", expected, actual);
	}

	/*
	 * ****************************************************************************************************************
	 * Code to parse formulas and terms.
	 * ****************************************************************************************************************
	 */

	private IProgramConst constructConst(final String name, final Sort sort) {
		mScript.declareFun(name, new Sort[0], sort);
		final IProgramConst constant = new ProgramConst(name, (ApplicationTerm) mScript.term(name), false);
		mSymbolTable.add(constant);
		return constant;
	}

	private IProgramNonOldVar constructVar(final String name, final Sort sort) {
		final IProgramNonOldVar variable = ProgramVarUtils.constructGlobalProgramVarPair(name, sort, mMgdScript, null);
		mSymbolTable.add(variable);
		return variable;
	}

	private Term parseWithInOutVariables(final String syntax) {
		final var inVars = suffixVars("_in");
		final var outVars = suffixVars("_out");
		return SmtParserUtils.parseWithVariables(syntax, mServices, mMgdScript,
				DataStructureUtils.union(inVars, outVars));
	}

	private Term parseWithVariables(final String syntax) {
		return SmtParserUtils.parseWithVariables(syntax, mServices, mMgdScript, mSymbolTable);
	}

	private Set<TermVariable> suffixVars(final String suffix) {
		return mSymbolTable.getGlobals().stream().map(
				pv -> mScript.getTheory().createTermVariable(pv.getTermVariable().getName() + suffix, pv.getSort()))
				.collect(Collectors.toSet());
	}

	private IPredicate pred(final String formula) {
		return mPredicateUnifier.getOrConstructPredicate(parseWithVariables(formula));
	}

	private TermVariable outVar(final IProgramVar variable) {
		return mScript.variable(variable.getTermVariable().getName() + "_out", variable.getSort());
	}

	private TermVariable inVar(final IProgramVar variable) {
		return mScript.variable(variable.getTermVariable().getName() + "_in", variable.getSort());
	}

	private UnmodifiableTransFormula assumeTrue() {
		// Build "assume true" statement
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(), true, Set.of(), true, null, true);
		tfb.setFormula(mScript.term("true"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mMgdScript);
	}

	/*
	 * ****************************************************************************************************************
	 * Actual tests.
	 * ****************************************************************************************************************
	 */

	@Test
	public void disjointVarsButConst() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(), false, Set.of(c), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(>= c 0)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.VALID, disjointVarsButConstVerdict(), "true", tf, "(>= c 0)");
	}

	protected Validity disjointVarsButConstVerdict() {
		return Validity.VALID;
	}

	@Test
	public void disjointVarsButConstToFalse() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(), false, Set.of(c), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(>= c 0)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.VALID, disjointVarsButConstToFalseVerdict(), "(< c 0)", tf, "false");
	}

	protected Validity disjointVarsButConstToFalseVerdict() {
		return Validity.VALID;
	}

	@Test
	public void constsButDisjoint() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(), false, Set.of(d), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(>= d 0)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.INVALID, constsButDisjointVerdict(), "true", tf, "(>= c 0)");
	}

	protected Validity constsButDisjointVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void constsButDisjointToFalse() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(), false, Set.of(d), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(>= d 0)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.INVALID, constsButDisjointToFalseVerdict(), "(<= c 0)", tf, "false");
	}

	protected Validity constsButDisjointToFalseVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void constsPreservedInternal() {
		final var tf = assumeTrue();
		testInternal(Validity.VALID, constsPreservedInternalVerdict(), "(<= c 0)", tf, "(<= c 0)");
	}

	protected Validity constsPreservedInternalVerdict() {
		return Validity.VALID;
	}

	@Test
	public void constsWeakenedInternal() {
		final var tf = assumeTrue();
		testInternal(Validity.VALID, constsWeakenedInternalVerdict(), "(= c 0)", tf, "(<= c 0)");
	}

	protected Validity constsWeakenedInternalVerdict() {
		return Validity.VALID;
	}

	@Test
	public void preImplPostNoAssign() {
		final var tfb =
				new TransFormulaBuilder(Map.of(x, inVar(x)), Map.of(x, inVar(x)), false, Set.of(), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(= x_in 3)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.VALID, preImplPostNoAssignVerdict(), "(>= x 2)", tf, "(>= x 0)");
	}

	protected Validity preImplPostNoAssignVerdict() {
		return Validity.VALID;
	}

	@Test
	public void preImplPostButAssigns() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(x, outVar(x)), false, Set.of(), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(= x_out 3)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.INVALID, preImplPostButAssignsVerdict(), "(= x 0)", tf, "(<= x 0)");
	}

	protected Validity preImplPostButAssignsVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void preImplPostAssignPreNotPost() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(x, outVar(x)), false, Set.of(), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(= x_out 3)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.VALID, preImplPostAssignPreNotPostVerdict(), "(and (= x 0) (= x y))", tf, "(<= y 0)");
	}

	protected Validity preImplPostAssignPreNotPostVerdict() {
		return Validity.VALID;
	}

	@Test
	public void preImplPostAssignPostNotPre() {
		final var tfb = new TransFormulaBuilder(Map.of(), Map.of(x, outVar(x)), false, Set.of(), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(= x_out 3)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.VALID, preImplPostAssignPostNotPreVerdict(), "(= y 0)", tf, "(or (<= y 0) (= x 0))");
	}

	protected Validity preImplPostAssignPostNotPreVerdict() {
		return Validity.VALID;
	}

	@Test
	public void noAssignAndNoImpl() {
		final var tfb =
				new TransFormulaBuilder(Map.of(x, inVar(x)), Map.of(x, inVar(x)), true, Set.of(), true, null, true);
		tfb.setFormula(parseWithInOutVariables("(= x_in 11)"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		final var tf = tfb.finishConstruction(mMgdScript);
		testInternal(Validity.INVALID, noAssignAndNoImplVerdict(), "(>= x 2)", tf, "(<= x 10)");
	}

	protected Validity noAssignAndNoImplVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void nonModifiableOldVar() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y,
				PROCEDURE) : "Test requires y to be non-modifiable";

		final var tf = assumeTrue();

		// This Hoare triple is valid because y is not modifiable in the procedure.
		testInternal(Validity.VALID, nonModifiableOldVarVerdict(), "(= y 42)", tf, "(= |old(y)| 42)");
	}

	protected Validity nonModifiableOldVarVerdict() {
		return Validity.VALID;
	}

	@Test
	public void nonModifiedOldVar() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, PROCEDURE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();

		// This Hoare triple is invalid, because x is modifiable in the procedure.
		testInternal(Validity.INVALID, nonModifiedOldVarVerdict(), "(= x 42)", tf, "(= |old(x)| 42)");
	}

	protected Validity nonModifiedOldVarVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void differentNonModifiableOldVars() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y,
				PROCEDURE) : "Test requires y to be non-modifiable";
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(z,
				PROCEDURE) : "Test requires z to be non-modifiable";

		final var tf = assumeTrue();
		testInternal(Validity.INVALID, differentNonModifiableOldVarsVerdict(), "(= y 42)", tf, "(= |old(z)| 42)");
	}

	protected Validity differentNonModifiableOldVarsVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void callNonModifiableOldNonOld() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLEE) : "Test requires y to be non-modifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, callNonModifiableOldNonOldVerdict(), "(= y 0)", tf, "(= |old(y)| 0)");
	}

	protected Validity callNonModifiableOldNonOldVerdict() {
		return Validity.VALID;
	}

	@Test
	public void callModifiableOldNonOld() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, CALLEE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, callModifiableOldNonOldVerdict(), "(= x 0)", tf, "(= |old(x)| 0)");
	}

	protected Validity callModifiableOldNonOldVerdict() {
		return Validity.VALID;
	}

	@Test
	public void callNonModifiableOld() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLER) : "Test requires y to be non-modifiable";
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLEE) : "Test requires y to be non-modifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, callNonModifiableOldVerdict(), "(= |old(y)| 0)", tf, "(= |old(y)| 0)");
	}

	protected Validity callNonModifiableOldVerdict() {
		return Validity.VALID;
	}

	@Test
	public void callCallerModifiableOld() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(z, CALLER) : "Test requires z to be modifiable";
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLEE) : "Test requires z to be non-modifiable";

		final var tf = assumeTrue();
		testCall(Validity.INVALID, callCallerModifiableOldVerdict(), "(= |old(z)| 0)", tf, "(= |old(z)| 0)");
	}

	protected Validity callCallerModifiableOldVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void callModifiableOld() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, CALLER) : "Test requires x to be modifiable";
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, CALLEE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testCall(Validity.INVALID, callModifiableOldVerdict(), "(= |old(x)| 0)", tf, "(= |old(x)| 0)");
	}

	protected Validity callModifiableOldVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void constsPreservedCall() {
		final var tf = assumeTrue();
		testCall(Validity.VALID, constsPreservedCallVerdict(), "(<= c 0)", tf, "(<= c 0)");
	}

	protected Validity constsPreservedCallVerdict() {
		return Validity.VALID;
	}

	@Test
	public void constsWeakenedCall() {
		final var tf = assumeTrue();
		testCall(Validity.VALID, constsWeakenedCallVerdict(), "(= c 0)", tf, "(<= c 0)");
	}

	protected Validity constsWeakenedCallVerdict() {
		return Validity.VALID;
	}

	@Test
	public void pseudoTautologicalPostInternal() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y,
				PROCEDURE) : "Test requires y to be unmodifiable";

		final var tf = assumeTrue();
		testInternal(Validity.VALID, pseudoTautologicalPostInternalVerdict(), "true", tf, "(= y |old(y)|)");
	}

	protected Validity pseudoTautologicalPostInternalVerdict() {
		return Validity.VALID;
	}

	@Test
	public void nonPseudoTautologicalPostInternal() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, PROCEDURE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testInternal(Validity.INVALID, nonPseudoTautologicalPostInternalVerdict(), "true", tf, "(= x |old(x)|)");
	}

	protected Validity nonPseudoTautologicalPostInternalVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void pseudoTautologicalPostCall() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLEE) : "Test requires y to be unmodifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, pseudoTautologicalPostCallVerdict(), "true", tf, "(= y |old(y)|)");
	}

	protected Validity pseudoTautologicalPostCallVerdict() {
		return Validity.VALID;
	}

	@Test
	public void nonPseudoTautologicalPostCall() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, CALLEE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, nonPseudoTautologicalPostCallVerdict(), "true", tf, "(= x |old(x)|)");
	}

	protected Validity nonPseudoTautologicalPostCallVerdict() {
		return Validity.VALID;
	}

	@Test
	public void pseudoInconsistentPreInternal() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y,
				PROCEDURE) : "Test requires y to be unmodifiable";

		final var tf = assumeTrue();
		testInternal(Validity.VALID, pseudoInconsistentPreInternalVerdict(), "(distinct y |old(y)|)", tf, "false");
	}

	protected Validity pseudoInconsistentPreInternalVerdict() {
		return Validity.VALID;
	}

	@Test
	public void nonPseudoInconsistentPreInternal() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, PROCEDURE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testInternal(Validity.INVALID, nonPseudoInconsistentPreInternalVerdict(), "(distinct x |old(x)|)", tf, "false");
	}

	protected Validity nonPseudoInconsistentPreInternalVerdict() {
		return Validity.INVALID;
	}

	@Test
	public void pseudoInconsistentPreCall() {
		assert !mCsToolkit.getModifiableGlobalsTable().isModifiable(y, CALLER) : "Test requires y to be unmodifiable";

		final var tf = assumeTrue();
		testCall(Validity.VALID, pseudoInconsistentPreCallVerdict(), "(distinct y |old(y)|)", tf, "false");
	}

	protected Validity pseudoInconsistentPreCallVerdict() {
		return Validity.VALID;
	}

	@Test
	public void nonPseudoInconsistentPreCall() {
		assert mCsToolkit.getModifiableGlobalsTable().isModifiable(x, CALLEE) : "Test requires x to be modifiable";

		final var tf = assumeTrue();
		testCall(Validity.INVALID, nonPseudoInconsistentPreCallVerdict(), "(distinct x |old(x)|)", tf, "false");
	}

	protected Validity nonPseudoInconsistentPreCallVerdict() {
		return Validity.INVALID;
	}
}

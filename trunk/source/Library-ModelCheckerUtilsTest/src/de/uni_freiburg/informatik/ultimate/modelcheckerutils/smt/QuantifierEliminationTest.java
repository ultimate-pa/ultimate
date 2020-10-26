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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;
import java.math.BigInteger;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.DeclarableFunctionSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.FunDecl.SortConstructor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

//@formatter:off
/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 10_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	public static Sort constructIntIntArray(final Script script) {
		return SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script), SmtSortUtils.getIntSort(script));
	}

	public static Sort constructIntIntIntArray(final Script script) {
		return SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script),
				SmtSortUtils.getArraySort(script, SmtSortUtils.getIntSort(script), SmtSortUtils.getIntSort(script)));
	}

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationTest.class.getSimpleName());
	}

	@AfterClass
	public static void afterAllTests() {
		if (WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY) {
			try {
				mCsvWriter.writeCsv();
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Before
	public void setUp() throws IOException {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		mLogger = mServices.getLoggingService().getLogger("lol");

		final Script solverInstance = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(solverInstance, "QuantifierEliminationTest.smt2", true);
		} else {
			mScript = solverInstance;
		}

		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
		mCsvWriter.reportTestFinished();
	}

	public static Sort getBv32(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, BigInteger.valueOf(32));
	}

	@Test
	public void prenexQuantifiedCapture() {
		final Term seventeen = mScript.numeral(BigInteger.valueOf(17));
		final Term fourtytwo = mScript.numeral(BigInteger.valueOf(42));
		final TermVariable x = mScript.variable("x", SmtSortUtils.getIntSort(mMgdScript));
		final Term eq1 = mScript.term("=", x, seventeen);
		final Term eq2 = mScript.term("=", x, fourtytwo);
		final Term qeq1 = mScript.quantifier(0, new TermVariable[] { x }, eq1);
		final Term qeq2 = mScript.quantifier(0, new TermVariable[] { x }, eq2);
		final Term term = mScript.term("and", qeq1, qeq2);
		final Term result = new PrenexNormalForm(mMgdScript).transform(term);
		mScript.assertTerm(result);
		final LBool checkSatRes = mScript.checkSat();
		Assert.assertTrue(checkSatRes == LBool.SAT);
	}

	@Test
	public void varStilThereBug() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::constructIntIntArray, "v_#valid_207", "#valid", "old(#valid)"),
		};
		final String formulaAsString = "(forall ((|v_old(#valid)_88| (Array Int Int)) (|v_old(#valid)_88| (Array Int Int)) (|v_old(#valid)_88| (Array Int Int))) (or (not (and (forall ((v_probe3_6_~p~9.base_40 Int) (v_probe3_6_~p~9.base_40 Int)) (or (= |v_old(#valid)_88| (store |v_#valid_207| v_probe3_6_~p~9.base_40 0)) (= v_probe3_6_~p~9.base_40 0) (not (= (select |v_#valid_207| v_probe3_6_~p~9.base_40) 0)))) (= |old(#valid)| |v_#valid_207|))) (= |#valid| |v_old(#valid)_88|)))";
		final String expextedResultAsString = null;
		runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void otherArrayBug() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::constructIntIntArray, "b"),
			new FunDecl(SmtSortUtils::getIntSort, "i"),
		};
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= (select a i) (select b 0)) (= (select a 0) (select b 1))))";
		final String expextedResultAsString = "(or (= (select b 0) (select b 1)) (not (= 0 i)))";
		runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest1() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool)) (and (<= 0 A) (or (and (not B) (not C)) (and C B)) (or (and (not D) (not E)) (and E D)) (or (and F G) (and (not G) (not F)))))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getRealSort, "T1", "T2"),
		};
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Int)) (or (<= 50.0 T2) (and (not F) (or (and (< T1 50.0) (or (and (not (< B 5)) (not (= H E))) (and (not (= H E)) (or (not F) (not G) (not (= A E)) (not C))))) (and (= H E) (or (not F) (= H E) (not (< B 5)) (not G) (not (= A E)) (not C))) (and (< T1 50.0) (= A E) (< B 5) C (not (= H E)) F G)) (not (= E D))) (< T2 50.0)))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest3() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getBoolSort, "HI", "HJ", "HK", "HL", "HM", "HO", "HP", "HQ", "HS", "HT", "HU", "HW", "HX", "HY", "HZ", "IA", "IB", "IC", "ID", "IE", "IF", "IG", "AA", "II", "IJ", "AC", "IK", "IL", "AE", "AF", "IN", "AG", "AI", "AK", "AL", "AM", "AN", "AO", "AP", "AQ", "AR", "AS", "AU", "AW", "AX", "AY", "AZ", "BA", "BC", "BD", "C", "BE", "D", "BF", "BG", "E", "F", "BI", "G", "H", "I", "BK", "J", "BL", "K", "BM", "L", "BO", "BP", "N", "O", "BQ", "BR", "P", "BS", "Q", "R", "BT", "BU", "S", "T", "U", "V", "W", "BY", "BZ", "X", "CB", "CC", "CD", "CE", "CI", "CJ", "CK", "CL", "CN", "CO", "CQ", "CS", "CT", "CW", "CX", "CY", "CZ", "DA", "DB", "DD", "DH", "DI", "DJ", "DK", "DO", "DP", "DQ", "DR", "DS", "DU", "DX", "DZ", "EA", "EB", "ED", "EE", "EF", "EG", "EH", "EI", "EJ", "EK", "EM", "EN", "EO", "EP", "ES", "EU", "EV", "EW", "EX", "EZ", "FA", "FB", "FC", "FE", "FF", "FG", "FH", "FI", "FK", "FL", "FM", "FN", "FP", "FR", "FS", "FT", "FW", "FX", "GA", "GB", "GE", "GF", "GH", "GI", "GJ", "GK", "GO", "GP", "GR", "GS", "GT", "GU", "GV", "GW", "GX", "GY", "GZ", "HA", "HB", "HC", "HE", "HF", "HG"),
				new FunDecl(SmtSortUtils::getRealSort, "AB", "DE", "CF", "IM", "CH", "AH", "CM", "FQ", "EQ", "HV", "DV", "T1", "GD", "FD"),
				new FunDecl(SmtSortUtils::getIntSort, "HH", "DF", "DG", "HN", "DL", "DM", "DN", "HR", "DT", "DW", "DY", "EC", "IH", "AD", "EL", "AJ", "ER", "ET", "AT", "EY", "AV", "BB", "A", "B", "FJ", "BH", "BJ", "FO", "BN", "M", "FU", "FV", "FY", "BV", "FZ", "BW", "BX", "Y", "Z", "GC", "CA", "GG", "CG", "GL", "GM", "GN", "GQ", "CP", "CR", "CU", "CV", "HD", "DC"),
		};
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (AA Bool) (AB Real) (AC Bool) (AD Int) (AE Bool) (AF Bool) (AG Bool) (AH Real) (AI Bool) (AJ Int) (AK Bool) (AL Bool) (AM Bool) (AN Bool) (AO Bool) (AP Bool) (AQ Bool) (AR Bool) (AS Bool) (AT Int) (AU Bool) (AV Int) (AW Bool) (AX Bool) (AY Bool) (AZ Bool) (BA Bool) (BB Int) (BC Bool) (BD Bool) (BE Bool) (BF Bool) (BG Bool) (BH Int) (BI Bool) (BJ Int) (BK Bool) (BL Bool) (BM Bool) (BN Int) (BO Bool) (BP Bool) (BQ Bool) (BR Bool) (BS Bool) (BT Bool) (BU Bool) (BV Int) (BW Int) (BX Int) (BY Bool) (BZ Bool) (CA Int) (CB Bool) (CC Bool) (CD Bool) (CE Bool) (CF Real) (CG Int) (CH Real) (CI Bool) (CJ Bool) (CK Bool) (CL Bool) (CM Real) (CN Bool) (CO Bool) (CP Int) (CQ Bool) (CR Int) (CS Bool) (CT Bool) (CU Int) (CV Int) (CW Bool) (CX Bool) (CY Bool) (CZ Bool) (DA Bool) (DB Bool) (DC Int) (DD Bool) (DE Real) (DF Int) (DG Int) (DH Bool) (DI Bool) (DJ Bool) (DK Bool) (DL Int) (DM Int) (DN Int) (DO Bool) (DP Bool) (DQ Bool) (DR Bool) (DS Bool) (DT Int) (DU Bool) (DV Real) (DW Int) (DX Bool) (DY Int) (DZ Bool) (EA Bool) (EB Bool) (EC Int) (ED Bool) (EE Bool) (EF Bool) (EG Bool) (EH Bool) (EI Bool) (EJ Bool) (EK Bool) (EL Int) (EM Bool) (EN Bool) (EO Bool) (EP Bool) (EQ Real) (ER Int) (ES Bool) (ET Int) (EU Bool) (EV Bool) (EW Bool) (EX Bool) (EY Int) (EZ Bool) (FA Bool) (FB Bool) (FC Bool) (FD Real) (FE Bool) (FF Bool) (FG Bool) (FH Bool) (FI Bool) (FJ Int) (FK Bool) (FL Bool) (FM Bool) (FN Bool) (FO Int) (FP Bool) (FQ Real) (FR Bool) (FS Bool) (FT Bool) (FU Int) (FV Int) (FW Bool) (FX Bool) (FY Int) (FZ Int) (GA Bool) (GB Bool) (GC Int) (GD Real) (GE Bool) (GF Bool) (GG Int) (GH Bool) (GI Bool) (GJ Bool) (GK Bool) (GL Int) (GM Int) (GN Int) (GO Bool) (GP Bool) (GQ Int) (GR Bool) (GS Bool) (GT Bool) (GU Bool) (GV Bool) (GW Bool) (GX Bool) (GY Bool) (GZ Bool) (HA Bool) (HB Bool) (HC Bool) (HD Int) (HE Bool) (HF Bool) (HG Bool) (HH Int) (HI Bool) (HJ Bool) (HK Bool) (HL Bool) (HM Bool) (HN Int) (HO Bool) (HP Bool) (HQ Bool) (HR Int) (HS Bool) (HT Bool) (HU Bool) (HV Real) (HW Bool) (HX Bool) (HY Bool) (HZ Bool) (IA Bool) (IB Bool) (IC Bool) (ID Bool) (IE Bool) (IF Bool) (IG Bool) (IH Int) (II Bool) (IJ Bool) (IK Bool) (IL Bool) (IM Real) (IN Bool)) (and (<= 0 DG) (= AZ HX) (= FV BJ) (or (not BT) DK) (<= 0 B) (= HA FE) (or FW (not AM)) (= IJ AX) (<= 0 DW) (<= AV 7) (= EF BA) (= AC CE) (= FN HI) (or (not GI) GZ) (or (not BQ) DB) (<= CV 255) (or (not FS) IL) (= AI HP) (or (not (< 0 DN)) (= DY 1)) (= AB (/ 3.0 2.0)) (= 2 Z) (= AT 19) (= HB V) (= N HE) (= AP EB) (or AE (not EZ)) (= GM 3) (<= 0 ER) (= DH AG) (or AK (not BD)) (= HJ P) (<= EY 3) (<= DT 3) (or (not EU) IN) (<= 0 EC) (= GN DC) (= X GY) (<= 0 DC) (<= B 15) (= GD 800.0) (= CS EX) (= HF EP) (<= 0 BW) (or HM (not GA)) (= BK DS) (or (not CQ) CI) (or (= 15 GQ) (= 14 GQ) (and (<= 0 GQ) (<= GQ 10))) (= FO HR) (<= IH 2) (or (= 14 ET) (and (<= ET 10) (<= 0 ET)) (= 15 ET)) (<= BX 3) (or (not ES) HY) (or (and GX IB FG S U G DX GP DJ AU BZ BO EV FR) (not (= CR FY))) (= GF DU) (= BM DR) (= BY O) (<= 0 EY) (= IG BE) (= CY EI) (or BL (not FC)) (= FD 4000.0) (or (not GT) J) (= BN 19) (<= 0 CG) (or (not CL) AO) (<= DW 6) (or DD (not GB)) (<= 0 BB) (= 2 GC) (= 50.0 FQ) (= EJ GS) (<= BB 2) (= EG FX) (= GR BF) (or (not AN) IK) (= HT AR) (= Q CK) (<= DC 255) (or (not (= 0 DN)) (= DY 0)) (or I (not E)) (= HO AS) (<= A 9) (<= 0 BV) (<= DM 9) (or (and (not HQ) (not GP)) (and GP (not HQ))) (or (= AD 126) (= AD 127) (and (<= AD 100) (<= 0 AD))) (= FM EH) (= ED EW) (<= 0 IH) (<= 0 HH) (<= 0 DT) (= AL BU) (= IM (/ 3.0 2.0)) (or HS (not FF)) (= R CJ) (<= 0 FZ) (= K BR) (or IC (not HG)) (<= 0 M) (or CD (not EE)) (<= FU 255) (= AY ID) (<= BV 7) (= AW CX) (= FA CB) (<= FZ 658) (= Y HN) (<= 0 AJ) (= DV (/ 3.0 2.0)) (<= HH 1023) (<= 0 FU) (or (not EA) II) (or (= 15 DL) (and (<= 0 DL) (<= DL 10)) (= 14 DL)) (<= ER 9) (= CW AQ) (= E GW) (<= CU 15) (= HL FP) (= CM 500.0) (= HC W) (= 2 HR) (= GK C) (<= AJ 3) (= 2 BH) (<= EL 3) (= CN L) (<= DG 7) (<= BW 63) (= FK GH) (<= EC 63) (<= 0 CV) (= 50.0 AH) (<= CP 9) (or DO (not FL)) (= 4000.0 EQ) (= EO GO) (= 20.0 CF) (= HZ FT) (<= 0 BX) (= BP F) (or (and GP HQ) (and (< T1 50.0) (not GP) HQ) (and (<= 50.0 T1) (not GP))) (= FB CC) (= DP BI) (= DZ BC) (<= 0 GG) (<= GG 255) (= DI CT) (or T (not AA)) (= DE 50.0) (or (not CZ) IE) (or BS (not D)) (= 800.0 HV) (= HW FH) (or AF (not GJ)) (or HK (not (= CR FY))) (<= 0 AV) (= CA FJ) (= EM GV) (<= 0 DM) (<= M 1023) (<= 0 EL) (<= 0 HD) (<= CG 2) (<= 0 A) (= CH 20.0) (or (not EN) (= CR FY)) (<= DF 3) (<= 0 CU) (= FI DQ) (= IF BG) (or (not GU) IA) (or DA (not EK)) (<= HD 3) (= HU GE) (<= 0 DF) (= 1 GL) (<= 0 CP) (or CO (not H))))";
		final String expextedResultAsString = "(<= 50.0 T1)";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest4() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getRealSort, "T1"),
		};
		final String formulaAsString = "(exists ((A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (AA Bool) (AB Int) (AC Int) (AD Bool) (AE Bool) (AF Bool) (AG Bool)) (or (< T1 50.0) (and (not E) (or (and (not S) (not AE) W) (and (not S) B (not AE)) (and (not S) (not AE) AF) (and (not S) (not AE) J) (and (not S) (not AE) Z) (and (not S) (not AE) F) (and (not S) (not AE) C) (and (not S) (not AE) AG) (and (< T1 50.0) (or (and (not U) (or (and (not J) (or (and (or (and (not O) (or (and (or (and (or (and (not AF) (or (and (not B) (or (and (or (and (not C) (or (and (not Y) (or (and (not F) (or (and (or (and (or (and (not S) (not AA)) (and (not S) AE)) (not G)) (and (not S) AE)) (not Z)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not W)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not M)) (and (not S) AE)) (not AG)) (and (not S) AE))) (and (not S) AE)) (not AD)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) (not AE) AA) (and (not S) (not AE) M) (and (not S) (not AE) U) (and (or (and (not U) (or (and (or (and (not AD) (or (and (not O) (or (and (not AG) (or AE (and (not M) (or (and (not AF) (or (and (not B) (or (and (not W) (or (and (or (and (or (and (not F) (or (and (or (and (or (not AA) AE) (not G)) AE) (not Z)) AE)) AE) (not Y)) AE) (not C)) AE)) AE)) AE)) AE)))) AE)) AE)) AE) (not J)) AE)) AE) (<= 50.0 T1)) (and (not S) (not AE) G) (and (not S) (not AE) AD) (and (not S) (not AE) O) (and (not S) (not AE) Y)) (or (and Q R A T V D X H I K L AE N P) (not (= AC AB))) (not (= AC AB)) (or (not R) (not P) (not AE) (not T) (not D) (not X) (not Q) (not I) (not V) (not L) (not H) (not A) (not K) (not N))) (<= 50.0 T1)))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getRealSort, "T1"),
		};
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Int) (AA Int) (AB Bool) (AC Real) (AD Bool) (AE Int) (AF Bool) (AG Bool) (AH Bool) (AI Real) (AJ Bool) (AK Int) (AL Bool) (AM Bool) (AN Bool) (AO Bool) (AP Bool) (AQ Bool) (AR Bool) (AS Bool) (AT Bool) (AU Bool) (AV Int) (AW Bool) (AX Int) (AY Bool) (AZ Bool) (BA Bool) (BB Bool) (BC Bool) (BD Bool) (BE Int) (BF Bool) (BG Bool) (BH Bool) (BI Bool) (BJ Bool) (BK Bool) (BL Int) (BM Bool) (BN Int) (BO Bool) (BP Bool) (BQ Bool) (BR Bool) (BS Int) (BT Bool) (BU Bool) (BV Bool) (BW Bool) (BX Bool) (BY Bool) (BZ Bool) (CA Bool) (CB Int) (CC Int) (CD Int) (CE Bool) (CF Bool) (CG Int) (CH Bool) (CI Bool) (CJ Bool) (CK Bool) (CL Real) (CM Int) (CN Real) (CO Bool) (CP Bool) (CQ Bool) (CR Bool) (CS Bool) (CT Real) (CU Bool) (CV Bool) (CW Int) (CX Bool) (CY Int) (CZ Bool) (DA Bool) (DB Int) (DC Int) (DD Bool) (DE Bool) (DF Bool) (DG Bool) (DH Bool) (DI Bool) (DJ Bool) (DK Int) (DL Bool) (DM Real) (DN Int) (DO Int) (DP Bool) (DQ Bool) (DR Bool) (DS Bool) (DT Int) (DU Int) (DV Int) (DW Bool) (DX Bool) (DY Bool) (DZ Bool) (EA Bool) (EB Int) (EC Bool) (ED Real) (EE Int) (EF Bool) (EG Bool) (EH Int) (EI Bool) (EJ Bool) (EK Bool) (EL Int) (EM Bool) (EN Bool) (EO Bool) (EP Bool) (EQ Bool) (ER Bool) (ES Bool) (ET Bool) (EU Int) (EV Bool) (EW Bool) (EX Bool) (EY Bool) (EZ Bool) (FA Real) (FB Int) (FC Bool) (FD Int) (FE Bool) (FF Bool) (FG Bool) (FH Bool) (FI Int) (FJ Bool) (FK Bool) (FL Bool) (FM Bool) (FN Bool) (FO Real) (FP Bool) (FQ Bool) (FR Bool) (FS Bool) (FT Bool) (FU Int) (FV Bool) (FW Bool) (FX Bool) (FY Bool) (FZ Int) (GA Bool) (GB Real) (GC Bool) (GD Bool) (GE Bool) (GF Bool) (GG Bool) (GH Int) (GI Int) (GJ Bool) (GK Bool) (GL Int) (GM Int) (GN Bool) (GO Bool) (GP Int) (GQ Real) (GR Bool) (GS Bool) (GT Int) (GU Bool) (GV Bool) (GW Bool) (GX Bool) (GY Int) (GZ Int) (HA Int) (HB Bool) (HC Int) (HD Bool) (HE Bool) (HF Bool) (HG Bool) (HH Bool) (HI Bool) (HJ Bool) (HK Bool) (HL Bool) (HM Bool) (HN Bool) (HO Bool) (HP Bool) (HQ Bool) (HR Int) (HS Bool) (HT Bool) (HU Bool) (HV Int) (HW Bool) (HX Bool) (HY Bool) (HZ Bool) (IA Bool) (IB Bool) (IC Int) (ID Bool) (IE Bool) (IF Int) (IG Bool) (IH Bool) (II Bool) (IJ Real) (IK Bool) (IL Bool) (IM Bool) (IN Bool) (IO Bool) (IP Bool) (IQ Bool) (IR Bool) (IS Bool) (IT Bool) (IU Bool) (IV Int) (IW Bool) (IX Bool) (IY Bool) (IZ Bool) (JA Bool) (JB Real) (JC Bool)) (and (<= 0 DO) (= BC IL) (= GI BN) (or (not BY) DR) (<= 0 B) (= HO FP) (or GJ (not AN)) (= IX AZ) (<= 0 EE) (<= AX 7) (= EO BD) (= AD CK) (= FY HW) (or (not GV) HN) (or (not BV) DJ) (<= DC 255) (or (not GD) IZ) (= AJ IE) (or (not (< 0 DV)) (= EH 1)) (= AC (/ 3.0 2.0)) (= 2 AA) (= AV 19) (= HP W) (= O HS) (= AQ EK) (or AF (not FJ)) (= GZ 3) (<= 0 FB) (= DP AH) (or AL (not BG)) (= HX Q) (<= FI 3) (<= EB 3) (or (not FE) JC) (<= 0 EL) (= HA DK) (= Y HM) (<= 0 DK) (<= B 15) (= GQ 800.0) (= CZ FH) (= HT EZ) (<= 0 CC) (or IB (not GN)) (= BO EA) (or (not CX) CO) (or (= 15 HC) (= 14 HC) (and (<= 0 HC) (<= HC 10))) (= FZ IF) (<= IV 2) (or (= 14 FD) (and (<= FD 10) (<= 0 FD)) (= 15 FD)) (<= CD 3) (or (not FC) IM) (or (and HL IP FR T V G EF HD DS AW CF BT FF GC) (not (= CY GL))) (= GS EC) (= BR DZ) (= CE P) (<= 0 FI) (= IU BH) (= DG ER) (or BP (not FN)) (or (= CY GL) (and HL IP FR T V G EF HD DS AW CF BT FF (not (= CY GL)) GC) (and (not (= CY GL)) (or (not IP) (not GC) (not BT) (not T) (not G) (not EF) (not HL) (not DS) (not V) (not CF) (not HD) (not FR) (not AW) (not FF)))) (= FO 4000.0) (or (not HG) K) (= BS 19) (<= 0 CM) (or (not CS) AP) (<= EE 6) (or DL (not GO)) (<= 0 BE) (= 2 GP) (= 50.0 GB) (= ES HF) (<= BE 2) (= EP GK) (= HE BI) (or (not AO) IY) (= IH AT) (= R CR) (<= DK 255) (or (not (= 0 DV)) (= EH 0)) (or I (not E)) (= ID AU) (<= A 9) (<= 0 CB) (<= DU 9) (or (= AE 126) (= AE 127) (and (<= AE 100) (<= 0 AE))) (= FX EQ) (= EM FG) (<= 0 IV) (<= 0 HV) (<= 0 EB) (= AM CA) (= JB (/ 3.0 2.0)) (or IG (not FQ)) (= S CP) (<= 0 GM) (= L BW) (or IQ (not HU)) (<= 0 N) (or CJ (not EN)) (<= GH 255) (= BB IR) (<= CB 7) (= AY DE) (= FL CH) (<= GM 658) (= Z IC) (<= 0 AK) (= ED (/ 3.0 2.0)) (<= HV 1023) (<= 0 GH) (or (not EJ) IW) (or (= 15 DT) (and (<= 0 DT) (<= DT 10)) (= 14 DT)) (<= FB 9) (= DD AR) (= E HK) (<= DB 15) (= IA GA) (= CT 500.0) (= HQ X) (= 2 IF) (= GX C) (<= AK 3) (= 2 BL) (<= EU 3) (= CU M) (<= DO 7) (<= CC 63) (= FV GU) (<= EL 63) (<= 0 DC) (= 50.0 AI) (<= CW 9) (or DW (not FW)) (= 4000.0 FA) (= EY HB) (= 20.0 CL) (= IN GE) (<= 0 CD) (= BU F) (= FM CI) (= DX BM) (= EI BF) (<= 0 GT) (<= GT 255) (= DQ DA) (or U (not AB)) (= DM 50.0) (or (not DH) IS) (or BX (not D)) (= 800.0 IJ) (= IK FS) (or AG (not GW)) (or HY (not (= CY GL))) (<= 0 AX) (= CG FU) (= EV HJ) (<= 0 DU) (<= N 1023) (<= 0 EU) (<= 0 HR) (<= CM 2) (<= 0 A) (= CN 20.0) (or (not EX) (= CY GL)) (<= DN 3) (<= 0 DB) (= FT DY) (= IT BK) (or (not HH) IO) (or DI (not ET)) (or (and (not GF) (not BT) FK) (and (not GF) EW (not BT)) (and (not GF) (not BT) JA) (and (not GF) (not BT) J) (and (not GF) (not BT) CQ) (and (not GF) (not BT) BZ) (and (not GF) (not BT) DF) (and (not GF) (not BT) HZ) (and (< T1 50.0) (or (and (not GG) (or (and (not J) (or (and (or (and (not BA) (or (and (or (and (or (and (not JA) (or (and (not EW) (or (and (or (and (not DF) (or (and (not EG) (or (and (not BZ) (or (and (or (and (or (and (not GF) (not BJ)) (and (not GF) BT)) (not AS)) (and (not GF) BT)) (not CQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not FK)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not HI)) (and (not GF) BT)) (not HZ)) (and (not GF) BT))) (and (not GF) BT)) (not BQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) (not BT) BJ) (and (not GF) (not BT) HI) (and (not GF) (not BT) GG) (and (or (and (not GG) (or (and (or (and (not BQ) (or (and (not BA) (or (and (not HZ) (or BT (and (not HI) (or (and (not JA) (or (and (not EW) (or (and (not FK) (or (and (or (and (or (and (not BZ) (or (and (or (and (or (not BJ) BT) (not AS)) BT) (not CQ)) BT)) BT) (not EG)) BT) (not DF)) BT)) BT)) BT)) BT)))) BT)) BT)) BT) (not J)) BT)) BT) (<= 50.0 T1)) (and (not GF) (not BT) AS) (and (not GF) (not BT) BQ) (and (not GF) (not BT) BA) (and (not GF) (not BT) EG)) (<= HR 3) (= II GR) (<= 0 DN) (= 1 GY) (<= 0 CW) (or CV (not H))))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Example for "ApplicationTerm cannot be cast to de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula"
	 */
	@Test
	public void plrTest6() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::constructIntIntIntArray, "B", "F", "oldB"),
				new FunDecl(QuantifierEliminationTest::constructIntIntArray, "A", "C", "D", "E", "oldC", "oldA"),
		};
		final String formulaAsString = "(forall ((v_idx_7 Int) (v_idx_8 Int) (v_idx_9 Int) (v_idx_12 Int) (v_idx_3 Int) (v_idx_10 Int) (v_idx_4 Int) (v_idx_11 Int) (v_idx_5 Int) (v_idx_6 Int) (v_idx_1 Int) (v_idx_2 Int)) (exists ((v_v_9_1 Int) (v_v_10_1 (Array Int Int)) (v_v_11_1 Int) (v_v_8_1 (Array Int Int)) (v_v_0_1 Int) (v_v_1_1 Int) (v_v_2_1 Int) (v_v_3_1 (Array Int Int)) (v_v_4_1 Int) (v_v_5_1 Int) (v_v_6_1 Int) (v_v_7_1 Int)) (and (= v_v_1_1 (select A v_idx_7)) (= v_v_0_1 (select D v_idx_4)) (= v_v_8_1 (select B v_idx_5)) (= (select F v_idx_9) v_v_3_1) (= v_v_11_1 (select v_v_10_1 v_idx_1)) (= (select v_v_3_1 v_idx_10) v_v_4_1) (= v_v_5_1 (select E v_idx_12)) (= v_v_7_1 (select oldC v_idx_3)) (= v_v_9_1 (select v_v_8_1 v_idx_11)) (= v_v_6_1 (select C v_idx_2)) (= v_v_10_1 (select oldB v_idx_6)) (= (select oldA v_idx_8) v_v_2_1))))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest07ExistsPositive() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
			};
		final String formulaAsString = "(exists ((x Bool)) (and (p x) x))";
		final String expextedResultAsString = "(p true)";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest08ExistsNegative() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(exists ((x Bool)) (and (p x) (not x)))";
		final String expextedResultAsString = "(p false)";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest09ForallPositive() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(forall ((x Bool)) (or (p x) x))";
		final String expextedResultAsString = "(p false)";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest10ForallNegative() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(forall ((x Bool)) (or (p x) (not x)))";
		final String expextedResultAsString = "(p true)";
		runQuantifierPusherTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest11Multinegation() {
		final FunDecl funDecl = new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p");
		funDecl.declareFuns(mScript);
		final String formulaAsString = "(exists ((x Bool)) (and (p x) (not (not (not (not x))))))";
		final String expextedResultAsString = "(p true)";
		runQuantifierPusherTest(formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest12Performance() {
		/*
		 * Example generated from synthetic requirement benchmarks on ReqAnalyzer
		 *
		 * Interesting because:
		 * - We generate many (binominal scaling) similar checks on these examples, and speedups would accumulate.
		 * - Solvers are currently much slower to prove validity of these formulas compared to PQE,
		 *   so they might make interesting benchmarks
		 *
		 */
		final FunDecl funDecl = new FunDecl(SmtSortUtils::getRealSort, "clock");
		final String formulaAsString = "(exists"
				+ "  ((A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) "
				+ "(K Bool) (L Bool) (M Bool) (N Bool))" + "  (and "
				+ "(or (not A) (not (= 0 F))) (or G (not (= 7 F))) (or B (not (= 3 F))) (or (not B) (not (= 2 F))) "
				+ "(or (not M) (not (= F 9))) (or E (not (= 4 F))) (or (not (= 5 F)) (not H)) (or C (not (= 2 F))) "
				+ "(or (not (= 0 F)) (= 1 F) (and (not (= 1 F)) (= 0 F) N) (not N)) (or (not (= 1 F)) (not C)) "
				+ "(or (not D) (not (= 4 F))) (or (not G) (not (= 6 F))) (or H (not (= 6 F))) (or (not (= F 10)) M) "
				+ "(or (not (= 5 F)) D) (or (not (= F 9)) I) (or (and (or (= 1 F) (not (= 2 F)) K L) (= 1 F)) "
				+ "(and (not (= 1 F)) (or (not (= 2 F)) K L) (< clock 10.0)) (and (not K) (not (= 1 F)) (= 2 F) "
				+ "(not L) (< clock 10.0))) (or (not (= 7 F)) (not J)) (or (not (= 3 F)) (not E)) "
				+ "(or (not (= 1 F)) A) (or (not (= 8 F)) J) (or (not (= 8 F)) (not I))))";
		final String expextedResultAsString = "true";
		runQuantifierPusherTest(new FunDecl[] { funDecl }, formulaAsString, expextedResultAsString, true, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void moduloUnsound() {
		/*
		 * Example generated from MCR
		 *
		 * Notes: Happens already in quantifier pusher
		 */
		final FunDecl funDecl = new FunDecl(SmtSortUtils::getBoolSort, "c");
		final String formulaAsString =
				"(forall ((g Int)) (or (not (or (and c (= g 1)) (and (not c) (= g 0)) )) (= 0 (mod g 256)) ) ) ";
		final String expextedResultAsString = "(not c)";
		runQuantifierPusherTest(new FunDecl[] { funDecl }, formulaAsString, expextedResultAsString, true, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void moduloUnsoundExists() {
		final FunDecl funDecl = new FunDecl(SmtSortUtils::getBoolSort, "c");
		final String formulaAsString =
				"(exists ((g Int)) (and (or (and c (= g 1)) (and (not c) (= g 0)) ) (not (= 0 (mod g 256))) ) ) ";
		final String expextedResultAsString = "c";
		runQuantifierPusherTest(new FunDecl[] { funDecl }, formulaAsString, expextedResultAsString, true, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divByZero() {
		mScript.declareFun("BK", new Sort[0], SmtSortUtils.getRealSort(mMgdScript));
		final String formulaAsString =
				"(exists ((C Real) (A Real) (BD Real) (AK Int) (AP Int) (BH Int) (BC Int) (J Real) (M Real) (AN Int) (AW Int) (AT Int) (AF Int) (AD Real) (U Real) (S Real) (D Real) (O Int) (BG Int) (AA Real) (I Int) (AL Int) (V Real) (AJ Int) (AS Int) (L Real) (W Real) (AI Int) (AX Int) (AM Int) (AC Real) (K Real) (BJ Int) (T Int) (Z Real) (P Real) (Y Real) (AR Real) (B Real) (AG Int) (BE Int) (AZ Int) (E Bool) (AB Bool) (BB Int) (H Int) (AV Int) (AO Real) (BI Int) (N Real) (BA Int) (AQ Int) (R Real) (Q Real) (AY Int) (AH Int) (G Int) (F Real) (BF Int) (X Real) (AE Int) (AU Int)) (and (<= 0.0 P) (<= BI 255) (or (and (or AB (not E)) (= AO V)) (not (< AA (* 5.0 C))) (not E) (and (or (and (not AB) E) (and (not (= AO V)) E)) (< AA (* 5.0 C)))) (<= 0.0 N) (<= L 5100.0) (<= AK 15) (<= N 5100.0) (<= G 2) (<= Z 255.0) (<= C 255.0) (<= 0.0 Q) (<= 0 AK) (<= AU 253) (<= AL 255) (<= M 5100.0) (<= BJ 255) (<= 0.0 X) (<= 0.0 AA) (<= 0 AL) (<= AI 1023) (<= K 5100.0) (<= F 255.0) (<= AW 254) (<= 0 BI) (<= 0.0 Z) (or (and (<= 0 AN) (<= AN 240)) (= AN 254) (= AN 255)) (or (= AG 1023) (and (<= AG 1000) (or (<= 1 AG) (= AG 0)))) (<= V 65535.0) (or (= BC 14) (= BC 1) (= BC 2) (= BC 0)) (<= Y 255.0) (<= R 1310700.0) (<= B 255.0) (<= S 5100.0) (<= H 3) (<= 0 BJ) (<= D 255.0) (<= AT 1000) (or (and (or (not (< U AC)) (not (= I H)) (and (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U))) (= AO U))) (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U))) (= AO U)) (and (< BK 50.0) (or (and (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U))) (not (= I H))) (and (not (< U AC)) (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U)))))) (and (= I H) (< BK 50.0) (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U))) (< U AC))) (<= 0.0 M) (<= AC 5000.0) (or (and (or (<= 1 AF) (= AF 0)) (<= AF 1000)) (= AF 1023)) (<= 0.0 C) (or (and (<= AS 201) (<= 1 AS)) (= AS 0)) (<= 0.0 J) (<= 0.0 AC) (<= Q 255.0) (<= A 255.0) (<= AA 5.0) (<= 0.0 R) (<= 0.0 S) (<= 0.0 U) (<= 0 AJ) (or (and (<= AH 254) (<= 1 AH)) (= 255 AH) (= 0 AH)) (<= 0.0 V) (<= AJ 255) (<= 0 G) (<= 0 T) (or (and (<= AV 1000) (<= 1 AV)) (= 0 AV)) (or (<= 1 AU) (= 0 AU)) (<= U 65535.0) (<= 0.0 B) (<= 0.0 F) (<= P 5100.0) (or (= BB 254) (and (<= 0 BB) (<= BB 100))) (<= J 5100.0) (<= 0 O) (<= 0.0 K) (<= 0.0 AD) (or (= 0 AZ) (= 1 AZ) (= 14 AZ)) (<= T 3) (<= BG 1023) (<= O 65535) (or (= 1022 AP) (= 1023 AP) (and (<= AP 1021) (<= 0 AP))) (<= X 255.0) (<= 0.0 L) (<= 0.0 D) (or (and (<= AM 240) (<= 0 AM)) (= 254 AM) (= 255 AM)) (or (and (<= AE 254) (<= 1 AE)) (= 0 AE) (= 255 AE)) (or (= BE 65535) (= BE 254) (= BE 65534) (and (<= BE 240) (<= 0 BE)) (= BE 255)) (or (and (<= BD 250.0) (<= 0.0 BD)) (= BD 254.0)) (or (and (<= 0 AX) (<= AX 1021)) (= 1022 AX)) (<= 0.0 A) (<= 0.0 W) (or (= 14 AY) (= 1 AY) (= 0 AY)) (<= W 255.0) (<= 0 AI) (<= 0 H) (or (and (<= 0 BF) (<= BF 240)) (= BF 65534) (= BF 254) (= BF 65535) (= BF 255)) (or (= 14 BA) (= 1 BA) (= 0 BA)) (or (= BH 1022) (= BH 1023) (and (<= BH 1021) (<= 0 BH))) (or (= 254 AQ) (= 255 AQ) (and (<= 0 AQ) (<= AQ 253))) (or (= 0 AT) (<= 1 AT)) (<= 0.0 Y) (<= AD 5000.0) (<= 0 AW) (<= 0 BG)))";
		final String expectedResultAsString = "true";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void divByZero2() {
		// it is the same formula as in divByZero but with other variable names
		mScript.declareFun("SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2", new Sort[0],
				SmtSortUtils.getRealSort(mMgdScript));
		final String formulaAsString =
				" (exists ((|adp_diag_ks_masse'| Real) (|adp_count_fast'| Real) (|s_mvb_Smartlightsensor_Sensorspannung'| Real) (|si_RLSs_01__RLS_Zaehler_LIN1'| Int) (|s_LS_Helligkeit_FW'| Int) (|so_RLS_01__LS_Helligkeit_FW_SCAN'| Int) (|s_mvb_Smartlightsensor_Licht'| Int) (|adp_lx_dawn_to_day'| Real) (|adp_lx_LHO_CHO_Schwelle'| Real) (|si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| Int) (|s_mvb_Helligkeit_Infrarot'| Int) (|s_mvb_Feuchtesensorik_Scheibentemperatur'| Int) (|si_FSs_01__FS_Taupunkt_LIN1'| Int) (|s_helligkeit_uin_mM_roh'| Real) (|adp_s_outmax'| Real) (|adp_s_inpmin'| Real) (|adp_diag_ks_versorgung'| Real) (|adp_lx_off_kombi'| Int) (|so_RLS_01__LS_Helligkeit_FW_KCAN'| Int) (|ai_helligkeit_uin'| Real) (|adp_Lichtsensor_Typ_SMART_LS'| Int) (|si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'| Int) (|adp_s_outmin'| Real) (|si_RLSs_01__LS_Helligkeit_IR_LIN1'| Int) (|s_mvb_Feuchtesensorik_relative_Luftfeuchte'| Int) (|adp_lx_fastcount'| Real) (|adp_step_fast'| Real) (|si_RLSs_01__LS_Helligkeit_FW_LIN1'| Int) (|s_mvb_Helligkeit_Sichtbar'| Int) (|si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'| Int) (|s_helligkeit_uin_mM'| Real) (|adp_lx_day_to_dawn'| Real) (|so_RLS_01__LS_Helligkeit_IR_SCAN'| Int) (|adp_sonnensensor_Typ'| Int) (|adp_t_ls_countmax'| Real) (|adp_lx_on'| Real) (|adp_t_ls_calc'| Real) (|s_ls_in'| Real) (|adp_count_slow'| Real) (|si_FSs_01__FS_Temp_Scheibe_LIN1'| Int) (|s_mvb_Sonnensensor_Sonnenintensitaet_links'| Int) (|s_mvb_Licht_ein_bei_Regen'| Int) (|adp_diag_qualifizierung_notlauf'| Bool) (|s_afl_error'| Bool) (|s_mvb_Smartlightsensor_Helligkeit'| Int) (|adp_Lichtsensor_Typ'| Int) (|s_mvb_Feuchtesensorik_Taupunkt'| Int) (|s_ls_anaout'| Real) (|so_RLS_01__LS_Helligkeit_IR_KCAN'| Int) (|adp_lx_off'| Real) (|s_mvb_RLS_Status'| Int) (|s_LS_Helligkeit_IR'| Int) (|adp_s_inpmax'| Real) (|adp_lx_tunnel'| Real) (|s_mvb_Licht_ein_bei_Autobahn'| Int) (|si_FSs_01__FS_Temp_Sensor_LIN1'| Int) (|adp_Feuchtesensor_Typ'| Int) (|adp_diag_unplausibel'| Real) (|s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| Int) (|adp_step_slow'| Real) (|si_FSs_01__FS_Luftfeuchte_rel_LIN1'| Int) (|s_mvb_Feuchtesensorik_Sensortemperatur'| Int)) (and (<= 0.0 |adp_lx_on'|) (<= |so_RLS_01__LS_Helligkeit_IR_KCAN'| 255) (or (and (or |s_afl_error'| (not |adp_diag_qualifizierung_notlauf'|)) (= |s_ls_anaout'| |adp_s_outmin'|)) (not (< |ai_helligkeit_uin'| (* 5.0 |adp_diag_ks_masse'|))) (not |adp_diag_qualifizierung_notlauf'|) (and (or (and (not |s_afl_error'|) |adp_diag_qualifizierung_notlauf'|) (and (not (= |s_ls_anaout'| |adp_s_outmin'|)) |adp_diag_qualifizierung_notlauf'|)) (< |ai_helligkeit_uin'| (* 5.0 |adp_diag_ks_masse'|)))) (<= 0.0 |adp_lx_off'|) (<= |adp_lx_fastcount'| 5100.0) (<= |si_RLSs_01__RLS_Zaehler_LIN1'| 15) (<= |adp_lx_off'| 5100.0) (<= |adp_Feuchtesensor_Typ'| 2) (<= |adp_t_ls_countmax'| 255.0) (<= |adp_diag_ks_masse'| 255.0) (<= 0.0 |adp_lx_tunnel'|) (<= 0 |si_RLSs_01__RLS_Zaehler_LIN1'|) (<= |s_mvb_Feuchtesensorik_Sensortemperatur'| 253) (<= |si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'| 255) (<= |adp_lx_LHO_CHO_Schwelle'| 5100.0) (<= |so_RLS_01__LS_Helligkeit_IR_SCAN'| 255) (<= 0.0 |adp_step_slow'|) (<= 0.0 |ai_helligkeit_uin'|) (<= 0 |si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'|) (<= |si_RLSs_01__LS_Helligkeit_FW_LIN1'| 1023) (<= |adp_lx_day_to_dawn'| 5100.0) (<= |adp_diag_unplausibel'| 255.0) (<= |s_mvb_Helligkeit_Infrarot'| 254) (<= 0 |so_RLS_01__LS_Helligkeit_IR_KCAN'|) (<= 0.0 |adp_t_ls_countmax'|) (or (and (<= 0 |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'|) (<= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 240)) (= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 254) (= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 255)) (or (= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 1023) (and (<= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 1000) (or (<= 1 |si_FSs_01__FS_Temp_Scheibe_LIN1'|) (= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 0)))) (<= |adp_s_outmin'| 65535.0) (or (= |s_mvb_Smartlightsensor_Licht'| 14) (= |s_mvb_Smartlightsensor_Licht'| 1) (= |s_mvb_Smartlightsensor_Licht'| 2) (= |s_mvb_Smartlightsensor_Licht'| 0)) (<= |adp_t_ls_calc'| 255.0) (<= |adp_s_inpmax'| 1310700.0) (<= |adp_count_slow'| 255.0) (<= |adp_s_inpmin'| 5100.0) (<= |adp_Lichtsensor_Typ'| 3) (<= 0 |so_RLS_01__LS_Helligkeit_IR_SCAN'|) (<= |adp_diag_ks_versorgung'| 255.0) (<= |s_mvb_Feuchtesensorik_Scheibentemperatur'| 1000) (or (and (or (not (< |adp_s_outmax'| |s_helligkeit_uin_mM'|)) (not (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|)) (and (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|))) (= |s_ls_anaout'| |adp_s_outmax'|))) (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|))) (= |s_ls_anaout'| |adp_s_outmax'|)) (and (< SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2 50.0) (or (and (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|))) (not (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|))) (and (not (< |adp_s_outmax'| |s_helligkeit_uin_mM'|)) (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|)))))) (and (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|) (< SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2 50.0) (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|))) (< |adp_s_outmax'| |s_helligkeit_uin_mM'|))) (<= 0.0 |adp_lx_LHO_CHO_Schwelle'|) (<= |s_helligkeit_uin_mM'| 5000.0) (or (and (or (<= 1 |si_FSs_01__FS_Taupunkt_LIN1'|) (= |si_FSs_01__FS_Taupunkt_LIN1'| 0)) (<= |si_FSs_01__FS_Taupunkt_LIN1'| 1000)) (= |si_FSs_01__FS_Taupunkt_LIN1'| 1023)) (<= 0.0 |adp_diag_ks_masse'|) (or (and (<= |s_mvb_Feuchtesensorik_relative_Luftfeuchte'| 201) (<= 1 |s_mvb_Feuchtesensorik_relative_Luftfeuchte'|)) (= |s_mvb_Feuchtesensorik_relative_Luftfeuchte'| 0)) (<= 0.0 |adp_lx_dawn_to_day'|) (<= 0.0 |s_helligkeit_uin_mM'|) (<= |adp_lx_tunnel'| 255.0) (<= |adp_count_fast'| 255.0) (<= |ai_helligkeit_uin'| 5.0) (<= 0.0 |adp_s_inpmax'|) (<= 0.0 |adp_s_inpmin'|) (<= 0.0 |adp_s_outmax'|) (<= 0 |si_RLSs_01__LS_Helligkeit_IR_LIN1'|) (or (and (<= |si_FSs_01__FS_Temp_Sensor_LIN1'| 254) (<= 1 |si_FSs_01__FS_Temp_Sensor_LIN1'|)) (= 255 |si_FSs_01__FS_Temp_Sensor_LIN1'|) (= 0 |si_FSs_01__FS_Temp_Sensor_LIN1'|)) (<= 0.0 |adp_s_outmin'|) (<= |si_RLSs_01__LS_Helligkeit_IR_LIN1'| 255) (<= 0 |adp_Feuchtesensor_Typ'|) (<= 0 |adp_sonnensensor_Typ'|) (or (and (<= |s_mvb_Feuchtesensorik_Taupunkt'| 1000) (<= 1 |s_mvb_Feuchtesensorik_Taupunkt'|)) (= 0 |s_mvb_Feuchtesensorik_Taupunkt'|)) (or (<= 1 |s_mvb_Feuchtesensorik_Sensortemperatur'|) (= 0 |s_mvb_Feuchtesensorik_Sensortemperatur'|)) (<= |adp_s_outmax'| 65535.0) (<= 0.0 |adp_count_slow'|) (<= 0.0 |adp_diag_unplausibel'|) (<= |adp_lx_on'| 5100.0) (or (= |s_mvb_Smartlightsensor_Helligkeit'| 254) (and (<= 0 |s_mvb_Smartlightsensor_Helligkeit'|) (<= |s_mvb_Smartlightsensor_Helligkeit'| 100))) (<= |adp_lx_dawn_to_day'| 5100.0) (<= 0 |adp_lx_off_kombi'|) (<= 0.0 |adp_lx_day_to_dawn'|) (<= 0.0 |s_helligkeit_uin_mM_roh'|) (or (= 0 |s_mvb_Licht_ein_bei_Regen'|) (= 1 |s_mvb_Licht_ein_bei_Regen'|) (= 14 |s_mvb_Licht_ein_bei_Regen'|)) (<= |adp_sonnensensor_Typ'| 3) (<= |so_RLS_01__LS_Helligkeit_FW_KCAN'| 1023) (<= |adp_lx_off_kombi'| 65535) (or (= 1022 |s_LS_Helligkeit_FW'|) (= 1023 |s_LS_Helligkeit_FW'|) (and (<= |s_LS_Helligkeit_FW'| 1021) (<= 0 |s_LS_Helligkeit_FW'|))) (<= |adp_step_slow'| 255.0) (<= 0.0 |adp_lx_fastcount'|) (<= 0.0 |adp_diag_ks_versorgung'|) (or (and (<= |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'| 240) (<= 0 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|)) (= 254 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|) (= 255 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|)) (or (and (<= |si_FSs_01__FS_Luftfeuchte_rel_LIN1'| 254) (<= 1 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|)) (= 0 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|) (= 255 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|)) (or (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 65535) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 254) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 65534) (and (<= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 240) (<= 0 |s_mvb_Sonnensensor_Sonnenintensitaet_links'|)) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 255)) (or (and (<= |s_mvb_Smartlightsensor_Sensorspannung'| 250.0) (<= 0.0 |s_mvb_Smartlightsensor_Sensorspannung'|)) (= |s_mvb_Smartlightsensor_Sensorspannung'| 254.0)) (or (and (<= 0 |s_mvb_Helligkeit_Sichtbar'|) (<= |s_mvb_Helligkeit_Sichtbar'| 1021)) (= 1022 |s_mvb_Helligkeit_Sichtbar'|)) (<= 0.0 |adp_count_fast'|) (<= 0.0 |adp_step_fast'|) (or (= 14 |s_mvb_Licht_ein_bei_Autobahn'|) (= 1 |s_mvb_Licht_ein_bei_Autobahn'|) (= 0 |s_mvb_Licht_ein_bei_Autobahn'|)) (<= |adp_step_fast'| 255.0) (<= 0 |si_RLSs_01__LS_Helligkeit_FW_LIN1'|) (<= 0 |adp_Lichtsensor_Typ'|) (or (and (<= 0 |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'|) (<= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 240)) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 65534) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 254) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 65535) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 255)) (or (= 14 |s_mvb_RLS_Status'|) (= 1 |s_mvb_RLS_Status'|) (= 0 |s_mvb_RLS_Status'|)) (or (= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1022) (= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1023) (and (<= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1021) (<= 0 |so_RLS_01__LS_Helligkeit_FW_SCAN'|))) (or (= 254 |s_LS_Helligkeit_IR'|) (= 255 |s_LS_Helligkeit_IR'|) (and (<= 0 |s_LS_Helligkeit_IR'|) (<= |s_LS_Helligkeit_IR'| 253))) (or (= 0 |s_mvb_Feuchtesensorik_Scheibentemperatur'|) (<= 1 |s_mvb_Feuchtesensorik_Scheibentemperatur'|)) (<= 0.0 |adp_t_ls_calc'|) (<= |s_helligkeit_uin_mM_roh'| 5000.0) (<= 0 |s_mvb_Helligkeit_Infrarot'|) (<= 0 |so_RLS_01__LS_Helligkeit_FW_KCAN'|)))";
		final String expectedResultAsString = "true";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void divByZero3() {
		// Problem: by applying DER we get a division whose second argument is zero.
		mScript.declareFun("c", new Sort[0], SmtSortUtils.getRealSort(mMgdScript));
		final String formulaAsString = " (exists ((x Real)) (and (= x c) (< 2.0 (/ 1.0 (- c x)))))";
		final String expectedResultAsString = "(< 2.0 (/ 1.0 0.0))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	/**
	 * Quantifier elimination use case that comes from using constant arrays to initialize array variables in the C to
	 * Boogie translation. Variant where the helper function is inlined.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	@Test
	public void constantArrayTest01() {
		mScript.declareFun("a", new Sort[0],
				SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getArraySort(
						mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getIntSort(mMgdScript))));
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));

		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) " + "(= a (store v_a i ((as const (Array Int Int)) 0))))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	/**
	 * Quantifier elimination use case that comes from using constant arrays to initialize array variables in the C to
	 * Boogie translation. Variant where a helper function is used that is defined via define-function. (Perhaps this
	 * makes no difference.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	@Test
	public void constantArrayTest02() {
		final Sort arrayFromIntToIntToInt =
				SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getArraySort(
						mScript, SmtSortUtils.getIntSort(mMgdScript), SmtSortUtils.getIntSort(mMgdScript)));

		final String[] paramIds = { "a", "i" };
		final Sort[] paramSorts = new Sort[] { arrayFromIntToIntToInt, SmtSortUtils.getIntSort(mMgdScript) };
		final Sort resultSort = arrayFromIntToIntToInt;
		final String functionDefinitionAsString = "(store a i ((as const (Array Int Int)) 0))";
		final DeclarableFunctionSymbol additionalFunction = DeclarableFunctionSymbol.createFromString(mScript,
				"~initToZeroAtPointerBaseAddress~int", functionDefinitionAsString, paramIds, paramSorts, resultSort);
		additionalFunction.defineOrDeclare(mScript);
		final SmtFunctionsAndAxioms smtSymbols = new SmtFunctionsAndAxioms(mScript);

		mScript.declareFun("b", new Sort[0], arrayFromIntToIntToInt);
		mScript.declareFun("j", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) " + "(= b (~initToZeroAtPointerBaseAddress~int v_a j)))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Before inlining: " + formulaAsTerm.toStringDirect());
		final Term inlined = smtSymbols.inline(formulaAsTerm);
		mLogger.info("After inlining : " + inlined.toStringDirect());
		final LBool isDistinct = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", formulaAsTerm, inlined));
		mLogger.info("isDistinct     : " + isDistinct);
		Assert.assertTrue(isDistinct == LBool.UNSAT);
		final Term result = elim(inlined);
		mLogger.info("Result         : " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	/**
	 * Simple test for DER.
	 */
	@Test
	public void derTest1() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("a", new Sort[0], intSort);
		mScript.declareFun("b", new Sort[0], intSort);

		final String formulaAsString = "(exists ((x Int)) (or (and (= x a) (= x 1)) (and (= x b) (= x 2))))";
		final String expectedResultAsString = "(or (= a 1) (= b 2))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntAffine1Exists() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("t", new Sort[0], intSort);
		mScript.declareFun("a", new Sort[0], intSort);
		final String formulaAsString = "(exists ((x Int)) (and (= (* x 2) t) (= (* x x x) 8)))";
		final String expectedResultAsString = "(and (= 8 (* (div t 2) (div t 2) (div t 2))) (= (mod t 2) 0))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntAffine1Forall() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("t", new Sort[0], intSort);
		mScript.declareFun("a", new Sort[0], intSort);
		final String formulaAsString = "(forall ((x Int)) (or (distinct (* x 2) t) (distinct (* x x x) 8)))";
		final String expectedResultAsString = "(or (not (= 8 (* (div t 2) (div t 2) (div t 2)))) (not (= (mod t 2) 0)))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntPoly1Exists() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(exists ((x Int)) (and (= (* x a a a 2) t) (= (* x x x) 8)))";
		final String expectedResultAsString = "(let ((.cse2 (div t 2)) (.cse1 (= (mod t 2) 0)) (.cse0 (= a 0))) (or (and .cse0 .cse1 (= .cse2 0)) (let ((.cse4 (* a a a))) (and (= (let ((.cse3 (div .cse2 .cse4))) (* .cse3 .cse3 .cse3)) 8) (= (mod .cse2 .cse4) 0) .cse1 (not .cse0)))))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntPoly1Forall() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(forall ((x Int)) (or (not (= (* x a a a 2) t)) (not (= (* x x x) 8))))";
		final String expectedResultAsString = "(let ((.cse2 (= a 0)) (.cse0 (div t 2)) (.cse1 (not (= (mod t 2) 0)))) (and (or (not (= .cse0 0)) .cse1 (not .cse2)) (let ((.cse3 (* a a a))) (or (not (= (mod .cse0 .cse3) 0)) .cse2 (not (= (let ((.cse4 (div .cse0 .cse3))) (* .cse4 .cse4 .cse4)) 8)) .cse1))))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}


	public void tirRealPoly1Exists() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("a", new Sort[0], realSort);
		mScript.declareFun("b", new Sort[0], realSort);
		mScript.declareFun("t", new Sort[0], realSort);
		mScript.declareFun("hi", new Sort[0], realSort);
		mScript.declareFun("lo", new Sort[0], realSort);
		final String formulaAsString = "(exists ((x Int)) (and (<= (* x a a b (- 2)) t) (<= lo x) (<= x hi)))";
		final String expectedResultAsString = "true";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}



	@Test
	public void critConsReform01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, intSort, intSort);
		mScript.declareFun("memPtr", new Sort[0], intintArraySort);
		mScript.declareFun("p2", new Sort[0], intSort);
		mScript.declareFun("b", new Sort[0], intSort);
		mScript.declareFun("p1", new Sort[0], intSort);
		mScript.declareFun("a", new Sort[0], intSort);
		mScript.declareFun("v_DerPreprocessor_1", new Sort[0], intSort);
		mScript.declareFun("v_DerPreprocessor_3", new Sort[0], intSort);
		final String formulaAsString =
				"(= (select (store (store (store (store memPtr p2 b) p1 b) a v_DerPreprocessor_1) b v_DerPreprocessor_3) p1) b)";
		final String expectedResultAsString =
				"(= (select (store (store (store (store memPtr p2 b) p1 b) a v_DerPreprocessor_1) b v_DerPreprocessor_3) p1) b)";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void selectOverStoreTest01() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript),
				SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("b", new Sort[0], intintArraySort);
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("v", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString =
				"(forall ((a (Array Int Int))) (or (not (= (select (store a k v) i) 7)) (not (= i k))))";
		final String expectedResultAsString = "(or (not (= v 7)) (not (= i k)))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void selectOverStoreTest02() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript),
				SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("b", new Sort[0], intintArraySort);
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("v", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= (select (store a k v) i) 7) (= i k)))";
		final String expectedResultAsString = "(and (= v 7) (= i k))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void selectOverStoreTest03() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript),
				SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("b", new Sort[0], intintArraySort);
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("v", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString =
				"(forall ((a (Array Int Int))) (or (not (= (select (store a k v) i) 7)) (= i k)))";
		final String expectedResultAsString = "(= i k)";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	static void runQuantifierEliminationTest(final FunDecl[] funDecls, final String eliminationInputAsString,
			final String expectedResultAsString, final boolean checkResultIsQuantifierFree,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final QuantifierEliminationTestCsvWriter csvWriter) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		runQuantifierEliminationTest(eliminationInputAsString, expectedResultAsString, checkResultIsQuantifierFree,
				services, logger, mgdScript, csvWriter);
	}

	/**
	 * @deprecated use instead method with argument "FunDecl[] funDecls"
	 */
	@Deprecated
	static void runQuantifierEliminationTest(final String eliminationInputAsString, final String expectedResultAsString,
			final boolean checkResultIsQuantifierFree, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final QuantifierEliminationTestCsvWriter csvWriter) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		csvWriter.reportEliminationBegin(formulaAsTerm);
		final Term result = PartialQuantifierElimination.tryToEliminate(services, logger, mgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		SmtUtils.simplifyWithStatistics(mgdScript, result, null, services, SimplificationTechnique.SIMPLIFY_DDA);
		logger.info("Result: " + result);
		if (checkResultIsQuantifierFree) {
			final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
			Assert.assertTrue("Not quantifier-free ", resultIsQuantifierFree);
		}
		if (expectedResultAsString != null) {
			final boolean resultIsEquivalentToExpectedResult =
					SmtTestUtils.areLogicallyEquivalent(mgdScript.getScript(), result, expectedResultAsString);
			Assert.assertTrue("Not equivalent to expected result " + result, resultIsEquivalentToExpectedResult);
		}
		csvWriter.reportEliminationSuccess(result);
	}


	static void runQuantifierPusherTest(final FunDecl[] funDecls, final String eliminationInputAsString,
			final String expectedResultAsString, final boolean checkResultIsQuantifierFree,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final QuantifierEliminationTestCsvWriter csvWriter) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		runQuantifierPusherTest(eliminationInputAsString, expectedResultAsString, checkResultIsQuantifierFree,
				services, logger, mgdScript, csvWriter);
	}

	/**
	 * @deprecated use instead method with argument "FunDecl[] funDecls"
	 */
	@Deprecated
	static void runQuantifierPusherTest(final String eliminationInputAsString, final String expectedResultAsString,
			final boolean checkResultIsQuantifierFree, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final QuantifierEliminationTestCsvWriter csvWriter) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		final Term unf = new UnfTransformer(mgdScript.getScript()).transform(letFree);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(unf);
		csvWriter.reportEliminationBegin(formulaAsTerm);
		final Term result = new QuantifierPusher(mgdScript, services, true, PqeTechniques.ALL_LOCAL).transform(nnf);
		logger.info("Result: " + result);
		if (checkResultIsQuantifierFree) {
			final boolean resultIsQuantifierFree = QuantifierUtils.isQuantifierFree(result);
			Assert.assertTrue("Not quantifier-free ", resultIsQuantifierFree);
		}
		if (expectedResultAsString != null) {
			final boolean resultIsEquivalentToExpectedResult =
					SmtTestUtils.areLogicallyEquivalent(mgdScript.getScript(), result, expectedResultAsString);
			Assert.assertTrue("Not equivalent to expected result " + result, resultIsEquivalentToExpectedResult);
		}
		csvWriter.reportEliminationSuccess(result);
	}

	@Test
	public void selectOverStoreBug01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("k", new Sort[0], intSort);
		mScript.declareFun("i", new Sort[0], intSort);
		mScript.declareFun("v", new Sort[0], intSort);
		final String formulaAsString =
				"(exists ((a (Array Int Bool))) (not (select (store (store a k true) i true) v)))";
		final String expectedResultAsString = "(and (not (= i v)) (not (= k v)))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void selectOverStoreMultiDimSomeIndex() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("kOuter", new Sort[0], intSort);
		mScript.declareFun("iOuter", new Sort[0], intSort);
		mScript.declareFun("kInner", new Sort[0], intSort);
		mScript.declareFun("iInner", new Sort[0], intSort);
		mScript.declareFun("v", new Sort[0], intSort);
		final String formulaAsString =
				"(forall ((a (Array Int (Array Int Int)))) (or (not (= (select (select (store a kOuter (store (select a kOuter) kInner v)) iOuter) iInner) 7)) (not (= iOuter kOuter))))";
		final String expectedResultAsString =
				"(and (or (not (= iOuter kOuter)) (= iInner kInner)) (or (not (= iOuter kOuter)) (not (= v 7))))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void antiDerPreprocessing() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript),
				SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("b", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("v", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (not (= a b)) (= (store b k v) a)))";
		final String expectedResultAsString = "(not (= v (select b k)))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derPreprocessingBug() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, intSort, intSort);
		final Sort intintintArraySort =
				SmtSortUtils.getArraySort(mScript, intSort, SmtSortUtils.getArraySort(mScript, intSort, intSort));
		mScript.declareFun("main_~#p~0.offset", new Sort[0], intSort);
		mScript.declareFun("#memory_$Pointer$.base", new Sort[0], intintintArraySort);
		mScript.declareFun("#valid", new Sort[0], intintArraySort);
		mScript.declareFun("main_#t~mem1.base", new Sort[0], intSort);
		mScript.declareFun("main_~#p~0.base", new Sort[0], intSort);
		final String formulaAsString =
				"(forall ((|v_#memory_$Pointer$.base_14| (Array Int (Array Int Int))) (|main_#t~mem1.offset| Int)) (or (not (= |v_#memory_$Pointer$.base_14| (store |#memory_$Pointer$.base| |main_#t~mem1.base| (store (select |#memory_$Pointer$.base| |main_#t~mem1.base|) (+ |main_#t~mem1.offset| 28) (select (select |v_#memory_$Pointer$.base_14| |main_#t~mem1.base|) (+ |main_#t~mem1.offset| 28)))))) (= 1 (select |#valid| (select (select |v_#memory_$Pointer$.base_14| |main_~#p~0.base|) |main_~#p~0.offset|)))))";
		final String expectedResultAsString =
				"(forall ((|main_#t~mem1.offset| Int) (v_DerPreprocessor_2 Int)) (= 1 (select |#valid| (select (select (store |#memory_$Pointer$.base| |main_#t~mem1.base| (store (select |#memory_$Pointer$.base| |main_#t~mem1.base|) (+ |main_#t~mem1.offset| 28) v_DerPreprocessor_2)) |main_~#p~0.base|) |main_~#p~0.offset|))))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, false, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void nestedSelfUpdateTest() {
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("j", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("ai", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("aj", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("ak", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vi", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vj", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vk", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (not (= i k)) (= (select a i) ai) (= (select a j) aj) (= (select a k) ak)  (= (store (store (store a i vi) j vj) k vk) a)))";
		final String expectedResultAsString =
				"(let ((.cse0 (= ai vi)) (.cse5 (= j k)) (.cse1 (= ak vk)) (.cse2 (= i j)) (.cse3 (= aj vj)) (.cse4 (not (= i k)))) (or (and .cse0 .cse1 (not .cse2) .cse3 .cse4 (not .cse5)) (and .cse0 .cse1 (= aj vk) .cse4 .cse5) (and .cse1 .cse2 .cse3 .cse4 (= ai aj))))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	/**
	 * TODO: Bug. Some array variable is not eliminated.
	 */
	@Test
	public void dimensionProblem() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("idx", new Sort[0], intSort);
		mScript.declareFun("main_#t~mem8", new Sort[0], intSort);
		final String formulaAsString =
				"(exists ((|v_#memory_int_30| (Array Int (Array Int Int))) (|~#a~1.base| Int) (|~#a~1.offset| Int) (|main_#t~ret4| Int) (|v_#memory_$Pointer$.base_34| (Array Int (Array Int Int))) (|~#p1~1.base| Int) (|v_#memory_$Pointer$.offset_34| (Array Int (Array Int Int))) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (|#memory_$Pointer$.offset| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.offset_31| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.base_31| (Array Int (Array Int Int)))) "
						+ "(and (= (store |v_#memory_$Pointer$.offset_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.offset_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.offset_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.offset_31|) (not (= |~#p1~1.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0))) (= |#memory_$Pointer$.base| (store |v_#memory_$Pointer$.base_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select |v_#memory_$Pointer$.base_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) (select (select |#memory_$Pointer$.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0))))) (= (store |v_#memory_$Pointer$.offset_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select |v_#memory_$Pointer$.offset_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) (select (select |#memory_$Pointer$.offset| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0)))) |#memory_$Pointer$.offset|) (= (store |v_#memory_$Pointer$.base_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.base_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.base_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.base_31|) (not (= |~#p1~1.base| |~#a~1.base|)) (= |main_#t~mem8| (select (select (store (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) 8)) (select (select |#memory_$Pointer$.base| |~#p1~1.base|) 0)) (select (select |#memory_$Pointer$.offset| |~#p1~1.base|) 0)))))";
		final String expectedResultAsString = "(= 8 |main_#t~mem8|)";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void nestedStoresTest() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, SmtSortUtils.getIntSort(mMgdScript),
				SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("i", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("j", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("k", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vi", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vj", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("vk", new Sort[0], SmtSortUtils.getIntSort(mMgdScript));
		mScript.declareFun("b", new Sort[0], intintArraySort);
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (= (select a k) vk) (= (store (store a i vi) j vj) b)))";
		final String expectedResultAsString =
				"(let ((.cse2 (= vk (select b k))) (.cse0 (= vi (select b i))) (.cse3 (= i j)) (.cse1 (= vj (select b j))) (.cse4 (= j k))) (or (and .cse0 .cse1 .cse2) (and .cse3 .cse1 .cse2) (and (= i k) .cse0 .cse1) (and .cse0 .cse1 .cse4) (and .cse3 .cse1 .cse4)))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void varStillThere02() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		final Sort intintintArraySort =
				SmtSortUtils.getArraySort(mScript, intSort, SmtSortUtils.getArraySort(mScript, intSort, intSort));
		mScript.declareFun("nonMain_~dstPlusTwo~0.base", new Sort[0], intSort);
		mScript.declareFun("nonMain_~dstPlusTwo~0.offset", new Sort[0], intSort);
		mScript.declareFun("#memory_int", new Sort[0], intintintArraySort);
		final String formulaAsString =
				"(exists ((|v_#memory_int_BEFORE_CALL_2| (Array Int (Array Int Int))) (|v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| Int) (|v_#Ultimate.C_memcpy_#t~loopctr6_8| Int) (v_prenex_1 Int) (|v_#Ultimate.C_memcpy_#t~loopctr6_9| Int) (|#Ultimate.C_memcpy_#t~mem7| Int)) (and (<= |v_#Ultimate.C_memcpy_#t~loopctr6_8| 0) (<= (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| 2) nonMain_~dstPlusTwo~0.offset) (= (select (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base) nonMain_~dstPlusTwo~0.offset) 23) (= |#memory_int| (store |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base (store (store (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base) (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| |v_#Ultimate.C_memcpy_#t~loopctr6_8|) v_prenex_1) (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| |v_#Ultimate.C_memcpy_#t~loopctr6_9|) |#Ultimate.C_memcpy_#t~mem7|))) (<= |v_#Ultimate.C_memcpy_#t~loopctr6_9| (+ |v_#Ultimate.C_memcpy_#t~loopctr6_8| 1))))";
		final String expectedResultAsString =
				"(= 23 (select (select |#memory_int| nonMain_~dstPlusTwo~0.base) nonMain_~dstPlusTwo~0.offset))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	/**
	 * TODO: Bug. Some array variable ist not eliminated.
	 */
	@Test
	public void caseShouldHaveBeenHandledByDerPqeBug04simplified01Forward() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("main_#t~mem8", new Sort[0], intSort);
		final String formulaAsString =
				"(exists ((|~#b~1.offset| Int) (|~#p1~1.base| Int) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (|#memory_$Pointer$.offset| (Array Int (Array Int Int))) (|main_#t~ret4| Int) (|~#b~1.base| Int) (|~#a~1.base| Int) (|~#a~1.offset| Int) (|#memory_int| (Array Int (Array Int Int)))) (and (= (select (select |#memory_int| (select (select |#memory_$Pointer$.base| |~#p1~1.base|) 0)) (select (select |#memory_$Pointer$.offset| |~#p1~1.base|) 0)) |main_#t~mem8|) (exists ((|v_#memory_$Pointer$.base_34| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.base_31| (Array Int (Array Int Int)))) (and (= |~#b~1.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (= |#memory_$Pointer$.base| (store |v_#memory_$Pointer$.base_31| |~#b~1.base| (store (select |v_#memory_$Pointer$.base_31| |~#b~1.base|) |~#b~1.offset| (select (select |#memory_$Pointer$.base| |~#b~1.base|) |~#b~1.offset|)))) (= (store |v_#memory_$Pointer$.base_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.base_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.base_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.base_31|))) (not (= |~#b~1.base| |~#p1~1.base|)) (exists ((|v_#memory_int_30| (Array Int (Array Int Int)))) (= |#memory_int| (store (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) |~#b~1.base| (store (select (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) |~#b~1.base|) |~#b~1.offset| 8)))) (exists ((|v_#memory_$Pointer$.offset_34| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.offset_31| (Array Int (Array Int Int)))) (and (= (store |v_#memory_$Pointer$.offset_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.offset_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.offset_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.offset_31|) (= |~#b~1.offset| (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0)) (= (store |v_#memory_$Pointer$.offset_31| |~#b~1.base| (store (select |v_#memory_$Pointer$.offset_31| |~#b~1.base|) |~#b~1.offset| (select (select |#memory_$Pointer$.offset| |~#b~1.base|) |~#b~1.offset|))) |#memory_$Pointer$.offset|))) (not (= |~#p1~1.base| |~#a~1.base|))))";
		final String expectedResultAsString = null;
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void multidimensionalNestedStore() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		final Sort intintintArraySort =
				SmtSortUtils.getArraySort(mScript, intSort, SmtSortUtils.getArraySort(mScript, intSort, intSort));
		mScript.declareFun("v_#memory_int_BEFORE_CALL_2", new Sort[0], intintintArraySort);
		mScript.declareFun("nonMain_~dst~0.base", new Sort[0], intSort);
		mScript.declareFun("v_#Ultimate.C_memcpy_#t~loopctr6_8", new Sort[0], intSort);
		mScript.declareFun("#Ultimate.C_memcpy_dest.offset", new Sort[0], intSort);
		mScript.declareFun("v_prenex_1", new Sort[0], intSort);
		mScript.declareFun("v_#Ultimate.C_memcpy_#t~loopctr6_9", new Sort[0], intSort);
		mScript.declareFun("#Ultimate.C_memcpy_#t~mem7", new Sort[0], intSort);
		mScript.declareFun("#memory_int", new Sort[0], intintintArraySort);
		mScript.declareFun("nonMain_~src~0.base", new Sort[0], intSort);
		mScript.declareFun("nonMain_~src~0.offset", new Sort[0], intSort);
		final String formulaAsString =
				"(store |v_#memory_int_BEFORE_CALL_2| nonMain_~dst~0.base (store (store (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dst~0.base) (+ |v_#Ultimate.C_memcpy_#t~loopctr6_8| |#Ultimate.C_memcpy_dest.offset|) v_prenex_1) (+ |v_#Ultimate.C_memcpy_#t~loopctr6_9| |#Ultimate.C_memcpy_dest.offset|) |#Ultimate.C_memcpy_#t~mem7|))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.convert(mScript, formulaAsTerm);
		Assert.assertTrue(mdns.getDimension() == 2);
	}

	@Test
	public void applyDistributivity() {
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript) },
				SmtSortUtils.getBoolSort(mMgdScript));
		final String formulaAsString =
				"(forall ((x Int)) (or (and (p x) (p (+ x 1))) (and (not (= x 7)) (not (= x 8)))))";
		final String expectedResultAsString = "(and (p 7) (p 8) (p 9))";
		runQuantifierEliminationTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void infinityRestrictorDrop() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("main_#t~mem8", new Sort[0], intSort);
		final String formulaAsString = "(exists ((x Int)) (> (* 11 x) 17))";
		final String expectedResultAsString = "true";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntegerDivisibilityExists() {
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript) },
				SmtSortUtils.getBoolSort(mMgdScript));
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(exists ((x Int)) (and (p x) (= (* 2 x) y)))";
		final String expectedResultAsString = "(and (= 0 (mod y 2)) (p (div y 2)))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derIntegerDivisibilityForall() {
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript) },
				SmtSortUtils.getBoolSort(mMgdScript));
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(forall ((x Int)) (or (p x) (not (= (* 2 x) y))))";
		final String expectedResultAsString = "(or (not (= 0 (mod y 2))) (p (div y 2)))";
		runQuantifierPusherTest(formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript,
				mCsvWriter);
	}

	@Test
	public void derBitvectorFail01() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBv32, "~g~0", "main_~a~0") };
		final String inputSTR = "(forall ((v_~g~0_24 (_ BitVec 32))) (or (not (= ~g~0 (bvadd v_~g~0_24 (_ bv4294967295 32)))) (= (bvadd main_~a~0 (_ bv1 32)) v_~g~0_24)))";
		final String expectedResult = "(= (bvadd main_~a~0 (_ bv1 32)) (bvadd ~g~0 (_ bv1 32)))";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsStrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (> x lo) (< x hi)))";
		final String expectedResult = "(< (+ lo 1) hi)";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsNonstrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (>= x lo) (<= x hi)))";
		final String expectedResult = "(<= lo hi)";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsMixed() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (> x lo) (<= x hi)))";
		final String expectedResult = "(< lo hi)";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallStrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (> x lo) (< x hi)))";
		final String expectedResult = "(< lo hi)";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallNonstrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (>= x lo) (<= x hi)))";
		final String expectedResult = "(<= lo (+ hi 1))";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallMixed() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (> x lo) (<= x hi)))";
		final String expectedResult = "(<= lo hi)";
		runQuantifierPusherTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterTIR() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(exists ((x Int)) 	(and (> (* 7 x) lo ) (> hi x)))";
		final String expectedResult = "(<= (+ (div (+ (+ lo 1) (- 1)) 7) 2) hi)";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessTIR() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(exists ((x Int)) 	(and (< (* 7 x) hi ) (< lo x)))";
		final String expectedResult = "(<= (+ lo 1) (div (+ hi (- 1)) 7))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterEqTIR() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* 7 x) lo ) (> hi x)))";
		final String expectedResult = "(< (div (+ lo (- 1)) 7) hi)";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessEqTIR() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* 7 x) hi ) (< lo x)))";
		final String expectedResult = "(< lo (+ (div (+ (+ hi 1) (- 1)) 7) 1))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvultTIR() {
		final Sort bvSort = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("lo", new Sort[0], bvSort);
		mScript.declareFun("hi", new Sort[0], bvSort);
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvule x hi ) (bvule lo x)))";
		final String expectedResult = "(bvule lo hi)";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterTIRNegativeCoef() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(exists ((x Int)) 	(and (> (* (- 7) x) hi ) (< lo x)))";
		final String expectedResult = "(<= (+ lo 2) (div (+ (+ hi 1) (- 1)) (- 7)))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessTIRNegativeCoef() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(exists ((x Int)) 	(and (< (* (- 7) x) lo ) (> hi x)))";
		final String expectedResult = "(<= (+ (div (+ lo (- 1)) (- 7)) 1) hi)";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterEqTIRNegativeCoef() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* (- 7) x) hi ) (> x lo)))";
		final String expectedResult = "(< lo (div (+ hi (- 1)) (- 7)))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessEqTIRNegativeCoef() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* (- 7) x) lo ) (> hi x)))";
		final String expectedResult = "(< (div (+ (+ lo 1) (- 1)) (- 7)) (+ hi 1))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void antiDerTirExist() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputSTR = "(exists ((x Int)) (and	(not(=(* 4 x) y)) (> x lo) (< x hi)) )";
		final String expectedResult =
				"(or (and (<= (+ lo 2) hi) (<= (+ lo 1) (div (+ y (- 1)) 4))) (and (<= (+ lo 2) hi) (<= (+ (div y 4) 2) hi)))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void antiDerTirForall() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("lo", new Sort[0], intSort);
		mScript.declareFun("hi", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputSTR = "(forall ((x Int)) (or	(=(* 4 x) y) (> x lo) (< x hi))  )";
		final String expectedResult =
				"(and (or (< lo hi) (< lo (+ (div y 4) 1))) (or (< (div (+ y (- 1)) 4) hi) (< lo hi)))";
		runQuantifierPusherTest(inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bugTirAntiDer() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "b") };
		final String formulaAsString = "(exists ((a Int)) (and (> (* 4 a) b ) (< a 3) (< b 12)))";
		final String expectedResultAsString = "(and (< b 12) (exists ((a Int)) (and (< a 3) (> (* 4 a) b))))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void bugTirAntiDer02() {
		final FunDecl funDecl = new FunDecl(SmtSortUtils::getIntSort, "a");
		final String formulaAsString =
				"(exists ((x Int)) (and (not (= (+ (* x (- 256)) 1) 0)) (>= x a) (<= x a) (= a 0)))";
		final String expextedResultAsString = "(= a 0)";
		runQuantifierPusherTest(new FunDecl[] { funDecl }, formulaAsString, expextedResultAsString, true, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void omegaTestRequired01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(exists ((x Int) ) (and (<= (* 256 x) 93) (<= (+ c 7) (* 256 x))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(<= c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void ironModulo() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p"),
				new FunDecl(SmtSortUtils::getIntSort, "y"),
		};
//		final String formulaAsString = "(exists ((x Int)) (and (p x) (= x (+ (mod x 23) y))))";
//		final String formulaAsString = "(exists ((x Int)) (and (p x) (= y (mod x 2))))";
		final String formulaAsString = "(exists ((x Int)) (and (p x) (= y (* x 2))))";
		final String expectedResultAsString = "(and (= 0 (mod y 2)) (p (div y 2)))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lraSchollSmt08Rnd4_15() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getRealSort, "x1") };
		final String formulaAsString = "(exists ((?y1 Real)) (exists ((?y2 Real)) (and (exists ((?y3 Real)) (exists ((?y4 Real)) (or (and (or (<= 7.0 (+ (* 73.0 ?y2) (* 56.0 ?y3) (* 13.0 ?y4) (* 51.0 x1) (* 15.0 ?y1))) (not (= 51.0 (+ (* ?y2 (- 62.0)) (* ?y4 (- 61.0)))))) (or (not (= (- 66.0) (+ (* ?y2 (- 12.0)) (* ?y3 (- 71.0)) (* ?y4 8.0) (* ?y1 (- 46.0))))) (not (= (- 66.0) (+ (* ?y2 (- 14.0)) (* ?y3 (- 77.0)) (* ?y4 65.0) (* x1 86.0) (* ?y1 (- 85.0))))))) (and (not (= 33.0 (+ (* ?y2 (- 95.0)) (* ?y3 (- 81.0)) (* ?y4 74.0) (* x1 10.0) (* ?y1 76.0)))) (= (- 85.0) (* ?y1 (- 25.0)))) (and (<= (+ (* 21.0 ?y4) (* 57.0 ?y1)) (+ (* 53.0 ?y2) (* 8.0 ?y3) (* 6.0 x1) 5.0)) (= 11.0 (+ (* ?y2 (- 98.0)) (* ?y3 (- 95.0)) (* ?y4 80.0) (* x1 (- 19.0)) (* ?y1 (- 16.0)))))))) (or (forall ((?y3 Real)) (and (or (not (= 36.0 (+ (* ?y2 (- 2.0)) (* ?y3 42.0) (* x1 7.0)))) (and (<= (+ (* 81.0 ?y2) (* 29.0 ?y1)) (+ (* 44.0 ?y3) (* 19.0 x1) 84.0)) (forall ((?y4 Real)) (and (<= (+ (* 14.0 ?y3) (* 54.0 ?y4) (* 48.0 x1) (* 77.0 ?y1) 64.0) (* 46.0 ?y2)) (<= 0.0 (+ (* 29.0 ?y3) (* 39.0 ?y4) (* 70.0 x1) 32.0)))) (= (- 30.0) (+ (* x1 9.0) (* ?y1 (- 4.0))))) (and (<= (* 17.0 ?y1) (* 11.0 x1)) (< (* 52.0 x1) (+ (* 66.0 ?y2) (* 74.0 ?y3) (* 46.0 ?y1) 25.0)))) (or (< (+ (* 46.0 ?y1) 80.0) (+ (* 4.0 ?y2) (* 34.0 ?y3) (* 32.0 x1))) (and (< 80.0 (* 59.0 ?y1)) (not (= 0.0 (+ (* ?y2 (- 40.0)) (* ?y3 (- 55.0)) (* x1 (- 35.0)))))) (and (or (= (- 24.0) (+ (* ?y2 (- 88.0)) (* ?y3 95.0))) (< (+ (* 37.0 ?y2) (* 15.0 ?y3) (* 63.0 ?y1)) (+ (* 27.0 x1) 79.0))) (or (<= (+ (* 41.0 ?y2) ?y1) (* 62.0 x1)) (<= (+ (* 79.0 x1) (* 74.0 ?y1)) (+ (* 17.0 ?y2) (* 10.0 ?y3) 14.0)))) (< (+ (* 21.0 ?y2) (* 30.0 ?y1)) (+ (* 77.0 ?y3) (* 100.0 x1) 19.0))))) (and (not (= (- 33.0) (+ (* ?y2 61.0) (* x1 (- 3.0)) (* ?y1 31.0)))) (exists ((?y4 Real)) (and (<= (+ (* 32.0 ?y4) (* 35.0 ?y1)) (* 84.0 x1)) (not (= 23.0 (+ (* ?y4 (- 21.0)) (* x1 53.0) (* ?y1 8.0)))) (or (<= (* 53.0 ?y2) (* 94.0 x1)) (<= (+ (* 94.0 ?y2) (* 50.0 ?y4) 69.0) (* 55.0 x1))) (or (and (= (- 63.0) (+ (* ?y2 (- 22.0)) (* ?y4 37.0) (* x1 (- 9.0)) (* ?y1 89.0))) (< 35.0 (+ (* 100.0 ?y2) (* 10.0 x1)))) (< (+ (* 88.0 ?y2) (* 2.0 ?y1)) (+ (* 31.0 x1) 46.0))))) (exists ((?y4 Real)) (and (<= (+ (* 82.0 ?y4) (* 88.0 x1)) (+ (* 39.0 ?y1) 95.0)) (< 0.0 (+ (* 86.0 ?y1) 21.0)))) (exists ((?y4 Real)) (and (= (- 93.0) (+ (* ?y4 75.0) (* x1 (- 19.0)))) (<= (+ ?y4 (* 38.0 x1) (* 15.0 ?y1)) (* 38.0 ?y2)))) (< (* 91.0 ?y1) 0.0))))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lraSchollSmt08Rnd4_15Red() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getRealSort, "x1", "?y2", "?y3", "?y4") };
		final String formulaAsString = "(exists ((?y1 Real)) (and (not (= (- 66.0) (+ (* ?y2 (- 14.0)) (* ?y3 (- 77.0)) (* ?y4 65.0) (* x1 86.0) (* ?y1 (- 85.0)))))  (or (forall ((?y3 Real)) (<= (+ (* 41.0 ?y2) ?y1) (* 62.0 x1)) ) (and (< 0.0 (+ (* 86.0 ?y1) 21.0)) (< (* 91.0 ?y1) 0.0)))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void multiTechniques() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= x b) (<= y x) (<= a y)))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(<= a b)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	/**
	 * Reveals conceptual bug in {@link QuantifierPusher}. We have to apply rules
	 * for nested quantifiers after elimination techniques.
	 */
	public void resolvedQuantifierNesting() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= x b) (exists ((z Int)) (and (<= y x) (= (* y y z z) 0)))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void uselessOuterQuantifier() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript)}, SmtSortUtils.getBoolSort(mMgdScript));
		final String formulaAsString = "(exists ((x Int) ) (forall ((y Int) (z Int)) (or (p z) (and (p x) (distinct y 0) ))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(forall ((z Int)) (p z))", false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void innerPush() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript)}, SmtSortUtils.getBoolSort(mMgdScript));
		final String formulaAsString = "(exists ((x Int) ) (and (<= a x) (forall ((y Int) (z Int)) (or (p z) (and (p x) (distinct y 0))))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(forall ((z Int)) (p z))", false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void wildboellen() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "z", "y") };
		final String formulaAsString = "(forall ((x Int) ) (or (= 0 x) (not (= (* z (+ x 1)) y))))";
		final String expectedResult = "(let ((.cse0 (+ y (- z))) (.cse1 (= 0 z))) (and (or (not (= 0 .cse0)) (not .cse1)) (or (= 0 (div .cse0 z)) (not (= 0 (mod (+ y (* z (- 1))) z))) .cse1)))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void oppenau() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getIntSort, "square"),
			new FunDecl(SmtSortUtils::getIntSort, "x", "y"),
		};
		final String formulaAsString = "(exists ((v_proc_i_AFTER_CALL_1 Int) (v_f_4 Int) (v_proc_res_BEFORE_RETURN_1 Int)) (and (exists ((v_f_4 Int)) (<= (+ x (square v_f_4)) v_proc_i_AFTER_CALL_1)) (<= v_proc_res_BEFORE_RETURN_1 y) (<= (+ x (square v_f_4)) v_proc_i_AFTER_CALL_1) (<= v_proc_i_AFTER_CALL_1 v_proc_res_BEFORE_RETURN_1)))";
		final String expectedResult = null;
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod01Exists() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(exists ((x Int) ) (and (<= c x) (<= x 100) (= 7 (mod x 256) )))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(<= c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod01Forall() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(forall ((x Int) ) (or (> c x) (> x 100) (not (= 7 (mod x 256) ))))";
		runQuantifierPusherTest(funDecls, formulaAsString, "(> c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod02Uneliminatable() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p"),
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= (div x 7) (div (+ y 1) 5)) (p x) (p y)))";
		final String expectedResult = "(exists ((x Int) (y Int)) (and (= (div x 7) (div (+ y 1) 5)) (p x) (p y)))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod03Nutz01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(exists ((x Int)) (and (<= (mod x 4294967296) 0) (= y (mod x 4294967296))))";
		final String expectedResult = "(let ((.cse0 (* y (- 1)))) (and (<= (div y (- 4294967296)) (div .cse0 4294967296)) (<= 0 y) (< y 4294967296) (<= (div y (- 4294967296)) (div (+ .cse0 4294967295) 4294967296))))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sandmanForward() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "c"), };
		final String formulaAsString = "(exists ((x Int)) (and (<= (mod x 256) (+ c 256)) (not (<= (mod x 256) 127))))";
		final String expectedResult = "(and (<= 0 (div (+ c 256) 256)) (<= 0 (+ c 256)) (<= 0 (div (+ c 128) 256)))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sandmanForwardStep() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "c"), };
		final String formulaAsString = "(exists ((x Int)) (and (< x 256) (not (<= (mod x 256) 127)) (<= x (+ c 256)) (<= 0 x)))";
		final String expectedResult = "(and (<= 0 (div (+ c 256) 256)) (<= 0 (+ c 256)) (<= 0 (div (+ c 128) 256)))";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void PointerInBooleanExpression() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "main_~a~0"), };
		final String formulaAsString = "(exists ((main_~p~0.offset Int) (|main_#t~malloc0.base| Int)) (and (not (= 0 |main_#t~malloc0.base|)) (or (and (= 0 main_~p~0.offset) (= 0 |main_#t~malloc0.base|) (= 1 main_~a~0)) (and (= 0 main_~a~0) (or (not (= 0 main_~p~0.offset)) (not (= 0 |main_#t~malloc0.base|)))))))";
		final String expectedResult = "(= 0 main_~a~0)";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor02WhiteRussia() {
		final FunDecl[] funDecls = new FunDecl[] {};
		final String formulaAsString = "(exists ((main_~a~0 Int) (main_~b~0 Int)) (and (<= 1 (mod (+ (* main_~b~0 4294967295) main_~a~0) 4294967296)) (= 0 main_~b~0) (not (< (mod main_~b~0 4294967296) (mod main_~a~0 4294967296))) (<= (mod main_~a~0 4294967296) 1)))";
		final String expectedResult = "false";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor03Gearshiftnut() {
		final FunDecl[] funDecls = new FunDecl[] {};
		final String formulaAsString = "(forall ((v_main_~i~0_6 Int) (v_main_~b~0_8 Int)) (or (< (div (+ (* (mod v_main_~i~0_6 4294967296) (- 1)) (* v_main_~b~0_8 (- 4294967295))) (- 4294967296)) (+ (div (+ (* v_main_~b~0_8 4294967295) (- 4294967296)) 4294967296) 2)) (not (and (= 0 v_main_~i~0_6) (= 0 v_main_~b~0_8)))))";
		final String expectedResult = "true";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "main_~i~0", "main_~b~0"), };
		final String formulaAsString = "(forall ((aux_div_aux_mod_main_~a~0_26_37 Int) (aux_mod_aux_mod_main_~a~0_26_37 Int)) (or (<= 4294967296 (+ (* 4294967296 aux_div_aux_mod_main_~a~0_26_37) aux_mod_aux_mod_main_~a~0_26_37)) (and (< 0 (mod (+ (* main_~b~0 4294967295) aux_mod_aux_mod_main_~a~0_26_37) 4294967296)) (<= (mod (+ (* main_~b~0 4294967295) aux_mod_aux_mod_main_~a~0_26_37) 4294967296) 1)) (> 0 aux_mod_aux_mod_main_~a~0_26_37) (>= aux_mod_aux_mod_main_~a~0_26_37 4294967296) (<= (+ (* 4294967296 aux_div_aux_mod_main_~a~0_26_37) aux_mod_aux_mod_main_~a~0_26_37) (mod main_~i~0 4294967296)) (< (mod (+ main_~i~0 1) 4294967296) aux_mod_aux_mod_main_~a~0_26_37) (< (+ (* 4294967296 aux_div_aux_mod_main_~a~0_26_37) aux_mod_aux_mod_main_~a~0_26_37) 0)))";
		final String expectedResult = "false";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "main_~i~0", "main_~b~0"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (and (< 0 (mod (+ (* main_~b~0 4294967295) moda) 4294967296)) (<= (mod (+ (* main_~b~0 4294967295) moda) 4294967296) 1)) (> 0 moda) (>= moda 4294967296) (<= (+ (* 4294967296 diva) moda) (mod main_~i~0 4294967296)) (< (mod (+ main_~i~0 1) 4294967296) moda) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "false";
		runQuantifierPusherTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void testNonTermination() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x0", "x1"), };
		final String formulaAsString = "(exists ((v_x1_32 Int) (v_x2_42 Int) (v_x1_28 Int) (v_x2_38 Int) (v_x2_60 Int) (v_x2_54 Int) (v_x1_41 Int) (v_x1_56 Int) (v_x0_46 Int) (v_x0_59 Int) (v_x3_53 Int)) (let ((.cse47 (+ v_x1_56 1)) (.cse4 (<= 0 v_x1_56)) (.cse2 (<= v_x1_56 0)) (.cse5 (<= 0 x1)) (.cse1 (<= x1 0))) (or (let ((.cse0 (<= v_x1_56 x1)) (.cse3 (<= x1 v_x1_56))) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 (let ((.cse23 (<= v_x2_42 v_x2_54)) (.cse52 (+ v_x2_38 1)) (.cse53 (+ v_x2_54 1)) (.cse29 (<= v_x2_42 0))) (let ((.cse22 (<= 0 v_x2_38)) (.cse7 (<= 0 v_x2_54)) (.cse49 (not .cse29)) (.cse48 (<= .cse53 v_x2_42)) (.cse50 (<= .cse52 v_x2_42)) (.cse51 (or (<= v_x2_42 v_x2_38) .cse23)) (.cse6 (<= v_x2_38 0)) (.cse32 (<= v_x2_54 0)) (.cse26 (<= 0 v_x2_42))) (or (let ((.cse8 (<= v_x2_38 v_x2_60)) (.cse9 (ite .cse48 (=> .cse49 (or .cse29 (ite (not .cse50) .cse6 .cse51))) .cse32)) (.cse10 (<= v_x2_60 0)) (.cse36 (<= v_x2_60 v_x2_38))) (and .cse6 .cse7 .cse8 .cse9 .cse1 .cse10 (let ((.cse11 (<= v_x1_41 v_x1_56))) (or (let ((.cse13 (<= v_x1_41 x1)) (.cse14 (<= v_x1_41 0)) (.cse15 (<= 0 v_x1_41)) (.cse12 (<= x1 v_x1_41)) (.cse16 (<= v_x1_56 v_x1_41))) (and .cse11 .cse0 .cse1 .cse3 .cse12 .cse5 (or (and .cse12 .cse13) (ite .cse14 (and (<= (+ v_x1_41 1) 0) .cse15) .cse14)) .cse16 .cse13 (let ((.cse17 (<= 0 v_x0_46))) (or (and (<= (+ v_x0_46 1) 0) .cse17) (let ((.cse33 (<= v_x0_46 0))) (and (let ((.cse44 (<= (+ x0 1) 0))) (let ((.cse18 (not .cse44)) (.cse40 (<= 0 x0))) (ite .cse18 (let ((.cse20 (<= x0 0))) (let ((.cse19 (not .cse20))) (or (ite .cse19 .cse20 (<= 1 x0)) (let ((.cse34 (<= 0 v_x0_59))) (let ((.cse37 (<= v_x0_46 x0)) (.cse42 (<= x0 v_x0_46)) (.cse45 (<= v_x0_46 v_x0_59)) (.cse46 (<= v_x0_59 v_x0_46)) (.cse38 (and (<= (+ v_x0_59 1) 0) .cse34))) (let ((.cse21 (or (and .cse45 .cse46 .cse17 .cse33) .cse38)) (.cse43 (ite .cse19 (or .cse42 .cse20) .cse17)) (.cse41 (ite .cse44 (or .cse37 .cse40) .cse33))) (and .cse21 (or (let ((.cse39 (<= v_x0_59 0))) (and (or (and (let ((.cse30 (+ v_x1_28 1)) (.cse35 (<= 0 v_x1_28))) (or (let ((.cse25 (<= v_x1_32 v_x2_42)) (.cse31 (and (<= (+ v_x1_32 1) 0) (<= 0 v_x1_32)))) (let ((.cse24 (or .cse25 .cse31)) (.cse28 (<= v_x1_28 v_x2_42)) (.cse27 (<= x1 v_x2_42))) (and (<= v_x2_42 v_x1_28) .cse8 .cse22 .cse23 .cse1 (<= 0 v_x2_60) .cse5 .cse24 .cse13 (<= v_x1_28 0) .cse6 .cse11 .cse7 (<= v_x2_42 x1) (or (and .cse25 .cse26 .cse1 .cse27 .cse5 .cse28) (and .cse1 .cse24 .cse5)) .cse27 .cse29 .cse14 .cse9 .cse15 (or (and (<= .cse30 v_x1_32) (<= v_x1_32 v_x1_28)) (and .cse1 .cse5 (<= x1 v_x1_32) (<= v_x1_32 x1)) .cse31) .cse10 .cse12 .cse28 (<= v_x2_54 v_x2_42) (<= v_x0_46 v_x2_54) .cse32 .cse17 .cse33 .cse34 (<= v_x2_42 v_x1_32) .cse26 .cse0 (<= v_x1_41 v_x2_54) .cse2 (<= v_x1_41 v_x2_42) .cse3 .cse4 (<= v_x2_42 v_x1_41) .cse35 .cse36 (or (and .cse1 .cse5) .cse27) .cse16 (<= v_x2_42 v_x1_56)))) (and (<= .cse30 0) .cse35))) .cse37 .cse20 (or .cse38 (and .cse21 .cse34 (or (ite .cse18 (and .cse21 .cse34 .cse39 .cse17) .cse40) .cse38) .cse17)) (<= v_x3_53 0) .cse32 .cse33 .cse17 .cse41 (<= 0 v_x3_53) .cse11 .cse42 .cse7 .cse34 .cse26 .cse39 .cse29 .cse16 .cse40 .cse43 (<= v_x3_53 v_x2_54)) .cse44) .cse34 .cse39 .cse45 .cse46 .cse17 .cse33)) .cse38) (or .cse44 (and .cse42 .cse37 .cse33 .cse17)) .cse43 .cse41 .cse33 .cse17)))) .cse44))) .cse40))) .cse33 .cse17)))))) (and (<= .cse47 v_x1_41) .cse11))) .cse5 .cse36 .cse29 .cse32)) (and (<= .cse52 0) .cse22) (and (<= .cse53 0) .cse7) (ite .cse49 (ite .cse48 (ite .cse50 .cse51 .cse6) .cse32) (and (<= (+ v_x2_42 1) 0) .cse26))))))) (ite .cse2 (and (<= .cse47 0) .cse4) .cse2) (ite .cse1 (and (<= (+ x1 1) 0) .cse5) .cse1))))";
		runQuantifierPusherTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Deprecated
	private Term elim(final Term quantFormula) {
		return PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, quantFormula,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}

}
//@formatter:on

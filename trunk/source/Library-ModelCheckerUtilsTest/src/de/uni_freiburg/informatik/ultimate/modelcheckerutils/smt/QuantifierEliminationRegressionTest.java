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

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.FunDecl.SortConstructor;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;


/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationRegressionTest {

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


	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationRegressionTest.class.getSimpleName());
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

	//@formatter:off

	@Test
	public void otherArrayBug() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			new FunDecl(SmtSortUtils::getIntSort, "i"),
		};
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= (select a i) (select b 0)) (= (select a 0) (select b 1))))";
		final String expextedResultAsString = "(or (= (select b 0) (select b 1)) (not (= 0 i)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest07ExistsPositive() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
			};
		final String formulaAsString = "(exists ((x Bool)) (and (p x) x))";
		final String expextedResultAsString = "(p true)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest08ExistsNegative() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(exists ((x Bool)) (and (p x) (not x)))";
		final String expextedResultAsString = "(p false)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest09ForallPositive() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(forall ((x Bool)) (or (p x) x))";
		final String expextedResultAsString = "(p false)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest1() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool)) (and (<= 0 A) (or (and (not B) (not C)) (and C B)) (or (and (not D) (not E)) (and E D)) (or (and F G) (and (not G) (not F)))))";
		final String expextedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest10ForallNegative() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
		};
		final String formulaAsString = "(forall ((x Bool)) (or (p x) (not x)))";
		final String expextedResultAsString = "(p true)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest11Multinegation() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getBoolSort }, SmtSortUtils::getBoolSort, "p")
			};
		final String formulaAsString = "(exists ((x Bool)) (and (p x) (not (not (not (not x))))))";
		final String expextedResultAsString = "(p true)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
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
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "clock"), };
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
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getRealSort, "T1", "T2"),
		};
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Int)) (or (<= 50.0 T2) (and (not F) (or (and (< T1 50.0) (or (and (not (< B 5)) (not (= H E))) (and (not (= H E)) (or (not F) (not G) (not (= A E)) (not C))))) (and (= H E) (or (not F) (= H E) (not (< B 5)) (not G) (not (= A E)) (not C))) (and (< T1 50.0) (= A E) (< B 5) C (not (= H E)) F G)) (not (= E D))) (< T2 50.0)))";
		final String expextedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
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
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest4() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getRealSort, "T1"),
		};
		final String formulaAsString = "(exists ((A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (AA Bool) (AB Int) (AC Int) (AD Bool) (AE Bool) (AF Bool) (AG Bool)) (or (< T1 50.0) (and (not E) (or (and (not S) (not AE) W) (and (not S) B (not AE)) (and (not S) (not AE) AF) (and (not S) (not AE) J) (and (not S) (not AE) Z) (and (not S) (not AE) F) (and (not S) (not AE) C) (and (not S) (not AE) AG) (and (< T1 50.0) (or (and (not U) (or (and (not J) (or (and (or (and (not O) (or (and (or (and (or (and (not AF) (or (and (not B) (or (and (or (and (not C) (or (and (not Y) (or (and (not F) (or (and (or (and (or (and (not S) (not AA)) (and (not S) AE)) (not G)) (and (not S) AE)) (not Z)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not W)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not M)) (and (not S) AE)) (not AG)) (and (not S) AE))) (and (not S) AE)) (not AD)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) (not AE) AA) (and (not S) (not AE) M) (and (not S) (not AE) U) (and (or (and (not U) (or (and (or (and (not AD) (or (and (not O) (or (and (not AG) (or AE (and (not M) (or (and (not AF) (or (and (not B) (or (and (not W) (or (and (or (and (or (and (not F) (or (and (or (and (or (not AA) AE) (not G)) AE) (not Z)) AE)) AE) (not Y)) AE) (not C)) AE)) AE)) AE)) AE)))) AE)) AE)) AE) (not J)) AE)) AE) (<= 50.0 T1)) (and (not S) (not AE) G) (and (not S) (not AE) AD) (and (not S) (not AE) O) (and (not S) (not AE) Y)) (or (and Q R A T V D X H I K L AE N P) (not (= AC AB))) (not (= AC AB)) (or (not R) (not P) (not AE) (not T) (not D) (not X) (not Q) (not I) (not V) (not L) (not H) (not A) (not K) (not N))) (<= 50.0 T1)))";
		final String expextedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void plrTest5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getRealSort, "T1"),
		};
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Int) (AA Int) (AB Bool) (AC Real) (AD Bool) (AE Int) (AF Bool) (AG Bool) (AH Bool) (AI Real) (AJ Bool) (AK Int) (AL Bool) (AM Bool) (AN Bool) (AO Bool) (AP Bool) (AQ Bool) (AR Bool) (AS Bool) (AT Bool) (AU Bool) (AV Int) (AW Bool) (AX Int) (AY Bool) (AZ Bool) (BA Bool) (BB Bool) (BC Bool) (BD Bool) (BE Int) (BF Bool) (BG Bool) (BH Bool) (BI Bool) (BJ Bool) (BK Bool) (BL Int) (BM Bool) (BN Int) (BO Bool) (BP Bool) (BQ Bool) (BR Bool) (BS Int) (BT Bool) (BU Bool) (BV Bool) (BW Bool) (BX Bool) (BY Bool) (BZ Bool) (CA Bool) (CB Int) (CC Int) (CD Int) (CE Bool) (CF Bool) (CG Int) (CH Bool) (CI Bool) (CJ Bool) (CK Bool) (CL Real) (CM Int) (CN Real) (CO Bool) (CP Bool) (CQ Bool) (CR Bool) (CS Bool) (CT Real) (CU Bool) (CV Bool) (CW Int) (CX Bool) (CY Int) (CZ Bool) (DA Bool) (DB Int) (DC Int) (DD Bool) (DE Bool) (DF Bool) (DG Bool) (DH Bool) (DI Bool) (DJ Bool) (DK Int) (DL Bool) (DM Real) (DN Int) (DO Int) (DP Bool) (DQ Bool) (DR Bool) (DS Bool) (DT Int) (DU Int) (DV Int) (DW Bool) (DX Bool) (DY Bool) (DZ Bool) (EA Bool) (EB Int) (EC Bool) (ED Real) (EE Int) (EF Bool) (EG Bool) (EH Int) (EI Bool) (EJ Bool) (EK Bool) (EL Int) (EM Bool) (EN Bool) (EO Bool) (EP Bool) (EQ Bool) (ER Bool) (ES Bool) (ET Bool) (EU Int) (EV Bool) (EW Bool) (EX Bool) (EY Bool) (EZ Bool) (FA Real) (FB Int) (FC Bool) (FD Int) (FE Bool) (FF Bool) (FG Bool) (FH Bool) (FI Int) (FJ Bool) (FK Bool) (FL Bool) (FM Bool) (FN Bool) (FO Real) (FP Bool) (FQ Bool) (FR Bool) (FS Bool) (FT Bool) (FU Int) (FV Bool) (FW Bool) (FX Bool) (FY Bool) (FZ Int) (GA Bool) (GB Real) (GC Bool) (GD Bool) (GE Bool) (GF Bool) (GG Bool) (GH Int) (GI Int) (GJ Bool) (GK Bool) (GL Int) (GM Int) (GN Bool) (GO Bool) (GP Int) (GQ Real) (GR Bool) (GS Bool) (GT Int) (GU Bool) (GV Bool) (GW Bool) (GX Bool) (GY Int) (GZ Int) (HA Int) (HB Bool) (HC Int) (HD Bool) (HE Bool) (HF Bool) (HG Bool) (HH Bool) (HI Bool) (HJ Bool) (HK Bool) (HL Bool) (HM Bool) (HN Bool) (HO Bool) (HP Bool) (HQ Bool) (HR Int) (HS Bool) (HT Bool) (HU Bool) (HV Int) (HW Bool) (HX Bool) (HY Bool) (HZ Bool) (IA Bool) (IB Bool) (IC Int) (ID Bool) (IE Bool) (IF Int) (IG Bool) (IH Bool) (II Bool) (IJ Real) (IK Bool) (IL Bool) (IM Bool) (IN Bool) (IO Bool) (IP Bool) (IQ Bool) (IR Bool) (IS Bool) (IT Bool) (IU Bool) (IV Int) (IW Bool) (IX Bool) (IY Bool) (IZ Bool) (JA Bool) (JB Real) (JC Bool)) (and (<= 0 DO) (= BC IL) (= GI BN) (or (not BY) DR) (<= 0 B) (= HO FP) (or GJ (not AN)) (= IX AZ) (<= 0 EE) (<= AX 7) (= EO BD) (= AD CK) (= FY HW) (or (not GV) HN) (or (not BV) DJ) (<= DC 255) (or (not GD) IZ) (= AJ IE) (or (not (< 0 DV)) (= EH 1)) (= AC (/ 3.0 2.0)) (= 2 AA) (= AV 19) (= HP W) (= O HS) (= AQ EK) (or AF (not FJ)) (= GZ 3) (<= 0 FB) (= DP AH) (or AL (not BG)) (= HX Q) (<= FI 3) (<= EB 3) (or (not FE) JC) (<= 0 EL) (= HA DK) (= Y HM) (<= 0 DK) (<= B 15) (= GQ 800.0) (= CZ FH) (= HT EZ) (<= 0 CC) (or IB (not GN)) (= BO EA) (or (not CX) CO) (or (= 15 HC) (= 14 HC) (and (<= 0 HC) (<= HC 10))) (= FZ IF) (<= IV 2) (or (= 14 FD) (and (<= FD 10) (<= 0 FD)) (= 15 FD)) (<= CD 3) (or (not FC) IM) (or (and HL IP FR T V G EF HD DS AW CF BT FF GC) (not (= CY GL))) (= GS EC) (= BR DZ) (= CE P) (<= 0 FI) (= IU BH) (= DG ER) (or BP (not FN)) (or (= CY GL) (and HL IP FR T V G EF HD DS AW CF BT FF (not (= CY GL)) GC) (and (not (= CY GL)) (or (not IP) (not GC) (not BT) (not T) (not G) (not EF) (not HL) (not DS) (not V) (not CF) (not HD) (not FR) (not AW) (not FF)))) (= FO 4000.0) (or (not HG) K) (= BS 19) (<= 0 CM) (or (not CS) AP) (<= EE 6) (or DL (not GO)) (<= 0 BE) (= 2 GP) (= 50.0 GB) (= ES HF) (<= BE 2) (= EP GK) (= HE BI) (or (not AO) IY) (= IH AT) (= R CR) (<= DK 255) (or (not (= 0 DV)) (= EH 0)) (or I (not E)) (= ID AU) (<= A 9) (<= 0 CB) (<= DU 9) (or (= AE 126) (= AE 127) (and (<= AE 100) (<= 0 AE))) (= FX EQ) (= EM FG) (<= 0 IV) (<= 0 HV) (<= 0 EB) (= AM CA) (= JB (/ 3.0 2.0)) (or IG (not FQ)) (= S CP) (<= 0 GM) (= L BW) (or IQ (not HU)) (<= 0 N) (or CJ (not EN)) (<= GH 255) (= BB IR) (<= CB 7) (= AY DE) (= FL CH) (<= GM 658) (= Z IC) (<= 0 AK) (= ED (/ 3.0 2.0)) (<= HV 1023) (<= 0 GH) (or (not EJ) IW) (or (= 15 DT) (and (<= 0 DT) (<= DT 10)) (= 14 DT)) (<= FB 9) (= DD AR) (= E HK) (<= DB 15) (= IA GA) (= CT 500.0) (= HQ X) (= 2 IF) (= GX C) (<= AK 3) (= 2 BL) (<= EU 3) (= CU M) (<= DO 7) (<= CC 63) (= FV GU) (<= EL 63) (<= 0 DC) (= 50.0 AI) (<= CW 9) (or DW (not FW)) (= 4000.0 FA) (= EY HB) (= 20.0 CL) (= IN GE) (<= 0 CD) (= BU F) (= FM CI) (= DX BM) (= EI BF) (<= 0 GT) (<= GT 255) (= DQ DA) (or U (not AB)) (= DM 50.0) (or (not DH) IS) (or BX (not D)) (= 800.0 IJ) (= IK FS) (or AG (not GW)) (or HY (not (= CY GL))) (<= 0 AX) (= CG FU) (= EV HJ) (<= 0 DU) (<= N 1023) (<= 0 EU) (<= 0 HR) (<= CM 2) (<= 0 A) (= CN 20.0) (or (not EX) (= CY GL)) (<= DN 3) (<= 0 DB) (= FT DY) (= IT BK) (or (not HH) IO) (or DI (not ET)) (or (and (not GF) (not BT) FK) (and (not GF) EW (not BT)) (and (not GF) (not BT) JA) (and (not GF) (not BT) J) (and (not GF) (not BT) CQ) (and (not GF) (not BT) BZ) (and (not GF) (not BT) DF) (and (not GF) (not BT) HZ) (and (< T1 50.0) (or (and (not GG) (or (and (not J) (or (and (or (and (not BA) (or (and (or (and (or (and (not JA) (or (and (not EW) (or (and (or (and (not DF) (or (and (not EG) (or (and (not BZ) (or (and (or (and (or (and (not GF) (not BJ)) (and (not GF) BT)) (not AS)) (and (not GF) BT)) (not CQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not FK)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not HI)) (and (not GF) BT)) (not HZ)) (and (not GF) BT))) (and (not GF) BT)) (not BQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) (not BT) BJ) (and (not GF) (not BT) HI) (and (not GF) (not BT) GG) (and (or (and (not GG) (or (and (or (and (not BQ) (or (and (not BA) (or (and (not HZ) (or BT (and (not HI) (or (and (not JA) (or (and (not EW) (or (and (not FK) (or (and (or (and (or (and (not BZ) (or (and (or (and (or (not BJ) BT) (not AS)) BT) (not CQ)) BT)) BT) (not EG)) BT) (not DF)) BT)) BT)) BT)) BT)))) BT)) BT)) BT) (not J)) BT)) BT) (<= 50.0 T1)) (and (not GF) (not BT) AS) (and (not GF) (not BT) BQ) (and (not GF) (not BT) BA) (and (not GF) (not BT) EG)) (<= HR 3) (= II GR) (<= 0 DN) (= 1 GY) (<= 0 CW) (or CV (not H))))";
		final String expextedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Example for "ApplicationTerm cannot be cast to de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula"
	 */
	@Test
	public void plrTest6() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "B", "F", "oldB"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "A", "C", "D", "E", "oldC", "oldA"),
		};
		final String formulaAsString = "(forall ((v_idx_7 Int) (v_idx_8 Int) (v_idx_9 Int) (v_idx_12 Int) (v_idx_3 Int) (v_idx_10 Int) (v_idx_4 Int) (v_idx_11 Int) (v_idx_5 Int) (v_idx_6 Int) (v_idx_1 Int) (v_idx_2 Int)) (exists ((v_v_9_1 Int) (v_v_10_1 (Array Int Int)) (v_v_11_1 Int) (v_v_8_1 (Array Int Int)) (v_v_0_1 Int) (v_v_1_1 Int) (v_v_2_1 Int) (v_v_3_1 (Array Int Int)) (v_v_4_1 Int) (v_v_5_1 Int) (v_v_6_1 Int) (v_v_7_1 Int)) (and (= v_v_1_1 (select A v_idx_7)) (= v_v_0_1 (select D v_idx_4)) (= v_v_8_1 (select B v_idx_5)) (= (select F v_idx_9) v_v_3_1) (= v_v_11_1 (select v_v_10_1 v_idx_1)) (= (select v_v_3_1 v_idx_10) v_v_4_1) (= v_v_5_1 (select E v_idx_12)) (= v_v_7_1 (select oldC v_idx_3)) (= v_v_9_1 (select v_v_8_1 v_idx_11)) (= v_v_6_1 (select C v_idx_2)) (= v_v_10_1 (select oldB v_idx_6)) (= (select oldA v_idx_8) v_v_2_1))))";
		final String expextedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void moduloUnsound() {
		/*
		 * Example generated from MCR
		 *
		 * Notes: Happens already in quantifier pusher
		 */
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getBoolSort, "c"), };
		final String formulaAsString = "(forall ((g Int)) (or (not (or (and c (= g 1)) (and (not c) (= g 0)) )) (= 0 (mod g 256)) ) ) ";
		final String expextedResultAsString = "(not c)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void moduloUnsoundExists() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getBoolSort, "c"), };
		final String formulaAsString = "(exists ((g Int)) (and (or (and c (= g 1)) (and (not c) (= g 0)) ) (not (= 0 (mod g 256))) ) ) ";
		final String expextedResultAsString = "c";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expextedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divByZero() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "BK"), };
		final String formulaAsString = "(exists ((C Real) (A Real) (BD Real) (AK Int) (AP Int) (BH Int) (BC Int) (J Real) (M Real) (AN Int) (AW Int) (AT Int) (AF Int) (AD Real) (U Real) (S Real) (D Real) (O Int) (BG Int) (AA Real) (I Int) (AL Int) (V Real) (AJ Int) (AS Int) (L Real) (W Real) (AI Int) (AX Int) (AM Int) (AC Real) (K Real) (BJ Int) (T Int) (Z Real) (P Real) (Y Real) (AR Real) (B Real) (AG Int) (BE Int) (AZ Int) (E Bool) (AB Bool) (BB Int) (H Int) (AV Int) (AO Real) (BI Int) (N Real) (BA Int) (AQ Int) (R Real) (Q Real) (AY Int) (AH Int) (G Int) (F Real) (BF Int) (X Real) (AE Int) (AU Int)) (and (<= 0.0 P) (<= BI 255) (or (and (or AB (not E)) (= AO V)) (not (< AA (* 5.0 C))) (not E) (and (or (and (not AB) E) (and (not (= AO V)) E)) (< AA (* 5.0 C)))) (<= 0.0 N) (<= L 5100.0) (<= AK 15) (<= N 5100.0) (<= G 2) (<= Z 255.0) (<= C 255.0) (<= 0.0 Q) (<= 0 AK) (<= AU 253) (<= AL 255) (<= M 5100.0) (<= BJ 255) (<= 0.0 X) (<= 0.0 AA) (<= 0 AL) (<= AI 1023) (<= K 5100.0) (<= F 255.0) (<= AW 254) (<= 0 BI) (<= 0.0 Z) (or (and (<= 0 AN) (<= AN 240)) (= AN 254) (= AN 255)) (or (= AG 1023) (and (<= AG 1000) (or (<= 1 AG) (= AG 0)))) (<= V 65535.0) (or (= BC 14) (= BC 1) (= BC 2) (= BC 0)) (<= Y 255.0) (<= R 1310700.0) (<= B 255.0) (<= S 5100.0) (<= H 3) (<= 0 BJ) (<= D 255.0) (<= AT 1000) (or (and (or (not (< U AC)) (not (= I H)) (and (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U))) (= AO U))) (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U))) (= AO U)) (and (< BK 50.0) (or (and (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U))) (not (= I H))) (and (not (< U AC)) (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U)))))) (and (= I H) (< BK 50.0) (or (not (= AR (/ (* (+ (* (- 1.0) AO) U) (+ (* (- 1.0) S) R)) (+ (* (- 1.0) V) U)))) (not (= AO U))) (< U AC))) (<= 0.0 M) (<= AC 5000.0) (or (and (or (<= 1 AF) (= AF 0)) (<= AF 1000)) (= AF 1023)) (<= 0.0 C) (or (and (<= AS 201) (<= 1 AS)) (= AS 0)) (<= 0.0 J) (<= 0.0 AC) (<= Q 255.0) (<= A 255.0) (<= AA 5.0) (<= 0.0 R) (<= 0.0 S) (<= 0.0 U) (<= 0 AJ) (or (and (<= AH 254) (<= 1 AH)) (= 255 AH) (= 0 AH)) (<= 0.0 V) (<= AJ 255) (<= 0 G) (<= 0 T) (or (and (<= AV 1000) (<= 1 AV)) (= 0 AV)) (or (<= 1 AU) (= 0 AU)) (<= U 65535.0) (<= 0.0 B) (<= 0.0 F) (<= P 5100.0) (or (= BB 254) (and (<= 0 BB) (<= BB 100))) (<= J 5100.0) (<= 0 O) (<= 0.0 K) (<= 0.0 AD) (or (= 0 AZ) (= 1 AZ) (= 14 AZ)) (<= T 3) (<= BG 1023) (<= O 65535) (or (= 1022 AP) (= 1023 AP) (and (<= AP 1021) (<= 0 AP))) (<= X 255.0) (<= 0.0 L) (<= 0.0 D) (or (and (<= AM 240) (<= 0 AM)) (= 254 AM) (= 255 AM)) (or (and (<= AE 254) (<= 1 AE)) (= 0 AE) (= 255 AE)) (or (= BE 65535) (= BE 254) (= BE 65534) (and (<= BE 240) (<= 0 BE)) (= BE 255)) (or (and (<= BD 250.0) (<= 0.0 BD)) (= BD 254.0)) (or (and (<= 0 AX) (<= AX 1021)) (= 1022 AX)) (<= 0.0 A) (<= 0.0 W) (or (= 14 AY) (= 1 AY) (= 0 AY)) (<= W 255.0) (<= 0 AI) (<= 0 H) (or (and (<= 0 BF) (<= BF 240)) (= BF 65534) (= BF 254) (= BF 65535) (= BF 255)) (or (= 14 BA) (= 1 BA) (= 0 BA)) (or (= BH 1022) (= BH 1023) (and (<= BH 1021) (<= 0 BH))) (or (= 254 AQ) (= 255 AQ) (and (<= 0 AQ) (<= AQ 253))) (or (= 0 AT) (<= 1 AT)) (<= 0.0 Y) (<= AD 5000.0) (<= 0 AW) (<= 0 BG)))";
		final String expectedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divByZero2() {
		// it is the same formula as in divByZero but with other variable names
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2"), };
		final String formulaAsString = "(exists ((|adp_diag_ks_masse'| Real) (|adp_count_fast'| Real) (|s_mvb_Smartlightsensor_Sensorspannung'| Real) (|si_RLSs_01__RLS_Zaehler_LIN1'| Int) (|s_LS_Helligkeit_FW'| Int) (|so_RLS_01__LS_Helligkeit_FW_SCAN'| Int) (|s_mvb_Smartlightsensor_Licht'| Int) (|adp_lx_dawn_to_day'| Real) (|adp_lx_LHO_CHO_Schwelle'| Real) (|si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| Int) (|s_mvb_Helligkeit_Infrarot'| Int) (|s_mvb_Feuchtesensorik_Scheibentemperatur'| Int) (|si_FSs_01__FS_Taupunkt_LIN1'| Int) (|s_helligkeit_uin_mM_roh'| Real) (|adp_s_outmax'| Real) (|adp_s_inpmin'| Real) (|adp_diag_ks_versorgung'| Real) (|adp_lx_off_kombi'| Int) (|so_RLS_01__LS_Helligkeit_FW_KCAN'| Int) (|ai_helligkeit_uin'| Real) (|adp_Lichtsensor_Typ_SMART_LS'| Int) (|si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'| Int) (|adp_s_outmin'| Real) (|si_RLSs_01__LS_Helligkeit_IR_LIN1'| Int) (|s_mvb_Feuchtesensorik_relative_Luftfeuchte'| Int) (|adp_lx_fastcount'| Real) (|adp_step_fast'| Real) (|si_RLSs_01__LS_Helligkeit_FW_LIN1'| Int) (|s_mvb_Helligkeit_Sichtbar'| Int) (|si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'| Int) (|s_helligkeit_uin_mM'| Real) (|adp_lx_day_to_dawn'| Real) (|so_RLS_01__LS_Helligkeit_IR_SCAN'| Int) (|adp_sonnensensor_Typ'| Int) (|adp_t_ls_countmax'| Real) (|adp_lx_on'| Real) (|adp_t_ls_calc'| Real) (|s_ls_in'| Real) (|adp_count_slow'| Real) (|si_FSs_01__FS_Temp_Scheibe_LIN1'| Int) (|s_mvb_Sonnensensor_Sonnenintensitaet_links'| Int) (|s_mvb_Licht_ein_bei_Regen'| Int) (|adp_diag_qualifizierung_notlauf'| Bool) (|s_afl_error'| Bool) (|s_mvb_Smartlightsensor_Helligkeit'| Int) (|adp_Lichtsensor_Typ'| Int) (|s_mvb_Feuchtesensorik_Taupunkt'| Int) (|s_ls_anaout'| Real) (|so_RLS_01__LS_Helligkeit_IR_KCAN'| Int) (|adp_lx_off'| Real) (|s_mvb_RLS_Status'| Int) (|s_LS_Helligkeit_IR'| Int) (|adp_s_inpmax'| Real) (|adp_lx_tunnel'| Real) (|s_mvb_Licht_ein_bei_Autobahn'| Int) (|si_FSs_01__FS_Temp_Sensor_LIN1'| Int) (|adp_Feuchtesensor_Typ'| Int) (|adp_diag_unplausibel'| Real) (|s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| Int) (|adp_step_slow'| Real) (|si_FSs_01__FS_Luftfeuchte_rel_LIN1'| Int) (|s_mvb_Feuchtesensorik_Sensortemperatur'| Int)) (and (<= 0.0 |adp_lx_on'|) (<= |so_RLS_01__LS_Helligkeit_IR_KCAN'| 255) (or (and (or |s_afl_error'| (not |adp_diag_qualifizierung_notlauf'|)) (= |s_ls_anaout'| |adp_s_outmin'|)) (not (< |ai_helligkeit_uin'| (* 5.0 |adp_diag_ks_masse'|))) (not |adp_diag_qualifizierung_notlauf'|) (and (or (and (not |s_afl_error'|) |adp_diag_qualifizierung_notlauf'|) (and (not (= |s_ls_anaout'| |adp_s_outmin'|)) |adp_diag_qualifizierung_notlauf'|)) (< |ai_helligkeit_uin'| (* 5.0 |adp_diag_ks_masse'|)))) (<= 0.0 |adp_lx_off'|) (<= |adp_lx_fastcount'| 5100.0) (<= |si_RLSs_01__RLS_Zaehler_LIN1'| 15) (<= |adp_lx_off'| 5100.0) (<= |adp_Feuchtesensor_Typ'| 2) (<= |adp_t_ls_countmax'| 255.0) (<= |adp_diag_ks_masse'| 255.0) (<= 0.0 |adp_lx_tunnel'|) (<= 0 |si_RLSs_01__RLS_Zaehler_LIN1'|) (<= |s_mvb_Feuchtesensorik_Sensortemperatur'| 253) (<= |si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'| 255) (<= |adp_lx_LHO_CHO_Schwelle'| 5100.0) (<= |so_RLS_01__LS_Helligkeit_IR_SCAN'| 255) (<= 0.0 |adp_step_slow'|) (<= 0.0 |ai_helligkeit_uin'|) (<= 0 |si_Sensorik_Dimmung_01__KBI_Phototransistor_KCAN'|) (<= |si_RLSs_01__LS_Helligkeit_FW_LIN1'| 1023) (<= |adp_lx_day_to_dawn'| 5100.0) (<= |adp_diag_unplausibel'| 255.0) (<= |s_mvb_Helligkeit_Infrarot'| 254) (<= 0 |so_RLS_01__LS_Helligkeit_IR_KCAN'|) (<= 0.0 |adp_t_ls_countmax'|) (or (and (<= 0 |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'|) (<= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 240)) (= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 254) (= |si_SoSes_01__SoSe_SunInt_2D_Re_LIN1'| 255)) (or (= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 1023) (and (<= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 1000) (or (<= 1 |si_FSs_01__FS_Temp_Scheibe_LIN1'|) (= |si_FSs_01__FS_Temp_Scheibe_LIN1'| 0)))) (<= |adp_s_outmin'| 65535.0) (or (= |s_mvb_Smartlightsensor_Licht'| 14) (= |s_mvb_Smartlightsensor_Licht'| 1) (= |s_mvb_Smartlightsensor_Licht'| 2) (= |s_mvb_Smartlightsensor_Licht'| 0)) (<= |adp_t_ls_calc'| 255.0) (<= |adp_s_inpmax'| 1310700.0) (<= |adp_count_slow'| 255.0) (<= |adp_s_inpmin'| 5100.0) (<= |adp_Lichtsensor_Typ'| 3) (<= 0 |so_RLS_01__LS_Helligkeit_IR_SCAN'|) (<= |adp_diag_ks_versorgung'| 255.0) (<= |s_mvb_Feuchtesensorik_Scheibentemperatur'| 1000) (or (and (or (not (< |adp_s_outmax'| |s_helligkeit_uin_mM'|)) (not (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|)) (and (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|))) (= |s_ls_anaout'| |adp_s_outmax'|))) (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|))) (= |s_ls_anaout'| |adp_s_outmax'|)) (and (< SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2 50.0) (or (and (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|))) (not (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|))) (and (not (< |adp_s_outmax'| |s_helligkeit_uin_mM'|)) (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|)))))) (and (= |adp_Lichtsensor_Typ_SMART_LS'| |adp_Lichtsensor_Typ'|) (< SysRS_ADLSw_360_0_Glob_BndResponseUT_117_X2 50.0) (or (not (= |s_ls_in'| (/ (* (+ (* (- 1.0) |s_ls_anaout'|) |adp_s_outmax'|) (+ (* (- 1.0) |adp_s_inpmin'|) |adp_s_inpmax'|)) (+ (* (- 1.0) |adp_s_outmin'|) |adp_s_outmax'|)))) (not (= |s_ls_anaout'| |adp_s_outmax'|))) (< |adp_s_outmax'| |s_helligkeit_uin_mM'|))) (<= 0.0 |adp_lx_LHO_CHO_Schwelle'|) (<= |s_helligkeit_uin_mM'| 5000.0) (or (and (or (<= 1 |si_FSs_01__FS_Taupunkt_LIN1'|) (= |si_FSs_01__FS_Taupunkt_LIN1'| 0)) (<= |si_FSs_01__FS_Taupunkt_LIN1'| 1000)) (= |si_FSs_01__FS_Taupunkt_LIN1'| 1023)) (<= 0.0 |adp_diag_ks_masse'|) (or (and (<= |s_mvb_Feuchtesensorik_relative_Luftfeuchte'| 201) (<= 1 |s_mvb_Feuchtesensorik_relative_Luftfeuchte'|)) (= |s_mvb_Feuchtesensorik_relative_Luftfeuchte'| 0)) (<= 0.0 |adp_lx_dawn_to_day'|) (<= 0.0 |s_helligkeit_uin_mM'|) (<= |adp_lx_tunnel'| 255.0) (<= |adp_count_fast'| 255.0) (<= |ai_helligkeit_uin'| 5.0) (<= 0.0 |adp_s_inpmax'|) (<= 0.0 |adp_s_inpmin'|) (<= 0.0 |adp_s_outmax'|) (<= 0 |si_RLSs_01__LS_Helligkeit_IR_LIN1'|) (or (and (<= |si_FSs_01__FS_Temp_Sensor_LIN1'| 254) (<= 1 |si_FSs_01__FS_Temp_Sensor_LIN1'|)) (= 255 |si_FSs_01__FS_Temp_Sensor_LIN1'|) (= 0 |si_FSs_01__FS_Temp_Sensor_LIN1'|)) (<= 0.0 |adp_s_outmin'|) (<= |si_RLSs_01__LS_Helligkeit_IR_LIN1'| 255) (<= 0 |adp_Feuchtesensor_Typ'|) (<= 0 |adp_sonnensensor_Typ'|) (or (and (<= |s_mvb_Feuchtesensorik_Taupunkt'| 1000) (<= 1 |s_mvb_Feuchtesensorik_Taupunkt'|)) (= 0 |s_mvb_Feuchtesensorik_Taupunkt'|)) (or (<= 1 |s_mvb_Feuchtesensorik_Sensortemperatur'|) (= 0 |s_mvb_Feuchtesensorik_Sensortemperatur'|)) (<= |adp_s_outmax'| 65535.0) (<= 0.0 |adp_count_slow'|) (<= 0.0 |adp_diag_unplausibel'|) (<= |adp_lx_on'| 5100.0) (or (= |s_mvb_Smartlightsensor_Helligkeit'| 254) (and (<= 0 |s_mvb_Smartlightsensor_Helligkeit'|) (<= |s_mvb_Smartlightsensor_Helligkeit'| 100))) (<= |adp_lx_dawn_to_day'| 5100.0) (<= 0 |adp_lx_off_kombi'|) (<= 0.0 |adp_lx_day_to_dawn'|) (<= 0.0 |s_helligkeit_uin_mM_roh'|) (or (= 0 |s_mvb_Licht_ein_bei_Regen'|) (= 1 |s_mvb_Licht_ein_bei_Regen'|) (= 14 |s_mvb_Licht_ein_bei_Regen'|)) (<= |adp_sonnensensor_Typ'| 3) (<= |so_RLS_01__LS_Helligkeit_FW_KCAN'| 1023) (<= |adp_lx_off_kombi'| 65535) (or (= 1022 |s_LS_Helligkeit_FW'|) (= 1023 |s_LS_Helligkeit_FW'|) (and (<= |s_LS_Helligkeit_FW'| 1021) (<= 0 |s_LS_Helligkeit_FW'|))) (<= |adp_step_slow'| 255.0) (<= 0.0 |adp_lx_fastcount'|) (<= 0.0 |adp_diag_ks_versorgung'|) (or (and (<= |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'| 240) (<= 0 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|)) (= 254 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|) (= 255 |si_SoSes_01__SoSe_SunInt_2D_Li_LIN1'|)) (or (and (<= |si_FSs_01__FS_Luftfeuchte_rel_LIN1'| 254) (<= 1 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|)) (= 0 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|) (= 255 |si_FSs_01__FS_Luftfeuchte_rel_LIN1'|)) (or (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 65535) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 254) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 65534) (and (<= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 240) (<= 0 |s_mvb_Sonnensensor_Sonnenintensitaet_links'|)) (= |s_mvb_Sonnensensor_Sonnenintensitaet_links'| 255)) (or (and (<= |s_mvb_Smartlightsensor_Sensorspannung'| 250.0) (<= 0.0 |s_mvb_Smartlightsensor_Sensorspannung'|)) (= |s_mvb_Smartlightsensor_Sensorspannung'| 254.0)) (or (and (<= 0 |s_mvb_Helligkeit_Sichtbar'|) (<= |s_mvb_Helligkeit_Sichtbar'| 1021)) (= 1022 |s_mvb_Helligkeit_Sichtbar'|)) (<= 0.0 |adp_count_fast'|) (<= 0.0 |adp_step_fast'|) (or (= 14 |s_mvb_Licht_ein_bei_Autobahn'|) (= 1 |s_mvb_Licht_ein_bei_Autobahn'|) (= 0 |s_mvb_Licht_ein_bei_Autobahn'|)) (<= |adp_step_fast'| 255.0) (<= 0 |si_RLSs_01__LS_Helligkeit_FW_LIN1'|) (<= 0 |adp_Lichtsensor_Typ'|) (or (and (<= 0 |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'|) (<= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 240)) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 65534) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 254) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 65535) (= |s_mvb_Sonnensensor_Sonnenintensitaet_rechts'| 255)) (or (= 14 |s_mvb_RLS_Status'|) (= 1 |s_mvb_RLS_Status'|) (= 0 |s_mvb_RLS_Status'|)) (or (= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1022) (= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1023) (and (<= |so_RLS_01__LS_Helligkeit_FW_SCAN'| 1021) (<= 0 |so_RLS_01__LS_Helligkeit_FW_SCAN'|))) (or (= 254 |s_LS_Helligkeit_IR'|) (= 255 |s_LS_Helligkeit_IR'|) (and (<= 0 |s_LS_Helligkeit_IR'|) (<= |s_LS_Helligkeit_IR'| 253))) (or (= 0 |s_mvb_Feuchtesensorik_Scheibentemperatur'|) (<= 1 |s_mvb_Feuchtesensorik_Scheibentemperatur'|)) (<= 0.0 |adp_t_ls_calc'|) (<= |s_helligkeit_uin_mM_roh'| 5000.0) (<= 0 |s_mvb_Helligkeit_Infrarot'|) (<= 0 |so_RLS_01__LS_Helligkeit_FW_KCAN'|)))";
		final String expectedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divByZero3() {
		// Problem: by applying DER we get a division whose second argument is zero.
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "c"), };
		final String formulaAsString = " (exists ((x Real)) (and (= x c) (< 2.0 (/ 1.0 (- c x)))))";
		final String expectedResultAsString = "(< 2.0 (/ 1.0 0.0))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Simple test for DER.
	 */
	@Test
	public void derTest1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "b"), };
		final String formulaAsString = "(exists ((x Int)) (or (and (= x a) (= x 1)) (and (= x b) (= x 2))))";
		final String expectedResultAsString = "(or (= a 1) (= b 2))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntAffine1Exists() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(exists ((x Int)) (and (= (* x 2) t) (= (* x x x) 8)))";
		final String expectedResultAsString = "(and (= 8 (* (div t 2) (div t 2) (div t 2))) (= (mod t 2) 0))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntAffine1Forall() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(forall ((x Int)) (or (distinct (* x 2) t) (distinct (* x x x) 8)))";
		final String expectedResultAsString = "(or (not (= 8 (* (div t 2) (div t 2) (div t 2)))) (not (= (mod t 2) 0)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntPoly1Exists() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(exists ((x Int)) (and (= (* x a a a 2) t) (= (* x x x) 8)))";
		final String expectedResultAsString = "(let ((.cse2 (div t 2)) (.cse1 (= (mod t 2) 0)) (.cse0 (= a 0))) (or (and .cse0 .cse1 (= .cse2 0)) (let ((.cse4 (* a a a))) (and (= (let ((.cse3 (div .cse2 .cse4))) (* .cse3 .cse3 .cse3)) 8) (= (mod .cse2 .cse4) 0) .cse1 (not .cse0)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntPoly1Forall() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "a", "t"), };
		final String formulaAsString = "(forall ((x Int)) (or (not (= (* x a a a 2) t)) (not (= (* x x x) 8))))";
		final String expectedResultAsString = "(let ((.cse2 (= a 0)) (.cse0 (div t 2)) (.cse1 (not (= (mod t 2) 0)))) (and (or (not (= .cse0 0)) .cse1 (not .cse2)) (let ((.cse3 (* a a a))) (or (not (= (mod .cse0 .cse3) 0)) .cse2 (not (= (let ((.cse4 (div .cse0 .cse3))) (* .cse4 .cse4 .cse4)) 8)) .cse1))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	public void tirRealPoly1Exists() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "a", "b", "t", "hi", "lo"), };
		final String formulaAsString = "(exists ((x Int)) (and (<= (* x a a b (- 2)) t) (<= lo x) (<= x hi)))";
		final String expectedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}



	@Test
	public void critConsReform01() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "p2", "b", "p1", "a", "v_DerPreprocessor_1", "v_DerPreprocessor_3"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "memPtr"),
			};
		final String formulaAsString =
				"(= (select (store (store (store (store memPtr p2 b) p1 b) a v_DerPreprocessor_1) b v_DerPreprocessor_3) p1) b)";
		final String expectedResultAsString =
				"(= (select (store (store (store (store memPtr p2 b) p1 b) a v_DerPreprocessor_1) b v_DerPreprocessor_3) p1) b)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void selectOverStoreTest01() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "i", "k", "v"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString =
				"(forall ((a (Array Int Int))) (or (not (= (select (store a k v) i) 7)) (not (= i k))))";
		final String expectedResultAsString = "(or (not (= v 7)) (not (= i k)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void selectOverStoreTest02() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "i", "k", "v"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= (select (store a k v) i) 7) (= i k)))";
		final String expectedResultAsString = "(and (= v 7) (= i k))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void selectOverStoreTest03() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "i", "k", "v"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString =
				"(forall ((a (Array Int Int))) (or (not (= (select (store a k v) i) 7)) (= i k)))";
		final String expectedResultAsString = "(= i k)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void selectOverStoreTest04HiddenValueInformation() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getBoolSort, "B"),
				new FunDecl(SmtSortUtils::getIntSort, "i", "k", "v"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (or (not (= (select (store a k v) i) 7)) B) (= v 7)))";
		final String expectedResultAsString = "(and (= v 7) (or B (not (= i k))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void selectOverStoreBug01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "k", "i", "v") };
		final String formulaAsString = "(exists ((a (Array Int Bool))) (not (select (store (store a k true) i true) v)))";
		final String expectedResultAsString = "(and (not (= i v)) (not (= k v)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void selectOverStoreMultiDimSomeIndex() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "kOuter", "iOuter", "kInner", "iInner", "v") };
		final String formulaAsString = "(forall ((a (Array Int (Array Int Int)))) (or (not (= (select (select (store a kOuter (store (select a kOuter) kInner v)) iOuter) iInner) 7)) (not (= iOuter kOuter))))";
		final String expectedResultAsString = "(and (or (not (= iOuter kOuter)) (= iInner kInner)) (or (not (= iOuter kOuter)) (not (= v 7))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void contextInauguration() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "k", "i", "x", "y") };
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= k i) (or (= (+ 0 (select a k)) (+ x (select a i))) (= (+ 1 (select a k)) (+ y (select a i))))))";
		final String expectedResultAsString = "(and (= i k) (or (= y 1) (= x 0)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void antiDerPreprocessing() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "k", "v"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (not (= a b)) (= (store b k v) a)))";
		final String expectedResultAsString = "(not (= v (select b k)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void nestedSelfUpdateTest() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "i", "j", "k", "ai", "aj", "ak", "vi", "vj", "vk") };
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (not (= i k)) (= (select a i) ai) (= (select a j) aj) (= (select a k) ak)  (= (store (store (store a i vi) j vj) k vk) a)))";
		final String expectedResultAsString =
				"(let ((.cse0 (= ai vi)) (.cse5 (= j k)) (.cse1 (= ak vk)) (.cse2 (= i j)) (.cse3 (= aj vj)) (.cse4 (not (= i k)))) (or (and .cse0 .cse1 (not .cse2) .cse3 .cse4 (not .cse5)) (and .cse0 .cse1 (= aj vk) .cse4 .cse5) (and .cse1 .cse2 .cse3 .cse4 (= ai aj))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * TODO: Bug. Some array variable is not eliminated.
	 */
	@Test
	public void dimensionProblem() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "idx", "main_#t~mem8") };
		final String formulaAsString =
				"(exists ((|v_#memory_int_30| (Array Int (Array Int Int))) (|~#a~1.base| Int) (|~#a~1.offset| Int) (|main_#t~ret4| Int) (|v_#memory_$Pointer$.base_34| (Array Int (Array Int Int))) (|~#p1~1.base| Int) (|v_#memory_$Pointer$.offset_34| (Array Int (Array Int Int))) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (|#memory_$Pointer$.offset| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.offset_31| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.base_31| (Array Int (Array Int Int)))) "
						+ "(and (= (store |v_#memory_$Pointer$.offset_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.offset_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.offset_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.offset_31|) (not (= |~#p1~1.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0))) (= |#memory_$Pointer$.base| (store |v_#memory_$Pointer$.base_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select |v_#memory_$Pointer$.base_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) (select (select |#memory_$Pointer$.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0))))) (= (store |v_#memory_$Pointer$.offset_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select |v_#memory_$Pointer$.offset_31| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) (select (select |#memory_$Pointer$.offset| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0)))) |#memory_$Pointer$.offset|) (= (store |v_#memory_$Pointer$.base_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.base_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.base_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.base_31|) (not (= |~#p1~1.base| |~#a~1.base|)) (= |main_#t~mem8| (select (select (store (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0) (store (select (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0) 8)) (select (select |#memory_$Pointer$.base| |~#p1~1.base|) 0)) (select (select |#memory_$Pointer$.offset| |~#p1~1.base|) 0)))))";
		final String expectedResultAsString = "(= 8 |main_#t~mem8|)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void nestedStoresTest() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "i", "j", "k", "vi", "vj", "vk"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "b"),
			};
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (= (select a k) vk) (= (store (store a i vi) j vj) b)))";
		final String expectedResultAsString =
				"(let ((.cse2 (= vk (select b k))) (.cse0 (= vi (select b i))) (.cse3 (= i j)) (.cse1 (= vj (select b j))) (.cse4 (= j k))) (or (and .cse0 .cse1 .cse2) (and .cse3 .cse1 .cse2) (and (= i k) .cse0 .cse1) (and .cse0 .cse1 .cse4) (and .cse3 .cse1 .cse4)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void varStillThere02() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "nonMain_~dstPlusTwo~0.base", "nonMain_~dstPlusTwo~0.offset"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			};
		final String formulaAsString =
				"(exists ((|v_#memory_int_BEFORE_CALL_2| (Array Int (Array Int Int))) (|v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| Int) (|v_#Ultimate.C_memcpy_#t~loopctr6_8| Int) (v_prenex_1 Int) (|v_#Ultimate.C_memcpy_#t~loopctr6_9| Int) (|#Ultimate.C_memcpy_#t~mem7| Int)) (and (<= |v_#Ultimate.C_memcpy_#t~loopctr6_8| 0) (<= (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| 2) nonMain_~dstPlusTwo~0.offset) (= (select (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base) nonMain_~dstPlusTwo~0.offset) 23) (= |#memory_int| (store |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base (store (store (select |v_#memory_int_BEFORE_CALL_2| nonMain_~dstPlusTwo~0.base) (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| |v_#Ultimate.C_memcpy_#t~loopctr6_8|) v_prenex_1) (+ |v_#Ultimate.C_memcpy_dest.offset_AFTER_CALL_4| |v_#Ultimate.C_memcpy_#t~loopctr6_9|) |#Ultimate.C_memcpy_#t~mem7|))) (<= |v_#Ultimate.C_memcpy_#t~loopctr6_9| (+ |v_#Ultimate.C_memcpy_#t~loopctr6_8| 1))))";
		final String expectedResultAsString =
				"(= 23 (select (select |#memory_int| nonMain_~dstPlusTwo~0.base) nonMain_~dstPlusTwo~0.offset))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * TODO: Bug. Some array variable ist not eliminated.
	 */
	@Test
	public void caseShouldHaveBeenHandledByDerPqeBug04simplified01Forward() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "main_#t~mem8") };
		final String formulaAsString =
				"(exists ((|~#b~1.offset| Int) (|~#p1~1.base| Int) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (|#memory_$Pointer$.offset| (Array Int (Array Int Int))) (|main_#t~ret4| Int) (|~#b~1.base| Int) (|~#a~1.base| Int) (|~#a~1.offset| Int) (|#memory_int| (Array Int (Array Int Int)))) (and (= (select (select |#memory_int| (select (select |#memory_$Pointer$.base| |~#p1~1.base|) 0)) (select (select |#memory_$Pointer$.offset| |~#p1~1.base|) 0)) |main_#t~mem8|) (exists ((|v_#memory_$Pointer$.base_34| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.base_31| (Array Int (Array Int Int)))) (and (= |~#b~1.base| (select (select |v_#memory_$Pointer$.base_34| |~#p1~1.base|) 0)) (= |#memory_$Pointer$.base| (store |v_#memory_$Pointer$.base_31| |~#b~1.base| (store (select |v_#memory_$Pointer$.base_31| |~#b~1.base|) |~#b~1.offset| (select (select |#memory_$Pointer$.base| |~#b~1.base|) |~#b~1.offset|)))) (= (store |v_#memory_$Pointer$.base_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.base_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.base_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.base_31|))) (not (= |~#b~1.base| |~#p1~1.base|)) (exists ((|v_#memory_int_30| (Array Int (Array Int Int)))) (= |#memory_int| (store (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) |~#b~1.base| (store (select (store |v_#memory_int_30| |~#a~1.base| (store (select |v_#memory_int_30| |~#a~1.base|) |~#a~1.offset| |main_#t~ret4|)) |~#b~1.base|) |~#b~1.offset| 8)))) (exists ((|v_#memory_$Pointer$.offset_34| (Array Int (Array Int Int))) (|v_#memory_$Pointer$.offset_31| (Array Int (Array Int Int)))) (and (= (store |v_#memory_$Pointer$.offset_34| |~#a~1.base| (store (select |v_#memory_$Pointer$.offset_34| |~#a~1.base|) |~#a~1.offset| (select (select |v_#memory_$Pointer$.offset_31| |~#a~1.base|) |~#a~1.offset|))) |v_#memory_$Pointer$.offset_31|) (= |~#b~1.offset| (select (select |v_#memory_$Pointer$.offset_34| |~#p1~1.base|) 0)) (= (store |v_#memory_$Pointer$.offset_31| |~#b~1.base| (store (select |v_#memory_$Pointer$.offset_31| |~#b~1.base|) |~#b~1.offset| (select (select |#memory_$Pointer$.offset| |~#b~1.base|) |~#b~1.offset|))) |#memory_$Pointer$.offset|))) (not (= |~#p1~1.base| |~#a~1.base|))))";
		final String expectedResultAsString = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationRushingMountaineer01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#a~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"),
		};
		final String formulaAsString = "(exists ((|v_#valid_16| (Array (_ BitVec 32) (_ BitVec 1))) (|#t~string2.base| (_ BitVec 32))) (= (store (store (store |v_#valid_16| (_ bv0 32) (_ bv0 1)) |#t~string2.base| (_ bv1 1)) |~#a~0.base| (_ bv1 1)) |#valid|))";
		final String expectedResult = "(and (exists ((|#t~string2.base| (_ BitVec 32))) (and (= (_ bv1 1) (select |#valid| |#t~string2.base|)) (or (= (_ bv0 32) |#t~string2.base|) (= (_ bv0 1) (select |#valid| (_ bv0 32))) (= (_ bv0 32) |~#a~0.base|)))) (= (_ bv1 1) (select |#valid| |~#a~0.base|)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationRushingMountaineer01Reduced() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "a"),
		};
		final String formulaAsString = "(exists ((ax (Array (_ BitVec 32) (_ BitVec 1))) (kx (_ BitVec 32))) (= (store (store ax (_ bv0 32) (_ bv0 1)) kx (_ bv1 1)) a))";
		final String expectedResult = "(exists ((kx (_ BitVec 32))) (and (= (select a kx) (_ bv1 1)) (or (= kx (_ bv0 32)) (= (select a (_ bv0 32)) (_ bv0 1)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, !true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationRushingMountaineer02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#a~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"),
		};
		final String formulaAsString = "(exists ((|v_#valid_34| (Array (_ BitVec 32) (_ BitVec 1))) (|#t~string0.base| (_ BitVec 32)) (|#t~string3.base| (_ BitVec 32)) (|#t~string6.base| (_ BitVec 32)) (|#t~string9.base| (_ BitVec 32)) (|#t~string12.base| (_ BitVec 32)) (|#t~string15.base| (_ BitVec 32))) (= (store (store (store (store (store (store (store |v_#valid_34| (_ bv0 32) (_ bv0 1)) |#t~string0.base| (_ bv1 1)) |#t~string3.base| (_ bv1 1)) |#t~string6.base| (_ bv1 1)) |#t~string9.base| (_ bv1 1)) |#t~string12.base| (_ bv1 1)) |#t~string15.base| (_ bv1 1)) |#valid|))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationRushingMountaineer03() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~x0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"),
		};
		final String formulaAsString = "(exists ((|v_#valid_64| (Array (_ BitVec 32) (_ BitVec 1))) (|main_#t~malloc1.base| (_ BitVec 32)) (|main_#t~malloc2.base| (_ BitVec 32)) (|main_#t~malloc3.base| (_ BitVec 32))) (and (= (store (store (store (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base| (_ bv1 1)) |main_#t~malloc2.base| (_ bv1 1)) |main_#t~malloc3.base| (_ bv1 1)) |#valid|) (= (select (store (store (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base| (_ bv1 1)) |main_#t~malloc2.base| (_ bv1 1)) |main_#t~malloc3.base|) (_ bv0 1)) (= (_ bv0 1) (select (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base|))))";
		final String expectedResult = "(and (exists ((|main_#t~malloc1.base| (_ BitVec 32)) (|main_#t~malloc3.base| (_ BitVec 32)) (|main_#t~malloc2.base| (_ BitVec 32))) (and (= (select |#valid| |main_#t~malloc1.base|) (_ bv1 1)) (not (= main_~x0~0.base |main_#t~malloc3.base|)) (= (_ bv1 1) (select |#valid| |main_#t~malloc2.base|)) (not (= |main_#t~malloc3.base| |main_#t~malloc1.base|)) (not (= |main_#t~malloc2.base| |main_#t~malloc3.base|)) (not (= main_~x0~0.base |main_#t~malloc1.base|)) (= (select |#valid| |main_#t~malloc3.base|) (_ bv1 1)))) (= (select |#valid| main_~x0~0.base) (_ bv1 1)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationFourSeasonsTotalLandscaping() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "nonMain_~src~0.offset"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"),
		};
		final String formulaAsString = "(forall ((|#length| (Array (_ BitVec 32) (_ BitVec 32))) (|nonMain_~src~0.base| (_ BitVec 32))) (or (not (bvule (bvadd nonMain_~src~0.offset (_ bv2 32)) (select |#length| nonMain_~src~0.base))) (bvule nonMain_~src~0.offset (bvadd nonMain_~src~0.offset (_ bv2 32)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayEliminationBugBolivia() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x"), };
		final String formulaAsString = "(forall ((a1 (Array Int (Array Int Int))) (a2 (Array Int Int)) (a3 (Array Int Int)) (b Int)) (or (= x 0) (forall ((a4 (Array Int Int)) (c Int) (a5 (Array Int Int)) (a6 (Array Int (Array Int Int))) (d Int)) (or (not (= (store a2 c 4) a5)) (not (= d 0)) (not (= (select a3 c) 0)) (not (= (store a3 c 1) a4)) (not (= a6 (store a1 c (store (select a1 c) d 2)))) (= c 0) (not (< b c))))))";
		final String expectedResult = "(= x 0)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayTirCaretakersOfHonor() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "end", "i"), };
		final String formulaAsString = "(and (exists ((a (Array Int Int)) (v_i_9 Int)) (and (<= i (+ v_i_9 1)) (= 42 (select a end)) (<= v_i_9 0) (not (= 42 (select a v_i_9))))) (<= 0 end))";
		final String expectedResult = "(and (<= i 1) (< i (+ end 1)) (<= 0 end))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void arrayInnerDerPossibilityNotRepruducible() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_a", "v_arrayElimArr_1"),
				new FunDecl(SmtSortUtils::getIntSort, "main_y", "main_x", "i", "end"), };
		final String formulaAsString = "(exists ((v_arrayElimArr_2 (Array Int Int))) (and (or (and (= main_a v_arrayElimArr_2) (not (= main_y main_x))) (and (= main_y main_x) (= main_a v_arrayElimArr_1))) (or (= main_y main_x) (= (select v_arrayElimArr_2 main_x) 1)) (= (select v_arrayElimArr_1 main_y) 0) (or (not (= main_y main_x)) (= (+ (select v_arrayElimArr_2 main_y) 1) 0)) (< main_y main_x) (= (select v_arrayElimArr_2 main_y) 999) (or (= (select v_arrayElimArr_1 main_x) 0) (not (= main_y main_x))) (or (= (select v_arrayElimArr_2 main_y) (select v_arrayElimArr_2 main_x)) (not (= main_y main_x))) (or (= (select v_arrayElimArr_1 main_x) 1) (= main_y main_x))))";
		final String expectedResult = "(and (= (select v_arrayElimArr_1 main_x) 1) (= (select v_arrayElimArr_1 main_y) 0) (< main_y main_x) (= (select main_a main_x) 1) (= 999 (select main_a main_y)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void applyDistributivity() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p") };
		final String formulaAsString =
				"(forall ((x Int)) (or (and (p x) (p (+ x 1))) (and (not (= x 7)) (not (= x 8)))))";
		final String expectedResultAsString = "(and (p 7) (p 8) (p 9))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void infinityRestrictorDrop() {
		final FunDecl[] funDecls = {};
		final String formulaAsString = "(exists ((x Int)) (> (* 11 x) 17))";
		final String expectedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntegerDivisibilityExists() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p"),
				new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(exists ((x Int)) (and (p x) (= (* 2 x) y)))";
		final String expectedResultAsString = "(and (= 0 (mod y 2)) (p (div y 2)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derIntegerDivisibilityForall() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p"),
				new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(forall ((x Int)) (or (p x) (not (= (* 2 x) y))))";
		final String expectedResultAsString = "(or (not (= 0 (mod y 2))) (p (div y 2)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void derBitvectorFail01() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~g~0", "main_~a~0") };
		final String inputSTR = "(forall ((v_~g~0_24 (_ BitVec 32))) (or (not (= ~g~0 (bvadd v_~g~0_24 (_ bv4294967295 32)))) (= (bvadd main_~a~0 (_ bv1 32)) v_~g~0_24)))";
		final String expectedResult = "(= (bvadd main_~a~0 (_ bv1 32)) (bvadd ~g~0 (_ bv1 32)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsStrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (> x lo) (< x hi)))";
		final String expectedResult = "(< (+ lo 1) hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsNonstrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (>= x lo) (<= x hi)))";
		final String expectedResult = "(<= lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsMixed() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) (and (> x lo) (<= x hi)))";
		final String expectedResult = "(< lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallStrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (> x lo) (< x hi)))";
		final String expectedResult = "(< lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallNonstrict() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (>= x lo) (<= x hi)))";
		final String expectedResult = "(<= lo (+ hi 1))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirForallMixed() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) (or (> x lo) (<= x hi)))";
		final String expectedResult = "(<= lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void tirExistsAntiDer() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi", "di") };
		final String inputSTR = "(exists ((x Int)) (and (>= x lo) (<= x hi) (distinct x di)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterTIR() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) 	(and (> (* 7 x) lo ) (> hi x)))";
		final String expectedResult = "(<= (+ (div (+ (+ lo 1) (- 1)) 7) 2) hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessTIR() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) 	(and (< (* 7 x) hi ) (< lo x)))";
		final String expectedResult = "(<= (+ lo 1) (div (+ hi (- 1)) 7))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterEqTIR() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* 7 x) lo ) (> hi x)))";
		final String expectedResult = "(< (div (+ lo (- 1)) 7) hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessEqTIR() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* 7 x) hi ) (< lo x)))";
		final String expectedResult = "(< lo (+ (div (+ (+ hi 1) (- 1)) 7) 1))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvuleTIR() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvule x hi ) (bvule lo x)))";
		final String expectedResult = "(bvule lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}
	@Test
	public void bvugeTIR() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvuge hi x  ) (bvuge  x lo)))";
		final String expectedResult = "(bvuge hi lo)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgeTIR() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsge hi x  ) (bvsge x lo)))";
		final String expectedResult = "(bvsge hi lo)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsleTIR() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsle x hi ) (bvsle lo x)))";
		final String expectedResult = "(bvsle lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTIRSignedUnsignedMix() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsle x hi ) (bvule lo x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTir01() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi x) (bvsle lo x)))";
		final String expectedResult = "(bvslt lo hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTir02() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "mi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi mi) (bvsge mi x) (bvsle lo x)))";
		final String expectedResult = "(and (bvsle lo mi) (bvsgt hi mi))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSimplify() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "mi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi mi) (bvsge mi x) (bvsle hi x)))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTir03Strict() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvugt hi x) (bvult lo x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug01() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((main_~x~0 (_ BitVec 32))) (and (bvsgt main_~x~0 (_ bv100 32)) (not (= (bvadd main_~x~0 (_ bv4294967286 32)) (_ bv91 32))) (not (bvsgt main_~x~0 (_ bv101 32)))))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug02() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((main_~x~0 (_ BitVec 32))) (and (not (= (bvadd main_~x~0 (_ bv4294967286 32)) (_ bv91 32)))  (bvsge main_~x~0 (_ bv101 32))))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug03strict() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (not (=  y x)) (bvule lo x) (bvult x hi) (bvule lo y) (bvult y hi)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug04nonstrict() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (not (=  y x)) (bvule lo x) (bvule x hi) (bvule lo y) (bvult y hi)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionExistsLowerUnsigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvult x a) (bvugt b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionExistsLowerSigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvslt x a) (bvsgt b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionExistsUpperUnsigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvugt x a) (bvult b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionExistsUpperSigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt x a) (bvslt b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionForallLowerUnsigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvule x a) (bvuge b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionForallLowerSigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvsle x a) (bvsge b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionForallUpperUnsigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvuge x a) (bvule b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirSingleDirectionForallUpperSigned() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvsge x a) (bvsle b x)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBugSingleDirectionAndAntiDer() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "c" , "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvult x c) (distinct x b)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug06LimitedDomain() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort1, "c") };
		final String inputSTR = "(exists ((x (_ BitVec 1)) (y (_ BitVec 1))) (and (not (= x y)) (not (= x c)) (not (= y c))))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirBug07() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~a~0", "main_~b~0") };
		final String inputSTR = "(forall ((|main_#t~post2| (_ BitVec 32)) (main_~i~0 (_ BitVec 32)) (|v_main_#t~post2_11| (_ BitVec 32)) (|v_main_#t~ret1_14| (_ BitVec 32)) (v_main_~b~0_19 (_ BitVec 32))) (or (bvult v_main_~b~0_19 main_~a~0) (bvult (bvadd (bvneg v_main_~b~0_19) main_~a~0) (_ bv1 32)) (not (bvult main_~i~0 main_~a~0)) (and (or (= |v_main_#t~ret1_14| (_ bv0 32)) (not (= (bvadd v_main_~b~0_19 (_ bv4294967295 32)) main_~b~0))) (or (not (= |v_main_#t~ret1_14| (_ bv0 32))) (not (= v_main_~b~0_19 main_~b~0)) (not (= |main_#t~post2| |v_main_#t~post2_11|))))))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirOffsetBug01() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvuge x a) (bvule x b)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvTirHospitalized() {
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "A", "q", "r") };
		final String inputSTR = "(forall ((B (_ BitVec 32))) (= A (bvadd (bvmul q B) r)))";
		final String expectedResult = inputSTR;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterTIRNegativeCoef() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) 	(and (> (* (- 7) x) hi ) (< lo x)))";
		final String expectedResult = "(<= (+ lo 2) (div (+ (+ hi 1) (- 1)) (- 7)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessTIRNegativeCoef() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(exists ((x Int)) 	(and (< (* (- 7) x) lo ) (> hi x)))";
		final String expectedResult = "(<= (+ (div (+ lo (- 1)) (- 7)) 1) hi)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterEqTIRNegativeCoef() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) 	(or (>= (* (- 7) x) hi ) (> x lo)))";
		final String expectedResult = "(< lo (div (+ hi (- 1)) (- 7)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lessEqTIRNegativeCoef() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi") };
		final String inputSTR = "(forall ((x Int)) 	(or (<= (* (- 7) x) lo ) (> hi x)))";
		final String expectedResult = "(< (div (+ (+ lo 1) (- 1)) (- 7)) (+ hi 1))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void antiDerTirExist() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi", "y") };
		final String inputSTR = "(exists ((x Int)) (and	(not(=(* 4 x) y)) (> x lo) (< x hi)) )";
		final String expectedResult =
				"(or (and (<= (+ lo 2) hi) (<= (+ lo 1) (div (+ y (- 1)) 4))) (and (<= (+ lo 2) hi) (<= (+ (div y 4) 2) hi)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void antiDerTirForall() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "lo", "hi", "y") };
		final String inputSTR = "(forall ((x Int)) (or	(=(* 4 x) y) (> x lo) (< x hi))  )";
		final String expectedResult =
				"(and (or (< lo hi) (< lo (+ (div y 4) 1))) (or (< (div (+ y (- 1)) 4) hi) (< lo hi)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, inputSTR, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bugTirAntiDer() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "b") };
		final String formulaAsString = "(exists ((a Int)) (and (> (* 4 a) b ) (< a 3) (< b 12)))";
		final String expectedResultAsString = "(and (< b 12) (exists ((a Int)) (and (< a 3) (> (* 4 a) b))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void bugTirAntiDer02() {
		final FunDecl funDecl = new FunDecl(SmtSortUtils::getIntSort, "a");
		final String formulaAsString =
				"(exists ((x Int)) (and (not (= (+ (* x (- 256)) 1) 0)) (>= x a) (<= x a) (= a 0)))";
		final String expextedResultAsString = "(= a 0)";
		QuantifierEliminationTest.runQuantifierEliminationTest(new FunDecl[] { funDecl }, formulaAsString, expextedResultAsString, true, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void omegaTestRequired01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(exists ((x Int) ) (and (<= (* 256 x) 93) (<= (- c 7) (* 256 x))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(<= c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void omegaTest02ProgVerifSheet10Ex04Square() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "square_res", "square_odd", "square_li", "square_i") };
		final String formulaAsString = "(forall ((aux_div_v_square_res_12_49 Int) (aux_mod_v_square_res_12_49 Int) (v_square_i_11 Int)) (or (< (+ (* 2 aux_div_v_square_res_12_49) aux_mod_v_square_res_12_49) (+ square_res (* 2 square_odd))) (not (<= v_square_i_11 (+ square_i 1))) (> 0 aux_mod_v_square_res_12_49) (<= v_square_i_11 aux_div_v_square_res_12_49) (>= aux_mod_v_square_res_12_49 2)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void omegaTest03calloc02() {
		final FunDecl[] funDecls = { };
		final String formulaAsString = "(exists ((|v_#Ultimate.meminit_#sizeOfFields_AFTER_CALL_3| Int) (|v_#Ultimate.meminit_#t~loopctr3_20| Int) (|v_#Ultimate.meminit_#t~loopctr3_BEFORE_RETURN_3| Int) (|v_#Ultimate.meminit_#product_AFTER_CALL_3| Int)) (and (<= |v_#Ultimate.meminit_#t~loopctr3_20| 0) (not (< |v_#Ultimate.meminit_#t~loopctr3_BEFORE_RETURN_3| |v_#Ultimate.meminit_#product_AFTER_CALL_3|)) (<= 12 |v_#Ultimate.meminit_#product_AFTER_CALL_3|) (<= |v_#Ultimate.meminit_#sizeOfFields_AFTER_CALL_3| 4) (<= |v_#Ultimate.meminit_#t~loopctr3_BEFORE_RETURN_3| (+ (* 2 |v_#Ultimate.meminit_#sizeOfFields_AFTER_CALL_3|) |v_#Ultimate.meminit_#t~loopctr3_20|))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
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
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lraSchollSmt08Rnd4_15() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getRealSort, "x1") };
		final String formulaAsString = "(exists ((?y1 Real)) (exists ((?y2 Real)) (and (exists ((?y3 Real)) (exists ((?y4 Real)) (or (and (or (<= 7.0 (+ (* 73.0 ?y2) (* 56.0 ?y3) (* 13.0 ?y4) (* 51.0 x1) (* 15.0 ?y1))) (not (= 51.0 (+ (* ?y2 (- 62.0)) (* ?y4 (- 61.0)))))) (or (not (= (- 66.0) (+ (* ?y2 (- 12.0)) (* ?y3 (- 71.0)) (* ?y4 8.0) (* ?y1 (- 46.0))))) (not (= (- 66.0) (+ (* ?y2 (- 14.0)) (* ?y3 (- 77.0)) (* ?y4 65.0) (* x1 86.0) (* ?y1 (- 85.0))))))) (and (not (= 33.0 (+ (* ?y2 (- 95.0)) (* ?y3 (- 81.0)) (* ?y4 74.0) (* x1 10.0) (* ?y1 76.0)))) (= (- 85.0) (* ?y1 (- 25.0)))) (and (<= (+ (* 21.0 ?y4) (* 57.0 ?y1)) (+ (* 53.0 ?y2) (* 8.0 ?y3) (* 6.0 x1) 5.0)) (= 11.0 (+ (* ?y2 (- 98.0)) (* ?y3 (- 95.0)) (* ?y4 80.0) (* x1 (- 19.0)) (* ?y1 (- 16.0)))))))) (or (forall ((?y3 Real)) (and (or (not (= 36.0 (+ (* ?y2 (- 2.0)) (* ?y3 42.0) (* x1 7.0)))) (and (<= (+ (* 81.0 ?y2) (* 29.0 ?y1)) (+ (* 44.0 ?y3) (* 19.0 x1) 84.0)) (forall ((?y4 Real)) (and (<= (+ (* 14.0 ?y3) (* 54.0 ?y4) (* 48.0 x1) (* 77.0 ?y1) 64.0) (* 46.0 ?y2)) (<= 0.0 (+ (* 29.0 ?y3) (* 39.0 ?y4) (* 70.0 x1) 32.0)))) (= (- 30.0) (+ (* x1 9.0) (* ?y1 (- 4.0))))) (and (<= (* 17.0 ?y1) (* 11.0 x1)) (< (* 52.0 x1) (+ (* 66.0 ?y2) (* 74.0 ?y3) (* 46.0 ?y1) 25.0)))) (or (< (+ (* 46.0 ?y1) 80.0) (+ (* 4.0 ?y2) (* 34.0 ?y3) (* 32.0 x1))) (and (< 80.0 (* 59.0 ?y1)) (not (= 0.0 (+ (* ?y2 (- 40.0)) (* ?y3 (- 55.0)) (* x1 (- 35.0)))))) (and (or (= (- 24.0) (+ (* ?y2 (- 88.0)) (* ?y3 95.0))) (< (+ (* 37.0 ?y2) (* 15.0 ?y3) (* 63.0 ?y1)) (+ (* 27.0 x1) 79.0))) (or (<= (+ (* 41.0 ?y2) ?y1) (* 62.0 x1)) (<= (+ (* 79.0 x1) (* 74.0 ?y1)) (+ (* 17.0 ?y2) (* 10.0 ?y3) 14.0)))) (< (+ (* 21.0 ?y2) (* 30.0 ?y1)) (+ (* 77.0 ?y3) (* 100.0 x1) 19.0))))) (and (not (= (- 33.0) (+ (* ?y2 61.0) (* x1 (- 3.0)) (* ?y1 31.0)))) (exists ((?y4 Real)) (and (<= (+ (* 32.0 ?y4) (* 35.0 ?y1)) (* 84.0 x1)) (not (= 23.0 (+ (* ?y4 (- 21.0)) (* x1 53.0) (* ?y1 8.0)))) (or (<= (* 53.0 ?y2) (* 94.0 x1)) (<= (+ (* 94.0 ?y2) (* 50.0 ?y4) 69.0) (* 55.0 x1))) (or (and (= (- 63.0) (+ (* ?y2 (- 22.0)) (* ?y4 37.0) (* x1 (- 9.0)) (* ?y1 89.0))) (< 35.0 (+ (* 100.0 ?y2) (* 10.0 x1)))) (< (+ (* 88.0 ?y2) (* 2.0 ?y1)) (+ (* 31.0 x1) 46.0))))) (exists ((?y4 Real)) (and (<= (+ (* 82.0 ?y4) (* 88.0 x1)) (+ (* 39.0 ?y1) 95.0)) (< 0.0 (+ (* 86.0 ?y1) 21.0)))) (exists ((?y4 Real)) (and (= (- 93.0) (+ (* ?y4 75.0) (* x1 (- 19.0)))) (<= (+ ?y4 (* 38.0 x1) (* 15.0 ?y1)) (* 38.0 ?y2)))) (< (* 91.0 ?y1) 0.0))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void lraSchollSmt08Rnd4_15Red() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getRealSort, "x1", "?y2", "?y3", "?y4") };
		final String formulaAsString = "(exists ((?y1 Real)) (and (not (= (- 66.0) (+ (* ?y2 (- 14.0)) (* ?y3 (- 77.0)) (* ?y4 65.0) (* x1 86.0) (* ?y1 (- 85.0)))))  (or (forall ((?y3 Real)) (<= (+ (* 41.0 ?y2) ?y1) (* 62.0 x1)) ) (and (< 0.0 (+ (* 86.0 ?y1) 21.0)) (< (* 91.0 ?y1) 0.0)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void multiTechniques() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= x b) (<= y x) (<= a y)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(<= a b)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	/**
	 * Reveals conceptual bug in {@link QuantifierPusher}. We have to apply rules
	 * for nested quantifiers after elimination techniques.
	 */
	public void resolvedQuantifierNesting() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= x b) (exists ((z Int)) (and (<= y x) (= (* y y z z) 0)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "true", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void uselessOuterQuantifier() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript)}, SmtSortUtils.getBoolSort(mMgdScript));
		final String formulaAsString = "(exists ((x Int) ) (forall ((y Int) (z Int)) (or (p z) (and (p x) (distinct y 0) ))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(forall ((z Int)) (p z))", false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void innerPush() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "a", "b") };
		mScript.declareFun("p", new Sort[] { SmtSortUtils.getIntSort(mMgdScript)}, SmtSortUtils.getBoolSort(mMgdScript));
		final String formulaAsString = "(exists ((x Int) ) (and (<= a x) (forall ((y Int) (z Int)) (or (p z) (and (p x) (distinct y 0))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(forall ((z Int)) (p z))", false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void wildboellen() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "z", "y") };
		final String formulaAsString = "(forall ((x Int) ) (or (= 0 x) (not (= (* z (+ x 1)) y))))";
		final String expectedResult = "(let ((.cse0 (+ y (- z))) (.cse1 (= 0 z))) (and (or (not (= 0 .cse0)) (not .cse1)) (or (= 0 (div .cse0 z)) (not (= 0 (mod (+ y (* z (- 1))) z))) .cse1)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void oppenau() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getIntSort, "square"),
			new FunDecl(SmtSortUtils::getIntSort, "x", "y"),
		};
		final String formulaAsString = "(exists ((v_proc_i_AFTER_CALL_1 Int) (v_f_4 Int) (v_proc_res_BEFORE_RETURN_1 Int)) (and (exists ((v_f_4 Int)) (<= (+ x (square v_f_4)) v_proc_i_AFTER_CALL_1)) (<= v_proc_res_BEFORE_RETURN_1 y) (<= (+ x (square v_f_4)) v_proc_i_AFTER_CALL_1) (<= v_proc_i_AFTER_CALL_1 v_proc_res_BEFORE_RETURN_1)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod01Exists() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(exists ((x Int) ) (and (<= c x) (<= x 100) (= 7 (mod x 256) )))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(<= c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod01Forall() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "c") };
		final String formulaAsString = "(forall ((x Int) ) (or (> c x) (> x 100) (not (= 7 (mod x 256) ))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, "(> c 7)", true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod02Uneliminatable() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(new SortConstructor[] { SmtSortUtils::getIntSort }, SmtSortUtils::getBoolSort, "p"),
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((x Int) (y Int)) (and (= (div x 7) (div (+ y 1) 5)) (p x) (p y)))";
		final String expectedResult = "(exists ((x Int) (y Int)) (and (= (div x 7) (div (+ y 1) 5)) (p x) (p y)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mod03Nutz01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(exists ((x Int)) (and (<= (mod x 4294967296) 0) (= y (mod x 4294967296))))";
		final String expectedResult = "(let ((.cse0 (* y (- 1)))) (and (<= (div y (- 4294967296)) (div .cse0 4294967296)) (<= 0 y) (< y 4294967296) (<= (div y (- 4294967296)) (div (+ .cse0 4294967295) 4294967296))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sandmanForward() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "c"), };
		final String formulaAsString = "(exists ((x Int)) (and (<= (mod x 256) (+ c 256)) (not (<= (mod x 256) 127))))";
		final String expectedResult = "(and (<= 0 (div (+ c 256) 256)) (<= 0 (+ c 256)) (<= 0 (div (+ c 128) 256)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sandmanForwardStep() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "c"), };
		final String formulaAsString = "(exists ((x Int)) (and (< x 256) (not (<= (mod x 256) 127)) (<= x (+ c 256)) (<= 0 x)))";
		final String expectedResult = "(and (<= 0 (div (+ c 256) 256)) (<= 0 (+ c 256)) (<= 0 (div (+ c 128) 256)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void PointerInBooleanExpression() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "main_~a~0"), };
		final String formulaAsString = "(exists ((main_~p~0.offset Int) (|main_#t~malloc0.base| Int)) (and (not (= 0 |main_#t~malloc0.base|)) (or (and (= 0 main_~p~0.offset) (= 0 |main_#t~malloc0.base|) (= 1 main_~a~0)) (and (= 0 main_~a~0) (or (not (= 0 main_~p~0.offset)) (not (= 0 |main_#t~malloc0.base|)))))))";
		final String expectedResult = "(= 0 main_~a~0)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void choirNightTrezor02WhiteRussia() {
		final FunDecl[] funDecls = new FunDecl[] {};
		final String formulaAsString = "(exists ((main_~a~0 Int) (main_~b~0 Int)) (and (<= 1 (mod (+ (* main_~b~0 4294967295) main_~a~0) 4294967296)) (= 0 main_~b~0) (not (< (mod main_~b~0 4294967296) (mod main_~a~0 4294967296))) (<= (mod main_~a~0 4294967296) 1)))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor03Gearshiftnut() {
		final FunDecl[] funDecls = new FunDecl[] {};
		final String formulaAsString = "(forall ((v_main_~i~0_6 Int) (v_main_~b~0_8 Int)) (or (< (div (+ (* (mod v_main_~i~0_6 4294967296) (- 1)) (* v_main_~b~0_8 (- 4294967295))) (- 4294967296)) (+ (div (+ (* v_main_~b~0_8 4294967295) (- 4294967296)) 4294967296) 2)) (not (and (= 0 v_main_~i~0_6) (= 0 v_main_~b~0_8)))))";
		final String expectedResult = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "b", "i"),
		};
		final String formulaAsString = "(and (forall ((v_prenex_1 Int)) (or (not (< i v_prenex_1)) (< b v_prenex_1) (< (mod (+ (* b 4294967295) v_prenex_1) 4294967296) 1))) (forall ((a Int)) (or (< (mod (+ b 1) 4294967296) a) (< (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) a) 4294967296) 1) (not (< i a)))))";
		final String expectedResultAsStringNotSimplified = "(let ((.cse3 (+ i 1))) (and (let ((.cse4 (+ b 1))) (let ((.cse2 (mod .cse4 4294967296))) (let ((.cse0 (* .cse2 (- 1))) (.cse1 (mod .cse4 4294967296))) (or (< (div (+ .cse0 (* .cse1 (- 4294967295))) (- 4294967296)) (+ (div (+ i (* .cse1 4294967295) (- 4294967295)) 4294967296) 2)) (< .cse2 .cse3) (< (div (+ .cse0 (* .cse1 (- 4294967295)) (- 1)) (- 4294967296)) (+ (div (+ i (* .cse1 4294967295) (- 4294967295)) 4294967296) 2)))))) (or (< b (+ (div (+ (* b 4294967295) i (- 4294967295)) 4294967296) 1)) (< b .cse3) (< b (+ (div (+ (* b 4294967295) i (- 4294967295)) 4294967296) 2)))))";
		final String expectedResultAsString = "(and (< b (+ (div (+ (* b 4294967295) i (- 4294967295)) 4294967296) 2)) (let ((.cse1 (+ b 1))) (let ((.cse0 (mod .cse1 4294967296))) (< (div (+ (* .cse0 (- 4294967295)) (* (mod .cse1 4294967296) (- 1))) (- 4294967296)) (+ (div (+ (* .cse0 4294967295) i (- 4294967295)) 4294967296) 2)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor01simpler() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "b", "i"),
		};
		final String formulaAsString = "(forall ((a Int)) (or (not (< i a)) (< (mod (+ b 1) 4294967296) a) (< (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) a) 4294967296) 1)))";
		final String expectedResultAsStringNotSimplified = "(let ((.cse3 (+ b 1))) (let ((.cse0 (mod .cse3 4294967296))) (let ((.cse1 (* .cse0 (- 1))) (.cse2 (mod .cse3 4294967296))) (or (< .cse0 (+ i 1)) (< (div (+ .cse1 (* .cse2 (- 4294967295)) (- 1)) (- 4294967296)) (+ (div (+ i (* .cse2 4294967295) (- 4294967295)) 4294967296) 2)) (< (div (+ .cse1 (* .cse2 (- 4294967295))) (- 4294967296)) (+ (div (+ i (* .cse2 4294967295) (- 4294967295)) 4294967296) 2))))))";
		final String expectedResultAsString = "(let ((.cse1 (+ b 1))) (let ((.cse0 (mod .cse1 4294967296))) (< (div (+ (* .cse0 (- 4294967295)) (* (mod .cse1 4294967296) (- 1))) (- 4294967296)) (+ (div (+ (* .cse0 4294967295) i (- 4294967295)) 4294967296) 2))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor01simplermore() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "b", "i"),
		};
		final String formulaAsString = "(exists ((a Int)) (and (>= (mod (+ b 1) 4294967296) a) (>= (mod (+ (* (mod (+ b 1) 4294967296) 4294967295) a) 4294967296) 1)))";
		final String expectedResultAsString = "true";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor02OilInMuseeum() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "b", "i"),
		};
		final String formulaAsString = "(forall ((aux_div_aux_mod_v_main_~i~0_16_31_42 Int) (aux_div_v_main_~c~0_6_30 Int) (aux_div_v_main_~i~0_16_31 Int) (aux_div_main_~a~0_26 Int)) (let ((.cse3 (* 4294967296 aux_div_aux_mod_v_main_~i~0_16_31_42)) (.cse2 (* 4294967296 aux_div_v_main_~c~0_6_30)) (.cse1 (* 4294967296 aux_div_main_~a~0_26)) (.cse0 (* 4294967296 aux_div_v_main_~i~0_16_31))) (or (< 0 .cse0) (< .cse1 (+ .cse2 .cse0)) (< .cse1 (+ .cse3 .cse2 .cse0 1)) (<= (+ .cse1 4294967295) .cse2) (<= (+ .cse3 .cse0 4294967296) 0) (< 0 (+ .cse3 .cse0)) (<= (+ .cse1 4294967296) .cse2) (<= (+ .cse2 4294967296) .cse1) (<= (+ .cse0 4294967296) 0))))";
		final String expectedResultAsString = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void scholl_smt08_model_model_6_62() {

		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getBoolSort, "bool.b8", "bool.b6", "bool.b7", "bool.b10", "bool.b23", "bool.b12", "bool.b22", "bool.b14", "bool.b5"),
			new FunDecl(SmtSortUtils::getRealSort, "x3", "x4", "x5"),
		};
		final String formulaAsString = "(forall ((?lambda Real)) (or (exists ((?lambdaprime Real)) (and (not (and (not (<= 10.0 (+ ?lambdaprime x5))) (not (and (not bool.b5) (not bool.b6) (not bool.b7) (not bool.b22) (not (and (not (<= 4100.0 (+ (* 20.0 ?lambdaprime) x4))) (not (<= 20.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))))))) (not (and (not bool.b5) bool.b6 (not (and (not (<= 20.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))) (not (<= 4910.0 (+ (* 20.0 ?lambdaprime) x4))))) (not bool.b7) (not bool.b22))) (not (and (not bool.b5) (not (and (not (<= 4500.0 (+ (* 20.0 ?lambdaprime) x4))) (not (<= 20.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))))) bool.b7 (not bool.b6) (not bool.b22))))) (<= 0.0 ?lambdaprime) (<= ?lambdaprime ?lambda))) (not (and (not bool.b22) (not (and (not (and (not bool.b6) bool.b5)) (not bool.b7))) (not (and (not (and (not (and (not bool.b23) (not (and (not (and (not (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0))) (not (and (not (and (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8))))) (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) 610.0) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 30.0) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not bool.b10) (not bool.b8))) (not (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0))))) (<= 10.0 (+ ?lambda x5)))))) (not (and (not (and (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 7.0 2.0) x5) 1165.0)) (not (and (not (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 7.0 2.0) x5) 688.0))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not bool.b10) (not bool.b8))))) (not (and (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 7.0 2.0) x5) 688.0)) (not (and (not (and (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8))))) (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) 610.0) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 30.0) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not bool.b10) (not bool.b8))) (not (<= (+ (* 2.0 ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0))))) (<= 10.0 (+ ?lambda x5)))))))) (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0)))))))) bool.b6 (not (and (not (and (<= 10.0 (+ ?lambda x5)) (not (and (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 0.0) (not (and (not bool.b5) (not (<= (+ (* 20.0 ?lambda) x4) 4820.0)))))) (not (and (not (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 0.0)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* 3.0 x5)) 50.0) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 40.0))))))) bool.b23)))) bool.b7)))) (< ?lambda 0.0)))";
		final String expectedResultAsString = "(let ((.cse17 (not bool.b5)) (.cse18 (not bool.b7))) (or (let ((.cse26 (* (/ 1.0 20.0) x4))) (let ((.cse1 (not bool.b6)) (.cse16 (not bool.b22)) (.cse25 (<= 225.0 .cse26)) (.cse20 (<= 205.0 .cse26)) (.cse21 (<= 40.0 (* 2.0 x3))) (.cse22 (<= 10.0 x5))) (let ((.cse23 (<= (/ 491.0 2.0) .cse26)) (.cse19 (and (or .cse20 .cse1 .cse21 .cse22) (or .cse20 .cse21 .cse16 .cse22) (or .cse20 bool.b7 .cse21 .cse22) (or .cse20 .cse21 .cse22 .cse25) (or .cse17 .cse20 .cse21 .cse22)))) (let ((.cse10 (or .cse18 .cse19)) (.cse11 (or .cse16 .cse19)) (.cse13 (or .cse17 .cse20 .cse21 .cse22 .cse23)) (.cse6 (or .cse20 .cse21 .cse16 .cse22 .cse23)) (.cse7 (or .cse20 .cse21 .cse22 .cse23 .cse25)) (.cse8 (or .cse17 .cse19)) (.cse9 (or .cse20 .cse1 .cse21 .cse22 .cse23)) (.cse15 (let ((.cse24 (and (or .cse1 .cse22) (or .cse17 .cse22) (or .cse21 .cse22 .cse25) (or bool.b7 .cse22) (or .cse16 .cse22)))) (and (or .cse17 .cse21 .cse22 .cse23) (or .cse16 .cse24) (or .cse18 .cse24) (or .cse1 .cse21 .cse22 .cse23) (or .cse21 .cse22 .cse23 .cse25) (or .cse21 .cse16 .cse22 .cse23) (or .cse17 .cse24) (or bool.b7 .cse21 .cse22 .cse23) (or bool.b6 .cse24)))) (.cse12 (or .cse20 bool.b7 .cse21 .cse22 .cse23)) (.cse14 (or bool.b6 .cse19))) (let ((.cse0 (and (or .cse15 .cse18) (or .cse15 .cse16) .cse10 .cse11 .cse13 .cse6 .cse7 (or .cse15 .cse1) .cse8 .cse9 (or .cse17 .cse15) .cse12 .cse14))) (and (or bool.b7 .cse0) (let ((.cse2 (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0)))) (or .cse1 (not .cse2) (and (or bool.b23 .cse0 .cse2) (let ((.cse3 (+ x3 (* (/ 3.0 20.0) x4))) (.cse4 (* (/ 7.0 2.0) x5))) (let ((.cse5 (<= .cse3 (+ .cse4 688.0)))) (or (not (<= .cse3 (+ .cse4 1165.0))) bool.b23 (and (or .cse5 (and .cse6 .cse7 .cse8 .cse9 .cse10 .cse11 .cse12 .cse13 .cse14)) (or .cse15 .cse5 .cse16) (or .cse17 .cse15 .cse5) (or .cse15 .cse5 .cse18) (or .cse15 .cse1 .cse5)) (and (not .cse5) (or bool.b8 bool.b10 bool.b12 bool.b14 bool.b5)))))))))))))) bool.b22 (and (or .cse17 bool.b6) .cse18)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void scholl_smt08_model_model_6_63() {

		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getBoolSort, "bool.b8", "bool.b6", "bool.b7", "bool.b10", "bool.b23", "bool.b12", "bool.b22", "bool.b14", "bool.b5"),
			new FunDecl(SmtSortUtils::getRealSort, "x3", "x4", "x5"),
		};
		final String formulaAsString = "(forall ((?lambda Real)) (or (exists ((?lambdaprime Real)) (and (not (and (not (<= 10.0 (+ ?lambdaprime x5))) (not (and (not bool.b5) bool.b6 (not (and (not (<= 30.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))) (not (<= 4910.0 (+ (* 40.0 ?lambdaprime) x4))))) (not bool.b7) (not bool.b22))) (not (and (not bool.b5) bool.b7 (not bool.b6) (not (and (not (<= 4500.0 (+ (* 40.0 ?lambdaprime) x4))) (not (<= 30.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))))) (not bool.b22))) (not (and (not bool.b5) (not bool.b6) (not bool.b7) (not (and (not (<= 30.0 (+ (* (/ 1.0 2.0) ?lambdaprime) x3))) (not (<= 4100.0 (+ (* 40.0 ?lambdaprime) x4))))) (not bool.b22))))) (<= 0.0 ?lambdaprime) (<= ?lambdaprime ?lambda))) (not (and (not (and bool.b7 (not (and bool.b6 (not (and (not bool.b23) (not (and (not (and (not (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0))) (not (and (<= 10.0 (+ ?lambda x5)) (not (and (not (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 30.0) (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) 610.0) (not bool.b10) (not bool.b8))))) (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8))) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0)))))))) (not (and (not (and (not (and (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 13.0 2.0) x5) 658.0)) (not (and (<= 10.0 (+ ?lambda x5)) (not (and (not (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 30.0) (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) 610.0) (not bool.b10) (not bool.b8))))) (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8))) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* (/ 3.0 40.0) x4)) (/ 743.0 2.0)))))))) (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 13.0 2.0) x5) 1135.0)) (not (and (not (<= (+ x3 (* (/ 3.0 20.0) x4)) (+ (* (/ 13.0 2.0) x5) 658.0))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not bool.b10) (not bool.b8))))))) (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0)))))))) (not (and (not (and (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (<= (+ (* (/ 7.0 2.0) ?lambda) x3 (* 3.0 x5)) 50.0) (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 1200.0) (not (<= (+ (* (/ 13.0 2.0) ?lambda) x3 (* (/ 3.0 20.0) x4)) 723.0)) (not bool.b10) (not bool.b8) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 40.0))) (not (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 0.0)))) (<= 10.0 (+ ?lambda x5)) (not (and (not (and (not bool.b5) (not (<= (+ (* 40.0 ?lambda) x4) 4820.0)))) (<= (+ (* (/ 1.0 2.0) ?lambda) x3) 0.0))))) bool.b23)))))) (not bool.b22) (not (and (not (and (not bool.b6) bool.b5)) (not bool.b7))))) (< ?lambda 0.0)))";
		final String expectedResultAsString = "(let ((.cse5 (not bool.b5)) (.cse4 (not bool.b7))) (or (let ((.cse35 (* (/ 1.0 40.0) x4))) (let ((.cse30 (<= (/ 491.0 4.0) .cse35)) (.cse1 (not bool.b22)) (.cse31 (<= (/ 205.0 2.0) .cse35)) (.cse32 (<= 60.0 (* 2.0 x3))) (.cse34 (<= (/ 225.0 2.0) .cse35)) (.cse33 (<= 10.0 x5))) (let ((.cse13 (or .cse5 .cse31 .cse32 .cse34 .cse33)) (.cse14 (or .cse31 bool.b6 .cse32 .cse34 .cse33)) (.cse15 (or .cse31 .cse4 .cse32 .cse34 .cse33)) (.cse26 (and (or .cse5 .cse32 .cse34 .cse33) (or .cse30 .cse32 .cse34 .cse33) (or bool.b6 .cse32 .cse34 .cse33) (or .cse32 .cse34 .cse1 .cse33) (or .cse4 .cse32 .cse34 .cse33))) (.cse16 (or .cse31 .cse32 .cse34 .cse1 .cse33)) (.cse17 (or .cse30 .cse31 .cse32 .cse34 .cse33)) (.cse20 (or .cse31 .cse32 .cse4 .cse33)) (.cse21 (or .cse31 .cse32 .cse1 .cse33)) (.cse22 (or .cse31 bool.b6 .cse32 .cse33)) (.cse23 (or .cse5 .cse31 .cse32 .cse33)) (.cse0 (not bool.b6)) (.cse25 (and (or bool.b6 .cse33) (or .cse5 .cse33) (or .cse4 .cse33) (or .cse1 .cse33) (or .cse30 .cse32 .cse33))) (.cse24 (or .cse30 .cse31 .cse32 .cse33))) (and (or .cse0 (let ((.cse27 (+ x3 (* (/ 3.0 20.0) x4))) (.cse28 (* (/ 13.0 2.0) x5))) (let ((.cse9 (<= .cse27 (+ .cse28 658.0))) (.cse11 (<= x3 (+ (* (/ 1.0 2.0) x5) 15.0)))) (let ((.cse6 (not .cse11)) (.cse8 (not (<= .cse27 (+ .cse28 1135.0)))) (.cse10 (and (not .cse9) (or bool.b8 bool.b10 bool.b12 bool.b14 bool.b5))) (.cse12 (not bool.b23))) (let ((.cse2 (and (or .cse6 (and (or .cse26 .cse8 .cse9 .cse10) (or .cse26 .cse11))) (or .cse26 .cse12))) (.cse3 (let ((.cse18 (and (or (and (or .cse8 .cse9 .cse10 .cse25) (or .cse25 .cse11)) .cse6) (or .cse12 .cse25)))) (and (or bool.b23 .cse4 .cse18) (or bool.b23 .cse1 .cse18) (or .cse5 bool.b23 .cse18) (or bool.b23 (let ((.cse19 (and .cse20 .cse21 .cse22 .cse23 .cse24))) (and (or (and (or .cse8 .cse9 .cse10 .cse19) (or .cse11 .cse19)) .cse6) (or .cse12 .cse19)))) (or .cse0 bool.b23 .cse18))))) (and (or bool.b23 .cse1 .cse2) (or bool.b7 .cse3) (or bool.b23 .cse4 .cse2) (or .cse3 .cse1) (or .cse5 bool.b23 .cse2) (or .cse0 bool.b23 .cse2) (or .cse5 .cse3) (or .cse0 .cse3) (or bool.b23 (let ((.cse7 (and .cse13 .cse14 .cse15 .cse16 .cse17))) (and (or .cse6 (and (or .cse7 .cse8 .cse9 .cse10) (or .cse7 .cse11))) (or .cse7 .cse12)))))))))) (or bool.b7 (let ((.cse29 (and .cse20 (or .cse4 .cse25) .cse21 .cse22 (or .cse5 .cse25) (or .cse1 .cse25) .cse23 (or .cse0 .cse25) .cse24))) (and (or bool.b7 .cse29) (or .cse26 .cse1) .cse13 (or .cse5 .cse26) (or .cse29 .cse1) .cse14 (or .cse5 .cse29) .cse15 (or .cse26 .cse4) (or .cse0 .cse29) (or .cse0 .cse26) .cse16 .cse17))))))) bool.b22 (and (or .cse5 bool.b6) .cse4)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Benchmark from MCR. Quantifier elimination did not terminate.
	 */
	@Test
	public void mcrPthreadWmm01 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x0", "x1"), };
		final String formulaAsString = "(exists ((v_x1_32 Int) (v_x2_42 Int) (v_x1_28 Int) (v_x2_38 Int) (v_x2_60 Int) (v_x2_54 Int) (v_x1_41 Int) (v_x1_56 Int) (v_x0_46 Int) (v_x0_59 Int) (v_x3_53 Int)) (let ((.cse47 (+ v_x1_56 1)) (.cse4 (<= 0 v_x1_56)) (.cse2 (<= v_x1_56 0)) (.cse5 (<= 0 x1)) (.cse1 (<= x1 0))) (or (let ((.cse0 (<= v_x1_56 x1)) (.cse3 (<= x1 v_x1_56))) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 (let ((.cse23 (<= v_x2_42 v_x2_54)) (.cse52 (+ v_x2_38 1)) (.cse53 (+ v_x2_54 1)) (.cse29 (<= v_x2_42 0))) (let ((.cse22 (<= 0 v_x2_38)) (.cse7 (<= 0 v_x2_54)) (.cse49 (not .cse29)) (.cse48 (<= .cse53 v_x2_42)) (.cse50 (<= .cse52 v_x2_42)) (.cse51 (or (<= v_x2_42 v_x2_38) .cse23)) (.cse6 (<= v_x2_38 0)) (.cse32 (<= v_x2_54 0)) (.cse26 (<= 0 v_x2_42))) (or (let ((.cse8 (<= v_x2_38 v_x2_60)) (.cse9 (ite .cse48 (=> .cse49 (or .cse29 (ite (not .cse50) .cse6 .cse51))) .cse32)) (.cse10 (<= v_x2_60 0)) (.cse36 (<= v_x2_60 v_x2_38))) (and .cse6 .cse7 .cse8 .cse9 .cse1 .cse10 (let ((.cse11 (<= v_x1_41 v_x1_56))) (or (let ((.cse13 (<= v_x1_41 x1)) (.cse14 (<= v_x1_41 0)) (.cse15 (<= 0 v_x1_41)) (.cse12 (<= x1 v_x1_41)) (.cse16 (<= v_x1_56 v_x1_41))) (and .cse11 .cse0 .cse1 .cse3 .cse12 .cse5 (or (and .cse12 .cse13) (ite .cse14 (and (<= (+ v_x1_41 1) 0) .cse15) .cse14)) .cse16 .cse13 (let ((.cse17 (<= 0 v_x0_46))) (or (and (<= (+ v_x0_46 1) 0) .cse17) (let ((.cse33 (<= v_x0_46 0))) (and (let ((.cse44 (<= (+ x0 1) 0))) (let ((.cse18 (not .cse44)) (.cse40 (<= 0 x0))) (ite .cse18 (let ((.cse20 (<= x0 0))) (let ((.cse19 (not .cse20))) (or (ite .cse19 .cse20 (<= 1 x0)) (let ((.cse34 (<= 0 v_x0_59))) (let ((.cse37 (<= v_x0_46 x0)) (.cse42 (<= x0 v_x0_46)) (.cse45 (<= v_x0_46 v_x0_59)) (.cse46 (<= v_x0_59 v_x0_46)) (.cse38 (and (<= (+ v_x0_59 1) 0) .cse34))) (let ((.cse21 (or (and .cse45 .cse46 .cse17 .cse33) .cse38)) (.cse43 (ite .cse19 (or .cse42 .cse20) .cse17)) (.cse41 (ite .cse44 (or .cse37 .cse40) .cse33))) (and .cse21 (or (let ((.cse39 (<= v_x0_59 0))) (and (or (and (let ((.cse30 (+ v_x1_28 1)) (.cse35 (<= 0 v_x1_28))) (or (let ((.cse25 (<= v_x1_32 v_x2_42)) (.cse31 (and (<= (+ v_x1_32 1) 0) (<= 0 v_x1_32)))) (let ((.cse24 (or .cse25 .cse31)) (.cse28 (<= v_x1_28 v_x2_42)) (.cse27 (<= x1 v_x2_42))) (and (<= v_x2_42 v_x1_28) .cse8 .cse22 .cse23 .cse1 (<= 0 v_x2_60) .cse5 .cse24 .cse13 (<= v_x1_28 0) .cse6 .cse11 .cse7 (<= v_x2_42 x1) (or (and .cse25 .cse26 .cse1 .cse27 .cse5 .cse28) (and .cse1 .cse24 .cse5)) .cse27 .cse29 .cse14 .cse9 .cse15 (or (and (<= .cse30 v_x1_32) (<= v_x1_32 v_x1_28)) (and .cse1 .cse5 (<= x1 v_x1_32) (<= v_x1_32 x1)) .cse31) .cse10 .cse12 .cse28 (<= v_x2_54 v_x2_42) (<= v_x0_46 v_x2_54) .cse32 .cse17 .cse33 .cse34 (<= v_x2_42 v_x1_32) .cse26 .cse0 (<= v_x1_41 v_x2_54) .cse2 (<= v_x1_41 v_x2_42) .cse3 .cse4 (<= v_x2_42 v_x1_41) .cse35 .cse36 (or (and .cse1 .cse5) .cse27) .cse16 (<= v_x2_42 v_x1_56)))) (and (<= .cse30 0) .cse35))) .cse37 .cse20 (or .cse38 (and .cse21 .cse34 (or (ite .cse18 (and .cse21 .cse34 .cse39 .cse17) .cse40) .cse38) .cse17)) (<= v_x3_53 0) .cse32 .cse33 .cse17 .cse41 (<= 0 v_x3_53) .cse11 .cse42 .cse7 .cse34 .cse26 .cse39 .cse29 .cse16 .cse40 .cse43 (<= v_x3_53 v_x2_54)) .cse44) .cse34 .cse39 .cse45 .cse46 .cse17 .cse33)) .cse38) (or .cse44 (and .cse42 .cse37 .cse33 .cse17)) .cse43 .cse41 .cse33 .cse17)))) .cse44))) .cse40))) .cse33 .cse17)))))) (and (<= .cse47 v_x1_41) .cse11))) .cse5 .cse36 .cse29 .cse32)) (and (<= .cse52 0) .cse22) (and (<= .cse53 0) .cse7) (ite .cse49 (ite .cse48 (ite .cse50 .cse51 .cse6) .cse32) (and (<= (+ v_x2_42 1) 0) .cse26))))))) (ite .cse2 (and (<= .cse47 0) .cse4) .cse2) (ite .cse1 (and (<= (+ x1 1) 0) .cse5) .cse1))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void mcrPthreadWmm02 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "~x~0", "~x$r_buff0_thd2~0", "~x$w_buff0_used~0", "~x$w_buff1_used~0", "~x$w_buff0~0", "~x$w_buff1~0", "~x$r_buff1_thd0~0"), };
		final String formulaAsString = "(forall ((~x$r_buff1_thd2~0 Int) (|P1Thread1of1ForFork0_#t~nondet35| Int)) (let ((.cse11 (= (mod ~x$r_buff0_thd2~0 256) 0)) (.cse19 (= (mod ~x$w_buff1_used~0 256) 0)) (.cse20 (= (mod ~x$r_buff1_thd2~0 256) 0))) (let ((.cse2 (= (mod ~x$w_buff0_used~0 256) 0)) (.cse21 (not .cse20)) (.cse18 (not .cse19)) (.cse13 (not .cse11))) (let ((.cse22 (or .cse18 .cse13)) (.cse14 (or .cse13 .cse21)) (.cse15 (not .cse2)) (.cse8 (= (mod |P1Thread1of1ForFork0_#t~nondet35| 256) 0))) (let ((.cse7 (not .cse8)) (.cse3 (and .cse11 .cse19)) (.cse4 (and .cse13 .cse15)) (.cse6 (and .cse11 .cse20)) (.cse1 (and .cse22 .cse14 .cse15))) (or (let ((.cse5 (or .cse2 .cse11))) (let ((.cse0 (let ((.cse16 (and .cse5 .cse13 .cse15))) (let ((.cse9 (let ((.cse17 (and .cse8 (or .cse7 (and (or .cse2 .cse16 .cse3 .cse6) .cse22 .cse14 .cse15))))) (and (or .cse7 (and (or (and (or .cse17 .cse4) (or .cse2 .cse11 (and (or .cse7 (and .cse18 (or .cse2 .cse19 .cse20) .cse21 .cse15)) .cse8))) .cse2 .cse3 .cse6) (or .cse17 .cse1))) (or .cse17 .cse8))))) (and (or .cse8 .cse9) (or .cse7 (and (or .cse2 .cse3 (let ((.cse10 (let ((.cse12 (and (or .cse7 (and (or .cse2 .cse16 .cse11 .cse6) .cse13 .cse14 .cse15)) .cse8))) (and (or .cse12 .cse8) (or .cse7 (and (or (and .cse5 (or .cse4 .cse12)) .cse2 .cse11 .cse6) (or .cse12 (and .cse13 .cse14 .cse15)))))))) (and (or .cse10 .cse4) (or .cse2 .cse11 .cse10))) .cse6) (or .cse1 .cse9)))))))) (and (or (and (or .cse0 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse0) .cse5) .cse6)) .cse7) (or .cse0 .cse8)))) (let ((.cse25 (<= ~x$w_buff0~0 0)) (.cse26 (= 0 ~x$w_buff1~0)) (.cse27 (= ~x$r_buff1_thd0~0 0))) (let ((.cse31 (let ((.cse32 (let ((.cse33 (and (= ~x~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 (and (or .cse33 .cse4) (or .cse2 .cse11 .cse33)) .cse6) (or .cse33 .cse1))) (or .cse33 .cse8))))) (and (or .cse7 (and (or .cse32 .cse1) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse32) (or .cse4 .cse32)) .cse6))) (or .cse32 .cse8))))) (let ((.cse28 (or .cse31 .cse8))) (and (or .cse2 .cse3 (and (or .cse4 (and (or .cse7 (let ((.cse23 (let ((.cse24 (and .cse25 .cse26 (= ~x$w_buff1~0 1) .cse27))) (and (or .cse24 .cse8) (or (and (or .cse24 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse24) (or .cse2 .cse11 .cse24)) .cse6)) .cse7))))) (and (or (and (or .cse1 .cse23) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse23) (or .cse4 .cse23)) .cse6)) .cse7) (or .cse8 .cse23)))) .cse28)) (or .cse2 .cse11 (and (or .cse7 (let ((.cse29 (let ((.cse30 (and (= ~x$w_buff0~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 .cse6 (and (or .cse2 .cse11 .cse30) (or .cse4 .cse30))) (or .cse30 .cse1))) (or .cse30 .cse8))))) (and (or .cse29 .cse8) (or .cse7 (and (or .cse2 .cse3 (and (or .cse2 .cse11 .cse29) (or .cse4 .cse29)) .cse6) (or .cse29 .cse1)))))) .cse28))) .cse6) (or (and (or .cse7 .cse31) .cse28) .cse1)))))))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void heap_data_calendar() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~ev1~0", "main_~ev2~0"),
		};
		final String formulaAsString =
				"(forall ((|#memory_int| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_main_~p~0.offset_6 (_ BitVec 32)) (v_main_~l~0.base_13 (_ BitVec 32)) (|v_main_#t~malloc5.offset_6| (_ BitVec 32)) (|v_#memory_int_19| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_main_~p~0.base_6 (_ BitVec 32)) (v_main_~l~0.offset_13 (_ BitVec 32))) (or (not (and (= v_main_~p~0.base_6 v_main_~l~0.base_13) (= |v_#memory_int_19| (store |#memory_int| v_main_~p~0.base_6 (store (store (store (select |#memory_int| v_main_~p~0.base_6) (bvadd v_main_~p~0.offset_6 (_ bv4 32)) main_~ev1~0) (bvadd v_main_~p~0.offset_6 (_ bv8 32)) main_~ev2~0) v_main_~p~0.offset_6 (select (select |v_#memory_int_19| v_main_~p~0.base_6) v_main_~p~0.offset_6)))) (= v_main_~l~0.offset_13 v_main_~p~0.offset_6) (or (not (= (_ bv3 32) main_~ev2~0)) (not (= (_ bv1 32) main_~ev1~0))) (= (_ bv0 32) |v_main_#t~malloc5.offset_6|) (= v_main_~p~0.offset_6 |v_main_#t~malloc5.offset_6|))) (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (v_DerPreprocessor_2 (_ BitVec 32)) (v_main_~p~0.base_5 (_ BitVec 32))) (or (not (= (bvadd (select (select (store |v_#memory_int_19| v_main_~p~0.base_5 (store (store (store (select |v_#memory_int_19| v_main_~p~0.base_5) (_ bv4 32) x) (_ bv8 32) y) (_ bv0 32) v_DerPreprocessor_2)) v_main_~l~0.base_13) (bvadd v_main_~l~0.offset_13 (_ bv8 32))) (_ bv4294967293 32)) (_ bv0 32))) (bvsgt x (_ bv3 32)) (= (_ bv3 32) y) (not (= (_ bv1 32) (select (store (store (store (select |v_#memory_int_19| v_main_~p~0.base_5) (_ bv4 32) x) (_ bv8 32) y) (_ bv0 32) v_DerPreprocessor_2) (_ bv4 32)))) (bvslt x (_ bv0 32)) (not (= (_ bv0 32) (bvadd (select (select (store |v_#memory_int_19| v_main_~p~0.base_5 (store (store (store (select |v_#memory_int_19| v_main_~p~0.base_5) (_ bv4 32) x) (_ bv8 32) y) (_ bv0 32) v_DerPreprocessor_2)) v_main_~l~0.base_13) (bvadd v_main_~l~0.offset_13 (_ bv4 32))) (_ bv4294967295 32))))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void heap_data_cart() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "idxDim1", "idxDim2"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "arr"),
		};
		final String formulaAsString =
				"(and (= idxDim2 (_ bv0 32)) (exists ((x (_ BitVec 32))) (and (exists ((y Bool) (|â| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (and (not y) (or (and (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) x)) (not y)) (and y (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) x))) (= (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))) (_ bv0 32)) (= arr (store |â| idxDim1 (store (store (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32)) x) (bvadd idxDim2 (_ bv4 32)) (select (store (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32)) x) (bvadd idxDim2 (_ bv4 32)))))))) (not (bvslt x (_ bv0 32))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void dll_01_2small() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_#t~mem25.offset", "main_#t~mem25.base"),
		};
		final String formulaAsString =
				"(exists ((main_~end~0.base Int) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (|#memory_$Pointer$.offset| (Array Int (Array Int Int))) (main_~end~0.offset Int)) (and (= (select (select |#memory_$Pointer$.offset| main_~end~0.base) (+ main_~end~0.offset 16)) |main_#t~mem25.offset|) (exists ((main_~list~0.base Int)) (and (= (select (select |#memory_$Pointer$.offset| main_~list~0.base) 16) main_~end~0.offset) (= (select (select |#memory_$Pointer$.base| main_~list~0.base) 16) main_~end~0.base) (= (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| main_~list~0.base) 16)) (+ (select (select |#memory_$Pointer$.offset| main_~list~0.base) 16) 16)) 0) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| main_~list~0.base) 16)) (+ (select (select |#memory_$Pointer$.offset| main_~list~0.base) 16) 16)) 0))) (= (select (select |#memory_$Pointer$.base| main_~end~0.base) (+ main_~end~0.offset 16)) |main_#t~mem25.base|)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void list_simple_dll2cupdateall() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~s~0.base", "main_~s~0.offset", "main_~new_data~0", "main_~len~0"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString =
				"(forall ((|v_dll_circular_update_at_#in~head.offset_11| (_ BitVec 32)) (|v_#memory_int_114| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_dll_circular_update_at_~head.offset_21 (_ BitVec 32)) (|v_#memory_int_115| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.base_115| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_dll_circular_update_at_~data_16 (_ BitVec 32)) (|v_dll_circular_update_at_#in~head.base_11| (_ BitVec 32)) (v_dll_circular_update_at_~head.base_21 (_ BitVec 32)) (|v_dll_circular_update_at_#in~data_10| (_ BitVec 32)) (|v_old(#memory_$Pointer$.base)_40| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (or (forall ((v_dll_circular_update_at_~head.offset_16 (_ BitVec 32)) (v_dll_circular_update_at_~data_12 (_ BitVec 32))) (= (select (select (store |v_#memory_int_115| (select (select |v_#memory_$Pointer$.base_115| main_~s~0.base) main_~s~0.offset) (store (select |v_#memory_int_115| (select (select |v_#memory_$Pointer$.base_115| main_~s~0.base) main_~s~0.offset)) (bvadd v_dll_circular_update_at_~head.offset_16 (_ bv8 32)) v_dll_circular_update_at_~data_12)) main_~s~0.base) (bvadd main_~s~0.offset (_ bv8 32))) main_~len~0)) (not (and (= v_dll_circular_update_at_~data_16 |v_dll_circular_update_at_#in~data_10|) (= |v_#memory_int_115| (store |v_#memory_int_114| v_dll_circular_update_at_~head.base_21 (store (select |v_#memory_int_114| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32)) v_dll_circular_update_at_~data_16))) (= main_~s~0.base |v_dll_circular_update_at_#in~head.base_11|) (= (store |v_old(#memory_$Pointer$.base)_40| v_dll_circular_update_at_~head.base_21 (store (select |v_old(#memory_$Pointer$.base)_40| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32)) (select (select |v_#memory_$Pointer$.base_115| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32))))) |v_#memory_$Pointer$.base_115|) (= |v_dll_circular_update_at_#in~head.base_11| v_dll_circular_update_at_~head.base_21) (= |v_dll_circular_update_at_#in~head.offset_11| main_~s~0.offset) (= main_~new_data~0 |v_dll_circular_update_at_#in~data_10|) (= |v_old(#memory_$Pointer$.base)_40| |#memory_$Pointer$.base|) (= |v_dll_circular_update_at_#in~head.offset_11| v_dll_circular_update_at_~head.offset_21)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * 30s elimination time
	 */
	@Test
	public void forester_heap_dll_optional() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~head~0.offset", "main_~head~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"),
		};
		final String formulaAsString =
				"(forall ((|#memory_INTTYPE4| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_DerPreprocessor_10 (_ BitVec 32)) (v_DerPreprocessor_9 (_ BitVec 32)) (|v_main_#t~malloc6.base_4| (_ BitVec 32)) (|main_#t~mem7.offset| (_ BitVec 32)) (v_DerPreprocessor_8 (_ BitVec 32)) (v_subst_6 (_ BitVec 32)) (v_DerPreprocessor_7 (_ BitVec 32)) (v_DerPreprocessor_6 (_ BitVec 32))) (or (not (= (select |#valid| |v_main_#t~malloc6.base_4|) (_ bv0 1))) (not (= (select (select (store (store |#memory_INTTYPE4| main_~head~0.base (store (store (store (select |#memory_INTTYPE4| main_~head~0.base) (bvadd main_~head~0.offset (_ bv12 32)) (_ bv0 32)) (bvadd main_~head~0.offset (_ bv8 32)) v_DerPreprocessor_10) main_~head~0.offset v_DerPreprocessor_9)) |v_main_#t~malloc6.base_4| (store (store (store (store (select (store |#memory_INTTYPE4| main_~head~0.base (store (store (store (select |#memory_INTTYPE4| main_~head~0.base) (bvadd main_~head~0.offset (_ bv12 32)) (_ bv0 32)) (bvadd main_~head~0.offset (_ bv8 32)) v_DerPreprocessor_10) main_~head~0.offset v_DerPreprocessor_9)) |v_main_#t~malloc6.base_4|) (bvadd |main_#t~mem7.offset| (_ bv4 32)) v_DerPreprocessor_8) v_subst_6 v_DerPreprocessor_7) (bvadd v_subst_6 (_ bv12 32)) (_ bv0 32)) (bvadd v_subst_6 (_ bv8 32)) v_DerPreprocessor_6)) main_~head~0.base) (bvadd main_~head~0.offset (_ bv12 32))) (_ bv2 32)))))";
		final String expectedResultAsString =
				"(forall ((v_subst_6 (_ BitVec 32)) (v_DerPreprocessor_8 (_ BitVec 32)) (|main_#t~mem7.offset| (_ BitVec 32)) (v_DerPreprocessor_7 (_ BitVec 32)) (|v_main_#t~malloc6.base_4| (_ BitVec 32)) (v_DerPreprocessor_6 (_ BitVec 32))) (or (not (= (select |#valid| |v_main_#t~malloc6.base_4|) (_ bv0 1))) (not (and (or (and (not (= (bvadd main_~head~0.offset (_ bv12 32)) (bvadd v_subst_6 (_ bv8 32)))) (= main_~head~0.base |v_main_#t~malloc6.base_4|) (or (and (= (bvadd main_~head~0.offset (_ bv12 32)) v_subst_6) (= (_ bv2 32) v_DerPreprocessor_7)) (and (not (= (bvadd main_~head~0.offset (_ bv12 32)) v_subst_6)) (= (_ bv2 32) v_DerPreprocessor_8) (= (bvadd main_~head~0.offset (_ bv12 32)) (bvadd |main_#t~mem7.offset| (_ bv4 32)))))) (and (= (bvadd main_~head~0.offset (_ bv12 32)) (bvadd v_subst_6 (_ bv8 32))) (= (_ bv2 32) v_DerPreprocessor_6) (= main_~head~0.base |v_main_#t~malloc6.base_4|))) (not (= (bvadd v_subst_6 (_ bv12 32)) (bvadd main_~head~0.offset (_ bv12 32))))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void sll_circular_traversal_2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sll_circular_create_~new_head~0.base", "sll_circular_create_~new_head~0.offset", "sll_circular_create_~head~0.offset", "sll_circular_create_~head~0.base", "sll_circular_create_~last~0.base", "sll_circular_create_~last~0.offset"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#length"),
		};
		final String formulaAsString =
				"(forall ((|#memory_$Pointer$.base| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|#memory_$Pointer$.offset| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.offset_156| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.base_164| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (or (and (= sll_circular_create_~new_head~0.base (select (select (store |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.base)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset)) (= (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) sll_circular_create_~new_head~0.offset)) (not (and (= (store |#memory_$Pointer$.offset| sll_circular_create_~new_head~0.base (store (select |#memory_$Pointer$.offset| sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset sll_circular_create_~head~0.offset)) |v_#memory_$Pointer$.offset_156|) (= (store |#memory_$Pointer$.base| sll_circular_create_~new_head~0.base (store (select |#memory_$Pointer$.base| sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset sll_circular_create_~head~0.base)) |v_#memory_$Pointer$.base_164|))) (and (bvule (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv8 32)) (select |#length| (select (select (store |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.base)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset))) (bvule (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv4 32)) (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv8 32))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	//@formatter:on
}
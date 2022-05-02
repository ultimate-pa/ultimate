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
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;


/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationTodos {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final boolean CHECK_SIMPLIFICATION_POSSIBILITY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 10_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final LogLevel LOG_LEVEL_SOLVER = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;


	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationTodos.class.getSimpleName());
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

		final Script solverInstance = new HistoryRecordingScript(
				UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL_SOLVER));
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
	public void understandingModulo() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(and (exists ((x Int))	(and (< x 256) (<= 0 x) (= y (mod (* 3 x) 256)))) (< y 256) (<= 0 y))";
		final String expectedResult = "(and (< y 256) (= (mod y 3) 0) (<= 0 y))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void understandingModulo2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(and (exists ((x Int))	(and (< x 256) (<= 0 x) (= y (mod (* 3 x) 256)))) (< y 256) (<= 0 y))";
		final String expectedResult = "(and (< y 256) (= (mod y 3) 0) (<= 0 y))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
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
	public void contextInauguration() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "k", "i", "x", "y") };
		final String formulaAsString = "(exists ((a (Array Int Int))) (and (= k i) (or (= (+ 0 (select a k)) (+ x (select a i))) (= (+ 1 (select a k)) (+ y (select a i))))))";
		final String expectedResultAsString = "(and (= i k) (or (= y 1) (= x 0)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}




	@Test
	public void choirNightTrezor04Triathlon() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (and (< 0 (mod (+ (* b 4294967295) moda) 4294967296)) (<= (mod (+ (* b 4294967295) moda) 4294967296) 1)) (> 0 moda) (>= moda 4294967296) (<= (+ (* 4294967296 diva) moda) (mod i 4294967296)) (< (mod (+ i 1) 4294967296) moda) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "(let ((.cse0 (* b (- 4294967295))) (.cse1 (* b 4294967295)) (.cse2 (mod i 4294967296))) (and (<= (div (+ .cse0 (* (mod (+ i 1) 4294967296) (- 1)) 1) (- 4294967296)) (+ (div (+ .cse1 .cse2 (- 4294967295)) 4294967296) 1)) (<= (div (+ .cse0 (- 4294967296)) (- 4294967296)) (+ (div (+ .cse1 .cse2) 4294967296) 1))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (<= (mod (+ (* b 4294967295) moda) 4294967296) 1)  (<= (+ (* 4294967296 diva) moda) (mod i 4294967296)) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon3() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (<= (mod (+ (* b 4294967295) moda) 4294967296) 1)  (<= (+ (* 4294967296 diva) moda) (mod i 4294967296)) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, formulaAsString, !true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon4() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (aux_mod_moda_42 Int) (aux_div_moda_42 Int)) (or (> 0 aux_mod_moda_42) (<= aux_mod_moda_42 1) (<= (+ (* 4294967295 b) 4294967296) (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42))) (>= aux_mod_moda_42 4294967296) (<= (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42)) (+ (* 4294967295 b) (mod i 4294967296))) (< (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42)) (* 4294967295 b))))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, formulaAsString, !true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon5() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "b"), };
		final String formulaAsString = "(forall ((x Int)) (<= (+ (* 7 b) 8) (* 8 x))))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, formulaAsString, !true, mServices, mLogger, mMgdScript, mCsvWriter);
	}




	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different
	 * file.
	 */
	@Test
	public void heap_data_cart2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "idxDim1", "idxDim2"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "arr"),
		};
		final String formulaAsString = "(and (= idxDim2 (_ bv0 32)) (exists ((x (_ BitVec 32))) (and (exists ((|â| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (y (_ BitVec 32)) (z Bool)) (and (or (and (not (bvslt (select (select |â| y) (_ bv4 32)) x)) (not z)) (and (bvslt (select (select |â| y) (_ bv4 32)) x) z)) (= (store |â| y (store (store (select |â| y) (_ bv8 32) x) (_ bv4 32) (select (store (select |â| y) (_ bv8 32) x) (_ bv4 32)))) arr) (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))))) (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))) (_ bv0 32))) (not z))) (not (bvslt x (_ bv0 32))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void dll_01_2big() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_#t~mem20.offset", "main_#t~mem20.base"),
		};
		final String formulaAsString =
				"(exists ((main_~inner~0.offset Int) (|#memory_$Pointer$.base| (Array Int (Array Int Int))) (main_~inner~0.base Int) (|#memory_$Pointer$.offset| (Array Int (Array Int Int)))) (and (= (select (select |#memory_$Pointer$.offset| main_~inner~0.base) (+ main_~inner~0.offset 16)) |main_#t~mem20.offset|) (or (exists ((main_~end~0.base Int) (v_prenex_12 Int)) (and (not (= (select (select |#memory_$Pointer$.base| v_prenex_12) 16) v_prenex_12)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_12) 16)) 16)) (= 0 (select (select |#memory_$Pointer$.offset| v_prenex_12) 0)) (not (= (select (select |#memory_$Pointer$.base| main_~end~0.base) 16) v_prenex_12)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_12) 8)) 8)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_12) 8)) (- 8))) (= (select (select |#memory_$Pointer$.offset| main_~end~0.base) 16) main_~inner~0.offset) (not (= (select (select |#memory_$Pointer$.base| v_prenex_12) 8) main_~end~0.base)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_12) 16)) 0)) (= (select (select |#memory_$Pointer$.base| v_prenex_12) 8) (select (select |#memory_$Pointer$.base| main_~end~0.base) 0)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| main_~end~0.base) 16)) 0)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_12) 16) 0)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_12) 16) (select (select |#memory_$Pointer$.base| v_prenex_12) 8))) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| main_~end~0.base) 16)) 16)) (not (= (select (select |#memory_$Pointer$.base| main_~end~0.base) 16) (select (select |#memory_$Pointer$.base| v_prenex_12) 16))) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_12) 16)) 0)) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_12) 16)) 16) 0) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| main_~end~0.base) 16)) 0)) (not (= (select (select |#memory_$Pointer$.base| main_~end~0.base) 16) (select (select |#memory_$Pointer$.base| v_prenex_12) 8))) (= 0 (select (select |#memory_$Pointer$.offset| main_~end~0.base) 0)) (= (select (select |#memory_$Pointer$.offset| v_prenex_12) 16) 0) (= (select (select |#memory_$Pointer$.offset| main_~end~0.base) 16) 0) (= (select (select |#memory_$Pointer$.base| main_~end~0.base) 16) main_~inner~0.base) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_12) 8)) (- 8)) v_prenex_12) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| main_~end~0.base) 16)) 16) 0) (= 0 (select (select |#memory_$Pointer$.base| v_prenex_12) 0)) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_12) 8)) 8)) (= (+ (select (select |#memory_$Pointer$.offset| v_prenex_12) 8) 8) 0))) (exists ((v_prenex_16 Int) (v_prenex_13 Int)) (and (= (select (select |#memory_$Pointer$.offset| v_prenex_13) 8) 8) (= 0 (select (select |#memory_$Pointer$.offset| v_prenex_13) 0)) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_13) 16)) 0)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_16) 16) (select (select |#memory_$Pointer$.base| v_prenex_13) 8))) (not (= (select (select |#memory_$Pointer$.base| v_prenex_16) 16) v_prenex_13)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_13) 16) 0)) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_13) 16)) 16) 0) (= (select (select |#memory_$Pointer$.base| v_prenex_16) 0) (select (select |#memory_$Pointer$.base| v_prenex_13) 8)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_13) 16) (select (select |#memory_$Pointer$.base| v_prenex_13) 8))) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_16) 16)) 16)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_16) 16)) 0)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_13) 16) v_prenex_13)) (= (select (select |#memory_$Pointer$.offset| v_prenex_13) 16) 0) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_16) 16)) 0)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_13) 8)) 24)) (= (select (select |#memory_$Pointer$.offset| v_prenex_16) 16) main_~inner~0.offset) (= 0 (select (select |#memory_$Pointer$.offset| v_prenex_16) 0)) (not (= (select (select |#memory_$Pointer$.base| v_prenex_16) 16) (select (select |#memory_$Pointer$.base| v_prenex_13) 16))) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_16) 16)) 16) 0) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_13) 16)) 0)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_13) 8)) 8)) (= 0 (select (select |#memory_$Pointer$.base| v_prenex_13) 0)) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_13) 8)) 24)) (not (= v_prenex_16 (select (select |#memory_$Pointer$.base| v_prenex_13) 8))) (= (select (select |#memory_$Pointer$.base| v_prenex_16) 16) main_~inner~0.base) (= (select (select |#memory_$Pointer$.offset| v_prenex_16) 16) 0) (= v_prenex_13 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_13) 8)) 8)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_13) 16)) 16)))) (exists ((v_prenex_14 Int)) (and (= (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16) main_~inner~0.offset) (= (select (select |#memory_$Pointer$.offset| v_prenex_14) 16) 0) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16) main_~inner~0.base) (= (select (select |#memory_$Pointer$.base| v_prenex_14) 8) (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 0)) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16) (select (select |#memory_$Pointer$.base| v_prenex_14) 16))) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_14) 16)) 16)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16)) 0)) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 16)) 0)) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 16)) 16) 0) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_14) 16)) 0)) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) (select (select |#memory_$Pointer$.offset| v_prenex_14) 8)) v_prenex_14) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16)) 16)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 0)) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16)) 0) 0) (not (= (select (select |#memory_$Pointer$.base| v_prenex_14) 16) v_prenex_14)) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16) v_prenex_14)) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) (+ (select (select |#memory_$Pointer$.offset| v_prenex_14) 8) 16))) (not (= (select (select |#memory_$Pointer$.base| v_prenex_14) 8) (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8))) (= 0 (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16)) 16)) (= (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) (select (select |#memory_$Pointer$.offset| v_prenex_14) 8)) 0) (= 0 (select (select |#memory_$Pointer$.base| v_prenex_14) 0)) (= 0 (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) (+ (select (select |#memory_$Pointer$.offset| v_prenex_14) 8) 16))) (not (= (select (select |#memory_$Pointer$.base| v_prenex_14) 16) (select (select |#memory_$Pointer$.base| v_prenex_14) 8))) (not (= (select (select |#memory_$Pointer$.base| v_prenex_14) 16) 0)) (= 0 (select (select |#memory_$Pointer$.offset| v_prenex_14) 0)) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8)) 16) (select (select |#memory_$Pointer$.base| v_prenex_14) 8))) (= (select (select |#memory_$Pointer$.offset| (select (select |#memory_$Pointer$.base| v_prenex_14) 8)) 8) 0)))) (= |main_#t~mem20.base| (select (select |#memory_$Pointer$.base| main_~inner~0.base) (+ main_~inner~0.offset 16)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void FakeFloatingMountaineer01 () {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~a~0", "~#f~0.offset", "~g~0"),
				new FunDecl(SmtSortUtils::getRoundingmodeSort, "currentRoundingMode"),
				};
		final String formulaAsString = "(forall ((|~#f~0.base| (_ BitVec 32)) (|v_#memory_int_38| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|#memory_int| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_skolemized_q#valueAsBitvector_3| (_ BitVec 32))) (or (not (= |v_#memory_int_38| (store |#memory_int| |~#f~0.base| (store (select |#memory_int| |~#f~0.base|) (bvadd (bvmul ~a~0 (_ bv4 32)) |~#f~0.offset|) |v_skolemized_q#valueAsBitvector_3|)))) (not (= ((_ to_fp 8 24) currentRoundingMode ~g~0) (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_3|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_3|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_3|)))) (forall ((|v_skolemized_q#valueAsBitvector_9| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_7| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_8| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_10| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_11| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_12| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_5| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_6| (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_4| (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (let ((.cse0 (bvmul ~a~0 (_ bv4 32)))) (store (store (store (store (store (store (store (store (store (select |v_#memory_int_38| |~#f~0.base|) (bvadd .cse0 |~#f~0.offset| (_ bv4 32)) |v_skolemized_q#valueAsBitvector_4|) (bvadd .cse0 |~#f~0.offset| (_ bv8 32)) |v_skolemized_q#valueAsBitvector_5|) (bvadd .cse0 |~#f~0.offset| (_ bv12 32)) |v_skolemized_q#valueAsBitvector_6|) (bvadd .cse0 |~#f~0.offset| (_ bv16 32)) |v_skolemized_q#valueAsBitvector_7|) (bvadd .cse0 |~#f~0.offset| (_ bv20 32)) |v_skolemized_q#valueAsBitvector_8|) (bvadd .cse0 |~#f~0.offset| (_ bv24 32)) |v_skolemized_q#valueAsBitvector_9|) (bvadd .cse0 |~#f~0.offset| (_ bv28 32)) |v_skolemized_q#valueAsBitvector_10|) (bvadd .cse0 |~#f~0.offset| (_ bv32 32)) |v_skolemized_q#valueAsBitvector_11|) (bvadd .cse0 |~#f~0.offset| (_ bv36 32)) |v_skolemized_q#valueAsBitvector_12|)) |~#f~0.offset|))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	/**
	 * 20190812 Matthias: In the competition we were able to solve this benchmark but now we obtain an AEA term.
	 */
	 @Test
	public void ALIA_piVC_piVC_d91441() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "V_6", "V_5", "t", "ix", "j", "i"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a"),
			};
		final String formulaAsString = "(and (<= 0 j) (= V_5 V_6) (forall ((?V_11 Int)) (=> (and (<= (+ ?V_11 1) i) (<= 0 ?V_11)) (forall ((?V_12 Int)) (=> (and (<= 0 ?V_12) (<= ?V_12 ?V_11)) (<= (select a ?V_12) (select a ?V_11)))))) (< t (select a j)) (<= 0 V_5) (<= 0 (+ j 1)) (<= (+ j 1) i) (or (<= V_6 i) (exists ((?V_8 Int)) (and (exists ((?V_9 Int)) (and (<= ?V_9 ?V_8) (<= 0 ?V_9) (< (select (store a (+ j 1) (select a j)) ?V_8) (select (store a (+ j 1) (select a j)) ?V_9)))) (<= (+ ?V_8 1) i) (<= 0 ?V_8))) (not (= V_5 V_6)) (and (< (select (store a (+ j 1) (select a j)) i) (select (store a (+ j 1) (select a j)) (+ i (- 1)))) (not (= (+ i (- 1)) (+ j (- 1))))) (< i 1) (< j 0) (< i j) (and (exists ((?V_7 Int)) (and (<= ?V_7 i) (<= j ?V_7) (<= (select (store a (+ j 1) (select a j)) ?V_7) t))) (not (= (+ i (- 1)) (+ j (- 1)))))) (<= 1 i) (< i V_6) (or (= (+ i (- 1)) j) (<= (select a (+ i (- 1))) (select a i))) (or (= (+ i (- 1)) j) (forall ((?V_10 Int)) (=> (and (<= ?V_10 i) (<= (+ j 1) ?V_10)) (< t (select a ?V_10))))))";
		final String expectedResultAsString = "(let ((.cse20 (+ i (- 1))) (.cse22 (+ j 1)) (.cse23 (select a j))) (let ((.cse9 (< i j)) (.cse14 (<= V_6 i)) (.cse19 (exists ((?V_7 Int)) (and (<= ?V_7 i) (<= j ?V_7) (<= (select (store a (+ j 1) (select a j)) ?V_7) t)))) (.cse17 (< j 0)) (.cse16 (let ((.cse24 (store a .cse22 .cse23))) (< (select .cse24 i) (select .cse24 .cse20)))) (.cse15 (not (= .cse20 (+ j (- 1))))) (.cse8 (= .cse20 j)) (.cse12 (< i 1)) (.cse0 (<= 0 j)) (.cse11 (forall ((?V_10 Int)) (or (not (<= ?V_10 i)) (< t (select a ?V_10)) (not (<= (+ j 1) ?V_10))))) (.cse1 (= V_5 V_6)) (.cse2 (< t .cse23)) (.cse3 (forall ((?V_11 Int) (?V_12 Int)) (or (not (<= 0 ?V_11)) (not (<= 0 ?V_12)) (not (<= ?V_12 ?V_11)) (<= (select a ?V_12) (select a ?V_11)) (not (<= (+ ?V_11 1) i))))) (.cse4 (<= 0 .cse22)) (.cse5 (<= .cse22 i)) (.cse6 (<= 0 V_5)) (.cse7 (<= 1 i)) (.cse18 (exists ((?V_9 Int) (?V_8 Int)) (and (<= ?V_9 ?V_8) (<= (+ ?V_8 1) i) (<= 0 ?V_8) (<= 0 ?V_9) (let ((.cse21 (store a (+ j 1) (select a j)))) (< (select .cse21 ?V_8) (select .cse21 ?V_9)))))) (.cse13 (<= (select a .cse20) (select a i))) (.cse10 (< i V_6))) (or (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse9 .cse10) (and .cse0 .cse1 .cse11 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse12 .cse13 .cse10) (and .cse0 .cse1 .cse11 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse9 .cse13 .cse10) (and .cse0 .cse14 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse10) (and .cse11 .cse3 .cse4 .cse5 .cse15 .cse0 .cse1 .cse16 .cse2 .cse6 .cse7 .cse13 .cse10) (and .cse0 .cse14 .cse1 .cse11 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse13 .cse10) (and .cse0 .cse1 .cse11 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse17 .cse13 .cse10) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse18 .cse8 .cse10) (and .cse11 .cse19 .cse3 .cse4 .cse5 .cse15 .cse0 .cse1 .cse2 .cse6 .cse7 .cse13 .cse10) (and .cse0 .cse1 .cse19 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse15 .cse10) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse17 .cse10) (and .cse0 .cse1 .cse16 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse15 .cse10) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse8 .cse12 .cse10) (and .cse0 .cse11 .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse7 .cse18 .cse13 .cse10))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}



	@Test
	public void maybeTooDifficult() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_save_byte_from_array_~storage.base", "ULTIMATE.start_save_byte_from_array_~storage.offset", "ULTIMATE.start_save_byte_from_array_~array.base", "ULTIMATE.start_save_byte_from_array_~array.offset", "ULTIMATE.start_aws_array_eq_harness_~rhs~0.base", "ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0.base", "ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0.offset", "ULTIMATE.start_aws_array_eq_harness_~lhs~0.offset", "ULTIMATE.start_aws_array_eq_harness_~lhs~0.base", "#StackHeapBarrier"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
			};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int))) (v_ULTIMATE.start_save_byte_from_array_~array.offset_44 Int) (v_ULTIMATE.start_save_byte_from_array_~storage.offset_46 Int) (|v_ULTIMATE.start_nondet_size_t_#res_14| Int) (|ULTIMATE.start_nondet_size_t_#res| Int) (|v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24| Int)) (or (let ((.cse1 (let ((.cse2 (store |#memory_int| ULTIMATE.start_save_byte_from_array_~storage.base (let ((.cse4 (store (select |#memory_int| ULTIMATE.start_save_byte_from_array_~storage.base) ULTIMATE.start_save_byte_from_array_~storage.offset |ULTIMATE.start_nondet_size_t_#res|))) (store .cse4 (+ 8 ULTIMATE.start_save_byte_from_array_~storage.offset) (select (select (store |#memory_int| ULTIMATE.start_save_byte_from_array_~storage.base .cse4) ULTIMATE.start_save_byte_from_array_~array.base) (+ ULTIMATE.start_save_byte_from_array_~array.offset |ULTIMATE.start_nondet_size_t_#res|))))))) (store .cse2 |v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24| (let ((.cse3 (store (select .cse2 |v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24|) v_ULTIMATE.start_save_byte_from_array_~storage.offset_46 |v_ULTIMATE.start_nondet_size_t_#res_14|))) (store .cse3 (+ 8 v_ULTIMATE.start_save_byte_from_array_~storage.offset_46) (select (select (store .cse2 |v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24| .cse3) ULTIMATE.start_aws_array_eq_harness_~rhs~0.base) (+ v_ULTIMATE.start_save_byte_from_array_~array.offset_44 |v_ULTIMATE.start_nondet_size_t_#res_14|)))))))) (let ((.cse0 (select .cse1 |ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0.base|))) (= (mod (select .cse0 (+ 8 |ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0.offset|)) 256) (mod (select (select .cse1 ULTIMATE.start_aws_array_eq_harness_~lhs~0.base) (+ ULTIMATE.start_aws_array_eq_harness_~lhs~0.offset (select .cse0 |ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0.offset|))) 256)))) (not (= (select |#valid| |v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24|) 0)) (<= |v_ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_rhs~0.base_24| |#StackHeapBarrier|)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}



	@Test
	public void selfUpdateAraucaria() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "v_ArrVal_398", "v_ArrVal_400", "ULTIMATE.start_main_~l~0#1.base"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "v_#memory_$Pointer$.base_58"),
			};
		final String formulaAsString = "(forall ((v_ArrVal_391 (Array Int Int))) (let ((.cse0 (select (store (store v_ArrVal_391 8 v_ArrVal_398) 4 v_ArrVal_400) 0))) (or (not (= v_ArrVal_391 (store (select |v_#memory_$Pointer$.base_58| .cse0) 0 |ULTIMATE.start_main_~l~0#1.base|))) (not (= (select |#valid| .cse0) 0)))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void selfUpdateAraucariaSimplified() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "v1", "v2", "x"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "mem"),
			};
		final String formulaAsString = "(exists ((a (Array Int Int))) (= a (store (select mem (select (store (store a 8 v1) 4 v2) 0)) 0 x)))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}





	/**
	 * Although bv4294967295 is -1, we cannot eliminate here (yet).
	 */
	@Test
	public void somePreinerSchollBenchmarkSubformula() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "?lambda", "x5"),

		};
		final String formulaAsString = "(exists ((?lambdaprime (_ BitVec 32))) (and (bvsle ?lambdaprime ?lambda) (bvsle (bvadd (bvmul x5 (_ bv4294967295 32)) (bvmul (_ bv4294967295 32) ?lambdaprime)) (_ bv4294967286 32)) (bvsle (_ bv0 32) ?lambdaprime)))";
		final String expectedResultAsString = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}



//	// read_type_#64._token is function symbol with
//	// param sorts [(Array Int (Array Int Int)), (Array Int (Array Int Int)), (Array Int (Array Int Int)), Int, Int]
//    // and return sort Int
//	@Test
//	public void daxus01() {
//		final FunDecl[] funDecls = new FunDecl[] {
//				new FunDecl(SmtSortUtils::getIntSort, "routine_#33910_luaX_next_local_#4227_ls_IN.base", "routine_#33910_luaX_next_local_#4227_ls_IN.offset"),
//				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "_memory", "old(_memory)", "read_type_#64._token"),
//			};
//		final String formulaAsString = "(exists ((v__memory_1153 (Array Int (Array Int Int))) (v__memory_ptr.base_1009 (Array Int (Array Int Int))) (v__memory_ptr.offset_1009 (Array Int (Array Int Int))) (|routine_#33910_luaX_next_local_#4227_ls.offset| Int)) (and (<= |routine_#33910_luaX_next_local_#4227_ls.offset| |routine_#33910_luaX_next_local_#4227_ls_IN.offset|) (= (store v__memory_1153 |routine_#33910_luaX_next_local_#4227_ls_IN.base| (let ((.cse0 (+ 32 |routine_#33910_luaX_next_local_#4227_ls.offset|))) (store (store (store (select v__memory_1153 |routine_#33910_luaX_next_local_#4227_ls_IN.base|) (+ 16 |routine_#33910_luaX_next_local_#4227_ls.offset|) (|read_type_#64._token| v__memory_1153 v__memory_ptr.base_1009 v__memory_ptr.offset_1009 |routine_#33910_luaX_next_local_#4227_ls_IN.base| .cse0)) (+ |routine_#33910_luaX_next_local_#4227_ls.offset| 24) (|read_type_#64._seminfo._i| v__memory_1153 v__memory_ptr.base_1009 v__memory_ptr.offset_1009 |routine_#33910_luaX_next_local_#4227_ls_IN.base| .cse0)) .cse0 289))) _memory) (<= |routine_#33910_luaX_next_local_#4227_ls_IN.offset| |routine_#33910_luaX_next_local_#4227_ls.offset|)))";
//		final String expectedResult = null;
//		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
//	}
//
//
//	// read_type_#64._token is function symbol with
//	// param sorts [(Array Int (Array Int Int)), (Array Int (Array Int Int)), (Array Int (Array Int Int)), Int, Int]
//    // and return sort Int
//	@Test
//	public void daxus02() {
//		final FunDecl[] funDecls = new FunDecl[] {
//				new FunDecl(SmtSortUtils::getIntSort, "routine_#33910_luaX_next_local_#4227_ls_IN.base", "routine_#33910_luaX_next_local_#4227_ls_IN.offset"),
//				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "_memory", "old(_memory)", "read_type_#64._token"),
//			};
//		final String formulaAsString = "(exists ((v__memory_ptr.offset_1308 (Array Int (Array Int Int))) (v__memory_ptr.base_1308 (Array Int (Array Int Int)))) (= _memory (store |old(_memory)| |routine_#33910_luaX_next_local_#4227_ls_IN.base| (let ((.cse2 (+ 32 |routine_#33910_luaX_next_local_#4227_ls_IN.offset|))) (store (let ((.cse0 (let ((.cse3 (select |old(_memory)| |routine_#33910_luaX_next_local_#4227_ls_IN.base|))) (store .cse3 (+ |routine_#33910_luaX_next_local_#4227_ls_IN.offset| 8) (select .cse3 (+ |routine_#33910_luaX_next_local_#4227_ls_IN.offset| 4)))))) (let ((.cse1 (store |old(_memory)| |routine_#33910_luaX_next_local_#4227_ls_IN.base| .cse0))) (store (store .cse0 (+ 16 |routine_#33910_luaX_next_local_#4227_ls_IN.offset|) (|read_type_#64._token| .cse1 v__memory_ptr.base_1308 v__memory_ptr.offset_1308 |routine_#33910_luaX_next_local_#4227_ls_IN.base| .cse2)) (+ |routine_#33910_luaX_next_local_#4227_ls_IN.offset| 24) (|read_type_#64._seminfo._i| .cse1 v__memory_ptr.base_1308 v__memory_ptr.offset_1308 |routine_#33910_luaX_next_local_#4227_ls_IN.base| .cse2)))) .cse2 289)))))";
//		final String expectedResult = null;
//		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
//	}




	//@formatter:on
}
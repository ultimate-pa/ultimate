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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mRealSort;
	private Sort mBoolSort;
	private Sort mIntSort;
	private Sort[] mEmptySort;
	private Term mTrueTerm;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mBoolSort = SmtSortUtils.getBoolSort(mMgdScript);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);
		mEmptySort = new Sort[0];
		mTrueTerm = mScript.term("true");
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void prenexQuantifiedCapture() {
		final Term seventeen = mScript.numeral(BigInteger.valueOf(17));
		final Term fourtytwo = mScript.numeral(BigInteger.valueOf(42));
		final TermVariable x = mScript.variable("x", mIntSort);
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

	public void varStilThereBug() {

		// Sorts
		final Sort sort_Array = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);

		// Constants
		final Term con_0 = mScript.numeral("0");
		final Term con_1 = mScript.numeral("1");

		// Vars
		final TermVariable var_v_oldvalid_88 = mScript.variable("v_old(#valid)_88", sort_Array);
		final TermVariable var_v_valid_207 = mScript.variable("v_#valid_207", sort_Array);
		final TermVariable var_v_probe3_6_p9base_40 = mScript.variable("v_probe3_6_~p~9.base_40", mIntSort);
		final TermVariable var_valid = mScript.variable("#valid", sort_Array);
		final TermVariable var_oldvalid = mScript.variable("old(#valid)", sort_Array);

		// Functions

		// term
		final Term term = mScript.quantifier(1,
				new TermVariable[] { var_v_oldvalid_88, var_v_oldvalid_88, var_v_oldvalid_88 },
				mScript.term("or", mScript.term("not", mScript.term(
						"and",
						mScript.quantifier(1, new TermVariable[] { var_v_probe3_6_p9base_40, var_v_probe3_6_p9base_40 },
								mScript.term("or",
										mScript.term("=", var_v_oldvalid_88,
												mScript.term("store",
														mScript.term("store", var_v_valid_207, var_v_probe3_6_p9base_40,
																con_1),
														var_v_probe3_6_p9base_40, con_0)),
										mScript.term("=", var_v_probe3_6_p9base_40, con_0),
										mScript.term("not",
												mScript.term("=",
														mScript.term("select", var_v_valid_207,
																var_v_probe3_6_p9base_40),
														con_0)))),
						mScript.term("=", var_oldvalid, var_v_valid_207))),
						mScript.term("=", var_valid, var_v_oldvalid_88)));

		PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, term,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		// //Sorts
		// final Sort sort_Bool = SmtSortUtils.getBoolSort(mScript);
		// final Sort sort_Int = SmtSortUtils.getIntSort(mScript);
		// final Sort sort_Array = SmtSortUtils.getArraySort(mScript, sort_Int, sort_Int);
		//
		// //Constants
		// final Term con_0 = script.numeral("0");
		// final Term con_1 = script.numeral("1");
		//
		// //Vars
		// final TermVariable oldValid33 = script.variable("v_old(#valid)_33", sort_Array);
		// final TermVariable valid = script.variable("#valid", sort_Array);
		// final TermVariable oldValid = script.variable("old(#valid)", sort_Array);
		// final TermVariable var_v_entry_point_array7base_21 = script.variable("v_entry_point_~array~7.base_21",
		// sort_Int);
		//
		// //Functions
		//
		// //term
		// final Term term = script.term("or", script.quantifier(0, new TermVariable[]{var_v_entry_point_array7base_21,
		// var_v_entry_point_array7base_21}, script.term("and", script.term("not", script.term("=", script.term("store",
		// script.term("store", oldValid, var_v_entry_point_array7base_21, con_1), var_v_entry_point_array7base_21,
		// con_0), oldValid33)), script.term("=", script.term("select", oldValid, var_v_entry_point_array7base_21),
		// con_0), script.term("not", script.term("=", var_v_entry_point_array7base_21, con_0)))), script.term("=",
		// valid, oldValid33));
		// PartialQuantifierElimination.tryToEliminate(services, services.getLoggingService().getLogger("lol"),
		// mgdScript, term, SimplificationTechnique.SIMPLIFY_DDA,
		// XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}

	@Test
	public void otherArrayBug() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("b", new Sort[0], intintArraySort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		final String formulaAsString =
				"(exists ((a (Array Int Int))) (and (= (select a i) (select b 0)) (= (select a 0) (select b 1))))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);

		final Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mLogger.info("Result: " + result);
		Assert.assertTrue(!SmtUtils.isTrue(result));
	}

	@Test
	public void plrTest1() {
		final String formulaAsString = "(exists ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) ) (and "
				+ "(<= 0 A) " + "(or (and (not B) (not C)) (and C B)) " + "(or (and (not D) (not E)) (and E D)) "
				+ "(or (and F G) (and (not G) (not F))) " + "))";

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);

		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result);

		final LBool checkSatResult = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", mTrueTerm, formulaAsTerm));
		Assert.assertTrue(checkSatResult == LBool.UNSAT);
		Assert.assertTrue(SmtUtils.isTrue(result));
	}

	@Test
	public void plrTest2() {
		mScript.declareFun("T1", new Sort[0], mRealSort);
		mScript.declareFun("T2", new Sort[0], mRealSort);
		final String formulaAsString = "(exists ((A Int) (B Int) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Int)) "
				+ "(or " + "(<= 50.0 T2) " + "(and " + "(not F) " + "(or " + "(and " + "(< T1 50.0) "
				+ "(or (and (not (< B 5)) (not (= H E))) (and (not (= H E)) (or (not F) (not G) (not (= A E)) (not C))))) "
				+ "(and (= H E) (or (not F) (= H E) (not (< B 5)) (not G) (not (= A E)) (not C))) "
				+ "(and (< T1 50.0) (= A E) (< B 5) C (not (= H E)) F G)) " + "(not (= E D))) " + "(< T2 50.0)))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);

		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result);
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	@Test
	public void plrTest3() {
		mScript.declareFun("T1", new Sort[0], mRealSort);
		final String quantVars =
				" (A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Int) (Z Int) (AA Bool) (AB Real) (AC Bool) (AD Int) (AE Bool) (AF Bool) (AG Bool) (AH Real) (AI Bool) (AJ Int) (AK Bool) (AL Bool) (AM Bool) (AN Bool) (AO Bool) (AP Bool) (AQ Bool) (AR Bool) (AS Bool) (AT Int) (AU Bool) (AV Int) (AW Bool) (AX Bool) (AY Bool) (AZ Bool) (BA Bool) (BB Int) (BC Bool) (BD Bool) (BE Bool) (BF Bool) (BG Bool) (BH Int) (BI Bool) (BJ Int) (BK Bool) (BL Bool) (BM Bool) (BN Int) (BO Bool) (BP Bool) (BQ Bool) (BR Bool) (BS Bool) (BT Bool) (BU Bool) (BV Int) (BW Int) (BX Int) (BY Bool) (BZ Bool) (CA Int) (CB Bool) (CC Bool) (CD Bool) (CE Bool) (CF Real) (CG Int) (CH Real) (CI Bool) (CJ Bool) (CK Bool) (CL Bool) (CM Real) (CN Bool) (CO Bool) (CP Int) (CQ Bool) (CR Int) (CS Bool) (CT Bool) (CU Int) (CV Int) (CW Bool) (CX Bool) (CY Bool) (CZ Bool) (DA Bool) (DB Bool) (DC Int) (DD Bool) (DE Real) (DF Int) (DG Int) (DH Bool) (DI Bool) (DJ Bool) (DK Bool) (DL Int) (DM Int) (DN Int) (DO Bool) (DP Bool) (DQ Bool) (DR Bool) (DS Bool) (DT Int) (DU Bool) (DV Real) (DW Int) (DX Bool) (DY Int) (DZ Bool) (EA Bool) (EB Bool) (EC Int) (ED Bool) (EE Bool) (EF Bool) (EG Bool) (EH Bool) (EI Bool) (EJ Bool) (EK Bool) (EL Int) (EM Bool) (EN Bool) (EO Bool) (EP Bool) (EQ Real) (ER Int) (ES Bool) (ET Int) (EU Bool) (EV Bool) (EW Bool) (EX Bool) (EY Int) (EZ Bool) (FA Bool) (FB Bool) (FC Bool) (FD Real) (FE Bool) (FF Bool) (FG Bool) (FH Bool) (FI Bool) (FJ Int) (FK Bool) (FL Bool) (FM Bool) (FN Bool) (FO Int) (FP Bool) (FQ Real) (FR Bool) (FS Bool) (FT Bool) (FU Int) (FV Int) (FW Bool) (FX Bool) (FY Int) (FZ Int) (GA Bool) (GB Bool) (GC Int) (GD Real) (GE Bool) (GF Bool) (GG Int) (GH Bool) (GI Bool) (GJ Bool) (GK Bool) (GL Int) (GM Int) (GN Int) (GO Bool) (GP Bool) (GQ Int) (GR Bool) (GS Bool) (GT Bool) (GU Bool) (GV Bool) (GW Bool) (GX Bool) (GY Bool) (GZ Bool) (HA Bool) (HB Bool) (HC Bool) (HD Int) (HE Bool) (HF Bool) (HG Bool) (HH Int) (HI Bool) (HJ Bool) (HK Bool) (HL Bool) (HM Bool) (HN Int) (HO Bool) (HP Bool) (HQ Bool) (HR Int) (HS Bool) (HT Bool) (HU Bool) (HV Real) (HW Bool) (HX Bool) (HY Bool) (HZ Bool) (IA Bool) (IB Bool) (IC Bool) (ID Bool) (IE Bool) (IF Bool) (IG Bool) (IH Int) (II Bool) (IJ Bool) (IK Bool) (IL Bool) (IM Real) (IN Bool)";
		final String formulaAsString =
				"(and (<= 0 DG) (= AZ HX) (= FV BJ) (or (not BT) DK) (<= 0 B) (= HA FE) (or FW (not AM)) (= IJ AX) (<= 0 DW) (<= AV 7) (= EF BA) (= AC CE) (= FN HI) (or (not GI) GZ) (or (not BQ) DB) (<= CV 255) (or (not FS) IL) (= AI HP) (or (not (< 0 DN)) (= DY 1)) (= AB (/ 3.0 2.0)) (= 2 Z) (= AT 19) (= HB V) (= N HE) (= AP EB) (or AE (not EZ)) (= GM 3) (<= 0 ER) (= DH AG) (or AK (not BD)) (= HJ P) (<= EY 3) (<= DT 3) (or (not EU) IN) (<= 0 EC) (= GN DC) (= X GY) (<= 0 DC) (<= B 15) (= GD 800.0) (= CS EX) (= HF EP) (<= 0 BW) (or HM (not GA)) (= BK DS) (or (not CQ) CI) (or (= 15 GQ) (= 14 GQ) (and (<= 0 GQ) (<= GQ 10))) (= FO HR) (<= IH 2) (or (= 14 ET) (and (<= ET 10) (<= 0 ET)) (= 15 ET)) (<= BX 3) (or (not ES) HY) (or (and GX IB FG S U G DX GP DJ AU BZ BO EV FR) (not (= CR FY))) (= GF DU) (= BM DR) (= BY O) (<= 0 EY) (= IG BE) (= CY EI) (or BL (not FC)) (= FD 4000.0) (or (not GT) J) (= BN 19) (<= 0 CG) (or (not CL) AO) (<= DW 6) (or DD (not GB)) (<= 0 BB) (= 2 GC) (= 50.0 FQ) (= EJ GS) (<= BB 2) (= EG FX) (= GR BF) (or (not AN) IK) (= HT AR) (= Q CK) (<= DC 255) (or (not (= 0 DN)) (= DY 0)) (or I (not E)) (= HO AS) (<= A 9) (<= 0 BV) (<= DM 9) (or (and (not HQ) (not GP)) (and GP (not HQ))) (or (= AD 126) (= AD 127) (and (<= AD 100) (<= 0 AD))) (= FM EH) (= ED EW) (<= 0 IH) (<= 0 HH) (<= 0 DT) (= AL BU) (= IM (/ 3.0 2.0)) (or HS (not FF)) (= R CJ) (<= 0 FZ) (= K BR) (or IC (not HG)) (<= 0 M) (or CD (not EE)) (<= FU 255) (= AY ID) (<= BV 7) (= AW CX) (= FA CB) (<= FZ 658) (= Y HN) (<= 0 AJ) (= DV (/ 3.0 2.0)) (<= HH 1023) (<= 0 FU) (or (not EA) II) (or (= 15 DL) (and (<= 0 DL) (<= DL 10)) (= 14 DL)) (<= ER 9) (= CW AQ) (= E GW) (<= CU 15) (= HL FP) (= CM 500.0) (= HC W) (= 2 HR) (= GK C) (<= AJ 3) (= 2 BH) (<= EL 3) (= CN L) (<= DG 7) (<= BW 63) (= FK GH) (<= EC 63) (<= 0 CV) (= 50.0 AH) (<= CP 9) (or DO (not FL)) (= 4000.0 EQ) (= EO GO) (= 20.0 CF) (= HZ FT) (<= 0 BX) (= BP F) (or (and GP HQ) (and (< T1 50.0) (not GP) HQ) (and (<= 50.0 T1) (not GP))) (= FB CC) (= DP BI) (= DZ BC) (<= 0 GG) (<= GG 255) (= DI CT) (or T (not AA)) (= DE 50.0) (or (not CZ) IE) (or BS (not D)) (= 800.0 HV) (= HW FH) (or AF (not GJ)) (or HK (not (= CR FY))) (<= 0 AV) (= CA FJ) (= EM GV) (<= 0 DM) (<= M 1023) (<= 0 EL) (<= 0 HD) (<= CG 2) (<= 0 A) (= CH 20.0) (or (not EN) (= CR FY)) (<= DF 3) (<= 0 CU) (= FI DQ) (= IF BG) (or (not GU) IA) (or DA (not EK)) (<= HD 3) (= HU GE) (<= 0 DF) (= 1 GL) (<= 0 CP) (or CO (not H)))";
		final int quantor = QuantifiedFormula.EXISTS;
		final Term quantFormula = createQuantifiedFormulaFromString(quantor, quantVars, formulaAsString);
		mLogger.info("Input: " + quantFormula.toStringDirect());
		final Term result = elim(quantFormula);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	@Test
	public void plrTest4() {
		mScript.declareFun("T1", new Sort[0], mRealSort);
		final String formulaAsString =
				"(exists ((A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (AA Bool) (AB Int) (AC Int) (AD Bool) (AE Bool) (AF Bool) (AG Bool)) (or (< T1 50.0) (and (not E) (or (and (not S) (not AE) W) (and (not S) B (not AE)) (and (not S) (not AE) AF) (and (not S) (not AE) J) (and (not S) (not AE) Z) (and (not S) (not AE) F) (and (not S) (not AE) C) (and (not S) (not AE) AG) (and (< T1 50.0) (or (and (not U) (or (and (not J) (or (and (or (and (not O) (or (and (or (and (or (and (not AF) (or (and (not B) (or (and (or (and (not C) (or (and (not Y) (or (and (not F) (or (and (or (and (or (and (not S) (not AA)) (and (not S) AE)) (not G)) (and (not S) AE)) (not Z)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not W)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE)) (not M)) (and (not S) AE)) (not AG)) (and (not S) AE))) (and (not S) AE)) (not AD)) (and (not S) AE))) (and (not S) AE))) (and (not S) AE))) (and (not S) (not AE) AA) (and (not S) (not AE) M) (and (not S) (not AE) U) (and (or (and (not U) (or (and (or (and (not AD) (or (and (not O) (or (and (not AG) (or AE (and (not M) (or (and (not AF) (or (and (not B) (or (and (not W) (or (and (or (and (or (and (not F) (or (and (or (and (or (not AA) AE) (not G)) AE) (not Z)) AE)) AE) (not Y)) AE) (not C)) AE)) AE)) AE)) AE)))) AE)) AE)) AE) (not J)) AE)) AE) (<= 50.0 T1)) (and (not S) (not AE) G) (and (not S) (not AE) AD) (and (not S) (not AE) O) (and (not S) (not AE) Y)) (or (and Q R A T V D X H I K L AE N P) (not (= AC AB))) (not (= AC AB)) (or (not R) (not P) (not AE) (not T) (not D) (not X) (not Q) (not I) (not V) (not L) (not H) (not A) (not K) (not N))) (<= 50.0 T1)))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	@Test
	public void plrTest5() {
		mScript.declareFun("T1", new Sort[0], mRealSort);
		// this was not eliminated ?!
		final String formulaAsString =
				"(exists ((A Int) (B Int) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Int) (AA Int) (AB Bool) (AC Real) (AD Bool) (AE Int) (AF Bool) (AG Bool) (AH Bool) (AI Real) (AJ Bool) (AK Int) (AL Bool) (AM Bool) (AN Bool) (AO Bool) (AP Bool) (AQ Bool) (AR Bool) (AS Bool) (AT Bool) (AU Bool) (AV Int) (AW Bool) (AX Int) (AY Bool) (AZ Bool) (BA Bool) (BB Bool) (BC Bool) (BD Bool) (BE Int) (BF Bool) (BG Bool) (BH Bool) (BI Bool) (BJ Bool) (BK Bool) (BL Int) (BM Bool) (BN Int) (BO Bool) (BP Bool) (BQ Bool) (BR Bool) (BS Int) (BT Bool) (BU Bool) (BV Bool) (BW Bool) (BX Bool) (BY Bool) (BZ Bool) (CA Bool) (CB Int) (CC Int) (CD Int) (CE Bool) (CF Bool) (CG Int) (CH Bool) (CI Bool) (CJ Bool) (CK Bool) (CL Real) (CM Int) (CN Real) (CO Bool) (CP Bool) (CQ Bool) (CR Bool) (CS Bool) (CT Real) (CU Bool) (CV Bool) (CW Int) (CX Bool) (CY Int) (CZ Bool) (DA Bool) (DB Int) (DC Int) (DD Bool) (DE Bool) (DF Bool) (DG Bool) (DH Bool) (DI Bool) (DJ Bool) (DK Int) (DL Bool) (DM Real) (DN Int) (DO Int) (DP Bool) (DQ Bool) (DR Bool) (DS Bool) (DT Int) (DU Int) (DV Int) (DW Bool) (DX Bool) (DY Bool) (DZ Bool) (EA Bool) (EB Int) (EC Bool) (ED Real) (EE Int) (EF Bool) (EG Bool) (EH Int) (EI Bool) (EJ Bool) (EK Bool) (EL Int) (EM Bool) (EN Bool) (EO Bool) (EP Bool) (EQ Bool) (ER Bool) (ES Bool) (ET Bool) (EU Int) (EV Bool) (EW Bool) (EX Bool) (EY Bool) (EZ Bool) (FA Real) (FB Int) (FC Bool) (FD Int) (FE Bool) (FF Bool) (FG Bool) (FH Bool) (FI Int) (FJ Bool) (FK Bool) (FL Bool) (FM Bool) (FN Bool) (FO Real) (FP Bool) (FQ Bool) (FR Bool) (FS Bool) (FT Bool) (FU Int) (FV Bool) (FW Bool) (FX Bool) (FY Bool) (FZ Int) (GA Bool) (GB Real) (GC Bool) (GD Bool) (GE Bool) (GF Bool) (GG Bool) (GH Int) (GI Int) (GJ Bool) (GK Bool) (GL Int) (GM Int) (GN Bool) (GO Bool) (GP Int) (GQ Real) (GR Bool) (GS Bool) (GT Int) (GU Bool) (GV Bool) (GW Bool) (GX Bool) (GY Int) (GZ Int) (HA Int) (HB Bool) (HC Int) (HD Bool) (HE Bool) (HF Bool) (HG Bool) (HH Bool) (HI Bool) (HJ Bool) (HK Bool) (HL Bool) (HM Bool) (HN Bool) (HO Bool) (HP Bool) (HQ Bool) (HR Int) (HS Bool) (HT Bool) (HU Bool) (HV Int) (HW Bool) (HX Bool) (HY Bool) (HZ Bool) (IA Bool) (IB Bool) (IC Int) (ID Bool) (IE Bool) (IF Int) (IG Bool) (IH Bool) (II Bool) (IJ Real) (IK Bool) (IL Bool) (IM Bool) (IN Bool) (IO Bool) (IP Bool) (IQ Bool) (IR Bool) (IS Bool) (IT Bool) (IU Bool) (IV Int) (IW Bool) (IX Bool) (IY Bool) (IZ Bool) (JA Bool) (JB Real) (JC Bool)) (and (<= 0 DO) (= BC IL) (= GI BN) (or (not BY) DR) (<= 0 B) (= HO FP) (or GJ (not AN)) (= IX AZ) (<= 0 EE) (<= AX 7) (= EO BD) (= AD CK) (= FY HW) (or (not GV) HN) (or (not BV) DJ) (<= DC 255) (or (not GD) IZ) (= AJ IE) (or (not (< 0 DV)) (= EH 1)) (= AC (/ 3.0 2.0)) (= 2 AA) (= AV 19) (= HP W) (= O HS) (= AQ EK) (or AF (not FJ)) (= GZ 3) (<= 0 FB) (= DP AH) (or AL (not BG)) (= HX Q) (<= FI 3) (<= EB 3) (or (not FE) JC) (<= 0 EL) (= HA DK) (= Y HM) (<= 0 DK) (<= B 15) (= GQ 800.0) (= CZ FH) (= HT EZ) (<= 0 CC) (or IB (not GN)) (= BO EA) (or (not CX) CO) (or (= 15 HC) (= 14 HC) (and (<= 0 HC) (<= HC 10))) (= FZ IF) (<= IV 2) (or (= 14 FD) (and (<= FD 10) (<= 0 FD)) (= 15 FD)) (<= CD 3) (or (not FC) IM) (or (and HL IP FR T V G EF HD DS AW CF BT FF GC) (not (= CY GL))) (= GS EC) (= BR DZ) (= CE P) (<= 0 FI) (= IU BH) (= DG ER) (or BP (not FN)) (or (= CY GL) (and HL IP FR T V G EF HD DS AW CF BT FF (not (= CY GL)) GC) (and (not (= CY GL)) (or (not IP) (not GC) (not BT) (not T) (not G) (not EF) (not HL) (not DS) (not V) (not CF) (not HD) (not FR) (not AW) (not FF)))) (= FO 4000.0) (or (not HG) K) (= BS 19) (<= 0 CM) (or (not CS) AP) (<= EE 6) (or DL (not GO)) (<= 0 BE) (= 2 GP) (= 50.0 GB) (= ES HF) (<= BE 2) (= EP GK) (= HE BI) (or (not AO) IY) (= IH AT) (= R CR) (<= DK 255) (or (not (= 0 DV)) (= EH 0)) (or I (not E)) (= ID AU) (<= A 9) (<= 0 CB) (<= DU 9) (or (= AE 126) (= AE 127) (and (<= AE 100) (<= 0 AE))) (= FX EQ) (= EM FG) (<= 0 IV) (<= 0 HV) (<= 0 EB) (= AM CA) (= JB (/ 3.0 2.0)) (or IG (not FQ)) (= S CP) (<= 0 GM) (= L BW) (or IQ (not HU)) (<= 0 N) (or CJ (not EN)) (<= GH 255) (= BB IR) (<= CB 7) (= AY DE) (= FL CH) (<= GM 658) (= Z IC) (<= 0 AK) (= ED (/ 3.0 2.0)) (<= HV 1023) (<= 0 GH) (or (not EJ) IW) (or (= 15 DT) (and (<= 0 DT) (<= DT 10)) (= 14 DT)) (<= FB 9) (= DD AR) (= E HK) (<= DB 15) (= IA GA) (= CT 500.0) (= HQ X) (= 2 IF) (= GX C) (<= AK 3) (= 2 BL) (<= EU 3) (= CU M) (<= DO 7) (<= CC 63) (= FV GU) (<= EL 63) (<= 0 DC) (= 50.0 AI) (<= CW 9) (or DW (not FW)) (= 4000.0 FA) (= EY HB) (= 20.0 CL) (= IN GE) (<= 0 CD) (= BU F) (= FM CI) (= DX BM) (= EI BF) (<= 0 GT) (<= GT 255) (= DQ DA) (or U (not AB)) (= DM 50.0) (or (not DH) IS) (or BX (not D)) (= 800.0 IJ) (= IK FS) (or AG (not GW)) (or HY (not (= CY GL))) (<= 0 AX) (= CG FU) (= EV HJ) (<= 0 DU) (<= N 1023) (<= 0 EU) (<= 0 HR) (<= CM 2) (<= 0 A) (= CN 20.0) (or (not EX) (= CY GL)) (<= DN 3) (<= 0 DB) (= FT DY) (= IT BK) (or (not HH) IO) (or DI (not ET)) (or (and (not GF) (not BT) FK) (and (not GF) EW (not BT)) (and (not GF) (not BT) JA) (and (not GF) (not BT) J) (and (not GF) (not BT) CQ) (and (not GF) (not BT) BZ) (and (not GF) (not BT) DF) (and (not GF) (not BT) HZ) (and (< T1 50.0) (or (and (not GG) (or (and (not J) (or (and (or (and (not BA) (or (and (or (and (or (and (not JA) (or (and (not EW) (or (and (or (and (not DF) (or (and (not EG) (or (and (not BZ) (or (and (or (and (or (and (not GF) (not BJ)) (and (not GF) BT)) (not AS)) (and (not GF) BT)) (not CQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not FK)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT)) (not HI)) (and (not GF) BT)) (not HZ)) (and (not GF) BT))) (and (not GF) BT)) (not BQ)) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) BT))) (and (not GF) (not BT) BJ) (and (not GF) (not BT) HI) (and (not GF) (not BT) GG) (and (or (and (not GG) (or (and (or (and (not BQ) (or (and (not BA) (or (and (not HZ) (or BT (and (not HI) (or (and (not JA) (or (and (not EW) (or (and (not FK) (or (and (or (and (or (and (not BZ) (or (and (or (and (or (not BJ) BT) (not AS)) BT) (not CQ)) BT)) BT) (not EG)) BT) (not DF)) BT)) BT)) BT)) BT)))) BT)) BT)) BT) (not J)) BT)) BT) (<= 50.0 T1)) (and (not GF) (not BT) AS) (and (not GF) (not BT) BQ) (and (not GF) (not BT) BA) (and (not GF) (not BT) EG)) (<= HR 3) (= II GR) (<= 0 DN) (= 1 GY) (<= 0 CW) (or CV (not H))) )";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = elim2(formulaAsTerm);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
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
				SmtSortUtils.getArraySort(mScript, mIntSort,
						SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort)));
		mScript.declareFun("i", new Sort[0], mIntSort);

		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) "
				+ "(= a (store v_a i ((as const (Array Int Int)) 0))))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}

	/**
	 * Quantifier elimination use case that comes from using constant arrays to initialize array variables in the C to
	 * Boogie translation. Variant where a helper function is used that is defined via define-function.
	 * (Perhaps this makes no difference.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	@Test
	public void constantArrayTest02() {
		final Sort arrayFromIntToIntToInt = SmtSortUtils.getArraySort(mScript, mIntSort,
						SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort));

		mScript.declareFun("a", new Sort[0], arrayFromIntToIntToInt);
		mScript.declareFun("i", new Sort[0], mIntSort);

		final String functionDefinitionAsString = "(exists ((a (Array Int (Array Int Int))) (i Int)) "
				+ "(store a i ((as const (Array Int Int)) 0)))";
		final Term functionDefinitionAsTerm =
				((QuantifiedFormula) TermParseUtils.parseTerm(mScript, functionDefinitionAsString)).getSubformula();

		mScript.defineFun("~initToZeroAtPointerBaseAddress~int",
				new TermVariable[] {
						mScript.variable("a", arrayFromIntToIntToInt),
						mScript.variable("i", mIntSort)
						},
				arrayFromIntToIntToInt,
				functionDefinitionAsTerm);

		final String formulaAsString =
				"(exists ((v_a (Array Int (Array Int Int)))) "
				+ "(= a (~initToZeroAtPointerBaseAddress~int v_a i)))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		// mLogger.info("Input: " + formulaAsTerm.toStringDirect());
		final Term result = elim(formulaAsTerm);
		mLogger.info("Result: " + result.toStringDirect());
		Assert.assertTrue(!(result instanceof QuantifiedFormula));
	}


	private Term createQuantifiedFormulaFromString(final int quantor, final String quantVars,
			final String formulaAsString) {
		// TODO: DD: Somehow the quantified formulas are too large / strange for TermParseUtils.parseTerm, but this way
		// should also work
		final String[] splitted = quantVars.split("\\)");
		final List<TermVariable> vars = new ArrayList<>();
		for (int i = 0; i < splitted.length; ++i) {
			final String current = splitted[i];
			final String[] tuple = current.substring(2).split(" ");
			final Sort sort;
			switch (tuple[1]) {
			case "Int":
				sort = mIntSort;
				break;
			case "Bool":
				sort = mBoolSort;
				break;
			case "Real":
				sort = mRealSort;
				break;
			default:
				throw new UnsupportedOperationException(tuple[1]);
			}
			mScript.declareFun(tuple[0], mEmptySort, sort);
			vars.add(mScript.variable(tuple[0], sort));
		}

		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		return mScript.quantifier(quantor, vars.toArray(new TermVariable[vars.size()]), formulaAsTerm, new Term[0]);
	}

	private Term elim(final Term quantFormula) {
		return PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, quantFormula,
				SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}


	/**
	 * Special method for partial quantifier elimination that applies only
	 * local elimination techniques and replaces the outermost
	 * quantifier by an existential quantifier.
	 */
	private Term elim2(final Term term) {
		final QuantifiedFormula quantFormula = (QuantifiedFormula) term;
		return PartialQuantifierElimination.quantifierCustom(mServices, mLogger, mMgdScript, PqeTechniques.ALL_LOCAL,
				QuantifiedFormula.EXISTS, Arrays.asList(quantFormula.getVariables()), quantFormula.getSubformula(),
				new Term[0]);
	}

}

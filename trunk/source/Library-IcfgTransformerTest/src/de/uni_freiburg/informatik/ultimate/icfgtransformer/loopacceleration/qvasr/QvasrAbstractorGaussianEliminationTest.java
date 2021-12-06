package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class QvasrAbstractorGaussianEliminationTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mRealSort;

	private QvasrAbstractor mQAbstractor;

	private Term mX;
	private Term mY;
	private Term mA;

	private Term mTwo;
	private Term mOne;
	private Term mZero;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mLogger.info("Before");
		mScript.declareFun("x", new Sort[0], mRealSort);
		mScript.declareFun("y", new Sort[0], mRealSort);
		mScript.declareFun("a", new Sort[0], mRealSort);

		mX = TermParseUtils.parseTerm(mScript, "x");
		mY = TermParseUtils.parseTerm(mScript, "y");
		mA = TermParseUtils.parseTerm(mScript, "a");

		mZero = mScript.decimal("0");
		mOne = mScript.decimal("1");
		mTwo = mScript.decimal("2");

		mQAbstractor = new QvasrAbstractor(mMgdScript, mLogger, mServices);

	}

	/**
	 * Test solving of {{x, 1, 0}, {1, x, 0}} = {{1, 0, 0}, {0, 1, 0}}
	 */
	@Test
	public void testGaussianElimination1() {
		Term[][] matrix = { { mX, mOne, mZero }, { mOne, mX, mZero } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, 2}, {1, 2, 0}} = {{1, 0, 2/x}, {0, 1, -1/x}}
	 */
	@Test
	public void testGaussianElimination2() {
		Term[][] matrix = { { mX, mZero, mTwo }, { mOne, mTwo, mZero } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ 2.0 x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 1.0) x)");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, 2}, {1, y, 0}} = {{1, 0, 2/x}, {0, 1, -2/xy}}
	 */
	@Test
	public void testGaussianElimination3() {
		Term[][] matrix = { { mX, mZero, mTwo }, { mOne, mY, mZero } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ 2.0 x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 2.0) (* y x))");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, y}, {1, y, 0}} = {{1, 0, y/x}, {0, 1, -1/x}}
	 */
	@Test
	public void testGaussianElimination4() {
		Term[][] matrix = { { mX, mZero, mY }, { mOne, mY, mZero } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ y x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 1.0) x)");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + 1, x + y + 1, a}, {1, y + 1, a}} = {{1, 0, 0}, {0, 1, 0}}
	 */
	@Test
	public void testGaussianElimination5() {
		final Term xPYP1 = TermParseUtils.parseTerm(mScript, "(+ x y 1.0)");
		final Term yP1 = TermParseUtils.parseTerm(mScript, "(+ y 1.0)");
		final Term xP1 = TermParseUtils.parseTerm(mScript, "(+ x 1.0)");

		Term[][] matrix = { { xP1, xPYP1, mA }, { mOne, yP1, mA }, { xP1, xP1, mA }, { mOne, mOne, mA } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero }, { mZero, mZero, mOne } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + 1, 2, a}, {1, 2, a}} = {{1, 0, 0}, {0, 1, a/2}}
	 */
	@Test
	public void testGaussianElimination6() {
		final Term xP1 = TermParseUtils.parseTerm(mScript, "(+ x 1.0)");

		Term[][] matrix = { { xP1, mTwo, mA }, { mOne, mTwo, mA }, { xP1, mTwo, mA }, { mOne, mTwo, mA } };
		matrix = mQAbstractor.gaussianSolve(matrix);
		final Term[][] result =
				{ { mOne, mZero, mZero }, { mZero, mOne, TermParseUtils.parseTerm(mScript, "(/ a 2.0)") } };
		testMatrixEquality(matrix, result);
	}

	static void testMatrixEquality(final Term[][] matrix1, final Term[][] matrix2) {
		MatcherAssert.assertThat(matrix1.length, IsEqual.equalTo(matrix2.length));
		MatcherAssert.assertThat(matrix1[0].length, IsEqual.equalTo(matrix2[0].length));
		for (int i = 0; i < matrix1.length; i++) {
			for (int j = 0; j < matrix1[0].length; j++) {
				MatcherAssert.assertThat(matrix1[i][j], IsEqual.equalTo(matrix2[i][j]));
			}
		}
	}

}

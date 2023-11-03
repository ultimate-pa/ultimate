/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.math.BigInteger;
import java.util.Deque;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Test Suite for the {@link QvasrAbstractionJoin} class.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrAbstractionJoinTest {

	private ManagedScript mMgdScript;

	/**
	 * Testsuite setup.
	 */
	@Before
	public void setUp() {
		final IUltimateServiceProvider mServices = UltimateMocks.createUltimateServiceProviderMock();
		final Script mScript = UltimateMocks.createZ3Script();
		final ILogger mLogger = mServices.getLoggingService().getLogger("log");
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mLogger.info("Before");
	}

	/**
	 * Test abstraction join.
	 */
	@Test
	public void testAbstractionJoin0() {
		final Integer[][] simulationMatrixOne = { { -4, 1 }, { 1, 0 } };
		final Rational[][] simulationMatrixTwoRational = {
				{ Rational.valueOf(new BigInteger("-7"), BigInteger.TWO),
						Rational.valueOf(new BigInteger("1"), BigInteger.ONE) },
				{ Rational.valueOf(new BigInteger("1"), BigInteger.ONE),
						Rational.valueOf(new BigInteger("0"), BigInteger.ONE) } };

		final Integer[] resetVectorOneOne = { 1, 1 };
		final Integer[] additionVectorOneOne = { 0, 1 };

		final Integer[] resetVectorTwoOne = { 1, 1 };
		final Integer[] additionVectorTwoOne = { 0, 1 };

		final Qvasr qvasrOne = new Qvasr();
		final Qvasr qvasrTwo = new Qvasr();

		final Rational[] resetVectorOneOneRational =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(resetVectorOneOne);
		final Rational[] additionVectorOneOneRational =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(additionVectorOneOne);

		final Rational[] resetVectorTwoOneRational =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(resetVectorTwoOne);
		final Rational[] additionVectorTwoOneRational =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(additionVectorTwoOne);

		qvasrOne.addTransformer(new Pair<>(resetVectorOneOneRational, additionVectorOneOneRational));
		qvasrTwo.addTransformer(new Pair<>(resetVectorTwoOneRational, additionVectorTwoOneRational));

		final Rational[][] simulationMatrixOneRational =
				QvasrVectorSpaceBasisConstructorTest.integerMatrixToRationalMatrix(simulationMatrixOne);

		final QvasrAbstraction abstractionOne =
				QvasrAbstractionBuilder.constructQvasrAbstraction(simulationMatrixOneRational, qvasrOne);
		final QvasrAbstraction abstractionTwo =
				QvasrAbstractionBuilder.constructQvasrAbstraction(simulationMatrixTwoRational, qvasrTwo);
		final QvasrAbstraction joinedAbstractions =
				QvasrAbstractionJoin.join(mMgdScript, abstractionOne, abstractionTwo).getThird();
		final Rational[][] simulationMatrixResult = {
				{ Rational.valueOf(new BigInteger("1"), BigInteger.ONE),
						Rational.valueOf(new BigInteger("0"), BigInteger.ONE) },
				{ Rational.valueOf(new BigInteger("-7"), BigInteger.TWO),
						Rational.valueOf(new BigInteger("1"), BigInteger.ONE) } };

		final Integer[] resetVectorResultOne = { 1, 1 };
		final Integer[] additionVectorResultOne = { 1, 0 };
		final Rational[] resetVectorResultRationalOne =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(resetVectorResultOne);
		final Rational[] additionVectorResultRationalOne =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(additionVectorResultOne);

		final Integer[] resetVectorResultTwo = { 1, 1 };
		final Rational[] resetVectorResultRationalTwo =
				QvasrVectorSpaceBasisConstructorTest.integerVectorToRationalVector(resetVectorResultTwo);
		final Rational[] additionVectorResultTwo = { Rational.valueOf(new BigInteger("1"), BigInteger.ONE),
				Rational.valueOf(new BigInteger("1"), BigInteger.TWO) };

		final Qvasr qvasrResult = new Qvasr(resetVectorResultRationalTwo, additionVectorResultTwo);
		qvasrResult.addTransformer(new Pair<>(resetVectorResultRationalOne, additionVectorResultRationalOne));

		testQvasrEquality(qvasrResult, joinedAbstractions.getVasr());
		testMatrixEquality(joinedAbstractions.getSimulationMatrix(), simulationMatrixResult);
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

	static void testQvasrEquality(final IVasr<Rational> qvasrOne, final IVasr<Rational> qvasrTwo) {
		MatcherAssert.assertThat(qvasrOne.getTransformer().size(), IsEqual.equalTo(qvasrTwo.getTransformer().size()));
		final Deque<Pair<Rational[], Rational[]>> transformerOne = new HashDeque<>();
		final Deque<Pair<Rational[], Rational[]>> transformerTwo = new HashDeque<>();
		transformerOne.addAll(qvasrOne.getTransformer());
		transformerTwo.addAll(qvasrTwo.getTransformer());
		while (!transformerOne.isEmpty()) {
			final Pair<Rational[], Rational[]> toBecheckedOne = transformerOne.pop();
			final Pair<Rational[], Rational[]> toBecheckedTwo = transformerTwo.pop();
			testTransformerEquality(toBecheckedOne, toBecheckedTwo);
		}
	}

	static void testTransformerEquality(final Pair<Rational[], Rational[]> transformerOne,
			final Pair<Rational[], Rational[]> transformerTwo) {
		for (int i = 0; i < transformerOne.getFirst().length; i++) {
			MatcherAssert.assertThat(transformerOne.getFirst()[i], IsEqual.equalTo(transformerTwo.getFirst()[i]));
		}
		for (int i = 0; i < transformerOne.getSecond().length; i++) {
			MatcherAssert.assertThat(transformerOne.getSecond()[i], IsEqual.equalTo(transformerTwo.getSecond()[i]));
		}
	}

	static void testMatrixEquality(final Rational[][] matrix1, final Rational[][] matrix2) {
		MatcherAssert.assertThat(matrix1.length, IsEqual.equalTo(matrix2.length));
		MatcherAssert.assertThat(matrix1[0].length, IsEqual.equalTo(matrix2[0].length));
		for (int i = 0; i < matrix1.length; i++) {
			for (int j = 0; j < matrix1[0].length; j++) {
				MatcherAssert.assertThat(matrix1[i][j], IsEqual.equalTo(matrix2[i][j]));
			}
		}
	}
}

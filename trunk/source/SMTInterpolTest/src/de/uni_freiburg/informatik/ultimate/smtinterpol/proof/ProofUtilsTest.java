/*
 * Copyright (C) 2012-2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.MinimalProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(JUnit4.class)
public class ProofUtilsTest {

	private final SMTInterpol mSmtInterpol;
	private final Theory mTheory;
	private final Random rng = new Random(123456);
	private final ProofUtils mProofUtils;
	private final MinimalProofChecker mProofChecker;

	public ProofUtilsTest() {
		mSmtInterpol = new SMTInterpol();
		mSmtInterpol.setOption(SMTLIBConstants.PRODUCE_PROOFS, SMTLIBConstants.TRUE);
		mSmtInterpol.setOption(SMTLIBConstants.INTERACTIVE_MODE, SMTLIBConstants.TRUE);
		mSmtInterpol.setLogic(Logics.ALL);
		mTheory = mSmtInterpol.getTheory();
		mProofUtils = new ProofUtils(new ProofRules(mTheory));
		mProofChecker = new MinimalProofChecker(mSmtInterpol, mSmtInterpol.getLogger());
		mSmtInterpol.declareSort("U", 0);
	}

	ProofLiteral termToProofLiteral(Term term) {
		Term atom = term;
		boolean polarity = true;
		while (atom instanceof ApplicationTerm
				&& ((ApplicationTerm) atom).getFunction().getName() == SMTLIBConstants.NOT) {
			atom = ((ApplicationTerm) atom).getParameters()[0];
			polarity = !polarity;
		}
		return new ProofLiteral(atom, polarity);
	}

	void checkProof(final Term proofTerm, final Term... lits) {
		final HashSet<ProofLiteral> expected = new HashSet<>();
		for (int i = 0; i < lits.length; i++) {
			expected.add(termToProofLiteral(lits[i]));
		}
		final ProofLiteral[] provedLits = mProofChecker.getProvedClause(proofTerm);
		final HashSet<ProofLiteral> actual = new HashSet<>(Arrays.asList(provedLits));
		Assert.assertEquals(expected, actual);
	}

	private void checkSingleDivMod(BigInteger num1, BigInteger num2) {
		assert num2.signum() != 0;
		final Sort intSort = mSmtInterpol.sort(SMTLIBConstants.INT);
		final Term op1 = Rational.valueOf(num1, BigInteger.ONE).toTerm(intSort);
		final Term op2 = Rational.valueOf(num2, BigInteger.ONE).toTerm(intSort);
		final Term divTerm = mSmtInterpol.term(SMTLIBConstants.DIV, op1, op2);
		final Term modTerm = mSmtInterpol.term(SMTLIBConstants.MOD, op1, op2);

		final BigInteger expectedMod = num1.mod(num2.abs());
		final BigInteger expectedDiv = num1.subtract(expectedMod).divide(num2);
		final Term expectedModTerm = Rational.valueOf(expectedMod, BigInteger.ONE).toTerm(intSort);
		final Term expectedDivTerm = Rational.valueOf(expectedDiv, BigInteger.ONE).toTerm(intSort);
		final Term expectedDivEq = mSmtInterpol.term(SMTLIBConstants.EQUALS, divTerm, expectedDivTerm);
		final Term expectedModEq = mSmtInterpol.term(SMTLIBConstants.EQUALS, modTerm, expectedModTerm);
		checkProof(mProofUtils.proveDivEquality(divTerm, expectedDivTerm), expectedDivEq);
		checkProof(mProofUtils.proveModConstant(modTerm, expectedModTerm), expectedModEq);
	}

	@Test
	public void testDivModConst() {
		final BigInteger[] values = new BigInteger[] {
				BigInteger.ONE, BigInteger.ZERO, BigInteger.valueOf(-1),
				BigInteger.valueOf(25),
				BigInteger.valueOf(1000000000000000L), BigInteger.valueOf(-1000000000000000L),
				BigInteger.valueOf(5000000000000000L), BigInteger.valueOf(-5000000000000000L),
				BigInteger.valueOf(999999999999999L), BigInteger.valueOf(-999999999999999L)
		};

		for (int i = 0; i < values.length; i++) {
			for (int j = 0; j < values.length; j++) {
				if (values[j].signum() != 0) {
					checkSingleDivMod(values[i], values[j]);
				}
			}
		}
	}

	private void checkSingleIsInt(Rational rat) {
		final Term isIntTerm = mSmtInterpol.term(SMTLIBConstants.TO_INT,
				rat.toTerm(mSmtInterpol.sort(SMTLIBConstants.REAL)));
		final Term result = rat.floor().toTerm(mSmtInterpol.sort(SMTLIBConstants.INT));
		final Term expectedEq = mSmtInterpol.term(SMTLIBConstants.EQUALS, isIntTerm, result);
		checkProof(mProofUtils.proveToIntConstant(isIntTerm, result), expectedEq);
	}

	@Test
	public void testIsIntConst() {
		final Rational[] rats = new Rational[] {
				Rational.ZERO, Rational.ONE, Rational.MONE, Rational.valueOf(3, 2), Rational.valueOf(-3, 2),
				Rational.valueOf(2, 3), Rational.valueOf(-2, 3),
				Rational.valueOf(BigInteger.valueOf(1L), BigInteger.valueOf(1000000000000000L)),
				Rational.valueOf(BigInteger.valueOf(999999999999999L), BigInteger.valueOf(1000000000000000L)),
				Rational.valueOf(BigInteger.valueOf(-1L), BigInteger.valueOf(1000000000000000L)),
				Rational.valueOf(BigInteger.valueOf(-5999999999999999L), BigInteger.valueOf(1000000000000000L)),
				Rational.valueOf(BigInteger.valueOf(-3000000000000001L), BigInteger.valueOf(1000000000000000L))
		};

		for (int i = 0; i < rats.length; i++) {
			checkSingleIsInt(rats[i]);
		}
	}

	private void checkUbvToIntAndBack(BigInteger val, int bitLength) {
		final String[] indices = new String[] { Integer.toString(bitLength) };
		final Sort intSort = mSmtInterpol.sort(SMTLIBConstants.INT);

		final BigInteger pow2 = BigInteger.ONE.shiftLeft(bitLength);
		final BigInteger valMod = val.mod(pow2);

		final Term bv = mSmtInterpol.term("bv" + valMod.toString(), indices, null);
		final Term intbv = mSmtInterpol.term(SMTLIBConstants.UBV_TO_INT, bv);
		final Term nat = Rational.valueOf(val, BigInteger.ONE).toTerm(intSort);
		final Term natMod = Rational.valueOf(valMod, BigInteger.ONE).toTerm(intSort);
		final Term bvnat = mSmtInterpol.term(SMTLIBConstants.INT_TO_BV, indices, null, nat);
		final Term intbvnat = mSmtInterpol.term(SMTLIBConstants.UBV_TO_INT, bvnat);
		checkProof(mProofUtils.proveIntToUbvToIntConstant(nat, BigInteger.valueOf(bitLength)),
				mSmtInterpol.term(SMTLIBConstants.EQUALS, intbvnat, natMod));
		if (nat == natMod) {
			checkProof(mProofUtils.proveUbvToIntConstant(bv), mSmtInterpol.term(SMTLIBConstants.EQUALS, intbv, natMod));
		}
		checkProof(mProofUtils.proveIntToBvConstant(nat, BigInteger.valueOf(bitLength)),
				mSmtInterpol.term(SMTLIBConstants.EQUALS, bvnat, bv));
	}

	@Test
	public void testBvConst() {
		final int[] bitLengths = { 1, 2, 7, 16, 256, 1024 };
		final BigInteger[] values = {
				BigInteger.ZERO, BigInteger.ONE, BigInteger.ONE.negate(),
				BigInteger.valueOf(127),
				BigInteger.valueOf(128),
				BigInteger.valueOf(129),
				BigInteger.valueOf(-5999999999999999L),
				BigInteger.valueOf(999999999999999L),
				new BigInteger("100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
		};
		for (int i = 0; i < bitLengths.length; i++) {
			for (int j = 0; j < values.length; j++) {
				checkUbvToIntAndBack(values[j], bitLengths[i]);
			}
		}
	}

	private void checkBvDiseq(BigInteger val1, BigInteger val2, int bitLength) {
		final String[] indices = new String[] { Integer.toString(bitLength) };
		final BigInteger pow2 = BigInteger.ONE.shiftLeft(bitLength);
		final BigInteger val1Mod = val1.mod(pow2);
		final BigInteger val2Mod = val2.mod(pow2);

		if (val1Mod.equals(val2Mod)) {
			return;
		}

		final Term bv1 = mSmtInterpol.term("bv" + val1Mod.toString(), indices, null);
		final Term bv2 = mSmtInterpol.term("bv" + val2Mod.toString(), indices, null);
		checkProof(mProofUtils.proveDisequality(bv1, bv2),
				mSmtInterpol.term(SMTLIBConstants.NOT, mSmtInterpol.term(SMTLIBConstants.EQUALS, bv1, bv2)));
	}

	@Test
	public void testBvDiseqs() {
		final int[] bitLengths = { 1, 2, 7, 16, 256, 1024 };
		final BigInteger[] values = { BigInteger.ZERO, BigInteger.ONE, BigInteger.ONE.negate(), BigInteger.valueOf(127),
				BigInteger.valueOf(128), BigInteger.valueOf(129), BigInteger.valueOf(-5999999999999999L),
				BigInteger.valueOf(999999999999999L), new BigInteger(
						"100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") };
		for (int i = 0; i < bitLengths.length; i++) {
			for (int j = 0; j < values.length; j++) {
				for (int k = 0; k < j; k++) {
					checkBvDiseq(values[j], values[k], bitLengths[i]);
				}
			}
		}
	}
}

/*
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;

@RunWith(JUnit4.class)
public class EqInterpolatorIntTest {
	SMTInterpol mSolver;
	Clausifier mClausifier;
	Interpolator mInterpolator;

	Theory mTheory;

	Sort mInt;
	Term mA, mB, mS;

	public EqInterpolatorIntTest() {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setOption(":produce-proofs", true);
		mSolver.setLogic("QF_UFLIA");
		mInt = mSolver.sort("Int");
		mSolver.declareFun("a", new Sort[0], mInt);
		mSolver.declareFun("b", new Sort[0], mInt);
		mSolver.declareFun("s", new Sort[0], mInt);
		mClausifier = mSolver.getClausifier();

		mA = mSolver.term("a");
		mB = mSolver.term("b");
		mS = mSolver.term("s");

		mTheory = mSolver.getTheory();
	}

	/**
	 * Test a trivial equality EQ lemma. The cc term is of the form {@code s + k1*a
	 * != s + k2*b + k3} where k3 mod gcd(k1,k2) != 0, and the la term is missing,
	 * since it is a trivial disequality.
	 */
	public void doTestEq1(final Rational k1, final Rational k2, final Rational k3, boolean ccswap,
			boolean addvar, boolean addconst, boolean abswap) {
		addvar = false;
		final Term a = mA;
		final Term b = mB;
		final SMTAffineTerm aterm = new SMTAffineTerm();
		aterm.add(k1, a);
		final SMTAffineTerm bterm = new SMTAffineTerm();
		bterm.add(k2, b);
		bterm.add(k3);
		if (addconst || addvar) {
			if (addvar) {
				aterm.add(Rational.ONE, mS);
				bterm.add(Rational.ONE, mS);
			}
			if (addconst) {
				aterm.add(Rational.ONE);
				bterm.add(Rational.ONE);
			}
		}
		final Term aSmt = aterm.toTerm(mInt);
		final Term bSmt = bterm.toTerm(mInt);
		final Term cceq = ccswap ? mTheory.term("=", aSmt, bSmt) : mTheory.term("=", bSmt, aSmt);
		final ProofLiteral[] lits = new ProofLiteral[] { new ProofLiteral(cceq, false) };
		final Annotation[] mAnnots = new Annotation[] { new Annotation(":EQ", null) };
		final Term lemma = new ProofRules(mTheory).oracle(lits, mAnnots);
		final Set<String> empty = Collections.emptySet();
		@SuppressWarnings("unchecked")
		final Set<String>[] partition = new Set[] { empty, empty };
		mInterpolator = new Interpolator(mSolver.getLogger(), null, null, mTheory, partition, new int[partition.length],
				new TimeoutHandler(mSolver.getTerminationRequest()));
		final HashSet<Term> bsubTerms = mInterpolator.getSubTerms(bSmt);
		final HashSet<Term> asubTerms = mInterpolator.getSubTerms(aSmt);
		for (final Term sub : asubTerms) {
			if (!(sub instanceof ConstantTerm)) {
				mInterpolator.addOccurrence(sub, abswap ? 1 : 0);
			}
		}
		for (final Term sub : bsubTerms) {
			if (!(sub instanceof ConstantTerm)) {
				mInterpolator.addOccurrence(sub, abswap ? 0 : 1);
			}
		}
		final Term[] interpolants = mInterpolator.interpolate(lemma);
		final TermVariable ccVar = mInterpolator.getAtomOccurenceInfo(cceq).getMixedVar();
		final SMTAffineTerm summands = new SMTAffineTerm();
		summands.add(Rational.MONE, ccVar);
		if (addvar) {
			summands.add(Rational.ONE, mSolver.term("s"));
		}
		if (addconst) {
			summands.add(Rational.ONE);
		}
		if (abswap) {
			summands.add(k3);
		}
		final Term rhs = summands.toTerm(mInt);
		final Rational gcd = k1.gcd(k2);
		final Term expected = mTheory.term(SMTLIBConstants.EQUALS,
				mTheory.term(SMTLIBConstants.MOD, rhs, gcd.toTerm(mInt)), Rational.ZERO.toTerm(mInt));
		Assert.assertSame(expected, interpolants[0]);
	}

	public void doTestEq(final boolean ccswap, final boolean abswap, final boolean laIsNeg, final boolean litswap,
			final boolean doubleab, final boolean addconst, boolean addvar) {
		addvar = false;
		final Term a = mA;
		final Term b = mB;
		final SMTAffineTerm aterm = new SMTAffineTerm();
		aterm.add(Rational.ONE, a);
		final SMTAffineTerm bterm = new SMTAffineTerm();
		bterm.add(Rational.ONE, b);
		if (doubleab || addconst || addvar) {
			if (doubleab) {
				aterm.mul(Rational.TWO);
				bterm.mul(Rational.TWO);
			}
			if (addvar) {
				aterm.add(Rational.ONE, mS);
				bterm.add(Rational.ONE, mS);
			}
			if (addconst) {
				aterm.add(Rational.TWO);
				bterm.add(Rational.TWO);
			}
		}
		final Term aSmt = aterm.toTerm(mInt);
		final Term bSmt = bterm.toTerm(mInt);
		final Term cceq = ccswap ? mTheory.term("=", aSmt, bSmt) : mTheory.term("=", bSmt, aSmt);
		final SMTAffineTerm linTerm = new SMTAffineTerm();
		linTerm.add(Rational.ONE, aterm);
		linTerm.add(Rational.MONE, bterm);
		linTerm.mul(linTerm.getGcd().inverse());
		final Term laeq = mTheory.term("=", linTerm.toTerm(mInt), Rational.ZERO.toTerm(mInt));
		final ProofLiteral[] lits = new ProofLiteral[] { new ProofLiteral(laIsNeg ^ litswap ? laeq : cceq, !litswap),
				new ProofLiteral(laIsNeg ^ litswap ? cceq : laeq, litswap) };
		final Annotation[] mAnnots = new Annotation[] { new Annotation(":EQ", null) };
		final Term lemma = new ProofRules(mTheory).oracle(lits, mAnnots);
		final Set<String> empty = Collections.emptySet();
		@SuppressWarnings("unchecked")
		final Set<String>[] partition = new Set[] { empty, empty };
		mInterpolator = new Interpolator(mSolver.getLogger(), null, null, mTheory, partition, new int[partition.length],
				new TimeoutHandler(mSolver.getTerminationRequest()));
		final HashSet<Term> bsubTerms = mInterpolator.getSubTerms(bSmt);
		final HashSet<Term> asubTerms = mInterpolator.getSubTerms(aSmt);
		for (final Term sub : asubTerms) {
			if (!(sub instanceof ConstantTerm)) {
				mInterpolator.addOccurrence(sub, abswap ? 1 : 0);
			}
		}
		for (final Term sub : bsubTerms) {
			if (!(sub instanceof ConstantTerm)) {
				mInterpolator.addOccurrence(sub, abswap ? 0 : 1);
			}
		}
		final Term[] interpolants = mInterpolator.interpolate(lemma);
		final TermVariable ccVar = mInterpolator.getAtomOccurenceInfo(cceq).getMixedVar();
		final TermVariable laVar = mInterpolator.getAtomOccurenceInfo(laeq).getMixedVar();
		Term var, rhs, modTerm = null;
		final SMTAffineTerm summands = new SMTAffineTerm();
		if (laIsNeg) {
			summands.add(Rational.ONE, ccVar);
			if (addvar) {
				summands.add(Rational.MONE, mSolver.term("s"));
			}
			if (addconst) {
				final Rational offset = Rational.TWO.negate();
				summands.add(offset);
			}
			if (abswap) {
				summands.negate();
			}
			var = laVar;
			rhs = summands.toTerm(mInt);
			if (doubleab) {
				modTerm = mTheory.term(SMTLIBConstants.MOD, rhs, Rational.TWO.toTerm(mInt));
				rhs = mTheory.term(SMTLIBConstants.DIV, rhs, Rational.TWO.toTerm(mInt));
			}
		} else {
			Rational factor = Rational.ONE;
			if (doubleab) {
				factor = Rational.TWO;
			}
			if (abswap) {
				factor = factor.negate();
			}
			if (addvar) {
				summands.add(Rational.ONE, mSolver.term("s"));
			}
			summands.add(factor, laVar);
			if (addconst) {
				final Rational offset = Rational.TWO;
				summands.add(offset);
			}
			var = ccVar;
			rhs = summands.toTerm(mInt);
		}
		Term expected = mTheory.term(Interpolator.EQ, var, rhs);
		if (modTerm != null) {
			expected = mTheory.term(SMTLIBConstants.AND, expected,
					mTheory.term(SMTLIBConstants.EQUALS, modTerm, Rational.ZERO.toTerm(mInt)));
		}
		Assert.assertSame(expected, interpolants[0]);
	}

	@Test
	public void testEq() {
		for (int i = 0; i < 128; i++) {
			doTestEq((i & 1) != 0, (i & 2) != 0, (i & 4) != 0, (i & 8) != 0, // NOCHECKSTYLE
					(i & 16) != 0, (i & 32) != 0, (i & 64) != 0);// NOCHECKSTYLE
		}
	}

	@Test
	public void testEq1() {
		final Rational[][] values = { { Rational.valueOf(2, 1), Rational.valueOf(2, 1), Rational.valueOf(1, 1) },
				{ Rational.valueOf(6, 1), Rational.valueOf(6, 1), Rational.valueOf(3, 1) },
				{ Rational.valueOf(6, 1), Rational.valueOf(10, 1), Rational.valueOf(5, 1) },
				{ Rational.valueOf(6, 1), Rational.valueOf(15, 1), Rational.valueOf(10, 1) }, };
		for (int i = 0; i < 16 * values.length; i++) {
			doTestEq1(values[i / 16][0], values[i / 16][1], values[i / 16][2], (i & 1) != 0, (i & 2) != 0, (i & 4) != 0,
					(i & 8) != 0);
		}
	}

}

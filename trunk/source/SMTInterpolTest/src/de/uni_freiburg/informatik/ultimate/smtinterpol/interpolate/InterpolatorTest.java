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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

@RunWith(JUnit4.class)
public class InterpolatorTest {
	SMTInterpol mSolver;
	Clausifier mClausifier;
	Interpolator mInterpolator;

	Theory mTheory;

	Sort mReal;
	Term mA, mB, mS;

	Annotation[] QUOTED_LA = new Annotation[] { new Annotation(":quotedLA", null) };
	Annotation[] QUOTED_CC = new Annotation[] { new Annotation(":quotedCC", null) };

	public InterpolatorTest() {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setOption(":produce-proofs", true);
		mSolver.setLogic("QF_UFLRA");
		mReal = mSolver.sort("Real");
		mSolver.declareFun("a", new Sort[0], mReal);
		mSolver.declareFun("b", new Sort[0], mReal);
		mSolver.declareFun("s", new Sort[0], mReal);
		mClausifier = mSolver.getClausifier();

		mA = mSolver.term("a");
		mB = mSolver.term("b");
		mS = mSolver.term("s");

		mTheory = mSolver.getTheory();
	}

	public void doTestEq(final boolean ccswap, final boolean abswap, final boolean clauseswap, final boolean litswap,
			final boolean doubleab, final boolean addconst, boolean addvar) {
		addvar = false;
		final Term a = mA;
		final Term b = mB;
		InterpolatorAffineTerm aterm = new InterpolatorAffineTerm().add(Rational.ONE, a);
		InterpolatorAffineTerm bterm = new InterpolatorAffineTerm().add(Rational.ONE, b);
		if (doubleab || addconst || addvar) {
			if (doubleab) {
				aterm = aterm.mul(Rational.TWO);
				bterm = bterm.mul(Rational.TWO);
			}
			if (addvar) {
				aterm = aterm.add(Rational.ONE, mS);
				bterm = bterm.add(Rational.ONE, mS);
			}
			if (addconst) {
				aterm = aterm.add(Rational.TWO);
				bterm = bterm.add(Rational.TWO);
			}
		}
		final Term aSmt = aterm.toSMTLib(mTheory, false);
		final Term bSmt = bterm.toSMTLib(mTheory, false);
		Term cceq = ccswap ? mTheory.term("=", aSmt, bSmt) : mTheory.term("=", bSmt, aSmt);
		cceq = mTheory.annotatedTerm(QUOTED_CC, cceq);
		final InterpolatorAffineTerm linTerm = aterm.add(Rational.MONE, bterm);
		linTerm.normalize();
		final InterpolatorAffineTerm zeroterm = new InterpolatorAffineTerm();
		Term laeq = mTheory.term("=", linTerm.toSMTLib(mTheory, false), zeroterm.toSMTLib(mTheory, false));
		laeq = mTheory.annotatedTerm(QUOTED_LA, laeq);
		final Term[] lits = clauseswap
				? litswap ? new Term[] { mTheory.term("not", cceq), laeq }
						: new Term[] { laeq, mTheory.term("not", cceq) }
				: litswap ? new Term[] { mTheory.term("not", laeq), cceq }
						: new Term[] { cceq, mTheory.term("not", laeq) };
		final Term clause = mTheory.term("or", lits);
		final Annotation[] mAnnots = new Annotation[] { new Annotation(":EQ", null) };
		final Term lemma = mTheory.term("@lemma", mTheory.annotatedTerm(mAnnots, clause));
		final Set<String> empty = Collections.emptySet();
		@SuppressWarnings("unchecked")
		final Set<String>[] partition = new Set[] { empty, empty };
		mInterpolator =
				new Interpolator(mSolver.getLogger(), mSolver, null, mTheory, partition, new int[partition.length]);
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
		final Interpolant[] interpolants = mInterpolator.interpolate(lemma);
		final TermVariable ccVar = mInterpolator.getLiteralInfo(cceq).getMixedVar();
		final TermVariable laVar = mInterpolator.getLiteralInfo(laeq).getMixedVar();
		Term var;
		final InterpolatorAffineTerm summands = new InterpolatorAffineTerm();
		if (clauseswap) {
			Rational factor = Rational.ONE;
			if (doubleab) {
				factor = Rational.TWO.inverse();
			}
			if (abswap) {
				factor = factor.negate();
			}

			summands.add(factor, ccVar);
			if (addvar) {
				summands.add(factor.negate(), mSolver.term("s"));
			}
			if (addconst) {
				final Rational offset = factor.mul(Rational.TWO).negate();
				summands.add(offset);
			}
			var = laVar;
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
		}
		final Term rhs = summands.toSMTLib(mTheory, false);
		final Term expected = mTheory.term("=", var, rhs);
		Assert.assertSame(expected, interpolants[0].mTerm);
	}

	@Test
	public void testEq() {
		for (int i = 0; i < 128; i++) {
			doTestEq((i & 1) != 0, (i & 2) != 0, (i & 4) != 0, (i & 8) != 0, // NOCHECKSTYLE
					(i & 16) != 0, (i & 32) != 0, (i & 64) != 0);// NOCHECKSTYLE
		}
	}

}

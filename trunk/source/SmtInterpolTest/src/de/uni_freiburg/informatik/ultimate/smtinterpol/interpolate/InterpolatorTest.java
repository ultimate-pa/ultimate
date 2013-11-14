/*
 * Copyright (C) 2009-2012 University of Freiburg
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
import java.util.Set;

import junit.framework.TestCase;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;

public class InterpolatorTest extends TestCase {
	SMTInterpol benchmark;
	Clausifier clausifier;
	Interpolator interpolator;
	
	Sort real;
	Term a, b, s;
	
	public InterpolatorTest() {
		benchmark = new SMTInterpol(Logger.getRootLogger());
		benchmark.setLogic("QF_UFLRA");
		real = benchmark.sort("Real");
		benchmark.declareFun("a", new Sort[0], real);
		benchmark.declareFun("b", new Sort[0], real);
		benchmark.declareFun("s", new Sort[0], real);
		clausifier = benchmark.getClausifier();
		
		a = benchmark.term("a");
		b = benchmark.term("b");
		s = benchmark.term("s");
	}
	
	public void doTestEq(boolean ccswap, boolean abswap, 
			boolean clauseswap, boolean litswap,
			boolean doubleab, boolean addconst, boolean addvar) {
		addvar = false; //FIXME how to check modulo order of vars?
		Term a = this.a;
		Term b = this.b;
		SharedTerm sa = clausifier.getSharedTerm(a);
		SharedTerm sb = clausifier.getSharedTerm(b);
		if (doubleab || addconst || addvar) {
			SMTAffineTerm aterm = SMTAffineTerm.create(a);
			SMTAffineTerm bterm = SMTAffineTerm.create(b);
			if (doubleab) {
				aterm = aterm.mul(Rational.TWO);
				bterm = bterm.mul(Rational.TWO);
			}
			if (addvar) {
				aterm = aterm.add(SMTAffineTerm.create(s));
				bterm = bterm.add(SMTAffineTerm.create(s));
			}
			if (addconst) {
				aterm = aterm.add(Rational.TWO);
				bterm = bterm.add(Rational.TWO);
			}
			sa = clausifier.getSharedTerm(aterm);
			sb = clausifier.getSharedTerm(bterm);
		}
		CCTermBuilder builder = clausifier.new CCTermBuilder();
		sa.shareWithLinAr(); builder.convert(sa.getTerm());
		sb.shareWithLinAr(); builder.convert(sb.getTerm());
		EqualityProxy eq = sa.createEquality(sb);
		assertNotSame(EqualityProxy.getFalseProxy(), eq);
		assertNotSame(EqualityProxy.getTrueProxy(), eq);
		CCEquality cceq = ccswap
				? eq.createCCEquality(sa, sb) : eq.createCCEquality(sb, sa);
		LAEquality laeq = cceq.getLASharedData();
		Literal[] lits = 
		    clauseswap ? (litswap ? new Literal[] { cceq.negate(), laeq }
		                          : new Literal[] { laeq, cceq.negate() })
	                   : (litswap ? new Literal[] { laeq.negate(), cceq }
	                   			  : new Literal[] { cceq, laeq.negate() });

		Clause clause = new Clause(lits);
		clause.setProof(new LeafNode(LeafNode.EQ, null));
		Set<String> empty = Collections.emptySet();
		@SuppressWarnings("unchecked")
		Set<String>[] partition = new Set[] { empty, empty };
		interpolator = 
			new Interpolator(benchmark.getLogger(), benchmark.getTheory(), 
					partition, clausifier);
		if (abswap) {
			interpolator.addOccurrence(sb, 0);
			interpolator.addOccurrence(sa, 1);
		} else {
			interpolator.addOccurrence(sa, 0);
			interpolator.addOccurrence(sb, 1);
		}
		Interpolant[] interpolants = interpolator.interpolate(clause);
		TermVariable ccVar = interpolator.getLiteralInfo(cceq).getMixedVar();
		TermVariable laVar = interpolator.getLiteralInfo(laeq).getMixedVar();
		Term var;
		InterpolatorAffineTerm summands = new InterpolatorAffineTerm();
		if (clauseswap) {
			Rational factor = Rational.ONE;
			if (doubleab)
				factor = Rational.TWO.inverse();
			if (abswap)
				factor = factor.negate();

			summands.add(factor, ccVar);
			if (addvar)
				summands.add(factor.negate(), benchmark.term("s"));
			if (addconst) {
				Rational offset = factor.mul(Rational.TWO).negate();
				summands.add(offset);
			}
			var = laVar;
		} else {
			Rational factor = Rational.ONE;
			if (doubleab)
				factor = Rational.TWO;
			if (abswap)
				factor = factor.negate();
			if (addvar)
				summands.add(Rational.ONE, benchmark.term("s"));
			summands.add(factor, laVar);
			if (addconst) {
				Rational offset = Rational.TWO;
				summands.add(offset);
			}
			var = ccVar;
		}
		Term rhs = summands.toSMTLib(benchmark.getTheory(), false);
		Term expected = benchmark.term("=", var, rhs);
		assertSame(expected, interpolants[0].m_term);
	}

	public void testEq() {
		for (int i = 0; i < 128; i++)
			doTestEq((i&1) != 0, (i&2) != 0, (i&4) != 0, (i&8) != 0,
					(i&16) != 0, (i&32) != 0, (i& 64) != 0);
	}
	
}

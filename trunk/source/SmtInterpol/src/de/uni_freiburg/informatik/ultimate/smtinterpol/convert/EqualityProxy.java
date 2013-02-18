/*
 * Copyright (C) 2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;

public class EqualityProxy {
	
	/**
	 * Singleton class to represent an equality that is a tautology.
	 * @author Juergen Christ
	 */
	public static final class TrueEqualityProxy extends EqualityProxy {
		private TrueEqualityProxy() {
			super(null, null, null);
		}
		public DPLLAtom getLiteral() {
			throw new InternalError("Should never be called");
		}
	}
	/**
	 * Singleton class to represent an equality that is unsatisfiable.
	 * @author Juergen Christ
	 */
	public static final class FalseEqualityProxy extends EqualityProxy {
		private FalseEqualityProxy() {
			super(null, null, null);
		}
		public DPLLAtom getLiteral() {
			throw new InternalError("Should never be called");
		}
	}
	
	private static final TrueEqualityProxy g_True = new TrueEqualityProxy();
	private static final FalseEqualityProxy g_False = new FalseEqualityProxy();
	
	public static TrueEqualityProxy getTrueProxy() {
		return g_True;
	}
	
	public static FalseEqualityProxy getFalseProxy() {
		return g_False;
	}
	
	private final class RemoveAtom extends Clausifier.TrailObject {

		@Override
		public void undo() {
			m_eqAtom = null;
		}

	}
	
	final Clausifier m_Clausifier;
	final SharedTerm mLhs, mRhs;
	DPLLAtom m_eqAtom;
	
	public EqualityProxy(Clausifier clausifier, SharedTerm lhs, SharedTerm rhs) {
		m_Clausifier = clausifier;
		mLhs = lhs;
		mRhs = rhs;
	}

//	@Override
//	public CCTerm toCCTerm() {
//		if (m_ccterm == null && mRhs == m_converter.TRUE) {
//			m_ccterm = mLhs.toCCTerm();
//			FlatFormula eqFalse = 
//				m_converter.createEqualityFormula(mLhs, m_converter.FALSE);
//			FlatFormula excludedMiddle = 
//				m_converter.convertDisjunction(this, eqFalse); 
//			excludedMiddle.addAsAxiom(null);
//			m_converter.m_UnshareCC.add(this);
//			return m_ccterm;
//		}
//		return super.toCCTerm();
//	}
//	
//	//@Override
//	public Term getSMTTerm(boolean useAuxVars) {
//		Theory t = m_converter.getTheory();
//		Sort sort = mLhs.getSort();
//		FunctionSymbol neq = 
//			t.getFunction("=", new Sort[] { sort, sort });
//		return t.term(neq, mLhs.getSMTTerm(useAuxVars), mRhs.getSMTTerm(useAuxVars)); 
//	}
	
	public LAEquality createLAEquality() {
		/* create la part */
		MutableAffinTerm at = m_Clausifier.createMutableAffinTerm(mLhs);
		at.add(Rational.MONE, m_Clausifier.createMutableAffinTerm(mRhs));
		return m_Clausifier.getLASolver().createEquality
			(m_Clausifier.getStackLevel(), at);
	}
	
	/**
	 * Creates a CCEquality for the given lhs and rhs.  The equality must
	 * match this EqualityFormula, i.e., 
	 * <code>lhs-rhs = c*(this.lhs-this.rhs)</code> for some rational c.
	 * This also has as side-effect, that it creates an LAEquality if it
	 * did not exists before.  For this reason it is only allowed to call
	 * it for integer or real terms. It will register LAEquality and CCEquality
	 * with each other.   
	 * @param lhs the left hand side.
	 * @param rhs the right hand side.
	 * @return The created (or cached) CCEquality.
	 */
	public CCEquality createCCEquality(SharedTerm lhs, SharedTerm rhs) {
		assert lhs.m_ccterm != null && rhs.m_ccterm != null;
		LAEquality laeq;
		if (m_eqAtom == null) {
			m_eqAtom = laeq = createLAEquality();
			m_Clausifier.addToUndoTrail(new RemoveAtom());
		} else if (m_eqAtom instanceof CCEquality) {
			CCEquality eq = (CCEquality) m_eqAtom;
			laeq = eq.getLASharedData();
			if (laeq == null) {
				MutableAffinTerm at = m_Clausifier.createMutableAffinTerm(mLhs);
				at.add(Rational.MONE, m_Clausifier.createMutableAffinTerm(mRhs));
				Rational normFactor = at.getGCD().inverse();
				laeq = createLAEquality();
				laeq.addDependentAtom(eq);
				eq.setLASharedData(laeq, normFactor);
			}
		} else {
			laeq = (LAEquality) m_eqAtom;
		}
		for (CCEquality eq : laeq.getDependentEqualities()) {
			assert (eq.getLASharedData() == laeq);
			if (eq.getLhs() == lhs.m_ccterm && eq.getRhs() == rhs.m_ccterm)
				return eq;
			if (eq.getRhs() == lhs.m_ccterm && eq.getLhs() == rhs.m_ccterm)
				return eq;
		}
		CCEquality eq = m_Clausifier.getCClosure().createCCEquality
			(m_Clausifier.getStackLevel(), lhs.m_ccterm, rhs.m_ccterm);
		MutableAffinTerm at = m_Clausifier.createMutableAffinTerm(lhs);
		at.add(Rational.MONE, m_Clausifier.createMutableAffinTerm(rhs));
		Rational normFactor = at.getGCD().inverse();
		laeq.addDependentAtom(eq);
		eq.setLASharedData(laeq, normFactor);
		return eq;
	}

	private DPLLAtom createAtom() {
		
		if (mLhs.m_ccterm == null && mRhs.m_ccterm == null) {
			/* if both terms do not exist in CClosure yet, it may be better to
			 * create them in linear arithmetic.
			 * Do this, if we don't have a CClosure, or the other term is
			 * already in linear arithmetic.
			 */
			if (m_Clausifier.getCClosure() == null 
					|| mLhs.m_offset != null && mRhs.m_offset == null)
				//m_Clausifier.createMutableAffinTerm(mRhs);
				mRhs.shareWithLinAr();
			if (m_Clausifier.getCClosure() == null 
					|| mLhs.m_offset == null && mRhs.m_offset != null)
				//m_Clausifier.createMutableAffinTerm(mLhs);
				mLhs.shareWithLinAr();
		}
		
		/* check if the shared terms share at least one theory. */
		if (! ( (mLhs.m_ccterm != null && mRhs.m_ccterm != null)
				|| (mLhs.m_offset != null && mRhs.m_offset != null))) {
			/* let them share congruence closure */
			CCTermBuilder cc = m_Clausifier.new CCTermBuilder();
			cc.convert(mLhs.getTerm());
			cc.convert(mRhs.getTerm());
		}

		/* Get linear arithmetic info, if both are arithmetic */
		if (mLhs.m_offset != null && mRhs.m_offset != null) {
			return createLAEquality();
		} else {
			/* create CC equality */
			return m_Clausifier.getCClosure().createCCEquality
				(m_Clausifier.getStackLevel(), mLhs.m_ccterm, mRhs.m_ccterm);
		}		
	}
	
	public DPLLAtom getLiteral() {
		if (m_eqAtom == null) {
			m_eqAtom = createAtom();
			if (m_Clausifier.getLogger().isDebugEnabled())
				m_Clausifier.getLogger().debug("Created Equality: " + m_eqAtom);
		}
		m_Clausifier.getTracker().eq(mLhs.getTerm(), mRhs.getTerm(), m_eqAtom);
		return m_eqAtom;
	}

}

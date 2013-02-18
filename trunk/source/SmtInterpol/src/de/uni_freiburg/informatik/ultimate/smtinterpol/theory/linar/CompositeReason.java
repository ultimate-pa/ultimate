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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


public class CompositeReason extends LAReason {
	private LAReason[] m_reasons;
	private Rational[] m_coeffs;
	private InfinitNumber m_exactBound;

	public CompositeReason(LinVar var, InfinitNumber bound, boolean isUpper,
			LAReason[] reasons, Rational[] coeffs, LiteralReason lastLiteral) {
		super(var, bound, lastLiteral.getStackDepth(), isUpper, lastLiteral);
		assert (lastLiteral != null);
		m_reasons = reasons;
		m_coeffs = coeffs;
		m_exactBound = bound;
		if (var.misint) {
			if (isUpper)
				m_bound = bound.floor();
			else
				m_bound = bound.ceil();
		} else {
			m_bound = bound;
		}
		assert (!getVar().misint || m_bound.isIntegral());
	}
		
	public InfinitNumber getExactBound() {
		// TODO: remove evil hack
		LinVar var = getVar();
		if (var.misint) {
			if (isUpper()
				? getVar().mconstraints.containsKey(getBound())
				: getVar().mconstraints.containsKey(getBound().sub(var.getEpsilon())))
				return getBound();
		}
		return m_exactBound;
	}
	
	@Override
	InfinitNumber explain(LAAnnotation annot,
			InfinitNumber slack, Rational factor, LinArSolve solver) {
		boolean needToExplain = false;
		if (isUpper()) {
			Entry<InfinitNumber, BoundConstraint> nextEntry = 
				getVar().mconstraints.ceilingEntry(getBound());
			if (nextEntry != null) {
				BoundConstraint nextBound = nextEntry.getValue();
				if (nextBound.getDecideStatus() == nextBound
					&& annot.canExplainWith(nextBound)) {
					InfinitNumber diff = nextBound.getBound().sub(getBound());
					if (slack.compareTo(diff) > 0) {
						annot.addLiteral(nextBound.negate(), factor);
						return slack.sub(diff);
					}
				} else {
					needToExplain = true;
				}
			}
		} else {
			Entry<InfinitNumber, BoundConstraint> nextEntry = 
				getVar().mconstraints.lowerEntry(getBound());
			if (nextEntry != null) {
				BoundConstraint nextBound = nextEntry.getValue();
				if (nextBound.getDecideStatus() == nextBound.negate()
					&& annot.canExplainWith(nextBound)) {
					InfinitNumber diff = getBound().sub(nextBound.getInverseBound());
					if (slack.compareTo(diff) > 0) {
						annot.addLiteral(nextBound, factor);
						return slack.sub(diff);
					}
				} else {
					needToExplain = true;
				}
			}
		}
		InfinitNumber diff = !getVar().misint ? InfinitNumber.ZERO 
				: isUpper()
				? m_exactBound.sub(getBound())
				: getBound().sub(m_exactBound);
		int decideLevel = annot.getExplainedLiteral() == null
			? solver.mengine.getDecideLevel()
			: annot.getExplainedLiteral().getAtom().getDecideLevel();
		if (needToExplain || 
			(slack.compareTo(diff) > 0
			 && getLastLiteral().getDecideLevel() >= decideLevel)) {
			boolean enoughSlack = slack.compareTo(diff) > 0;
			if (!enoughSlack) {
				annot.addAnnotation(this, factor, solver);
				return slack;
			}
			slack = slack.sub(diff);
			assert (slack.compareTo(InfinitNumber.ZERO) > 0);
			for (int i = 0; i < m_reasons.length; i++) {
				Rational coeff = m_coeffs[i];
				slack = slack.div(coeff.abs());
				slack = m_reasons[i].explain(annot, 
						slack, factor.mul(coeff), solver);
				slack = slack.mul(coeff.abs());
				assert (slack.compareTo(InfinitNumber.ZERO) > 0);
			}
			return slack;
		}
		Literal lit = solver.createCompositeLiteral(this, annot.getExplainedLiteral());
		assert (lit.getAtom().getDecideStatus() == lit);
		annot.addLiteral(lit.negate(), factor);
		return slack;
	}
}
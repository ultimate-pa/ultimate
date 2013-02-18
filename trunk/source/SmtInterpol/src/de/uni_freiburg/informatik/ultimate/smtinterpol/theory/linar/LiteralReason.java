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

import java.util.ArrayDeque;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;


public class LiteralReason extends LAReason {
	private Literal m_literal;
	ArrayDeque<LAReason> m_dependents;
	private static int s_ctrDependentLists;
	private static int s_ctrDependents;
	
	public LiteralReason(LinVar var, InfinitNumber bound, int depth,
			boolean isUpper, Literal lit, LiteralReason lastLit) {
		super(var, bound, depth, isUpper, lastLit);
		m_literal = lit;
	}

	public LiteralReason(LinVar var, InfinitNumber bound, int depth,
			boolean isUpper, Literal lit) {
		this(var, bound, depth, isUpper, lit, null);
	}

	public Literal getLiteral() {
		return m_literal;
	}
	
	public void addDependent(LAReason reason) {
		assert getLastLiteral() == this;
		if (m_dependents == null) {
			m_dependents = new ArrayDeque<LAReason>();
			s_ctrDependentLists++;
		}
		s_ctrDependents++;
		m_dependents.addFirst(reason);
	}
	
	public Iterable<LAReason> getDependents() {
		if (m_dependents == null)
			return Collections.emptySet();
		return m_dependents;
	}

	@Override
	InfinitNumber explain(LAAnnotation annot, 
			InfinitNumber slack, Rational factor, LinArSolve solver) {
		if (annot.getLiterals().contains(m_literal)) {
			assert getBound().equals(getOldReason().getBound());
			return getOldReason().explain(annot, slack, factor, solver);
		}
		assert(m_literal.getAtom().getDecideStatus() == m_literal);
		if (m_literal.negate() instanceof LAEquality) {
			InfinitNumber newSlack;
			newSlack = slack.sub(getVar().getEpsilon());
			if (newSlack.compareTo(InfinitNumber.ZERO) > 0) {
				return getOldReason().explain(annot, newSlack, factor, solver);
			} else {
				annot.addEQAnnotation(this, factor, solver);
				return slack;
			}
		}
		annot.addLiteral(m_literal.negate(), factor);
		return slack;
	}

	/**
	 * Returns the minimal DPLL decide level on which this reason can 
	 * be propagated.  Normally, this is just the decide level of the
	 * underlying literal.  However, for inequalities the decide level
	 * of the next literal in the chain must be taken into account.
	 * @return the DPLL decide level.
	 */
	public int getDecideLevel() {
		int level = 0;
		LiteralReason reason = this;
		while (true) {
			int reasonLevel = reason.getLiteral().getAtom().getDecideLevel();
			if (reasonLevel > level)
				level = reasonLevel;
			if (!(reason.m_literal.negate() instanceof LAEquality))
				return level;
			reason = reason.getOldReason().getLastLiteral();
		}
	}

	public int getStackPosition() {
		int pos = 0;
		LiteralReason reason = this;
		while (true) {
			int reasonPos = reason.getLiteral().getAtom().getStackPosition();
			if (reasonPos > pos)
				pos = reasonPos;
			if (!(reason.m_literal.negate() instanceof LAEquality))
				return pos;
			reason = reason.getOldReason().getLastLiteral();
		}
	}
}

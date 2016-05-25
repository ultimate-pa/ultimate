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
	private final Literal mLiteral;
	ArrayDeque<LAReason> mDependents;
	
	public LiteralReason(LinVar var, InfinitNumber bound, boolean isUpper,
			Literal lit, LiteralReason lastLit) {
		super(var, bound, isUpper, lastLit);
		mLiteral = lit;
	}

	public LiteralReason(LinVar var, InfinitNumber bound, boolean isUpper,
			Literal lit) {
		this(var, bound, isUpper, lit, null);
	}

	public Literal getLiteral() {
		return mLiteral;
	}
	
	public void addDependent(LAReason reason) {
		assert getLastLiteral() == this;
		if (mDependents == null) {
			mDependents = new ArrayDeque<LAReason>();
		}
		mDependents.addFirst(reason);
	}
	
	public Iterable<LAReason> getDependents() {
		if (mDependents == null) {
			return Collections.emptySet();
		}
		return mDependents;
	}

	@Override
	InfinitNumber explain(Explainer explainer, 
			InfinitNumber slack, Rational factor) {
		if (!explainer.canExplainWith(mLiteral)) {
			assert getBound().equals(getOldReason().getBound());
			return getOldReason().explain(explainer, slack, factor);
		}
		assert(mLiteral.getAtom().getDecideStatus() == mLiteral);
		if (mLiteral.negate() instanceof LAEquality) {
			InfinitNumber newSlack;
			newSlack = slack.sub(getVar().getEpsilon());
			if (newSlack.compareTo(InfinitNumber.ZERO) > 0) {
				return getOldReason().explain(explainer, newSlack, factor);
			} else {
				explainer.addEQAnnotation(this, factor);
				return slack;
			}
		}
		explainer.addLiteral(mLiteral.negate(), factor);
		return slack;
	}

	/**
	 * Returns the minimal DPLL decide level on which the literal
	 * behind this reason can be propagated.  This is just the decide 
	 * level of the underlying literal.
	 * 
	 * Note that this is not necessarily the decide level of this reason.
	 * Use getLastLiteral().getDecideLevel() to get this. 
	 * @return the DPLL decide level.
	 */
	public int getDecideLevel() {
		return getLiteral().getAtom().getDecideLevel();
	}

	/**
	 * Returns the stack position of the literal behind this reason.
	 * @return the stack position of the literal.
	 */
	public int getStackPosition() {
		return getLiteral().getAtom().getStackPosition();
	}
}

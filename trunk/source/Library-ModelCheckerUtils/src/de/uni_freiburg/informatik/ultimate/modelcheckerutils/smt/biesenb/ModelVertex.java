/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * The ModelVertex is part of the {@link PredicateTrie} and stores a model
 *
 * @author Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 */
public class ModelVertex implements IVertex {

	private final Map<Term, Term> mWitness;
	private IVertex mTrueChild;
	private IVertex mFalseChild;

	protected ModelVertex(final IVertex trueChild, final IVertex falseChild, final Map<Term, Term> witness) {
		mWitness = witness;
		mTrueChild = trueChild;
		mFalseChild = falseChild;
	}

	protected void setTrueChild(final IVertex trueChild) {
		mTrueChild = trueChild;
	}

	protected void setFalseChild(final IVertex falseChild) {
		mFalseChild = falseChild;
	}

	protected IVertex getChild(final boolean edge) {
		if (edge) {
			return mTrueChild;
		}
		return mFalseChild;
	}

	/**
	 * swap the predicate "oldChild" with the new predicate
	 *
	 * @param oldChild
	 * @param newChild
	 */
	protected void swapChild(final IVertex oldChild, final IVertex newChild) {
		if (oldChild.equals(mTrueChild)) {
			mTrueChild = newChild;
		} else if (oldChild.equals(mFalseChild)) {
			mFalseChild = newChild;
		} else {
			throw new IllegalArgumentException("the node to swap is not a child of this node");
		}
	}

	protected Map<Term, Term> getWitness() {
		return mWitness;
	}

	@Override
	public String print() {
		return ("inner: " + hashCode() % 100 + mWitness.toString() + " : " + mTrueChild.hashCode() % 100
				+ mTrueChild.toString() + " | " + mFalseChild.hashCode() % 100 + mFalseChild.toString());
	}

	@Override
	public String toString() {
		return mWitness.toString();
	}

}
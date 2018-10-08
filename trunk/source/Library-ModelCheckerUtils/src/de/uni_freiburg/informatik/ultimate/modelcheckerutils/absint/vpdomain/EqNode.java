/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosureElement;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class EqNode implements IEqNodeIdentifier<EqNode>, ICongruenceClosureElement<EqNode> {

	protected final EqNodeAndFunctionFactory mEqNodeFactory;

	protected final Term mTerm;

	private final boolean mDependsOnUntrackedArray;

	public EqNode(final Term term, final EqNodeAndFunctionFactory eqNodeFactory, final boolean dependsOnUntrackedArray) {
		assert term != null;
		mTerm = term;
		mEqNodeFactory = eqNodeFactory;

		mDependsOnUntrackedArray = dependsOnUntrackedArray;
	}

	@Override
	public abstract boolean isLiteral();

	public Collection<TermVariable> getFreeVariables() {
		return Arrays.asList(mTerm.getFreeVars());
	}

	@Override
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public final EqNode renameVariables(final Map<Term, Term> substitutionMapping) {
		final Term substitutedTerm =
				new Substitution(mEqNodeFactory.getScript(), substitutionMapping).transform(getTerm());
		return mEqNodeFactory.getOrConstructNode(substitutedTerm);
	}

	@Override
	public boolean isDependentNonFunctionApplication() {
		// this is the default case NonAtomicBaseNode must override this
		return false;
	}

	@Override
	public Set<EqNode> getSupportingNodes() {
		// this is the default case NonAtomicBaseNode must override this
		throw new UnsupportedOperationException("check isDependent first");
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	public Sort getSort() {
		return mTerm.getSort();
	}

	@Override
	public boolean hasSameTypeAs(final EqNode other) {
		return mTerm.getSort().equals(other.mTerm.getSort());
	}


	/**
	 * default implementation, override in EqFunctionApplicationNode
	 */
	@Override
	public EqNode getArgument() {
		throw new UnsupportedOperationException();
	}

	/**
	 * default implementation, override in EqFunctionApplicationNode
	 */
	@Override
	public EqNode replaceAppliedFunction(final EqNode replacer) {
		throw new UnsupportedOperationException();
	}

	/**
	 * default implementation, override in EqFunctionApplicationNode
	 */
	@Override
	public EqNode replaceArgument(final EqNode replacer) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean dependsOnUntrackedArray() {
		return mDependsOnUntrackedArray;
	}

	@Override
	public final int hashCode() {
		return mTerm.hashCode();
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final EqNode other = (EqNode) obj;
		return other.mTerm == mTerm;
	}
}

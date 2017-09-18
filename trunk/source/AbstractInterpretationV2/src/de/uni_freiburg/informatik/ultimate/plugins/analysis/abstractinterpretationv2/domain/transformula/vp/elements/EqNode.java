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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class EqNode implements IEqNodeIdentifier<EqNode>, ICongruenceClosureElement<EqNode> {

	protected final EqNodeAndFunctionFactory mEqNodeFactory;

	protected boolean mIsConstant;

	private final Set<EqNode> mParents = new HashSet<>();

	protected Term mTerm;

	private final MultiDimensionalSort mMdSort;

	public EqNode(final Term term, final EqNodeAndFunctionFactory eqNodeFactory) {
		mTerm = term;
		mEqNodeFactory = eqNodeFactory;

		mMdSort = mEqNodeFactory.isFunction(term) ? new MultiDimensionalSort(mTerm.getSort()) : null;
	}

	@Override
	public abstract boolean isLiteral();

	public boolean isConstant() {
		return mIsConstant;
	}

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
				new Substitution(mEqNodeFactory.mMgdScript, substitutionMapping).transform(getTerm());
		return mEqNodeFactory.getOrConstructNode(substitutedTerm);
	}

	@Override
	public boolean isDependent() {
		// this is the default case NonAtomicBaseNode must override this
		return false;
	}

	@Override
	public Collection<EqNode> getSupportingNodes() {
		// this is the default case NonAtomicBaseNode must override this
		throw new UnsupportedOperationException("check isDependent first");
	}

//	@Override
//	public Collection<EqFunction> getSupportingFunctions() {
//		// this is the default case NonAtomicBaseNode must override this
//		throw new UnsupportedOperationException("check isDependent first");
//	}



//	@Override
//	public String getFunctionName() {
//		assert isFunction();
////		assert false : "what's the right string here?";
////		return mPvoc.toString();
//		return mTerm.toString();
//	}

	@Override
	public boolean isFunction() {
		return mMdSort != null;
	}

	@Override
	public int getArity() {
		assert isFunction();
		return mMdSort.getDimension();
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	public Sort getSort() {
		assert isFunction();
		return mTerm.getSort();
//		return mMdSort;
	}

	@Override
	public boolean hasSameTypeAs(final EqNode other) {
		return mTerm.getSort().equals(other.mTerm.getSort());
	}

	@Override
	public void addParent(final EqNode parent) {
		mParents.add(parent);
	}

	@Override
	public Set<EqNode> getParents() {
		return Collections.unmodifiableSet(mParents);
	}

	/**
	 * default implementation, override in EqFunctionApplicationNode
	 */
	@Override
	public EqNode getArgument() {
		throw new UnsupportedOperationException();
	}

	/**
	 * unclear if we really want to have this method..
	 */
	@Override
	public int getHeight() {
		throw new UnsupportedOperationException();
	}



}

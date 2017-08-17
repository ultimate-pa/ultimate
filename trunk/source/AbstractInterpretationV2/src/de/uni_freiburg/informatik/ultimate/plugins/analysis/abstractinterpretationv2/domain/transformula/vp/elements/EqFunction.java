/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqFunction implements IEqFunctionIdentifier<EqNode, EqFunction> {

	@Deprecated
	private IProgramVarOrConst mPvoc;

	private final Term mTerm;

	@Deprecated
	private boolean mIsVersioned;

	private final EqNodeAndFunctionFactory mFactory;

	private final int mArity;

	public EqFunction(final Term term, final EqNodeAndFunctionFactory factory) {
		mTerm = term;
		mFactory = factory;
		assert mTerm.getSort().isArraySort();
//		mArity = mTerm.getSort().getArguments().length - 1;
		mArity = new MultiDimensionalSort(mTerm.getSort()).getDimension();
	}

	public boolean isGlobal() {
		return mPvoc.isGlobal();
	}

	public String getProcedure() {
		if (isGlobal()) {
			return null;
		}

		if (mPvoc instanceof IProgramVar) {
			return ((IProgramVar) mPvoc).getProcedure();
		}

		assert false : "how to determine the procedure of a non-global constant?? -- if that makes sense..";
		return null;
	}



	@Override
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public EqFunction renameVariables(final Map<Term, Term> substitutionMapping) {
//		final Term renamed = substitutionMapping.get(mTerm);
//		if (renamed == null) {
//			return this;
//		}
//		return mFactory.getOrConstructEqFunction(mPvoc, renamed);
		return mFactory.constructRenamedEqFunction(this, substitutionMapping);
	}

	public IProgramVarOrConst getPvoc() {
		return mPvoc;
	}

	public String getFunctionName() {
//		assert false : "what's the right string here?";
//		return mPvoc.toString();
		return mTerm.toString();
	}

	@Override
	public int getArity() {
		return mArity;
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	@Deprecated
	public boolean dependsOn(final EqFunction f) {
		return this.equals(f);
	}

	@Override
	@Deprecated
	public boolean isStore() {
		return false;
	}

	@Override
	@Deprecated
	public EqFunction getFunction() {
		throw new AssertionError("check isStore() first");
	}

	@Override
	@Deprecated
	public List<EqNode> getStoreIndices() {
		throw new AssertionError("check isStore() first");
	}

	@Override
	@Deprecated
	public EqNode getValue() {
		throw new AssertionError("check isStore() first");
	}

	@Override
	@Deprecated
	public EqFunction getInnerMostFunction() {
		return this;
	}

}

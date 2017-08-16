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

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@Deprecated
public class EqStoreFunction extends EqFunction {

	private final EqFunction mFunction;
	private final List<EqNode> mIndices;
	private final EqNode mValue;

	public EqStoreFunction(final EqFunction function, final List<EqNode> indices, final EqNode value, final Term term,
			final EqNodeAndFunctionFactory factory) {
		super(term, factory);
		mFunction = function;
		mIndices = indices;
		mValue = value;
	}

	@Override
	public String getFunctionName() {
		assert false : "does not make sense, here";
		return super.getFunctionName();
	}

	@Override
	public boolean dependsOn(final EqFunction f) {
		if (this.equals(f)) {
			return true;
		}
		if ((mFunction instanceof EqStoreFunction)) {
			return mFunction.dependsOn(f);
		}
		return mFunction.equals(f);
	}

	@Override
	public EqFunction getFunction() {
		return mFunction;
	}

	@Override
	public List<EqNode> getStoreIndices() {
		return mIndices;
	}

	@Override
	public EqNode getValue() {
		return mValue;
	}

	@Override
	public boolean isStore() {
		return true;
	}

	@Override
	public EqFunction getInnerMostFunction() {
		return mFunction.getInnerMostFunction();
	}
}

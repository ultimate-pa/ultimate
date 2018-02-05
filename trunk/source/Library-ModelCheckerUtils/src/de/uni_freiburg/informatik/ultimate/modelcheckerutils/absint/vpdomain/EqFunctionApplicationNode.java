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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqFunctionApplicationNode extends EqNode {

	private final EqNode mFunction;
	private final EqNode mArg;

	public EqFunctionApplicationNode(final EqNode function, final EqNode arg, final Term term,
			final EqNodeAndFunctionFactory eqNodeFactory, final boolean isUntrackedArray) {
		super(term, eqNodeFactory, isUntrackedArray);

		mFunction = function;
		mArg = arg;
	}

	@Override
	public EqNode getAppliedFunction() {
		return mFunction;
	}

	@Override
	public EqNode getArgument() {
		return mArg;
	}

	@Override
	public boolean isLiteral() {
		// a function node is never a literal
		return false;
	}

	@Override
	public boolean isFunctionApplication() {
		return true;
	}

	@Override
	public String toString() {
		return mFunction.toString() + "[" + mArg.toString() + "]";
	}

	@Override
	public EqNode replaceAppliedFunction(final EqNode replacer) {
		return mEqNodeFactory.getOrConstructFuncAppElement(replacer, mArg);
	}

	@Override
	public EqNode replaceArgument(final EqNode replacer) {
		return mEqNodeFactory.getOrConstructFuncAppElement(mFunction, replacer);
	}

	@Override
	public EqNode replaceSubNode(final Map<EqNode, EqNode> mapping) {
		final EqNode replacer = mapping.get(this);
		if (replacer != null) {
			return replacer;
		} else {
			return mEqNodeFactory.getOrConstructFuncAppElement(mFunction.replaceSubNode(mapping),
					mArg.replaceSubNode(mapping));
		}
	}

}

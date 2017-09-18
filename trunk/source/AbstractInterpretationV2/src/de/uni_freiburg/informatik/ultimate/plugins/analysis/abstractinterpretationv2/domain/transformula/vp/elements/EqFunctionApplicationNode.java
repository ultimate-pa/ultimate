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

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqFunctionApplicationNode extends EqNode {

	private final EqNode mFunction;
//	private final List<EqNode> mArgs;
	private final EqNode mArg;

//	public EqFunctionApplicationNode(final EqNode function, final List<EqNode> args, final Term term,
	public EqFunctionApplicationNode(final EqNode function, final EqNode arg, final Term term,
			final EqNodeAndFunctionFactory eqNodeFactory) {
		super(term, eqNodeFactory);
//		assert args.size() == function.getArity();
//		assert args.size() > 0;

		mFunction = function;
//		mArgs = Collections.unmodifiableList(args);
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

//	@Override
//	public List<EqNode> getArguments() {
//		return mArgs;
//	}

//	@Override
//	public String toString() {
//		return mFunction.toString() + mArgs.toString();
//	}

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
}

/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqConstantArrayNode extends EqNode {

	private final EqNode mValue;

	public EqConstantArrayNode(final Term term,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final EqNode value) {
		super(term, eqNodeAndFunctionFactory, false);
		mValue = value;
	}

	@Override
	public boolean isConstantFunction() {
		return true;
	}

	/**
	 *
	 * @return the value that this constant array has at every index
	 */
	@Override
	public EqNode getConstantFunctionValue() {
		return mValue;
	}

	@Override
	public boolean isFunctionApplication() {
		return false;
	}

	@Override
	public EqNode getAppliedFunction() {
		throw new AssertionError();
	}

	@Override
	public EqNode replaceSubNode(final Map<EqNode, EqNode> replacementMapping) {
		throw new AssertionError();
	}

	@Override
	public boolean isLiteral() {
		return false;
	}

	@Override
	public boolean isDependentNonFunctionApplication() {
		return true;
	}

	@Override
	public Set<EqNode> getSupportingNodes() {
		return Collections.singleton(getConstantFunctionValue());
	}


}

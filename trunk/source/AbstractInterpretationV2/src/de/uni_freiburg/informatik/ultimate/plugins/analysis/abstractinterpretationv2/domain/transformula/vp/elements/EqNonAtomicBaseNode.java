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

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class EqNonAtomicBaseNode extends EqNode {

	private final Collection<EqNode> mSupporters;

	public EqNonAtomicBaseNode(final Term term, final Collection<EqNode> supporters,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory) {
		super(term, eqNodeAndFunctionFactory);
		assert !supporters.isEmpty();
		assert supporters.stream().allMatch(n -> n instanceof EqAtomicBaseNode);
		mSupporters = Collections.unmodifiableCollection(supporters);
	}

	@Override
	public boolean isLiteral() {
		return false;
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	public boolean isFunctionApplication() {
		return false;
	}

	@Override
	public EqFunction getAppliedFunction() {
		assert false : "check for isFunction() first";
		return null;
	}

	@Override
	public List<EqNode> getArguments() {
		assert false : "check for isFunction() first";
		return null;
	}

	@Override
	public boolean isDependent() {
		return true;
	}

	@Override
	public Collection<EqNode> getSupporters() {
		return mSupporters;
	}
}

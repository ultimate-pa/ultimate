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

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqAtomicBaseNode extends EqNode {

	private final boolean mIsLiteral;
	private final Set<EqNonAtomicBaseNode> mDependentNonAtomicNodes = new HashSet<>();

	public EqAtomicBaseNode(final Term term, final boolean isLiteral,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final boolean isUntrackedArray) {
		super(term, eqNodeAndFunctionFactory, isUntrackedArray);
		mIsLiteral = isLiteral;
	}

	@Override
	public String toString() {
		return mTerm.toString();
	}

	@Override
	public boolean isLiteral() {
		return mIsLiteral;
	}

	public void addDependentNonAtomicBaseNode(final EqNonAtomicBaseNode node) {
		mDependentNonAtomicNodes.add(node);
	}

	public Set<EqNonAtomicBaseNode> getDependentNonAtomicBaseNodes() {
		return Collections.unmodifiableSet(mDependentNonAtomicNodes);
	}

	@Override
	public boolean isFunctionApplication() {
		return false;
	}

	@Override
	public EqNode getAppliedFunction() {
		throw new IllegalStateException("check for isFunctionApplication() first");
	}

	@Override
	public EqNode replaceSubNode(final Map<EqNode, EqNode> mapping) {
		final EqNode replacer = mapping.get(this);
		if (replacer != null) {
			return replacer;
		}
		return this;
	}
}

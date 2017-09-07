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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class EqNode implements IEqNodeIdentifier<EqNode, EqFunction>,
		ICongruenceClosureElement<EqNode, EqFunction> {

	protected final EqNodeAndFunctionFactory mEqNodeFactory;

	protected boolean mIsConstant;

	private final Set<EqNode> mParents = new HashSet<>();

	protected Term mTerm;

	public EqNode(final Term term, final EqNodeAndFunctionFactory eqNodeFactory) {
		mTerm = term;
		mEqNodeFactory = eqNodeFactory;
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
	public Collection<EqNode> getSupporters() {
		// this is the default case NonAtomicBaseNode must override this
		throw new UnsupportedOperationException("check isDependent first");
	}
}

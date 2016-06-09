/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IFunctionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of the function evaluator in the {@link CongruenceDomain}.
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CongruenceFunctionEvaluator
        implements IFunctionEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> {

	private final String mName;
	private final int mInParamCount;

	private final List<IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar>> mInputParamEvaluators;

	protected CongruenceFunctionEvaluator(final String name, final int numInParams) {
		mName = name;
		mInParamCount = numInParams;
		mInputParamEvaluators = new ArrayList<>();
	}

	@Override
	public List<IEvaluationResult<CongruenceDomainValue>> evaluate(final CongruenceDomainState currentState) {
		final List<IEvaluationResult<CongruenceDomainValue>> returnList = new ArrayList<>();

		final CongruenceDomainEvaluationResult res = new CongruenceDomainEvaluationResult(CongruenceDomainValue.createTop(),
		        new BooleanValue());

		returnList.add(res);
		return returnList;
	}

	@Override
	public void addSubEvaluator(final IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator) {
		if (mInputParamEvaluators.size() < mInParamCount) {
			mInputParamEvaluators.add(evaluator);
		} else {
			throw new UnsupportedOperationException("No sub evaluators left.");
		}
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return new HashSet<>();
	}

	@Override
	public boolean hasFreeOperands() {
		return mInputParamEvaluators.size() < mInParamCount;
	}

	@Override
	public boolean containsBool() {
		return false;
	}

	@Override
	public int getNumberOfInParams() {
		return mInParamCount;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(mName).append('(');
		for (int i = 0; i < mInputParamEvaluators.size(); i++) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(mInputParamEvaluators.get(i));
		}
		sb.append(')');

		return sb.toString();
	}

	@Override
	public List<CongruenceDomainState> inverseEvaluate(final IEvaluationResult<CongruenceDomainValue> computedValue,
	        final CongruenceDomainState currentState) {
		final List<CongruenceDomainState> returnList = new ArrayList<>();
		returnList.add(currentState);
		return returnList;
	}
}

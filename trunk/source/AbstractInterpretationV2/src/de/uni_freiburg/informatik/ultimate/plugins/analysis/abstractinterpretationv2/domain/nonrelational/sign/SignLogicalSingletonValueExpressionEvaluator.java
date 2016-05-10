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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents a boolean expression in the {@link SignDomain}. This requires the program to be analyzed to contain the
 * literals "True" or "False". If "True" is read, the value of {@link this} is <code>true</code>, otherwise
 * <code>false</code>.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignLogicalSingletonValueExpressionEvaluator extends SignSingletonValueExpressionEvaluator<Boolean>
        implements IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> {

	private BooleanValue mBooleanValue;

	public SignLogicalSingletonValueExpressionEvaluator(String value) {
		super(value);
		mBooleanValue = new BooleanValue(false);
	}

	@Override
	public List<IEvaluationResult<Values>> evaluate(SignDomainState currentState) {
		final List<IEvaluationResult<Values>> returnList = new ArrayList<>();

		if (mValue) {
			returnList.add(new SignDomainValue(Values.POSITIVE));
		} else {
			returnList.add(new SignDomainValue(Values.NEGATIVE));
		}

		return returnList;
	}

	private SignDomainState logicallyInterpret(SignDomainState currentState) {
		return currentState;
	}

	@Override
	protected Boolean instantiate(String value) {
		Boolean bool = Boolean.valueOf(value);

		return bool;
	}

	@Override
	protected int getSignum() {
		return 0;
	}

	private boolean logicalEvaluation(SignDomainState currentState) {
		// TODO Think about if this is right here.
		return false;
	}

	@Override
	public boolean containsBool() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<SignDomainState> inverseEvaluate(final IEvaluationResult<Values> computedValue,
	        final SignDomainState currentState) {
		// TODO Auto-generated method stub
		return null;
	}
}

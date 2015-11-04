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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * The binary expression evaluator of the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalBinaryExpressionEvaluator
        implements INAryEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	protected IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> mLeftSubEvaluator;
	protected IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> mRightSubEvaluator;

	protected final Set<String> mVariableSet;

	protected final Logger mLogger;
	protected Operator mOperator;

	/**
	 * Creates an instance of the binary expression evaluator of the interval domain.
	 * 
	 * @param services
	 */
	protected IntervalBinaryExpressionEvaluator(Logger logger) {
		mLogger = logger;
		mVariableSet = new HashSet<String>();
	}

	/**
	 * Internal constructor for testing reasons. Not accessible from outside of the package.
	 * 
	 * <p>
	 * <b>Note:</b> This constructor is for testing purposes only and is not supposed to be called outside of the unit
	 * tests as it does not instanciate the class correctly.
	 * </p>
	 */
	IntervalBinaryExpressionEvaluator() {
		mLogger = null;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> evaluate(
	        IAbstractState<CodeBlock, BoogieVar> currentState) {

		assert currentState != null;

		for (String var : mLeftSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}
		for (String var : mRightSubEvaluator.getVarIdentifiers()) {
			mVariableSet.add(var);
		}

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> firstResult = mLeftSubEvaluator
		        .evaluate(currentState);
		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> secondResult = mRightSubEvaluator
		        .evaluate(currentState);

		switch (mOperator) {
		case ARITHPLUS:
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(
			        firstResult.getResult().getEvaluatedValue().add(secondResult.getResult().getEvaluatedValue()),
			        currentState);
		case ARITHMINUS:
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(
			        firstResult.getResult().getEvaluatedValue().subtract(secondResult.getResult().getEvaluatedValue()),
			        currentState);
		case ARITHMUL:
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(
			        firstResult.getResult().getEvaluatedValue().multiply(secondResult.getResult().getEvaluatedValue()),
			        currentState);
		case COMPEQ:
		default:
			mLogger.warn(
			        "Possible loss of precision: cannot handle operator " + mOperator + ". Returning current state.");
			return new EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>(null, currentState);
		}
	}

	@Override
	public void addSubEvaluator(
	        IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator) {
		if (mLeftSubEvaluator != null && mRightSubEvaluator != null) {
			throw new UnsupportedOperationException("There are no free sub evaluators left to be assigned.");
		}

		if (mLeftSubEvaluator == null) {
			mLeftSubEvaluator = evaluator;
			return;
		}

		mRightSubEvaluator = evaluator;

	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return (mLeftSubEvaluator == null || mRightSubEvaluator == null);
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;

		mOperator = (Operator) operator;
	}

	@Override
	public int getArity() {
		return 2;
	}
}

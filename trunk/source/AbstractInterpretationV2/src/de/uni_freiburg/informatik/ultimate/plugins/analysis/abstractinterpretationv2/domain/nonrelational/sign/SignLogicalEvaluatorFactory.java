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

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignLogicalEvaluatorFactory implements IEvaluatorFactory<SignDomainValue, SignDomainState, CodeBlock> {

	private final ILogger mLogger;

	public SignLogicalEvaluatorFactory(ILogger logger) {
		mLogger = logger;
	}

	@Override
	public INAryEvaluator<SignDomainValue, SignDomainState, CodeBlock> createNAryExpressionEvaluator(int arity,
			EvaluatorType type) {

		assert arity >= 1 && arity <= 2;

		switch (arity) {
		case 1:
			return new SignLogicalUnaryExpressionEvaluator();
		case 2:
			return new SignLogicalBinaryExpressionEvaluator(mLogger, type);
		default:
			throw new UnsupportedOperationException("Arity of " + arity + " is not implemented.");
		}
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createSingletonValueExpressionEvaluator(String value,
			Class<?> valueType) {

		if (valueType.equals(BigInteger.class)) {
			return new SignLogicalSingletonIntegerExpressionEvaluator(value);
		}

		if (valueType.equals(BigDecimal.class)) {
			return new SignLogicalSingletonDecimalExpressionEvaluator(value);
		}

		if (valueType.equals(Boolean.class)) {
			return new SignLogicalSingletonValueExpressionEvaluator(value);
		}

		throw new UnsupportedOperationException("The type " + valueType.toString() + " is not supported.");
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock>
			createSingletonVariableExpressionEvaluator(IBoogieVar variableName) {
		return new SignLogicalSingletonVariableExpressionEvaluator(variableName);
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock>
			createSingletonLogicalValueExpressionEvaluator(BooleanValue value) {
		return null;
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createFunctionEvaluator(String functionName,
			int inputParamCount) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createConditionalEvaluator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IEvaluator<SignDomainValue, SignDomainState, CodeBlock> createSingletonValueTopEvaluator() {
		// TODO Auto-generated method stub
		return null;
	}

}

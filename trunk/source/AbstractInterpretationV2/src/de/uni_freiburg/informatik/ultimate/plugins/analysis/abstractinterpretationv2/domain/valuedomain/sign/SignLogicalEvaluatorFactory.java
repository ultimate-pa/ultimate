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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignLogicalEvaluatorFactory implements IEvaluatorFactory<Values, CodeBlock, IBoogieVar> {

	SignStateConverter<CodeBlock, IBoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	public SignLogicalEvaluatorFactory(IUltimateServiceProvider services,
	        SignStateConverter<CodeBlock, IBoogieVar> stateConverter) {
		mServices = services;
		mStateConverter = stateConverter;
	}

	@Override
	public INAryEvaluator<Values, CodeBlock, IBoogieVar> createNAryExpressionEvaluator(int arity) {

		assert arity >= 1 && arity <= 2;

		switch (arity) {
		case 1:
			return new SignLogicalUnaryExpressionEvaluator();
		case 2:
			return new SignLogicalBinaryExpressionEvaluator(mServices);
		default:
			throw new UnsupportedOperationException("Arity of " + arity + " is not implemented.");
		}
	}

	@Override
	public IEvaluator<Values, CodeBlock, IBoogieVar> createSingletonValueExpressionEvaluator(String value,
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
	public IEvaluator<Values, CodeBlock, IBoogieVar> createSingletonVariableExpressionEvaluator(String variableName) {
		return new SignLogicalSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}

	@Override
	public IEvaluator<Values, CodeBlock, IBoogieVar> createSingletonLogicalValueExpressionEvaluator(
	        BooleanValue value) {
		return null;
	}

}

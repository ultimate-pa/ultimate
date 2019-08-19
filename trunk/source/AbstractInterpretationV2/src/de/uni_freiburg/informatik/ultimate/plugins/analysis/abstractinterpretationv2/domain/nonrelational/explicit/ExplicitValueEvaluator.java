/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.ExpressionNormalizer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class ExplicitValueEvaluator extends NonrelationalEvaluator<ExplicitValueState, BaseExplicitValueValue> {

	protected ExplicitValueEvaluator(final ILogger logger, final BoogieSymbolTable boogieSymbolTable,
			final IBoogieSymbolTableVariableProvider bpl2SmtSymbolTable, final int maxParallelStates,
			final int maxRecursionDepth) {
		super(logger, boogieSymbolTable, bpl2SmtSymbolTable, maxParallelStates, maxRecursionDepth);
	}

	@Override
	protected IEvaluatorFactory<BaseExplicitValueValue, ExplicitValueState>
			createEvaluatorFactory(final int maxParallelStates, final int maxRecursionDepth) {

		final EvaluatorFactory.Function<String, BaseExplicitValueValue> valueExpressionEvaluatorCreator =
				(value, type) -> new ExplicitValueValue(Rational.valueOf(new BigInteger(value), BigInteger.ONE));
		final INonrelationalValueFactory<BaseExplicitValueValue> valueFac =
				new INonrelationalValueFactory<BaseExplicitValueValue>() {

					@Override
					public BaseExplicitValueValue createTopValue() {
						return ExplicitValueTop.DEFAULT;
					}

					@Override
					public BaseExplicitValueValue createBottomValue() {
						return ExplicitValueBottom.DEFAULT;
					}
				};
		return new EvaluatorFactory<>(getLogger(), maxParallelStates, maxRecursionDepth, valueFac,
				valueExpressionEvaluatorCreator);
	}

	@Override
	protected Expression normalizeExpression(final Expression expr) {
		return new ExpressionNormalizer().transform(expr);
	}
}

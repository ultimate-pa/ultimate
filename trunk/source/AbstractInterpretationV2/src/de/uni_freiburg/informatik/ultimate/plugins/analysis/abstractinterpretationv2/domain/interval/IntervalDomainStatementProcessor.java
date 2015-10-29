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

import java.math.BigDecimal;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomainStatementProcessor extends BoogieVisitor {

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	private IntervalDomainState<CodeBlock, BoogieVar> mOldState;
	private IntervalDomainState<CodeBlock, BoogieVar> mNewState;

	IEvaluatorFactory<IntervalDomainValue, CodeBlock, BoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mExpressionEvaluator;

	private String mLhsVariable;
	
	private final Logger mLogger;

	protected IntervalDomainStatementProcessor(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
		mServices = services;
		
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		
		mLhsVariable = null;
	}

	public IntervalDomainState<CodeBlock, BoogieVar> process(IntervalDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = (IntervalDomainState<CodeBlock, BoogieVar>) mOldState.copy();

		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

		mEvaluatorFactory = new IntervalEvaluatorFactory(mServices, mStateConverter);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			mExpressionEvaluator = new ExpressionEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>();

//			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			processExpression(rhs[i]);

			assert mExpressionEvaluator.isFinished();
			assert mExpressionEvaluator.getRootEvaluator() != null;

			final IEvaluationResult<IntervalDomainValue> result = mExpressionEvaluator.getRootEvaluator()
			        .evaluate(mOldState);

			final IntervalDomainValue newValue = result.getResult();
			mNewState.setValue(varname, newValue);
		}
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

	@Override
	protected void visit(IntegerLiteral expr) {
		assert mEvaluatorFactory != null;
		
		final IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(BinaryExpression expr) {

		mLogger.fatal(expr);
		mLogger.fatal(expr.getOperator().toString());
		mLogger.fatal(expr.getLeft());
		mLogger.fatal(expr.getRight());
		
		super.visit(expr);
	}

	@Override
	protected void visit(AssumeStatement statement) {
		mEvaluatorFactory = new IntervalLogicalEvaluatorFactory();
		
		super.visit(statement);
	}

}

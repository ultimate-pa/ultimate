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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import java.math.BigDecimal;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainStatementProcessor extends BoogieVisitor {

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final BoogieSymbolTable mSymbolTable;

	private IntervalDomainState<CodeBlock, BoogieVar> mOldState;
	private IntervalDomainState<CodeBlock, BoogieVar> mNewState;

	IEvaluatorFactory<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	private final Logger mLogger;

	protected IntervalDomainStatementProcessor(Logger logger,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter, BoogieSymbolTable symbolTable) {
		mStateConverter = stateConverter;
		mSymbolTable = symbolTable;

		mLogger = logger;

		mEvaluatorFactory = new IntervalEvaluatorFactory(mLogger, mStateConverter);

		mLhsVariable = null;
	}

	public IntervalDomainState<CodeBlock, BoogieVar> process(IntervalDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = (IntervalDomainState<CodeBlock, BoogieVar>) mOldState.copy();

		mLhsVariable = null;

		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			mExpressionEvaluator = new ExpressionEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar>();

			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			processExpression(rhs[i]);

			assert mExpressionEvaluator.isFinished() : "Expression evaluator is not finished";
			assert mExpressionEvaluator.getRootEvaluator() != null;

			final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> result = mExpressionEvaluator
			        .getRootEvaluator().evaluate(mOldState);

			final IntervalDomainValue newValue = result.getResult().getEvaluatedValue();

			if (newValue == null) {
				mNewState.setValue(varname, new IntervalDomainValue());
			} else {
				mNewState.setValue(varname, newValue);
			}
		}
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

	@Override
	protected void visit(IntegerLiteral expr) {
		assert mEvaluatorFactory != null;

		final IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(BinaryExpression expr) {

		final INAryEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createNAryExpressionEvaluator(2);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(AssumeStatement statement) {

		mEvaluatorFactory = new IntervalLogicalEvaluatorFactory(mLogger, mStateConverter);
		
		mExpressionEvaluator = new ExpressionEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar>();

		Expression formula = statement.getFormula();

		if (formula instanceof BooleanLiteral) {
			BooleanLiteral boolform = (BooleanLiteral) formula;
			if (!boolform.getValue()) {
				mNewState.setToBottom();
			}
			// We return since newState is a copy of the old state and the application of true is the old state.
			return;
		}

		processExpression(formula);

		assert mExpressionEvaluator.isFinished();

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> evaluationResult = mExpressionEvaluator
		        .getRootEvaluator().evaluate(mOldState);

		mNewState = (IntervalDomainState<CodeBlock, BoogieVar>) evaluationResult.getResult().getEvaluatedState().copy();

	}

	@Override
	protected void visit(FunctionApplication expr) {
		IntervalSingletonValueExpressionEvaluator evaluator;

		List<Declaration> decls = mSymbolTable.getFunctionOrProcedureDeclaration(expr.getIdentifier());

		// If we don't have a specification for the function, we return top.
		if (decls == null || decls.isEmpty()) {
			evaluator = new IntervalSingletonValueExpressionEvaluator(new IntervalDomainValue());
		} else {

			assert decls.get(0) instanceof FunctionDeclaration;

			FunctionDeclaration fun = (FunctionDeclaration) decls.get(0);

			// If the body is empty (as in undefined), we return top.
			if (fun.getBody() == null) {
				evaluator = new IntervalSingletonValueExpressionEvaluator(new IntervalDomainValue());
			} else {
				// TODO Handle bitshifts, bitwise and, bitwise or, etc.

				throw new UnsupportedOperationException(
				        "The function application for not inlined functions is not yet supported.");
			}
		}

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(HavocStatement statement) {

		for (VariableLHS var : statement.getIdentifiers()) {
			mNewState.setValue(var.getIdentifier(), new IntervalDomainValue());
		}
	}

	@Override
	protected void visit(IdentifierExpression expr) {

		final IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createSingletonVariableExpressionEvaluator(expr.getIdentifier());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(UnaryExpression expr) {

		final INAryEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createNAryExpressionEvaluator(1);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		final IEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> evaluator = mEvaluatorFactory
		        .createSingletonLogicalValueExpressionEvaluator(expr.getValue());

		mExpressionEvaluator.addEvaluator(evaluator);
	}

}

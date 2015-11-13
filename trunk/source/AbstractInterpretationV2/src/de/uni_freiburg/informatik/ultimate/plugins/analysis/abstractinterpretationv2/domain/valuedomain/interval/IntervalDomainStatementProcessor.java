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

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainStatementProcessor extends BoogieVisitor {

	private final BoogieSymbolTable mSymbolTable;

	private IntervalDomainState mOldState;
	private IntervalDomainState mNewState;

	IEvaluatorFactory<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	private final Logger mLogger;

	protected IntervalDomainStatementProcessor(Logger logger, BoogieSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
		mLogger = logger;
		// mEvaluatorFactory = new IntervalEvaluatorFactory(mLogger, mStateConverter);
		mLhsVariable = null;
	}

	public IntervalDomainState process(IntervalDomainState oldState, Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = (IntervalDomainState) mOldState.copy();

		mLhsVariable = null;

		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(AssignmentStatement statement) {

		mEvaluatorFactory = new IntervalEvaluatorFactory(mLogger);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			mExpressionEvaluator = new ExpressionEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar>();

			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			processExpression(rhs[i]);

			assert mExpressionEvaluator.isFinished() : "Expression evaluator is not finished";
			assert mExpressionEvaluator.getRootEvaluator() != null;

			final IEvaluationResult<IntervalDomainEvaluationResult> result = mExpressionEvaluator.getRootEvaluator()
					.evaluate(mOldState);

			final IntervalDomainValue newValue = result.getResult().getEvaluatedValue();

			if (newValue == null) {
				// If the value is null, it should be a boolean. If not, throw exception.
				if (ILogicalEvaluator.class.isAssignableFrom(mExpressionEvaluator.getRootEvaluator().getClass())) {
					mNewState.setBooleanValue(varname, getBooleanValue());
				} else {
					throw new UnsupportedOperationException("The evaluator should be a logical one.");
				}
				// mNewState.setValue(varname, new IntervalDomainValue());
			} else {
				final IBoogieVar type = mOldState.getVariableType(varname);
				if (type.getIType() instanceof PrimitiveType) {
					final PrimitiveType primitiveType = (PrimitiveType) type.getIType();

					if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
						if (ILogicalEvaluator.class
								.isAssignableFrom(mExpressionEvaluator.getRootEvaluator().getClass())) {
							mNewState.setBooleanValue(varname, getBooleanValue());
						}
					} else {
						mNewState.setValue(varname, newValue);
					}
				} else if (type.getIType() instanceof ArrayType) {
					// TODO:
					// We treat Arrays as normal variables for the time being.
					mNewState.setValue(varname, newValue);
				} else {
					mNewState.setValue(varname, newValue);
				}
			}
		}
	}

	private BooleanValue getBooleanValue() {
		return ((ILogicalEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar>) mExpressionEvaluator
				.getRootEvaluator()).booleanValue();
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

	@Override
	protected void visit(IntegerLiteral expr) {
		assert mEvaluatorFactory != null;

		final IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(BinaryExpression expr) {

		final INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createNAryExpressionEvaluator(2);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(AssumeStatement statement) {

		mEvaluatorFactory = new IntervalLogicalEvaluatorFactory(mLogger);
		mExpressionEvaluator = new ExpressionEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar>();

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

		final IEvaluationResult<IntervalDomainEvaluationResult> evaluationResult = mExpressionEvaluator.getRootEvaluator()
				.evaluate(mOldState);

		mNewState = (IntervalDomainState) evaluationResult.getResult().getEvaluatedState().copy();

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

		mEvaluatorFactory = new IntervalEvaluatorFactory(mLogger);

		for (VariableLHS var : statement.getIdentifiers()) {
			final IBoogieVar type = mOldState.getVariables().get(var.getIdentifier());

			if (type.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) type.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					mNewState.setBooleanValue(var.getIdentifier(), new BooleanValue());
				} else {
					mNewState.setValue(var.getIdentifier(), new IntervalDomainValue());
				}
			} else if (type.getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				mNewState.setValue(var.getIdentifier(), new IntervalDomainValue());
			} else {
				mNewState.setValue(var.getIdentifier(), new IntervalDomainValue());
			}
		}
	}

	@Override
	protected void visit(IdentifierExpression expr) {

		final IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonVariableExpressionEvaluator(expr.getIdentifier());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(UnaryExpression expr) {
		final INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createNAryExpressionEvaluator(1);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		final IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonLogicalValueExpressionEvaluator(new BooleanValue(expr.getValue()));

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(ArrayStoreExpression expr) {
		// TODO Implement proper handling of arrays.
		mExpressionEvaluator
				.addEvaluator(new IntervalLogicalSingletonValueExpressionEvaluator(new IntervalDomainValue()));
	}

	@Override
	protected void visit(ArrayAccessExpression expr) {
		// TODO Implement proper handling of arrays.
		mExpressionEvaluator
				.addEvaluator(new IntervalLogicalSingletonValueExpressionEvaluator(new IntervalDomainValue()));
	}

}

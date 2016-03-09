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

import java.math.BigInteger;
import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link CongruenceDomainState} for the given statement.
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CongruenceDomainStatementProcessor extends BoogieVisitor {

	private final BoogieSymbolTable mSymbolTable;

	private CongruenceDomainState mOldState;
	private List<CongruenceDomainState> mReturnState;

	IEvaluatorFactory<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	private final Logger mLogger;

	protected CongruenceDomainStatementProcessor(final Logger logger, final BoogieSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
		mLogger = logger;
		mLhsVariable = null;
	}

	public List<CongruenceDomainState> process(final CongruenceDomainState oldState, final Statement statement) {

		mReturnState = new ArrayList<>();

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;

		mLhsVariable = null;
		
		processStatement(statement);

		assert mReturnState.size() != 0;

		return mReturnState;
	}

	@Override
	protected Statement processStatement(Statement statement) {
		if (statement instanceof AssignmentStatement) {
			handleAssignment((AssignmentStatement) statement);
			return statement;
		} else if (statement instanceof AssumeStatement) {
			handleAssumeStatement((AssumeStatement) statement);
			return statement;
		} else if (statement instanceof HavocStatement) {
			handleHavocStatement((HavocStatement) statement);
			return statement;
		}

		return super.processStatement(statement);
	}
	
	@Override
	protected Expression processExpression(Expression expr) {	
		if (expr instanceof ArrayStoreExpression) {
			mExpressionEvaluator.addEvaluator(new CongruenceSingletonValueExpressionEvaluator(new CongruenceDomainValue()));
			return expr;
		} else if (expr instanceof ArrayAccessExpression) {
			mExpressionEvaluator.addEvaluator(new CongruenceSingletonValueExpressionEvaluator(new CongruenceDomainValue()));
			return expr;
		}
		final ExpressionTransformer t = new ExpressionTransformer();
		Expression newExpr = t.transform(expr);
		if (!newExpr.toString().equals(expr.toString()) && mLogger.isDebugEnabled()) {
			mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Expression ")
			        .append(BoogiePrettyPrinter.print(expr)).append(" rewritten to: ")
			        .append(BoogiePrettyPrinter.print(newExpr)));
		}
		return super.processExpression(newExpr);
	}

	private void handleAssignment(final AssignmentStatement statement) {
		mEvaluatorFactory = new CongruenceEvaluatorFactory(mLogger);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		List<CongruenceDomainState> currentStateList = new ArrayList<>();
		currentStateList.add(mOldState);

		for (int i = 0; i < lhs.length; i++) {
			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			mExpressionEvaluator = new ExpressionEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar>();

			processExpression(rhs[i]);

			assert mExpressionEvaluator.isFinished() : "Expression evaluator is not finished";
			assert mExpressionEvaluator.getRootEvaluator() != null;

			final List<CongruenceDomainState> newStates = new ArrayList<>();

			for (final CongruenceDomainState currentState : currentStateList) {
				final List<IEvaluationResult<CongruenceDomainValue>> result = mExpressionEvaluator.getRootEvaluator()
				        .evaluate(currentState);

				if (result.size() == 0) {
					throw new UnsupportedOperationException(
					        "There is supposed to be at least on evaluation result for the assingment expression.");
				}

				for (final IEvaluationResult<CongruenceDomainValue> res : result) {
					CongruenceDomainState newState = currentState.copy();

					final IBoogieVar type = newState.getVariableDeclarationType(varname);
					// Always assign non-constant values for variables
					//CongruenceDomainValue newValue = new CongruenceDomainValue(res.getValue().value(), false);
					
					CongruenceDomainValue newValue = res.getValue();
					
					if (type.getIType() instanceof PrimitiveType) {
						final PrimitiveType primitiveType = (PrimitiveType) type.getIType();
						if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
							newState = currentState.setBooleanValue(varname, res.getBooleanValue());
						} else {
							newState = newState.setValue(varname, newValue);
						}
					} else if (type.getIType() instanceof ArrayType) {
						// TODO:
						// We treat Arrays as normal variables for the time being.
						newState = newState.setValue(varname, newValue);
					} else {
						newState = newState.setValue(varname, newValue);
					}

					newStates.add(newState);
				}
			}

			currentStateList = newStates;
		}

		mReturnState.addAll(currentStateList);
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

	@Override
	protected void visit(IntegerLiteral expr) {
		assert mEvaluatorFactory != null;
		
		final IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);

		mExpressionEvaluator.addEvaluator(evaluator);
	}
	
	@Override
	protected void visit(RealLiteral expr) {
		assert mEvaluatorFactory != null;

		mExpressionEvaluator.addEvaluator(new CongruenceSingletonValueExpressionEvaluator(new CongruenceDomainValue()));
	}

	@Override
	protected void visit(BinaryExpression expr) {

		assert mEvaluatorFactory != null;

		final INAryEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
		        .createNAryExpressionEvaluator(2, EvaluatorUtils.getEvaluatorType(expr.getType()));

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	private void handleAssumeStatement(final AssumeStatement statement) {
		mEvaluatorFactory = new CongruenceEvaluatorFactory(mLogger);
		mExpressionEvaluator = new ExpressionEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar>();

		final Expression formula = statement.getFormula();

		if (formula instanceof BooleanLiteral) {
			final BooleanLiteral boolform = (BooleanLiteral) formula;
			if (!boolform.getValue()) {
				mReturnState.add(mOldState.bottomState());
			} else {
				mReturnState.add(mOldState);
			}
			// We return since newState is a copy of the old state and the application of true is the old state.
			return;
		}

		processExpression(formula);

		assert mExpressionEvaluator.isFinished();

		final List<IEvaluationResult<CongruenceDomainValue>> result = mExpressionEvaluator.getRootEvaluator()
		        .evaluate(mOldState);

		for (final IEvaluationResult<CongruenceDomainValue> res : result) {
			if (res.getValue().isBottom() || res.getBooleanValue().getValue() == Value.BOTTOM
			        || res.getBooleanValue().getValue() == Value.FALSE) {
				mReturnState.add(mOldState.bottomState());
			} else {
				final List<CongruenceDomainState> resultStates = mExpressionEvaluator.getRootEvaluator()
				        .inverseEvaluate(res, mOldState);
				mReturnState.addAll(resultStates);
			}
		}
	}

	@Override
	protected void visit(FunctionApplication expr) {
		assert mEvaluatorFactory != null;

		IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator;

		List<Declaration> decls = mSymbolTable.getFunctionOrProcedureDeclaration(expr.getIdentifier());

		// If we don't have a specification for the function, we return top.
		if (decls == null || decls.isEmpty()) {
			evaluator = new CongruenceSingletonValueExpressionEvaluator(new CongruenceDomainValue());
		} else {

			assert decls.get(0) instanceof FunctionDeclaration;

			FunctionDeclaration fun = (FunctionDeclaration) decls.get(0);

			// If the body is empty (as in undefined), we return top.
			if (fun.getBody() == null) {
				// evaluator = new CongruenceSingletonValueExpressionEvaluator(new CongruenceDomainValue());
				evaluator = mEvaluatorFactory.createFunctionEvaluator(fun.getIdentifier(), fun.getInParams().length);
			} else {
				// TODO Handle bitshifts, bitwise and, bitwise or, etc.

				throw new UnsupportedOperationException(
				        "The function application for not inlined functions is not yet supported.");
			}
		}

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	protected void handleHavocStatement(HavocStatement statement) {
		mEvaluatorFactory = new CongruenceEvaluatorFactory(mLogger);

		CongruenceDomainState currentNewState = mOldState.copy();

		for (VariableLHS var : statement.getIdentifiers()) {
			final IBoogieVar type = mOldState.getVariables().get(var.getIdentifier());

			if (type.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) type.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					currentNewState = currentNewState.setBooleanValue(var.getIdentifier(), new BooleanValue());
				} else {
					currentNewState = currentNewState.setValue(var.getIdentifier(), new CongruenceDomainValue());
				}
			} else if (type.getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				currentNewState = currentNewState.setValue(var.getIdentifier(), new CongruenceDomainValue());
			} else {
				currentNewState = currentNewState.setValue(var.getIdentifier(), new CongruenceDomainValue());
			}
		}

		mReturnState.add(currentNewState);
	}

	@Override
	protected void visit(IdentifierExpression expr) {
		assert mEvaluatorFactory != null;

		final IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonVariableExpressionEvaluator(expr.getIdentifier());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(UnaryExpression expr) {
		assert mEvaluatorFactory != null;

		final INAryEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createNAryExpressionEvaluator(1, EvaluatorType.INTEGER);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		assert mEvaluatorFactory != null;

		final IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
				.createSingletonLogicalValueExpressionEvaluator(new BooleanValue(expr.getValue()));

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(ArrayStoreExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}

	@Override
	protected void visit(ArrayAccessExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}
	
	@Override
	protected void visit(IfThenElseExpression expr) {
		assert mEvaluatorFactory != null;

		final IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator = mEvaluatorFactory
		        .createConditionalEvaluator();

		mExpressionEvaluator.addEvaluator(evaluator);

		// Create a new expression for the negative case
		UnaryExpression newUnary = new UnaryExpression(expr.getLocation(), UnaryExpression.Operator.LOGICNEG,
		        expr.getCondition());

		// This expression should be added first to the evaluator inside the handling of processExpression.
		processExpression(newUnary);
	}	
}

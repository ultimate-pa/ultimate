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
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link SignDomainState} for the given Statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignDomainStatementProcessor extends BoogieVisitor {

	private SignDomainState mOldState;
	private List<SignDomainState> mNewState;
	private SignDomainState mCurrentNewState;

	private final IUltimateServiceProvider mServices;

	IEvaluatorFactory<Values, SignDomainState, CodeBlock, IBoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	protected SignDomainStatementProcessor(IUltimateServiceProvider services) {
		mServices = services;
	}

	protected List<SignDomainState> process(SignDomainState oldState, Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = new ArrayList<>();
		mCurrentNewState = oldState.copy();

		mLhsVariable = null;

		// Process the current statement and alter mNewState
		processStatement(statement);

		return mNewState;
	}

	@Override
	protected void visit(HavocStatement statement) {

		mEvaluatorFactory = new SignEvaluatorFactory(mServices);

		final VariableLHS[] vars = statement.getIdentifiers();
		for (final VariableLHS var : vars) {
			mCurrentNewState.setValue(var.getIdentifier(), new SignDomainValue(Values.TOP));
		}
		
		mNewState.add(mCurrentNewState);
	}

	@Override
	protected void visit(AssignmentStatement statement) {
		mEvaluatorFactory = new SignEvaluatorFactory(mServices);

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();

		for (int i = 0; i < lhs.length; i++) {
			mExpressionEvaluator = new ExpressionEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar>();

			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);
			assert mLhsVariable != null;
			final String varname = mLhsVariable;
			mLhsVariable = null;

			processExpression(rhs[i]);
			assert mExpressionEvaluator.isFinished();
			final List<IEvaluationResult<Values>> result = mExpressionEvaluator.getRootEvaluator().evaluate(mOldState);

			for (final IEvaluationResult<Values> res : result) {
				final SignDomainState retState = mCurrentNewState.copy();
				final SignDomainValue newValue = new SignDomainValue((Values) res.getResult());
				retState.setValue(varname, newValue);
				mNewState.add(retState);
			}
		}
	}

	@Override
	protected void visit(AssumeStatement statement) {

		// We are in a situation where we need to evaluate a logical formula (and update the abstract state
		// accordingly). Therefore, we use the SignLogicalEvaluatorFactory to allow for all evaluators to also be able
		// to interpret the result logically and return a new abstract state which will then be intersected with the
		// current abstract state.
		mEvaluatorFactory = new SignLogicalEvaluatorFactory(mServices);

		mExpressionEvaluator = new ExpressionEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar>();

		Expression formula = statement.getFormula();

		if (formula instanceof BooleanLiteral) {
			BooleanLiteral binform = (BooleanLiteral) formula;
			if (!binform.getValue()) {
				final SignDomainState ret = mCurrentNewState.copy();
				ret.setToBottom();
				mNewState.add(ret);
			}
			return;
		}

		processExpression(formula);

		// final IAbstractState<CodeBlock, IBoogieVar> newState = ((ILogicalEvaluator<Values, CodeBlock, IBoogieVar>)
		// mExpressionEvaluator
		// .getRootEvaluator()).logicallyInterpret(mOldState);
		throw new UnsupportedOperationException("Logical interpretation not yet implemented.");

		// mNewState = (SignDomainState) newState;
	}

	@Override
	protected void visit(AssertStatement statement) {
		mEvaluatorFactory = new SignLogicalEvaluatorFactory(mServices);
		// TODO Auto-generated method stub
		super.visit(statement);
	}

	@Override
	protected void visit(BinaryExpression expr) {
		INAryEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> evaluator;

		evaluator = mEvaluatorFactory.createNAryExpressionEvaluator(2);

		evaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		if (!(mEvaluatorFactory instanceof SignLogicalEvaluatorFactory)) {
			throw new UnsupportedOperationException(
			        "Boolean literas are only allowed in a boolean context, i.e. when visiting logic formulas.");
		}

		final SignLogicalEvaluatorFactory logicalEvaluatorFactory = (SignLogicalEvaluatorFactory) mEvaluatorFactory;

		final String booleanValue = expr.getValue() ? "True" : "False";

		IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> booleanExpressionEvaluator = logicalEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(booleanValue, Boolean.class);

		mExpressionEvaluator.addEvaluator(booleanExpressionEvaluator);
	}

	@Override
	protected void visit(RealLiteral expr) {
		IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> integerExpressionEvaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(IntegerLiteral expr) {

		IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> integerExpressionEvaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);

		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(UnaryExpression expr) {

		SignUnaryExpressionEvaluator unaryExpressionEvaluator = (SignUnaryExpressionEvaluator) mEvaluatorFactory
		        .createNAryExpressionEvaluator(1);

		unaryExpressionEvaluator.setOperator(expr.getOperator());

		mExpressionEvaluator.addEvaluator(unaryExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(IdentifierExpression expr) {

		final IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> variableExpressionEvaluator = mEvaluatorFactory
		        .createSingletonVariableExpressionEvaluator(expr.getIdentifier());

		mExpressionEvaluator.addEvaluator(variableExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}

}

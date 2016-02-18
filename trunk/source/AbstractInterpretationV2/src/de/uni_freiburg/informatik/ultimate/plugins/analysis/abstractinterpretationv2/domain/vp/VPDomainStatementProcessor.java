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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link VPDomainState} for the given Statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class VPDomainStatementProcessor extends BoogieVisitor {

	private VPDomainState mOldState;
	private List<VPDomainState> mNewState;
	private VPDomainState mCurrentNewState;

	private final IUltimateServiceProvider mServices;

	IEvaluatorFactory<Values, VPDomainState, CodeBlock, IBoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	protected VPDomainStatementProcessor(IUltimateServiceProvider services) {
		mServices = services;
	}

	protected List<VPDomainState> process(VPDomainState oldState, Statement statement) {

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
		
		final VPDomainState retState = mCurrentNewState.copy();
		Set<Expression> exprSet;
		
		final VariableLHS[] vars = statement.getIdentifiers();
		for (final VariableLHS var : vars) {
			
			if (retState.getExpressionMap().containsKey(var.getIdentifier())) {
				retState.getExpressionMap().clear();
				retState.getExpressionMap().get(var.getIdentifier()).addAll(retState.getExprSet());
			} else {
				exprSet = new HashSet<Expression>();
				exprSet.addAll(retState.getExprSet());
				retState.getExpressionMap().put(var.getIdentifier(), exprSet);
			}
		}
		mNewState.add(retState);
	}

	@Override
	protected void visit(AssignmentStatement statement) {
//		mEvaluatorFactory = new VPEvaluatorFactory(mServices);
		
		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();
		final VPDomainState retState = mCurrentNewState.copy();
		
		for (int i = 0; i < lhs.length; i++) {
//			mExpressionEvaluator = new ExpressionEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar>();

			assert mLhsVariable == null;
			processLeftHandSide(lhs[i]);	// determine mLhsVariable
			
			assert mLhsVariable != null;
			final String varName = mLhsVariable;
			mLhsVariable = null;

//			processExpression(rhs[i]);
//			assert mExpressionEvaluator.isFinished();
			
			retState.getExprSet().add(rhs[i]);
			if (retState.getVarExprMap().containsKey(varName)) {
				retState.getVarExprMap().get(varName).clear();
				retState.getVarExprMap().get(varName).add(rhs[i]);
			} else {
				Set<Expression> exprSet = new HashSet<Expression>();
				exprSet.add(rhs[i]);
				retState.getVarExprMap().put(varName, exprSet);
			}
		}
		mNewState.add(retState);
	}
	
	@Override
	protected void visit(WhileStatement statement) {
		
		for (Statement stmt : statement.getBody()) {
			processStatement(stmt);
			assert mNewState.size() == 1;
			mOldState = mCurrentNewState.copy();
			mCurrentNewState = mNewState.get(0).copy();
			mNewState.clear();
		}
		mNewState.add(mCurrentNewState);
	}
	
	@Override
	protected void visit(IfStatement statement) {
		
		final VPDomainState thenPartState;
		final VPDomainState elsePartState;
		
		for (Statement stmt : statement.getThenPart()) {
			processStatement(stmt);
			assert mNewState.size() == 1;
			mOldState = mCurrentNewState.copy();
			mCurrentNewState = mNewState.get(0).copy();
			mNewState.clear();
		}
		thenPartState = mCurrentNewState.copy();

		for (Statement stmt : statement.getElsePart()) {
			processStatement(stmt);
			assert mNewState.size() == 1;
			mOldState = mCurrentNewState.copy();
			mCurrentNewState = mNewState.get(0).copy();
			mNewState.clear();
		}
		elsePartState = mCurrentNewState.copy();
		
		mNewState.add(thenPartState);
		mNewState.add(elsePartState);
		
	}
	
	@Override
	protected void visit(AssumeStatement statement) {
		mNewState.add(mCurrentNewState);
	}

	@Override
	protected void visit(AssertStatement statement) {
//		mEvaluatorFactory = new VPLogicalEvaluatorFactory(mServices);
//		// TODO Auto-generated method stub
		super.visit(statement);
	}

	@Override
	protected void visit(BinaryExpression expr) {
		INAryEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> evaluator;

//		evaluator = mEvaluatorFactory.createNAryExpressionEvaluator(2, EvaluatorUtils.getEvaluatorType(expr.getType()));
//
//		evaluator.setOperator(expr.getOperator());
//
//		mExpressionEvaluator.addEvaluator(evaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(BooleanLiteral expr) {
		
	}

	@Override
	protected void visit(RealLiteral expr) {
		IEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> integerExpressionEvaluator = mEvaluatorFactory
		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);

		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(IntegerLiteral expr) {
//
//		IEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> integerExpressionEvaluator = mEvaluatorFactory
//		        .createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);
//
//		mExpressionEvaluator.addEvaluator(integerExpressionEvaluator);
	}

	@Override
	protected void visit(UnaryExpression expr) {

//		VPUnaryExpressionEvaluator unaryExpressionEvaluator = (VPUnaryExpressionEvaluator) mEvaluatorFactory
//		        .createNAryExpressionEvaluator(1, EvaluatorUtils.getEvaluatorType(expr.getType()));
//
//		unaryExpressionEvaluator.setOperator(expr.getOperator());
//
//		mExpressionEvaluator.addEvaluator(unaryExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(IdentifierExpression expr) {

//		final IEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> variableExpressionEvaluator = mEvaluatorFactory
//		        .createSingletonVariableExpressionEvaluator(expr.getIdentifier());
//
//		mExpressionEvaluator.addEvaluator(variableExpressionEvaluator);

		super.visit(expr);
	}

	@Override
	protected void visit(VariableLHS lhs) {
		mLhsVariable = lhs.getIdentifier();
	}
	
	@Override
	protected void visit(StructLHS lhs) {
		mLhsVariable = lhs.getField();
	}
	
}

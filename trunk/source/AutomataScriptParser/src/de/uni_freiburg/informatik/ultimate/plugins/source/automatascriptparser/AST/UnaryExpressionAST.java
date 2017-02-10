/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 */
/*
 
 */
public class UnaryExpressionAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1809386058471685881L;
	private UnaryOperatorAST moperator;
	
	public UnaryExpressionAST(ILocation loc) {
		super(loc);
		mReturnType = Integer.class;
		mExpectingType = mReturnType;
	}
	
	public UnaryExpressionAST(ILocation loc, VariableExpressionAST expr) {
		super(loc);
		mReturnType = Integer.class;
		mExpectingType = mReturnType;
		addOutgoingNode(expr);
	}
	
	public UnaryOperatorAST getOperator() {
		return moperator;
	}

	public void setOperator(UnaryOperatorAST operator) {
		moperator = operator;
	}

	@Override
	public String toString() {
		return "UnaryExpression [" + operatorToString(moperator) + "]";
	}
	
	private String operatorToString(UnaryOperatorAST uo) {
		switch (uo) {
		case EXPR_PLUSPLUS: return " expr++ ";
		case EXPR_MINUSMINUS: return " expr-- ";
		case PLUSPLUS_EXPR: return " ++expr ";
		case MINUSMINUS_EXPR: return " --expr ";
		default: return "";
		}
	}

	public String getOperatorAsString() {
		return operatorToString(moperator);
	}
	@Override
	public String getAsString() {
		switch (moperator) {
		case EXPR_PLUSPLUS: return mChildren.get(0).getAsString() + "++";
		case EXPR_MINUSMINUS: return mChildren.get(0).getAsString() + "--";
		case PLUSPLUS_EXPR: return "++" + mChildren.get(0).getAsString();
		case MINUSMINUS_EXPR: return "--" + mChildren.get(0).getAsString();
		default: return "";
		}
	}
	
	
}

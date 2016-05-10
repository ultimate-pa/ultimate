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


import de.uni_freiburg.informatik.ultimate.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de 
 */


public class BinaryExpressionAST extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 561094736879070816L;
	private BinaryOperatorAST m_operator;
	
	public BinaryExpressionAST(ILocation loc) {
		super(loc);
		// The default type of a binary expression is Integer 
		setBothTypesTo(Integer.class);
	}

	/**
	 * 
	 */
	private void setBothTypesTo(Class<?> type) {
		m_returnType = type;
		m_expectingType = type;
	}
	
	public BinaryExpressionAST(ILocation loc, AtsASTNode leftChild, AtsASTNode rightChild) {
		super(loc);
		setBothTypesTo(Integer.class);
		addOutgoingNode(leftChild);
		addOutgoingNode(rightChild);
	}

	
	public void setOperator(BinaryOperatorAST op) {
		m_operator = op;
		// If the operator is '+' and if one of the operands has type 'String'
		// then the operation is 'String concatenation' and not 'Addition'
		// therefore the return type is 'String.
		if (op == BinaryOperatorAST.PLUS) {
			for (AtsASTNode astn : getOutgoingNodes()) {
				if (astn.getReturnType() == String.class) {
					setBothTypesTo(String.class);
					break;
				}
			}
		}
	}
	
	public BinaryOperatorAST getOperator()
	{
		return m_operator;
	}

	public String getOperatorAsString() {
		return operatorToString(m_operator);
	}
	@Override
	public String toString() {
		return "BinaryExpression [Operator: " + operatorToString(m_operator) + "]";
	}
	
	private String operatorToString(BinaryOperatorAST bo) {
		switch(bo) {
		case PLUS: return " + ";
		case MINUS: return " - ";
		case MULTIPLICATION: return " * ";
		case DIVISION: return " / ";
		default: return "";
		}
	}

	@Override
	public String getAsString() {
		if (m_children.size() == 2) {
			return m_children.get(0).getAsString() + 
		           operatorToString(m_operator) + 
				   m_children.get(1).getAsString();
		} else {
			return "";
		}
		
	}
	
	

}

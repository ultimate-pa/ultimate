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
 *
 */

public class RelationalExpressionAST extends AtsASTNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -5806173754091876977L;
	private RelationalOperatorAST moperator;

	public RelationalOperatorAST getOperator() {
		return moperator;
	}

	public void setOperator(RelationalOperatorAST operator) {
		moperator = operator;
	}
	
	public RelationalExpressionAST(ILocation loc) {
		super(loc);
		mReturnType = Boolean.class;
		mExpectingType = Integer.class;
	}

	@Override
	public String toString() {
		return "RelationalExpression [Operator: " + operatorToString(moperator) + "]";
	}
	
	private String operatorToString(RelationalOperatorAST ro) {
		switch(ro) {
		case LESSTHAN: return " < ";
		case LESS_EQ_THAN: return " <= ";
		case GREATERTHAN: return " > ";
		case GREATER_EQ_THAN: return " >= ";
		case EQ: return " == ";
		case NOT_EQ: return " != ";
		default: return "";
		}
	}

	public String getOperatorAsString() {
		return operatorToString(moperator);
	}
	
	@Override
	public String getAsString() {
		if (mChildren.size() == 2) {
			return mChildren.get(0).getAsString() +  
		           operatorToString(moperator) +
				   mChildren.get(1).getAsString();	
		} else {
			return "";
		}
	}
	
	
}

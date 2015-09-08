/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Cookiefy plug-in.
 * 
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.BinaryOperator;
import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.Formula;
import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.Literal;
import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.UnaryOperator;
import de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model.Visitor;

import de.uni_freiburg.informatik.ultimate.cookiefy.utils.Tuple;

public class SubVisitor extends Visitor {

	private final Stack<String> mStack = new Stack<String>();
	private final List<Tuple<Formula, String>> mList = new ArrayList<Tuple<Formula, String>>(); 

	public List<Tuple<Formula, String>> sub(Formula f) {
		mStack.clear();
		mList.clear();
		
		mStack.add("T");
		f.acceptPreOrder(this);
		return mList;
	}

	public void visit(Literal f) {
		String context = mStack.pop();
		mList.add(new Tuple<Formula, String>(f, context));
	}

	public void visit(BinaryOperator f) {
		String context = mStack.pop();
		mList.add(new Tuple<Formula, String>(f, context));
		mStack.add(context + "R");
		mStack.add(context + "L");
	}

	public void visit(UnaryOperator f) {
		String context = mStack.pop();
		mList.add(new Tuple<Formula, String>(f, context));
		mStack.add(context + "L");
	}

}

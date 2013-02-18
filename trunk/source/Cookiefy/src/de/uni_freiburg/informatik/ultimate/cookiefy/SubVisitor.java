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

/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.synthesis;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class RelationTemplate extends Template {
	TermVariable[] mVariables;
	String mName;
	public RelationTemplate(Script script, int relation,
			Set<TermVariable> vars, String name) {
		mScript = script;

		mName = name;
		int l = vars.size();
		int i = 0;
		Term[] t = new Term[l];
		mVariables = new TermVariable[l+1];
		Term lhs = null;
		for (TermVariable v : vars ){
			TermVariable lambda = mScript.variable( "v_" + name + "-" + i,  mScript.sort("Real"));
			mVariables[i] = lambda;
			t[i] = mScript.term("*", lambda, v);
			if(i==0){
				lhs = mScript.term("*", lambda,v);
				System.out.print("lhs is " + lhs.toString());
			} else{
				lhs = mScript.term("+", lhs, mScript.term("*", lambda, v) );
				System.out.print("lhs is " + lhs.toString());
			}
			i++;
		}
		
		TermVariable rhs = mScript.variable( "v_" + name + "-" + i,  mScript.sort("Real"));
		mVariables[l] = rhs;
		if(l == 0){
			// TODO should this be posssible?
			mTerm=mScript.term("true");
			return;
		}
		switch (relation) {
		case 0:
			mTerm = mScript.term("=", lhs, rhs);
			break;
		case 1:
			mTerm = mScript.term("<=", lhs, rhs);
			break;
		case 2:
			mTerm = mScript.term("<", lhs, rhs);
			break;
		default:
			break;
		}
	}
}

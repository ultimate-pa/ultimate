/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;


public class CCAppTerm extends CCTerm {
	CCTerm func, arg;
//	int lastFormula, firstFormula;
	Parent leftParInfo, rightParInfo;
	
	class Parent extends SimpleListable<Parent> {
		private boolean mark = false;
		CCAppTerm getData() {
			return CCAppTerm.this;
		}
		public final boolean isMarked() {
			assert (!mark || CCAppTerm.this.repStar.numMembers > 1);
			return mark;
		}
		public String toString() {
			return CCAppTerm.this.toString();
		}
	}
	
	/**
	 * Constructor for CCAppTerms that are not permanently stored in the CC graph
	 */
	public CCAppTerm(CCTerm func, CCTerm arg) {
		 super();
		 this.func = func;
		 this.arg = arg;
	}

	public CCAppTerm(boolean isFunc, int parentPos, CCTerm func, CCTerm arg,
			SharedTerm term, CClosure engine) {
		super(isFunc, parentPos, term,
				HashUtils.hashJenkins(func.hashCode(), arg));
		this.func = func;
		this.arg = arg;
//		firstFormula = Integer.MAX_VALUE; lastFormula = -1;
		leftParInfo = new Parent();
		rightParInfo = new Parent();
		
		//func.addParentInfo(0, leftParInfo, engine);
		//arg.addParentInfo(func.parentPosition, rightParInfo, engine);
	}
	
	public CCTerm getFunc() {
		return func;
	}

	public CCTerm getArg() {
		return arg;
	}

	private CCAppTerm findCongruentAppTerm(CCTerm func, CCTerm arg) {
		CCParentInfo argInfo = arg.ccpars.getInfo(func.parentPosition);
		if (argInfo != null) {
			for (Parent p : argInfo.m_CCParents) {
				if (p.getData() != this) {
					CCParentInfo funcInfo = func.ccpars.getInfo(0);
					if (funcInfo != null) {
						for (Parent q : funcInfo.m_CCParents) {
							if (p.getData() == q.getData()) {
								return p.getData();
							}
						}
					}
				}
			}
		}
		return null;
	}
	
	public CCAppTerm addParentInfo(CClosure engine) {
		CCTerm func = this.func;
		CCTerm arg = this.arg;
		
		CCAppTerm congruentAppTerm = null;
		while (func.rep != func || arg.rep != arg) {
			if (congruentAppTerm == null) {
				congruentAppTerm = findCongruentAppTerm(func, arg);
			}

			if (func.rep == func || 
				arg.rep != arg && arg.mergeTime > func.mergeTime) {
				// Reverse arg rep
				arg.ccpars.addParentInfo(func.parentPosition, rightParInfo, false, null);
				arg = arg.rep;
			} else {
				// Reverse func rep
				func.ccpars.addParentInfo(0, leftParInfo, false, null);
				func = func.rep;
			}
		}
		if (congruentAppTerm == null) {
			congruentAppTerm = findCongruentAppTerm(func, arg);
		}
		func.ccpars.addParentInfo(0, leftParInfo, true, engine);
		arg.ccpars.addParentInfo(func.parentPosition, rightParInfo, true, engine);
		return congruentAppTerm;
	}
	
	public void unlinkParentInfos() {
		leftParInfo.removeFromList();
		rightParInfo.removeFromList();
	}
	
	public void markParentInfos() {
		leftParInfo.mark = rightParInfo.mark = true;
	}
	
	public void unmarkParentInfos() {
		leftParInfo.mark = rightParInfo.mark = false;
	}
	
//	public int getFirstFormula() {
//		return firstFormula;
//	}
//	
//	public int getLastFormula() {
//		return lastFormula;
//	}
	
//	public void occursIn(int formulaNr) {
//		func.occursIn(formulaNr);
//		arg.occursIn(formulaNr);
//		if (formulaNr < firstFormula)
//			firstFormula = formulaNr;
//		if (formulaNr > lastFormula)
//			lastFormula = formulaNr;
//	}

	public void toStringHelper(StringBuilder sb, HashSet<CCAppTerm> visited) {
		if (func instanceof CCAppTerm) {
			((CCAppTerm)func).toStringHelper(sb, visited);
			sb.append(" ");
		} else {
			sb.append("(").append(func).append(" ");
		}
		if (arg instanceof CCAppTerm) {
			CCAppTerm arg2 = (CCAppTerm) arg;
//			sb.append("[").append(arg2.hashCode).append("]");
			if (!visited.contains(arg2)) {
				arg2.toStringHelper(sb, visited);
				sb.append(")");
				visited.add((CCAppTerm) arg2);
			}
		} else {
			sb.append(arg);
		}
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		toStringHelper(sb, new HashSet<CCAppTerm>());
		sb.append(")");
		return sb.toString();
	}

	public Term toSMTTerm(Theory theory, boolean useAuxVars)
	{
		assert !isFunc;
		CCTerm t = this;
		while (t instanceof CCAppTerm)
			t = ((CCAppTerm) t).func;
		CCBaseTerm basefunc = (CCBaseTerm) t;
		FunctionSymbol sym = (FunctionSymbol) basefunc.symbol;
		Term[] args = new Term[sym.getParameterCount()];
		int dest = args.length;
		t = this;
		while (t instanceof CCAppTerm) {
			args[--dest] = ((CCAppTerm)t).arg.toSMTTerm(theory, useAuxVars);
			t = ((CCAppTerm) t).func;
		}
		return Coercion.buildApp(sym, args);
	}
}

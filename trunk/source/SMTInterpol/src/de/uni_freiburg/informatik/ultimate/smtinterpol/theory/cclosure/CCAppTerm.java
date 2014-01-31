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
	final CCTerm mFunc, mArg;
	final Parent mLeftParInfo, mRightParInfo;
	
	class Parent extends SimpleListable<Parent> {
		private boolean mMark = false;
		CCAppTerm getData() {
			return CCAppTerm.this;
		}
		public final boolean isMarked() {
			assert (!mMark || CCAppTerm.this.mRepStar.mNumMembers > 1);
			return mMark;
		}
		public String toString() {
			return CCAppTerm.this.toString();
		}
	}
	
	public CCAppTerm(boolean isFunc, int parentPos, CCTerm func, CCTerm arg,
			SharedTerm term, CClosure engine) {
		super(isFunc, parentPos, term,
				HashUtils.hashJenkins(func.hashCode(), arg));
		this.mFunc = func;
		this.mArg = arg;
//		firstFormula = Integer.MAX_VALUE; lastFormula = -1;
		mLeftParInfo = new Parent();
		mRightParInfo = new Parent();
		
		//func.addParentInfo(0, leftParInfo, engine);
		//arg.addParentInfo(func.parentPosition, rightParInfo, engine);
	}
	
	public CCTerm getFunc() {
		return mFunc;
	}

	public CCTerm getArg() {
		return mArg;
	}

	private CCAppTerm findCongruentAppTerm(CCTerm func, CCTerm arg) {
		CCParentInfo argInfo = arg.mCCPars.getInfo(func.mParentPosition);
		if (argInfo != null) {
			for (Parent p : argInfo.mCCParents) {
				if (p.getData() != this) {
					CCParentInfo funcInfo = func.mCCPars.getInfo(0);
					if (funcInfo != null) {
						for (Parent q : funcInfo.mCCParents) {
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
		CCTerm func = this.mFunc;
		CCTerm arg = this.mArg;
		
		CCAppTerm congruentAppTerm = null;
		while (func.mRep != func || arg.mRep != arg) {
			if (congruentAppTerm == null) {
				congruentAppTerm = findCongruentAppTerm(func, arg);
			}

			if (func.mRep == func 
				|| arg.mRep != arg && arg.mMergeTime > func.mMergeTime) {
				// Reverse arg rep
				arg.mCCPars.addParentInfo(
				        func.mParentPosition, mRightParInfo, false, null);
				arg = arg.mRep;
			} else {
				// Reverse func rep
				func.mCCPars.addParentInfo(0, mLeftParInfo, false, null);
				func = func.mRep;
			}
		}
		if (congruentAppTerm == null) {
			congruentAppTerm = findCongruentAppTerm(func, arg);
		}
		func.mCCPars.addParentInfo(0, mLeftParInfo, true, engine);
		arg.mCCPars.addParentInfo(func.mParentPosition, mRightParInfo, true, engine);
		return congruentAppTerm;
	}
	
	public void unlinkParentInfos() {
		mLeftParInfo.removeFromList();
		mRightParInfo.removeFromList();
	}
	
	public void markParentInfos() {
		mLeftParInfo.mMark = mRightParInfo.mMark = true;
	}
	
	public void unmarkParentInfos() {
		mLeftParInfo.mMark = mRightParInfo.mMark = false;
	}

	public void toStringHelper(StringBuilder sb, HashSet<CCAppTerm> visited) {
		if (mFunc instanceof CCAppTerm) {
			((CCAppTerm)mFunc).toStringHelper(sb, visited);
			sb.append(' ');
		} else {
			sb.append('(').append(mFunc).append(' ');
		}
		if (mArg instanceof CCAppTerm) {
			CCAppTerm arg2 = (CCAppTerm) mArg;
			if (!visited.contains(arg2)) {
				arg2.toStringHelper(sb, visited);
				sb.append(')');
				visited.add((CCAppTerm) arg2);
			}
		} else {
			sb.append(mArg);
		}
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		toStringHelper(sb, new HashSet<CCAppTerm>());
		sb.append(')');
		return sb.toString();
	}

	public Term toSMTTerm(Theory theory, boolean useAuxVars) {
		assert !mIsFunc;
		CCTerm t = this;
		while (t instanceof CCAppTerm)
			t = ((CCAppTerm) t).mFunc;
		CCBaseTerm basefunc = (CCBaseTerm) t;
		FunctionSymbol sym = (FunctionSymbol) basefunc.mSymbol;
		Term[] args = new Term[sym.getParameterSorts().length];
		int dest = args.length;
		t = this;
		while (t instanceof CCAppTerm) {
			args[--dest] = ((CCAppTerm)t).mArg.toSMTTerm(theory, useAuxVars);
			t = ((CCAppTerm) t).mFunc;
		}
		return Coercion.buildApp(sym, args);
	}
}

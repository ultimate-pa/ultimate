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

import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCAppTerm extends CCTerm {
	final CCTerm mFunc, mArg;
	final Parent mLeftParInfo, mRightParInfo;
	Term mSmtTerm;

	class Parent extends SimpleListable<Parent> {
		private boolean mMark = false;

		CCAppTerm getData() {
			return CCAppTerm.this;
		}

		public final boolean isMarked() {
			assert (!mMark || CCAppTerm.this.mRepStar.mNumMembers > 1);
			return mMark;
		}

		@Override
		public String toString() {
			return CCAppTerm.this.toString();
		}
	}

	public CCAppTerm(boolean isFunc, int parentPos, CCTerm func, CCTerm arg, SharedTerm term, CClosure engine) {
		super(isFunc, parentPos, term, HashUtils.hashJenkins(func.hashCode(), arg));
		mFunc = func;
		mArg = arg;
		// firstFormula = Integer.MAX_VALUE; lastFormula = -1;
		mLeftParInfo = new Parent();
		mRightParInfo = new Parent();

		// func.addParentInfo(0, leftParInfo, engine);
		// arg.addParentInfo(func.parentPosition, rightParInfo, engine);
	}

	public CCTerm getFunc() {
		return mFunc;
	}

	public CCTerm getArg() {
		return mArg;
	}

	/**
	 * Searches the current mCCPar list of args and func to find an application term that is congruent to this term. The
	 * congruence is detected by finding a CCAppTerm that is in both parent lists.
	 * 
	 * @param func
	 *            A term on the path from this.mFunc to this.mFunc.mRepStar.
	 * @param arg
	 *            A term on the path from this.mArg to this.mArg.mRepStar.
	 * @return The congruent CCAppTerm appearing in both terms.
	 */
	private CCAppTerm findCongruentAppTerm(CCTerm func, CCTerm arg) {
		final CCParentInfo argInfo = arg.mCCPars.getInfo(func.mParentPosition);
		final CCParentInfo funcInfo = func.mCCPars.getInfo(0);
		if (argInfo != null && funcInfo != null) {
			for (final Parent p : argInfo.mCCParents) {
				if (p.getData() != this) {
					for (final Parent q : funcInfo.mCCParents) {
						if (p.getData() == q.getData()) {
							return p.getData();
						}
					}
				}
			}
		}
		return null;
	}

	/**
	 * Add this app term to the parent info lists of its function and argument. Also adds it to the mCCPars of all the
	 * oldReps on the path to the repStar, which is necessary for unmerging correctly.
	 * 
	 * @param engine
	 *            the congruence closure engine.
	 * @return the first term that is congruent to the current application term. I.e., the first term that would have
	 *         been merged if the term would have existed earlier.
	 */
	public CCAppTerm addParentInfo(CClosure engine) {
		CCTerm func = mFunc;
		CCTerm arg = mArg;

		CCAppTerm congruentAppTerm = null;
		/*
		 * Store the parent info in all mCCPars of the representatives occuring on the path to the root, so that it is
		 * still present when we unmerge later.
		 * 
		 * Also find the first congruent application term.
		 */
		while (func.mRep != func || arg.mRep != arg) {
			if (congruentAppTerm == null) {
				congruentAppTerm = findCongruentAppTerm(func, arg);
			}

			if (func.mRep == func || arg.mRep != arg && arg.mMergeTime > func.mMergeTime) {
				// Reverse arg rep
				arg.mCCPars.addParentInfo(func.mParentPosition, mRightParInfo, false, null);
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

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final HashMap<CCAppTerm, Integer> visited = new HashMap<CCAppTerm, Integer>();
		final ArrayDeque<Object> todo = new ArrayDeque<>();
		todo.add(")");
		todo.add(this);
		todo.add("(");
		while (!todo.isEmpty()) {
			Object item = todo.removeLast();
			if (item instanceof String) {
				sb.append(item);
			} else if (item instanceof CCAppTerm) {
				CCAppTerm app = (CCAppTerm) item;
				Integer id = visited.get(item);
				if (id != null) {
					sb.append("@" + id);
				} else {
					visited.put(app, visited.size());
					if (app.mArg instanceof CCAppTerm) {
						todo.add(")");
						todo.add(app.mArg);
						todo.add("(");
					} else {
						todo.add(app.mArg);
					}
					todo.add(" ");
					todo.add(app.mFunc);
				}
			} else if (item instanceof CCBaseTerm) {
				sb.append(item);
			} else {
				throw new AssertionError("Unknown CCTerm " + item);
			}
		}
		return sb.toString();
	}
}

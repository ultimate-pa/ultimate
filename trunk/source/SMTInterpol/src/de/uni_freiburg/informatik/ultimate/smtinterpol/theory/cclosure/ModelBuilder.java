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
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;

public class ModelBuilder {
	
	private static class ArgHelper {
		private int[] mArgs;
		private int mNextPos;
		public ArgHelper() {
			mArgs = new int[4];
			mNextPos = 0;
		}
		public void add(int arg) {
			if (mNextPos == mArgs.length) {
				int[] old = mArgs;
				mArgs = new int[old.length << 1];
				System.arraycopy(old, 0, mArgs, 0, old.length);
			}
			mArgs[mNextPos++] = arg;
		}
		public int[] toArray() {
			int[] res = new int[mNextPos];
			int pos = 0;
			for (int i = mNextPos - 1; i >= 0; --i)
				res[pos++] = mArgs[i];
			return res;
		}
	}
	
	private static class Delay {
		private final CCTerm mTerm;
		private int mValue;
		private boolean mInitialized;
		public Delay(CCTerm term) {
			mTerm = term;
			mInitialized = false;
		}
		public Delay(CCTerm term, int value) {
			mTerm = term;
			mValue = value;
			mInitialized = true;
		}
		public boolean isInitialized() {
			return mInitialized;
		}
		public void initialize(int value) {
			assert !mInitialized;
			mValue = value;
			mInitialized = true;
		}
		public CCTerm getTerm() {
			return mTerm;
		}
		public int getValue() {
			return mValue;
		}
	}
	
	private final HashMap<CCTerm, Integer> mProduced =
			new HashMap<CCTerm, Integer>();
	
	private final HashMap<CCTerm, Delay> mDelayed =
			new HashMap<CCTerm, Delay>();
	
	private final Deque<Delay> mTodo = new ArrayDeque<Delay>();
	
	private final CClosure mCClosure;
	
	public ModelBuilder(CClosure closure, List<CCTerm> terms, Model model,
			Theory t, SharedTermEvaluator ste,
			CCTerm trueNode, CCTerm falseNode) {
		mCClosure = closure;
		Rational biggest = Rational.MONE;
		Set<CCTerm> delayed = new HashSet<CCTerm>();
		for (CCTerm term : terms) {
			if (term == term.mRepStar) {
				int value;
				Term smtterm = term.toSMTTerm(t);
				if (smtterm.getSort().isNumericSort()) {
					Rational v;
					if (term.getSharedTerm() != null) // NOPMD
						v = ste.evaluate(term.getSharedTerm(), t);
					else if (smtterm instanceof ConstantTerm)
						v = (Rational) ((ConstantTerm) smtterm).getValue();
					else {
						delayed.add(term);
						continue;
					}
					biggest = v.compareTo(biggest) > 0 ? v : biggest;
					value = model.putNumeric(v);
				} else if (term == trueNode.mRepStar) {
					value = model.getTrueIdx();
				} else if (term == falseNode.mRepStar 
						|| smtterm.getSort() == t.getBooleanSort()) {
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = model.getFalseIdx();
				} else if (smtterm.getSort().isArraySort()) {
					//Array sort
					ArraySortInterpretation arrSort = (ArraySortInterpretation)
							model.provideSortInterpretation(smtterm.getSort());
					value = arrSort.createEmptyArrayValue();
				} else {
					value = model.extendFresh(smtterm.getSort());
				}
				term.mModelVal = value;
				for (CCTerm mem : term.mMembers)
					add(model, mem, value, t);
			}
		}
		// Handle all delayed elements
		// We use the smallest integer bigger than biggest
		biggest = biggest.add(Rational.ONE).floor();
		for (CCTerm term : delayed) {
			int idx = model.putNumeric(biggest);
			term.mModelVal = idx;
			for (CCTerm mem : term.mMembers)
				add(model, mem, idx, t);
			biggest = biggest.add(Rational.ONE);
		}
		finishModel(model, t);
		// no cleanup here since this whole object gets garbage collected anyway
	}
	
	private void add(Model model, CCTerm term, int value, Theory t) {
		if (term instanceof CCBaseTerm) {
			CCBaseTerm bt = (CCBaseTerm) term;
			if (!bt.isFunctionSymbol()) {
				// We have to remember the value of the term for applications
				mProduced.put(term, value);
				return;
			}
			FunctionSymbol symb = bt.getFunctionSymbol();
			if (!symb.isIntern()) {
				model.map(symb, value);
				mProduced.put(term, value);
			}
		} else {
			// It is a CCAppTerm
			CCAppTerm app = (CCAppTerm) term;
			assert(!app.mIsFunc);
			addApp(model, app, value, t);
		}
	}
	
	private void addApp(Model model, CCAppTerm app, int value, Theory t) {
		ArgHelper args = new ArgHelper();
		CCTerm walk = app;
		boolean enqueued = false;
		while (walk instanceof CCAppTerm) {
			CCAppTerm appwalk = (CCAppTerm) walk;
			Integer val = mProduced.get(appwalk.getArg());
			if (val == null) {
				if (!enqueued) {
					Delay delay = mDelayed.get(app);
					if (delay == null) {
						delay = new Delay(app, value);
						mDelayed.put(app, delay);
					} else if (!delay.isInitialized())
						delay.initialize(value);
					mTodo.push(delay);
					enqueued = true;
				}
				Delay delay = mDelayed.get(appwalk.getArg());
				if (delay == null) {
					delay = new Delay(appwalk.getArg());
					mDelayed.put(appwalk.getArg(), delay);
				}
				mTodo.push(delay);
			} else
				args.add(val);
			walk = appwalk.getFunc();
		}
		// Now, walk is the CCBaseTerm corresponding the the function
		// If we did not enqueue an argument, we can extend the model.
		if (!enqueued) {
			CCBaseTerm base = (CCBaseTerm) walk;
			if (base.isFunctionSymbol()
					&& (!mCClosure.isArrayTheory()
					|| (base.mParentPosition != mCClosure.getSelectNum()
					&& base.mParentPosition != mCClosure.getStoreNum()
					&& base.mParentPosition != mCClosure.getDiffNum()))) {
				FunctionSymbol fs = base.getFunctionSymbol();
				model.map(fs, args.toArray(), value);
			}
			mProduced.put(app, value);
		}
	}
	
	private void finishModel(Model model, Theory t) {
		while (!mTodo.isEmpty()) {
			Delay d = mTodo.pop();
			if (!mProduced.containsKey(d.getTerm())) {
				assert d.isInitialized();
				add(model, d.getTerm(), d.getValue(), t);
			}
		}
	}
}

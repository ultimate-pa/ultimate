/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
*
* @author Jill Enke (enkei@informatik.uni-freiburg.de)
*
*/
public class OctagonDetector extends NonRecursive {
	
	private final HashSet<Term> mCheckedTerms;
	private final HashSet<Term> mSubTerms;
	private final HashSet<TermVariable> mCurrentVars;
	private boolean mOctagon;
	private final ILogger mLogger;
	private boolean mIsOctTerm;
	
	public OctagonDetector(ILogger logger) {
		super();
		mCheckedTerms = new HashSet<>();
		mSubTerms = new HashSet<>();
		mCurrentVars = new HashSet<>();
		mOctagon = true;
		mLogger = logger;
	}
	
	private static class ConcatinationWalker implements NonRecursive.Walker {

		final Term mTerm;
		final ILogger mLogger;
		
		public ConcatinationWalker(Term t, ILogger logger) {
			mTerm = t;
			mLogger = logger;
			mLogger.debug("New Concatination Walker for term:" + t.toString());
		}
		
		@Override
		public void walk(NonRecursive engine) {
			// TODO Auto-generated method stub
			mLogger.debug("walk called");
			((OctagonDetector) engine).addConcatTerms(mTerm);
		}
		
	}
	
	private static class OctagonDetectionWalker implements NonRecursive.Walker {

		private final Term mTerm;
		
		OctagonDetectionWalker(Term t) {
			mTerm = t;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			// TODO Auto-generated method stub
			((OctagonDetector) engine).check(mTerm);
			
		}
		
	}
	
	public HashSet<Term> getConcatSubTerms(Term t) {
		mCheckedTerms.clear();
		run(new ConcatinationWalker(t, mLogger));
		return mSubTerms;
	}
	
	private void addConcatTerms(Term t) {
		
		mLogger.debug("Current Term:" + t.toString());
		
		if (mCheckedTerms.contains(t)) {
			mLogger.debug("Already checked");
			return;
		}
		
		if (t instanceof ApplicationTerm) {
			mLogger.debug("ApplicationTerm");
			ApplicationTerm aT = (ApplicationTerm) t;
			if ((aT).getFunction().getName().compareTo("and") == 0) {
				mCheckedTerms.add(t);
				mLogger.debug("> with function name = " + aT.getFunction().getName());
				
				for (final Term arg : (aT).getParameters()) {
					enqueueWalker(new ConcatinationWalker(arg, mLogger));
				}
				return;
			}
		}
		

		mLogger.debug("Other Term");
		
		mSubTerms.add(t);
		mCheckedTerms.add(t);
		
	}
	
	public boolean isOctagonTerm(Term t) {
		mCheckedTerms.clear();
		mIsOctTerm = true;
		mCurrentVars.clear();
		run(new OctagonDetectionWalker(t));
		mLogger.debug(((mIsOctTerm) ? "Term is Oct" : "Term is NOT Oct"));
		return mIsOctTerm;
	}
	
	private void check(Term t) {
		mLogger.debug("Checking Term:" + t.toString());
		
		if(!mIsOctTerm) {
			return;
		}
		
		if(t instanceof TermVariable) {
			mCurrentVars.add((TermVariable) t);
			if (mCurrentVars.size() > 2) mIsOctTerm = false;
		} else if (t instanceof ApplicationTerm) {
			ApplicationTerm aT = (ApplicationTerm) t;
			String functionName = aT.getFunction().getName();
			if (functionName.compareTo("<=") == 0
					|| functionName.compareTo("<") == 0
					|| functionName.compareTo(">") == 0
					|| functionName.compareTo(">=") == 0) {
				for(Term arg : aT.getParameters()) {
					enqueueWalker(new OctagonDetectionWalker(arg));
				}
			} else {
				mIsOctTerm = false;
				return;
			}
		} else if (t instanceof ConstantTerm) {
			return;
		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new OctagonDetectionWalker(((AnnotatedTerm)t).getSubterm()));
		} else {
			mIsOctTerm = false;
			return;
		}
		
		
	}
	
	public void clearChecked() {
		mCheckedTerms.clear();
	}
	
	public HashSet<Term> getSubTerms(){
		return mSubTerms;
	}


	public boolean isOctagon() {
		return mOctagon;
	}
}

/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

public class TermTransferrerBooleanCore extends TermTransferrer {
	
	private final Term mAuxiliaryTerm;
	private final String mFreshTermPrefix = "FBV_";
	private int mFreshTermCounter;
	private final ConstructionCache<Term, Term> mConstructionCache;

	public TermTransferrerBooleanCore(Script script) {
		super(script);
		mAuxiliaryTerm = constructAuxiliaryTerm();
		mFreshTermCounter = 0;
		IValueConstruction<Term, Term> valueComputation = new IValueConstruction<Term, Term>() {
			
			@Override
			public Term constructValue(Term key) {
				String name = mFreshTermPrefix + mFreshTermCounter;
				mFreshTermCounter++;
				mScript.declareFun(name, new Sort[0], mScript.sort("Bool"));
				Term value = mScript.term(name);
				mBacktransferMapping.put(value, key);
				return value;
			}
		};
		mConstructionCache = new ConstructionCache<Term, Term>(valueComputation );
	}
	
	public Term constructAuxiliaryTerm() {
		String name = this.getClass().getCanonicalName() + "_AUX";
		mScript.declareFun(name, new Sort[0], mScript.sort("Bool"));
		return mScript.term(name);
	}

	@Override
	protected void convert(Term term) {
		if (term.getSort().getName().equals("Bool")) {
			super.convert(term);
		} else {
			setResult(mAuxiliaryTerm);
		}
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		
		if (Arrays.asList(newArgs).contains(mAuxiliaryTerm)) {
			Term result = mConstructionCache.getOrConstuct(appTerm);
			setResult(result);
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}
	
	
	
	

}

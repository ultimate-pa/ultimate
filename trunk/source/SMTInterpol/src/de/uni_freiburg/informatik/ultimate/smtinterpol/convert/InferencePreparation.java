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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CollectionsHelper;


public class InferencePreparation {
	private final Theory mTeory;
	private final Set<TermVariable> mVars;
	private final Stack<Term> mBoolTerms;
	private Term mSubst;
	private ApplicationTerm mIte;
	
	public InferencePreparation(Theory theory,Set<TermVariable> vars) {
		mTeory = theory;
		mVars = vars;
		mBoolTerms = new Stack<Term>();
	}
	public Term prepare(Term body) {
		assert body.getSort() == mTeory.getBooleanSort() : "Non-boolean term as quantifier sub?";
		final FormulaUnLet unflet = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
		return recprepare(unflet.unlet(body));
	}
	
	private Term recprepare(Term subterm) {
		if (!CollectionsHelper.containsAny(subterm.getFreeVars(), mVars)) {
			return subterm;
		}
		while (subterm instanceof AnnotatedTerm) {
			subterm = ((AnnotatedTerm)subterm).getSubterm();
		}
		if (subterm instanceof ApplicationTerm) {
			final ApplicationTerm app = (ApplicationTerm)subterm;
			if (app.getSort() == mTeory.getBooleanSort()) {
				mBoolTerms.push(subterm);
			} else if (app.getFunction().isIntern() 
					&& app.getFunction().getName().equals("ite")) {
				// Here, we have a term-ite...
				mSubst = mIte = app;
				return null;
			}
			final Term[] params = app.getParameters();
			final Term[] newparams = new Term[params.length];
			for (int i = 0; i < params.length; ++i) {
				newparams[i] = recprepare(params[i]);
				while (newparams[i] == null) {
					// Found term ite in parameter i
					// TODO This does not work: (and p q) vs. (p (f...))
					if (mBoolTerms.peek() != subterm) {
						return null;
					}
					if (mBoolTerms.peek() == subterm) {
						mBoolTerms.pop();
						return recprepare(generateIte(subterm));
					}
				}
			}
			if (mBoolTerms.peek() == subterm) {
				mBoolTerms.pop();
			}
			return mTeory.term(app.getFunction(), newparams);
		}
		return subterm;
	}
	private Term generateIte(Term subterm) {
		final Term trueCase = generateCase(subterm,true);
		final Term falseCase = generateCase(subterm,false);
		final Term res = mTeory.ifthenelse(
				mIte.getParameters()[0], trueCase, falseCase);
		mIte = null; 
		mSubst = null;
		return res;
	}
	private Term generateCase(Term subterm,boolean which) {
		while (subterm instanceof AnnotatedTerm) {
			subterm = ((AnnotatedTerm)subterm).getSubterm();
		}
		if (subterm == mSubst) {
			return mIte.getParameters()[which ? 1 : 2];
		}
		if (subterm instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm)subterm;
			final Term[] params = at.getParameters();
			final Term[] newparams = new Term[params.length];
			boolean changed = false;
			for (int i = 0; i < params.length; ++i) {
				newparams[i] = generateCase(params[i], which);
				changed |= params[i] != newparams[i];
			}
			return changed ? mTeory.term(at.getFunction(),newparams) : at;	
		}
		return subterm;
	}
	
}

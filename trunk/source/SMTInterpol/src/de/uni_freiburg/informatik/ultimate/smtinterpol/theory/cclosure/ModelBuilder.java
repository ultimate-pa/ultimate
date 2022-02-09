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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.NumericSortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;

public class ModelBuilder {

	Map<CCTerm, Term> mModelValues = new HashMap<>();

	public ModelBuilder(final CClosure closure, final List<CCTerm> terms, final Model model,
			final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory array, final CCTerm trueNode, final CCTerm falseNode) {
		fillInTermValues(terms, model, t, ste, trueNode, falseNode);
		if (array != null) {
			array.fillInModel(this, model, t, ste);
		}
		fillInFunctions(terms, model, t);
	}

	public Term getModelValue(final CCTerm term) {
		return mModelValues.get(term.getRepresentative());
	}

	public void setModelValue(final CCTerm term, final Term value) {
		assert term == term.getRepresentative();
		final Term old = mModelValues.put(term, value);
		assert old == null || old == value;
	}

	public void fillInTermValues(final List<CCTerm> terms, final Model model, final Theory t, final SharedTermEvaluator ste, final CCTerm trueNode,
			final CCTerm falseNode) {
		final Set<CCTerm> delayed = new HashSet<>();
		for (final CCTerm ccterm : terms) {
			if (ccterm == ccterm.mRepStar && !ccterm.isFunc()) {
				Term value;
				final Term smtterm = ccterm.getFlatTerm();
				final Sort sort = smtterm.getSort();
				if (sort.isNumericSort()) {
					Rational v;
					if (ccterm.getSharedTerm() != null) {
						v = ste.evaluate(ccterm.getSharedTerm().getFlatTerm(), t);
						if (smtterm.getSort().getName().equals("Int") && !v.isIntegral()) {
							throw new AssertionError("Int term has non-integral value");
						}
						value = model.getNumericSortInterpretation().extend(v, smtterm.getSort());
					} else {
						delayed.add(ccterm);
						continue;
					}
				} else if (ccterm == trueNode.mRepStar) {
					value = sort.getTheory().mTrue;
				} else if (smtterm.getSort() == t.getBooleanSort()) {
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = sort.getTheory().mFalse;
				} else if (smtterm.getSort().isArraySort()) {
					// filled in later by ArrayTheory
					continue;
				} else if (sort.getSortSymbol().isDatatype()) {
					throw new UnsupportedOperationException("Modelproduction for data type theory not implemented.");
				} else {
					value = model.extendFresh(smtterm.getSort());
				}
				setModelValue(ccterm, value);
			}
		}
		// Handle all delayed elements
		// note that extendFresh must be called after all values in the model have been extended to the numeric sort.
		for (final CCTerm ccterm : delayed) {
			final Term value = model.extendFresh(ccterm.getFlatTerm().getSort());
			setModelValue(ccterm, value);
		}
	}

	public void fillInFunctions(final List<CCTerm> terms, final Model model, final Theory t) {
		for (final CCTerm term : terms) {
			if (!term.isFunc()) {
				add(model, term, mModelValues.get(term.getRepresentative()), t);
			}
		}
	}

	private void add(final Model model, final CCTerm term, final Term value, final Theory t) {
		assert !term.isFunc();
		if (term instanceof CCBaseTerm) {
			final CCBaseTerm bt = (CCBaseTerm) term;
			final Term btTerm = bt.getFlatTerm();
			if (btTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) btTerm;
				final FunctionSymbol symb = appTerm.getFunction();
				if (!symb.isIntern() && appTerm.getParameters().length == 0) {
					model.map(symb, value);
				}
			}
		} else {
			// It is a CCAppTerm
			final CCAppTerm app = (CCAppTerm) term;
			addApp(model, app, value, t);
		}
	}

	private static boolean isDivision(final FunctionSymbol fs) {
		final String name = fs.getName();
		return name == "/" || name == "div" || name == "mod";
	}

	private void addApp(final Model model, final CCAppTerm app, final Term value, final Theory t) {
		final ArrayDeque<Term> args = new ArrayDeque<>();
		CCTerm walk = app;
		while (walk instanceof CCAppTerm) {
			final CCAppTerm appwalk = (CCAppTerm) walk;
			args.addFirst(mModelValues.get(appwalk.getArg().getRepresentative()));
			walk = appwalk.getFunc();
		}
		// Now, walk is the CCBaseTerm corresponding the the function
		// If we did not enqueue an argument, we can extend the model.
		final CCBaseTerm base = (CCBaseTerm) walk;
		if (base.isFunctionSymbol()) {
			final FunctionSymbol fs = base.getFunctionSymbol();
			if (!fs.isIntern() ||
					(isDivision(fs) && NumericSortInterpretation.toRational(args.getLast()) == Rational.ZERO)) {
				model.map(fs, args.toArray(new Term[args.size()]), value);
			}
		}
	}
}

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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
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
		public void add(final int arg) {
			if (mNextPos == mArgs.length) {
				final int[] old = mArgs;
				mArgs = new int[old.length << 1];
				System.arraycopy(old, 0, mArgs, 0, old.length);
			}
			mArgs[mNextPos++] = arg;
		}
		public int[] toArray() {
			final int[] res = new int[mNextPos];
			int pos = 0;
			for (int i = mNextPos - 1; i >= 0; --i) {
				res[pos++] = mArgs[i];
			}
			return res;
		}
	}

	public ModelBuilder(final CClosure closure, final List<CCTerm> terms, final Model model,
			final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory array, final CCTerm trueNode, final CCTerm falseNode) {
		fillInTermValues(terms, model, t, ste, trueNode, falseNode);
		if (array != null) {
			array.fillInModel(model, t, ste);
		}
		fillInFunctions(terms, model, t);
	}

	public void fillInTermValues(final List<CCTerm> terms, final Model model, final Theory t, final SharedTermEvaluator ste, final CCTerm trueNode,
			final CCTerm falseNode) {
		Rational biggest = Rational.MONE;
		final Set<CCTerm> delayed = new HashSet<>();
		for (final CCTerm term : terms) {
			if (term == term.mRepStar && !term.isFunc()) {
				int value;
				final Term smtterm = term.getFlatTerm();
				if (smtterm.getSort().isNumericSort()) {
					Rational v;
					if (term.getSharedTerm() != null) {
						v = ste.evaluate(term.getSharedTerm().getFlatTerm(), t);
						if (smtterm.getSort().getName().equals("Int") && !v.isIntegral()) {
							throw new AssertionError("Int term has non-integral value");
						}
						biggest = v.compareTo(biggest) > 0 ? v : biggest;
						value = model.putNumeric(v);
					} else {
						delayed.add(term);
						continue;
					}
				} else if (term == trueNode.mRepStar) {
					value = model.getTrueIdx();
				} else if (smtterm.getSort() == t.getBooleanSort()) {
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = model.getFalseIdx();
				} else if (smtterm.getSort().isArraySort()) {
					// filled in later by ArrayTheory
					continue;
				} else {
					value = model.extendFresh(smtterm.getSort());
				}
				term.mModelVal = value;
			}
		}
		// Handle all delayed elements
		// We use the smallest integer bigger than biggest
		biggest = biggest.add(Rational.ONE).floor();
		for (final CCTerm term : delayed) {
			final int idx = model.putNumeric(biggest);
			term.mModelVal = idx;
			biggest = biggest.add(Rational.ONE);
		}
	}

	public void fillInFunctions(final List<CCTerm> terms, final Model model, final Theory t) {
		for (final CCTerm term : terms) {
			if (!term.isFunc()) {
				add(model, term, term.getRepresentative().mModelVal, t);
			}
		}
	}

	private void add(final Model model, final CCTerm term, final int value, final Theory t) {
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

	private void addApp(final Model model, final CCAppTerm app, final int value, final Theory t) {
		final ArgHelper args = new ArgHelper();
		CCTerm walk = app;
		while (walk instanceof CCAppTerm) {
			final CCAppTerm appwalk = (CCAppTerm) walk;
			args.add(appwalk.getArg().getRepresentative().mModelVal);
			walk = appwalk.getFunc();
		}
		// Now, walk is the CCBaseTerm corresponding the the function
		// If we did not enqueue an argument, we can extend the model.
		final CCBaseTerm base = (CCBaseTerm) walk;
		if (base.isFunctionSymbol()) {
			final FunctionSymbol fs = base.getFunctionSymbol();
			if (!fs.isIntern()) {
				model.map(fs, args.toArray(), value);
			}
		}
	}
}

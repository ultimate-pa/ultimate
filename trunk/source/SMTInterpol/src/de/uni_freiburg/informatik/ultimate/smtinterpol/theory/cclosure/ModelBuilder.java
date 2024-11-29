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

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ArraySortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.BitVectorInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.NumericSortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ComputeSCC;

public class ModelBuilder {

	Model mModel;
	SharedTermEvaluator mEvaluator;
	Map<CCTerm, Term> mModelValues = new HashMap<>();
	Theory mTheory;

	public ModelBuilder(final CClosure closure, final List<CCTerm> terms, final Model model,
			final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory arrayTheory, final DataTypeTheory datatypeTheory, final CCTerm trueNode,
			final CCTerm falseNode) {
		mModel = model;
		mEvaluator = ste;
		mTheory = t;

		// create a map from sorts to representatives of that sort.
		final LinkedHashMap<Sort, List<CCTerm>> repsBySort = new LinkedHashMap<>();
		for (final CCTerm term : terms) {
			if (term.getRepresentative() == term && term.getFlatTerm() != null) {
				final Sort sort = term.getFlatTerm().getSort();
				List<CCTerm> reps = repsBySort.get(sort);
				if (reps == null) {
					reps = new ArrayList<>();
					repsBySort.put(sort, reps);
				}
				reps.add(term);
			}
		}

		// We need a topological ordering on the sorts.
		final ComputeSCC.ComputeSuccessor<Sort> dependencies = (final Sort sort) ->  {
			if (sort.isArraySort()) {
				return Arrays.asList(sort.getArguments()).iterator();
			} else if (sort.getSortSymbol().isDatatype()) {
				final Sort[] datatypeParameters = sort.getArguments();
				final Constructor[] constrs = ((DataType) sort.getSortSymbol()).getConstructors();
				return new Iterator<Sort>() {
					int mConstructorIdx = 0;
					int mSortIdx = 0;
					// datatypes always depend on Bool for tester
					Sort[] mSorts = new Sort[] { t.getBooleanSort() };

					@Override
					public boolean hasNext() {
						while (mSortIdx >= mSorts.length) {
							if (mConstructorIdx == constrs.length) {
								return false;
							}
							mSorts = constrs[mConstructorIdx++].getArgumentSorts();
							mSortIdx = 0;
						}
						return true;
					}

					@Override
					public Sort next() {
						while (mSortIdx >= mSorts.length) {
							mSorts = constrs[mConstructorIdx++].getArgumentSorts();
							mSortIdx = 0;
						}
						final Sort dependentSort = mSorts[mSortIdx++];
						return datatypeParameters == null ? dependentSort : dependentSort.mapSort(datatypeParameters);
					}
				};
			} else if (sort.isBitVecSort()) {
				return Collections.singleton(sort.getTheory().getNumericSort()).iterator();
			} else {
				return Collections.emptyListIterator();
			}
		};
		final List<List<Sort>> sortSCCs = new ComputeSCC<>(dependencies).getSCCs(repsBySort.keySet().iterator());

		for (final List<Sort> scc : sortSCCs) {
			if (scc.get(0).getSortSymbol().isDatatype()) {
				datatypeTheory.fillInModel(this, scc, repsBySort);
			} else {
				assert scc.size() == 1;
				final Sort sort = scc.get(0);
				if (repsBySort.containsKey(sort)) {
					if (sort.isArraySort()) {
						arrayTheory.fillInModel(this, repsBySort.get(sort));
					} else {
						fillInTermValues(repsBySort.get(sort), trueNode, falseNode);
					}
				}
			}
		}
		fillInFunctions(terms, model, t);
	}

	public Model getModel() {
		return mModel;
	}

	public Theory getTheory() {
		return mTheory;
	}

	public SharedTermEvaluator getEvaluator() {
		return mEvaluator;
	}

	public Term getModelValue(final CCTerm term) {
		return mModelValues.get(term.getRepresentative());
	}

	public void setModelValue(final CCTerm term, final Term value) {
		assert term == term.getRepresentative();
		final Term old = mModelValues.put(term, value);
		mModel.provideSortInterpretation(value.getSort()).register(value);
		assert old == null || old == value;
	}

	public void fillInTermValues(final List<CCTerm> terms, final CCTerm trueNode, final CCTerm falseNode) {
		final Set<CCTerm> delayed = new HashSet<>();
		for (final CCTerm ccterm : terms) {
			if (ccterm == ccterm.mRepStar && !ccterm.isFunc()) {
				Term value;
				final Term smtterm = ccterm.getFlatTerm();
				final Sort sort = smtterm.getSort();
				if (sort.isNumericSort()) {
					Rational v;
					if (ccterm.getSharedTerm() != null) {
						v = mEvaluator.evaluate(ccterm.getSharedTerm().getFlatTerm(), mTheory);
						if (smtterm.getSort().getName().equals("Int") && !v.isIntegral()) {
							throw new AssertionError("Int term has non-integral value");
						}
						value = v.toTerm(sort);
					} else {
						delayed.add(ccterm);
						continue;
					}
				} else if (ccterm.getFlatTerm().getSort().isBitVecSort()) {
					value = null;
					for (final CCTerm member : ccterm.mRepStar.mMembers) {
						final Term t = member.getFlatTerm();
						if (t instanceof ApplicationTerm) {
							if (((ApplicationTerm) t).getFunction().getName().equals("nat2bv")) {
								final Term arg = ((ApplicationTerm) t).getParameters()[0];
								final Rational v = mEvaluator.evaluate(arg, mTheory);
								assert v.isIntegral();
								BigInteger vInt = v.numerator();
								final int width = Integer.parseInt(t.getSort().getIndices()[0]);
								vInt = vInt.mod(BigInteger.ONE.shiftLeft(width));
								value = BitVectorInterpretation.BV(vInt, t.getSort());
								break;
							}
						}
					}
					assert value != null;
				} else if (ccterm == trueNode.mRepStar) {
					value = sort.getTheory().mTrue;
				} else if (sort.isInternal() && sort.getName().equals(SMTLIBConstants.BOOL)) {
					// By convention, we convert to == TRUE.  Hence, if a value
					// is not equal to TRUE but Boolean, we have to adjust the
					// model and set it to false.
					value = sort.getTheory().mFalse;
				} else {
					assert !sort.isArraySort() && !sort.getSortSymbol().isDatatype();
					value = mModel.extendFresh(sort);
				}
				setModelValue(ccterm, value);
			}
		}
		// Handle all delayed elements
		// note that extendFresh must be called after all values in the model have been extended to the numeric sort.
		for (final CCTerm ccterm : delayed) {
			final Term value = mModel.extendFresh(ccterm.getFlatTerm().getSort());
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

	private boolean isUndefinedFor(FunctionSymbol fs, ArrayDeque<Term> args) {
		if (fs.isSelector()) {
			final DataType datatype = (DataType) fs.getParameterSorts()[0].getSortSymbol();
			final ApplicationTerm arg = (ApplicationTerm) args.getFirst();
			final Constructor c = datatype.getConstructor(arg.getFunction().getName());
			// A selector is undefined if the argument's constructor doesn't match
			return !Arrays.asList(c.getSelectors()).contains(fs.getName());
		} else if (isDivision(fs)) {
			// A division by zero is undefined
			return NumericSortInterpretation.toRational(args.getLast()) == Rational.ZERO;
		}
		return false;
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
			if (!fs.isIntern() || isUndefinedFor(fs, args)) {
				model.map(fs, args.toArray(new Term[args.size()]), value);
			} else if (fs.getName() == SMTInterpolConstants.DIFF) {
				final ArraySortInterpretation arraySort = (ArraySortInterpretation) model
						.provideSortInterpretation(fs.getParameterSorts()[0]);
				assert args.size() == 2;
				arraySort.addDiff(args.getFirst(), args.getLast(), value);
			}
		}
	}

}

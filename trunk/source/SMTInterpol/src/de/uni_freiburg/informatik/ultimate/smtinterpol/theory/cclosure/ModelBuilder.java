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
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
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
	/**
	 * For each representative of a numeric congruence class, the minimal/maximal offset at which any use site (a class
	 * member or a function application argument) references the class. The value at such a use site is the
	 * representative's value plus the offset, so a freshly chosen class value must keep the whole range
	 * {@code [value+min, value+max]} clear of other model values, not just the value itself.
	 */
	Map<CCTerm, Rational> mMinOffset = new HashMap<>();
	Map<CCTerm, Rational> mMaxOffset = new HashMap<>();

	public ModelBuilder(final CClosure closure, final List<CCTerm> terms, final Model model,
			final Theory t, final SharedTermEvaluator ste,
			final ArrayTheory arrayTheory, final DataTypeTheory datatypeTheory, final CCTerm trueNode,
			final CCTerm falseNode) {
		mModel = model;
		mEvaluator = ste;
		mTheory = t;

		// collect the offset range at which each numeric class is used: every member and every function application
		// argument is a use site whose model value is the representative's value plus its offset to the representative.
		for (final CCTerm term : terms) {
			final Term flatTerm = term.getFlatTerm();
			if (flatTerm != null && flatTerm.getSort().isNumericSort()) {
				updateOffsetRange(term.getRepresentative(), term.getOffsetToRep());
			}
			if (term instanceof CCAppTerm) {
				final CCAppTerm app = (CCAppTerm) term;
				for (int i = 0; i < app.getArgCount(); i++) {
					final CCParameter arg = app.getArgParam(i);
					final Term argTerm = arg.getCCTerm().getFlatTerm();
					if (argTerm != null && argTerm.getSort().isNumericSort()) {
						updateOffsetRange(arg.getRepresentative(), arg.getOffsetToRep());
					}
				}
			}
		}

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

	/**
	 * The model value of a {@link CCParameter} value {@code term + offset}: the representative's model value shifted by
	 * the parameter's offset to the representative. A bare {@link CCTerm} is an offset-free parameter, so this returns
	 * its representative's value; a numeric member additionally adds its offset to the representative. Returns
	 * {@code null} if the class has no model value yet (used as a "value computed?" check) &mdash; this only happens for
	 * non-numeric sorts, where no offset arithmetic is attempted on the missing value.
	 *
	 * <p>This is the only model-value accessor: there is deliberately no {@code getModelValue(CCTerm)}, since looking up
	 * a bare representative would silently drop a member's offset (returning the representative's value instead of the
	 * member's) &mdash; a subtle source of wrong models for numeric terms.
	 */
	public Term getModelValue(final CCParameter param) {
		final Term repValue = mModelValues.get(param.getRepresentative());
		final Sort sort = param.getCCTerm().getFlatTerm().getSort();
		if (!sort.isNumericSort()) {
			assert param.getOffsetToRep().equals(Rational.ZERO);
			return repValue;
		}
		// the member's value is the representative's value shifted by the parameter's offset to the representative
		// (which folds in both the class offset and the structural argument offset, e.g. the +5 in x+5).
		return NumericSortInterpretation.toRational(repValue).add(param.getOffsetToRep()).toTerm(sort);
	}

	private void updateOffsetRange(final CCTerm rep, final Rational offset) {
		final Rational min = mMinOffset.get(rep);
		if (min == null || offset.compareTo(min) < 0) {
			mMinOffset.put(rep, offset);
		}
		final Rational max = mMaxOffset.get(rep);
		if (max == null || offset.compareTo(max) > 0) {
			mMaxOffset.put(rep, offset);
		}
	}

	public void setModelValue(final CCTerm term, final Term value) {
		assert term == term.getRepresentative();
		final Term old = mModelValues.put(term, value);
		mModel.provideSortInterpretation(value.getSort()).register(value);
		if (value.getSort().isNumericSort()) {
			// mark the largest use-site value of the class as used, so fresh values avoid the whole class range.
			final Rational maxOffset = mMaxOffset.get(term);
			if (maxOffset != null && maxOffset.signum() > 0) {
				mModel.provideSortInterpretation(value.getSort())
						.register(NumericSortInterpretation.toRational(value).add(maxOffset).toTerm(value.getSort()));
			}
		}
		assert old == null || old == value;
	}

	public void fillInTermValues(final List<CCTerm> terms, final CCTerm trueNode, final CCTerm falseNode) {
		final Set<CCTerm> delayed = new HashSet<>();
		for (final CCTerm ccterm : terms) {
			if (ccterm == ccterm.mRepStar) {
				Term value;
				final Term smtterm = ccterm.getFlatTerm();
				final Sort sort = smtterm.getSort();
				if (sort.isNumericSort()) {
					Rational v;
					if (ccterm.getSharedTerm() != null) {
						final CCTerm shared = ccterm.getSharedTerm();
						// evaluate gives the value of the (offset-free) shared term; the representative's value is that
						// minus the shared term's offset to the representative.
						v = mEvaluator.evaluate(shared.getFlatTerm(), mTheory).sub(shared.getOffsetToRep());
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
							if (((ApplicationTerm) t).getFunction().getName().equals(SMTLIBConstants.INT_TO_BV)) {
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
			final Sort sort = ccterm.getFlatTerm().getSort();
			Rational value = NumericSortInterpretation.toRational(mModel.extendFresh(sort));
			// shift by the class's smallest use-site offset, so even the smallest use-site value (value + minOffset)
			// is the fresh one; setModelValue then marks the largest one (value + maxOffset) as used.
			final Rational minOffset = mMinOffset.get(ccterm);
			if (minOffset != null && minOffset.signum() < 0) {
				value = value.sub(minOffset);
			}
			setModelValue(ccterm, value.toTerm(sort));
		}
	}

	public void fillInFunctions(final List<CCTerm> terms, final Model model, final Theory t) {
		for (final CCTerm term : terms) {
			add(model, term, getModelValue(term), t);
		}
	}

	private void add(final Model model, final CCTerm term, final Term value, final Theory t) {
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

	private boolean isUndefinedFor(FunctionSymbol fs, Term[] args) {
		if (fs.isSelector()) {
			final DataType datatype = (DataType) fs.getParameterSorts()[0].getSortSymbol();
			final ApplicationTerm arg = (ApplicationTerm) args[0];
			final Constructor c = datatype.getConstructor(arg.getFunction().getName());
			// A selector is undefined if the argument's constructor doesn't match
			return !Arrays.asList(c.getSelectors()).contains(fs.getName());
		} else if (isDivision(fs)) {
			// A division by zero is undefined
			return NumericSortInterpretation.toRational(args[1]) == Rational.ZERO;
		} else if (fs.getName() == Interpolator.EQ) {
			return true;
		}
		return false;
	}

	private void addApp(final Model model, final CCAppTerm app, final Term value, final Theory t) {
		Term[] args = new Term[app.getArgCount()];
		for (int i = 0; i < args.length; i++) {
			// the actual argument is the CCParameter's term + offset, evaluated at its model value
			final CCParameter argParam = app.getArgParam(i);
			args[i] = getModelValue(argParam);
		}
		final FunctionSymbol fs = app.getFunctionSymbol();
		if (!fs.isIntern() || isUndefinedFor(fs, args)) {
			model.map(fs, args, value);
		} else if (fs.getName() == SMTInterpolConstants.DIFF) {
			final ArraySortInterpretation arraySort = (ArraySortInterpretation) model
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			assert args.length == 2;
			arraySort.addDiff(args[0], args[1], value);
		}
	}

}

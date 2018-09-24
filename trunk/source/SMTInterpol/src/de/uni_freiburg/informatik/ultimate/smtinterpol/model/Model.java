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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue.Index;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;

/**
 * A model represented as injection between integers and domain values. The integers should be positive. Furthermore,
 * the model reserves <code>-1</code> for undefined values, <code>0</code> for the default value, and <code>1</code> for
 * the second value.
 * 
 * @author Juergen Christ
 */
public class Model implements de.uni_freiburg.informatik.ultimate.logic.Model {

	private final HashMap<Sort, SortInterpretation> mSorts = new HashMap<>();

	private final HashMap<Sort, ArraySortInterpretation> mArraySorts = new HashMap<>();

	private final BoolSortInterpretation mBoolSort;

	private final NumericSortInterpretation mNumSorts;

	private final HashMap<FunctionSymbol, FunctionValue> mFuncVals = new HashMap<>();

	private final Theory mTheory;

	private final ModelEvaluator mEval;

	private final FormulaUnLet mUnlet = new FormulaUnLet(FormulaUnLet.UnletType.EXPAND_DEFINITIONS);

	private final boolean mPartialModel;

	public Model(final Clausifier clausifier, final Theory t, final boolean partial) {
		mTheory = t;
		mPartialModel = partial;
		mBoolSort = new BoolSortInterpretation();
		mNumSorts = new NumericSortInterpretation();
		// Extract Boolean model
		final FunctionValue trueValue = new FunctionValue(mBoolSort.getTrueIdx());
		final FunctionValue falseValue = new FunctionValue(mBoolSort.getFalseIdx());
		for (final BooleanVarAtom atom : clausifier.getBooleanVars()) {
			final ApplicationTerm at = (ApplicationTerm) atom.getSMTFormula(t);
			FunctionValue value;
			if (atom.getDecideStatus() == null) {
				value = atom.getPreferredStatus() == atom ? trueValue : falseValue;
			} else {
				value = atom.getDecideStatus() == atom ? trueValue : falseValue;
			}
			mFuncVals.put(at.getFunction(), value);
		}
		// Extract different theories
		final CClosure cc = clausifier.getCClosure();
		LinArSolve la = null;
		ArrayTheory array = null;
		for (final ITheory theory : clausifier.getEngine().getAttachedTheories()) {
			if (theory instanceof LinArSolve) {
				la = (LinArSolve) theory;
			} else if (theory instanceof ArrayTheory) {
				array = (ArrayTheory) theory;
			} else if (theory != cc) {
				throw new InternalError("Modelproduction for theory not implemented: " + theory);
			}
		}
		final SharedTermEvaluator ste = new SharedTermEvaluator(la);
		if (la != null) {
			la.fillInModel(this, t, ste);
		}
		if (cc != null) {
			cc.fillInModel(this, t, ste, array);
		}
		if (!partial) {
			for (final FunctionSymbol fs : t.getDeclaredFunctions().values()) {
				if (!fs.isIntern() && !mFuncVals.containsKey(fs)) {
					final SortInterpretation si = provideSortInterpretation(fs.getReturnSort());
					// ensure the sort is inhabited
					si.ensureCapacity(1);
					map(fs, 0);
				}
			}
		}
		mEval = new ModelEvaluator(this);
	}

	public boolean checkTypeValues(final LogProxy logger) {
		boolean correct = true;
		for (final Map.Entry<FunctionSymbol, FunctionValue> me : mFuncVals.entrySet()) {
			final FunctionSymbol fs = me.getKey();
			if (fs.getReturnSort().getName().equals("Int")) {
				if (!mNumSorts.get(me.getValue().getDefault()).isIntegral()) {
					correct = false;
					if (fs.getParameterSorts().length == 0) {
						logger.fatal("Non-integral value for integer variable " + fs);
					} else {
						logger.fatal("Non-integral default value for function " + fs);
					}
				}
				for (final Map.Entry<Index, Integer> val : me.getValue().values().entrySet()) {
					if (!mNumSorts.get(val.getValue()).isIntegral()) {
						correct = false;
						logger.fatal("Non-integral value for function " + fs + " at index " + me.getKey());
					}
				}
			}
		}
		return correct;
	}

	public int getFalseIdx() {
		return mBoolSort.getFalseIdx();
	}

	public int getTrueIdx() {
		return mBoolSort.getTrueIdx();
	}

	public int extendNumeric(final FunctionSymbol fsym, final Rational rat) {
		assert fsym.getReturnSort().isNumericSort();
		assert !fsym.getReturnSort().getName().equals("Int") || rat.isIntegral();
		final int idx = mNumSorts.extend(rat);
		mFuncVals.put(fsym, new FunctionValue(idx));
		return idx;
	}

	public int putNumeric(final Rational rat) {
		return mNumSorts.extend(rat);
	}

	public int extendFresh(final Sort s) {
		if (s.isArraySort()) {
			ArraySortInterpretation si = mArraySorts.get(s);
			if (si == null) {
				si = new ArraySortInterpretation(provideSortInterpretation(s.getArguments()[0]),
						provideSortInterpretation(s.getArguments()[1]));
				mArraySorts.put(s, si);
			}
			return si.extendFresh();
		}
		SortInterpretation si = mSorts.get(s);
		if (si == null) {
			si = new FiniteSortInterpretation();
			mSorts.put(s, si);
		}
		return si.extendFresh();
	}

	@Override
	public Set<FunctionSymbol> getDefinedFunctions() {
		return Collections.unmodifiableSet(mFuncVals.keySet());
	}

	Term index2Term(final Index index, final TermVariable[] vars) {
		final int[] idx = index.getArray();
		assert vars.length == idx.length;
		final Term[] conj = new Term[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			conj[i] = mTheory.equals(vars[i], toModelTerm(idx[i], vars[i].getSort()));
		}
		return mTheory.and(conj);
	}

	public Term getFunctionDefinition(final FunctionSymbol fs, final TermVariable[] vars) {
		final FunctionValue value = mFuncVals.get(fs);
		if (value == null) {
			throw new IllegalArgumentException("No model for " + fs);
		}
		if (fs.getParameterSorts().length != vars.length) {
			throw new IllegalArgumentException("Wrong number of variables");
		}
		final int defaultVal = value.getDefault();
		final Sort resultSort = fs.getReturnSort();
		Term definition = toModelTerm(defaultVal, resultSort);
		for (final Entry<Index, Integer> me : value.values().entrySet()) {
			if (me.getValue() != defaultVal) {
				final Term cond = index2Term(me.getKey(), vars);
				final Term val = toModelTerm(me.getValue(), resultSort);
				definition = mTheory.ifthenelse(cond, val, definition);
			}
		}
		return definition;
	}

	@Override
	public Term getFunctionDefinition(final String func, final TermVariable[] args) {
		final Sort[] argTypes = new Sort[args.length];
		for (int i = 0; i < args.length; i++) {
			argTypes[i] = args[i].getSort();
		}
		final FunctionSymbol fs = mTheory.getFunction(func, argTypes);
		if (fs == null) {
			throw new IllegalArgumentException("Function " + func + " not defined.");
		}
		return getFunctionDefinition(fs, args);
	}

	public FunctionValue map(final FunctionSymbol fs, final int value) {
		FunctionValue res = mFuncVals.get(fs);
		if (res == null) {
			res = new FunctionValue(value);
			mFuncVals.put(fs, res);
		}
		assert res.getDefault() == value;
		return res;
	}

	public FunctionValue map(final FunctionSymbol fs, final int[] args, final int value) {
		assert fs.getParameterSorts().length == args.length;
		FunctionValue val = mFuncVals.get(fs);
		if (val == null) {
			val = new FunctionValue();
			mFuncVals.put(fs, val);
		}
		val.put(value, args);
		return val;
	}

	Term getUndefined(final Sort s) {
		final FunctionSymbol fsym = mTheory.getFunctionWithResult("@undefined", null, s);
		return mTheory.term(fsym);
	}

	@Override
	public Term evaluate(final Term input) {
		final Term unletted = mUnlet.unlet(input);
		return mEval.evaluate(unletted);
	}

	@Override
	public Map<Term, Term> evaluate(final Term[] input) {
		final LinkedHashMap<Term, Term> values = new LinkedHashMap<>();
		for (final Term t : input) {
			values.put(t, evaluate(t));
		}
		return values;
	}

	@Override
	public String toString() {
		final ModelFormatter mf = new ModelFormatter(mTheory, this);
		// if (!mSorts.isEmpty())
		// mf.appendComment("Sort interpretations");
		// for (Map.Entry<Sort, SortInterpretation> me : mSorts.entrySet())
		// mf.appendSortInterpretation(me.getValue(), me.getKey());
		// // Only if we printed ";; Sort interpretations" we should print the
		// // delimiting comment ";; Function interpretations"
		// if (!mSorts.isEmpty())
		// mf.appendComment("Function interpretations");
		for (final Map.Entry<FunctionSymbol, FunctionValue> me : mFuncVals.entrySet()) {
			if (!me.getKey().isIntern()) {
				mf.appendValue(me.getKey(), me.getValue(), mTheory);
			}
		}
		return mf.finish();
	}

	Theory getTheory() {
		return mTheory;
	}

	public boolean isPartialModel() {
		return mPartialModel;
	}

	public BoolSortInterpretation getBoolSortInterpretation() {
		return mBoolSort;
	}

	public NumericSortInterpretation getNumericSortInterpretation() {
		return mNumSorts;
	}

	public SortInterpretation provideSortInterpretation(final Sort sort) {
		if (sort.isNumericSort()) {
			return mNumSorts;
		}
		if (sort == mTheory.getBooleanSort()) {
			return mBoolSort;
		}

		if (sort.isArraySort()) {
			ArraySortInterpretation array = mArraySorts.get(sort);
			if (array == null) {
				array = new ArraySortInterpretation(provideSortInterpretation(sort.getArguments()[0]),
						provideSortInterpretation(sort.getArguments()[1]));
				mArraySorts.put(sort, array);
			}
			return array;
		}
		SortInterpretation res = mSorts.get(sort);
		if (res == null) {
			res = new FiniteSortInterpretation();
			mSorts.put(sort, res);
		}
		return res;
	}

	public FunctionValue getFunctionValue(final FunctionSymbol fs) {
		return mFuncVals.get(fs);
	}

	public Term toModelTerm(final int idx, final Sort resultSort) {
		if (idx == -1) {
			return getUndefined(resultSort);
		}
		if (resultSort == mTheory.getBooleanSort()) {
			return mBoolSort.get(idx, resultSort, mTheory);
		}
		if (resultSort.isNumericSort()) {
			final Rational val = mNumSorts.get(idx);
			return val.toTerm(resultSort);
		}
		if (resultSort.isArraySort()) {
			ArraySortInterpretation array = mArraySorts.get(resultSort);
			if (array == null) {
				if (mPartialModel) {
					return getUndefined(resultSort);
				}
				array = new ArraySortInterpretation(provideSortInterpretation(resultSort.getArguments()[0]),
						provideSortInterpretation(resultSort.getArguments()[1]));
				mArraySorts.put(resultSort, array);
			}
			return array.get(idx, resultSort, mTheory);
		}
		SortInterpretation si = mSorts.get(resultSort);
		if (si == null) {
			if (mPartialModel) {
				return getUndefined(resultSort);
			}
			si = new FiniteSortInterpretation();
			si.ensureCapacity(idx + 1);
		}
		return si.get(idx, resultSort, mTheory);
	}

	public ArraySortInterpretation getArrayInterpretation(final Sort arraySort) {
		// FIXME might not exist
		return mArraySorts.get(arraySort);
	}

}

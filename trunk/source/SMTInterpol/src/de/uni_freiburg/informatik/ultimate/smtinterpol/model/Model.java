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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.DataTypeTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;

/**
 * A model represented as injection between integers and domain values. The integers should be positive. Furthermore,
 * the model reserves <code>-1</code> for undefined values, <code>0</code> for the default value, and <code>1</code> for
 * the second value.
 *
 * @author Juergen Christ
 */
public class Model implements de.uni_freiburg.informatik.ultimate.logic.Model {

	private final HashMap<Sort, SortInterpretation> mSorts = new HashMap<>();

	private final HashMap<FunctionSymbol, FunctionValue> mFuncVals = new HashMap<>();

	private final Theory mTheory;

	private final ModelEvaluator mEval;

	private int mModelValueCounter;

	public Model(final Clausifier clausifier, final Theory theory) {
		mTheory = theory;
		mSorts.put(theory.getBooleanSort(), new BoolSortInterpretation());
		if (theory.getLogic().hasIntegers() || theory.getLogic().hasReals()) {
			final SortInterpretation numericInterpretation = new NumericSortInterpretation();
			if (theory.getLogic().hasIntegers()) {
				mSorts.put(theory.getNumericSort(), numericInterpretation);
			}
			if (theory.getLogic().hasReals()) {
				mSorts.put(theory.getRealSort(), numericInterpretation);
			}
		}
		// Extract Boolean model
		final FunctionValue trueValue = new FunctionValue(theory.mTrue);
		final FunctionValue falseValue = new FunctionValue(theory.mFalse);
		for (final BooleanVarAtom atom : clausifier.getBooleanVars()) {
			final ApplicationTerm at = (ApplicationTerm) atom.getSMTFormula(theory);
			FunctionValue value;
			if (atom.getDecideStatus() == null) {
				value = atom.getPreferredStatus() == atom ? trueValue : falseValue;
			} else {
				value = atom.getDecideStatus() == atom ? trueValue : falseValue;
			}
			mFuncVals.put(at.getFunction(), value);
		}
		// Extract different theories
		CClosure cc = null;
		LinArSolve la = null;
		ArrayTheory array = null;
		DataTypeTheory datatype = null;
		for (final ITheory theorySolver : clausifier.getEngine().getAttachedTheories()) {
			if (theorySolver instanceof CClosure) {
				cc = (CClosure) theorySolver;
			} else if (theorySolver instanceof LinArSolve) {
				la = (LinArSolve) theorySolver;
			} else if (theorySolver instanceof ArrayTheory) {
				array = (ArrayTheory) theorySolver;
			} else if (theorySolver instanceof DataTypeTheory) {
				datatype = (DataTypeTheory) theorySolver;
			} else if (theorySolver instanceof QuantifierTheory) {
				if (!((QuantifierTheory) theorySolver).getQuantClauses().isEmpty()) {
					throw new UnsupportedOperationException("Modelproduction for quantifier theory not implemented.");
				}
			} else if (theorySolver instanceof EprTheory) {
				if (!EprTheorySettings.FullInstatiationMode) {
					throw new UnsupportedOperationException("Modelproduction for EPR theory not implemented.");
				}
			} else {
				throw new InternalError("Unknown theory: " + theorySolver);
			}
		}
		final SharedTermEvaluator ste = new SharedTermEvaluator(clausifier);
		if (la != null) {
			la.fillInModel(this, theory, ste);
		}
		if (cc != null) {
			cc.fillInModel(this, theory, ste, array, datatype);
		}
		for (final FunctionSymbol fs : theory.getDeclaredFunctions().values()) {
			if (fs.getDefinition() == null && !fs.isIntern() && !mFuncVals.containsKey(fs)) {
				map(fs, getSomeValue(fs.getReturnSort()));
			}
		}
		mEval = new ModelEvaluator(this);
		mModelValueCounter = 0;
	}

	public boolean checkTypeValues(final LogProxy logger) {
		boolean correct = true;
		for (final Map.Entry<FunctionSymbol, FunctionValue> me : mFuncVals.entrySet()) {
			final FunctionSymbol fs = me.getKey();
			final FunctionValue functionMap = me.getValue();
			// Check that all integer functions/constants map to integer
			if (fs.getReturnSort().getName().equals("Int")) {
				if (!NumericSortInterpretation.toRational(functionMap.getDefault()).isIntegral()) {
					if (fs.getParameterSorts().length == 0) {
						logger.fatal("Non-integral value for integer variable " + fs);
					} else {
						logger.fatal("Non-integral default value for function " + fs);
					}
					correct = false;
				}
				for (final Map.Entry<Index, Term> valEntry : functionMap.values().entrySet()) {
					if (!NumericSortInterpretation.toRational(valEntry.getValue()).isIntegral()) {
						logger.fatal("Non-integral value for function " + fs + " at index " + valEntry.getKey());
						correct = false;
					}
				}
			}
		}
		return correct;
	}

	/**
	 * Get a fresh value. This returns an index that was not yet used for creating a
	 * model value.
	 *
	 * @return the fresh value.
	 */
	public int getFreshModelValue() {
		return mModelValueCounter++;
	}

	public Term getModelValue(final int index, final Sort sort) {
		return provideSortInterpretation(sort).getModelValue(index, sort);
	}

	public Term getSomeValue(final Sort sort) {
		return getModelValue(0, sort);
	}

	public Term getSecondValue(final Sort sort) {
		return getModelValue(1, sort);
	}

	public Term extendFresh(final Sort sort) {
		return provideSortInterpretation(sort).extendFresh(sort);
	}

	@Override
	public Set<FunctionSymbol> getDefinedFunctions() {
		return Collections.unmodifiableSet(mFuncVals.keySet());
	}

	Term generateCondition(final Index index, final TermVariable[] vars) {
		final Term[] idx = index.toArray();
		assert vars.length == idx.length;
		final Term[] conj = new Term[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			conj[i] = mTheory.equals(vars[i], idx[i]);
		}
		return mTheory.and(conj);
	}

	private static boolean isDivision(final FunctionSymbol fs) {
		final String name = fs.getName();
		return fs.isIntern() && (name == "/" || name == "div" || name == "mod");
	}

	public Term getFunctionDefinition(final FunctionSymbol fs, final TermVariable[] vars) {
		final FunctionValue value = mFuncVals.get(fs);
		if (value == null) {
			throw new IllegalArgumentException("No model for " + fs);
		}
		if (fs.getParameterSorts().length != vars.length) {
			throw new IllegalArgumentException("Wrong number of variables");
		}
		final Term defaultVal = value.getDefault();
		Term definition = defaultVal;
		for (final Entry<Index, Term> me : value.values().entrySet()) {
			if (me.getValue() != defaultVal) {
				final Term cond = generateCondition(me.getKey(), vars);
				definition = mTheory.ifthenelse(cond, me.getValue(), definition);
			}
		}
		if (fs.isSelector()) {
			assert vars.length == 1;
			final Sort sort = fs.getParameterSorts()[0];
			final DataType datatype = (DataType) sort.getSortSymbol();
			Constructor constr = null;
			for (final Constructor c : datatype.getConstructors()) {
				if (Arrays.asList(c.getSelectors()).contains(fs.getName())) {
					constr = c;
				}
			}
			final Term tester = mTheory.term(SMTLIBConstants.IS, new String[] { constr.getName() }, null, vars[0]);
			definition = mTheory.ifthenelse(tester, mTheory.term(fs, vars[0]), definition);
		}
		if (isDivision(fs)) {
			final Term isZero = mTheory.term(SMTLIBConstants.EQUALS, vars[1], Rational.ZERO.toTerm(vars[1].getSort()));
			definition = mTheory.ifthenelse(mTheory.term(SMTLIBConstants.NOT, isZero),
					mTheory.term(fs, vars[0], vars[1]), definition);
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

	public FunctionValue map(final FunctionSymbol fs, final Term value) {
		FunctionValue res = mFuncVals.get(fs);
		if (res == null) {
			res = new FunctionValue(value);
			mFuncVals.put(fs, res);
		}
		assert res.getDefault() == value;
		return res;
	}

	public FunctionValue map(final FunctionSymbol fs, final Term[] args, final Term value) {
		assert fs.getParameterSorts().length == args.length;
		FunctionValue val = mFuncVals.get(fs);
		if (val == null) {
			val = new FunctionValue(value);
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
		return mEval.evaluate(input);
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
		final ModelFormatter mf = new ModelFormatter(mTheory);
		for (final Map.Entry<FunctionSymbol, FunctionValue> me : mFuncVals.entrySet()) {
			final FunctionSymbol fs = me.getKey();
			if (!fs.isIntern() || fs.getDefinition() == null) {
				final Sort[] paramSorts = fs.getParameterSorts();
				final TermVariable[] vars = new TermVariable[paramSorts.length];
				for (int i = 0; i < vars.length; ++i) {
					vars[i] = mTheory.createTermVariable("@p" + i, paramSorts[i]);
				}
				mf.appendValue(fs, vars, getFunctionDefinition(fs, vars));
			}
		}
		return mf.finish();
	}

	Theory getTheory() {
		return mTheory;
	}

	public SortInterpretation provideSortInterpretation(final Sort sort) {
		SortInterpretation interpretation = mSorts.get(sort);
		if (interpretation == null) {
			if (sort.isArraySort()) {
				interpretation = new ArraySortInterpretation(this, provideSortInterpretation(sort.getArguments()[0]),
						provideSortInterpretation(sort.getArguments()[1]));
			} else if (sort.getSortSymbol().isDatatype()) {
				interpretation = new DataTypeInterpretation(this, sort);
			} else {
				interpretation = new FiniteSortInterpretation(this);
			}
			mSorts.put(sort, interpretation);
		}
		return interpretation;
	}

	public FunctionValue getFunctionValue(final FunctionSymbol fs) {
		return mFuncVals.get(fs);
	}
}

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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * An evaluator for terms against the current model.
 * @author Juergen Christ
 */
public class ModelEvaluator extends NonRecursive {
	
	/**
	 * A helper to enqueue either the true or the false branch of an ite.
	 * @author Juergen Christ
	 */
	private static class ITESelector implements Walker {

		private final ApplicationTerm mIte;
		
		public ITESelector(ApplicationTerm ite) {
			mIte = ite;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final ModelEvaluator eval = (ModelEvaluator) engine;
			final int selector = eval.getConverted();
			if (selector == -1) {
				eval.setResult(-1);
			} else {
				eval.pushTerm(mIte.getParameters()
						[selector == eval.mModel.getBoolSortInterpretation()
						.getTrueIdx() ? 1 : 2]);
			}
		}
		
	}
	
	private static class AddToCache implements Walker {
		
		private final Term mTerm;
		public AddToCache(Term t) {
			mTerm = t;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final ModelEvaluator eval = (ModelEvaluator) engine;
			eval.mCache.put(mTerm, eval.mEvaluated.peekLast());
		}
		
	}
	
	private static class Evaluator implements Walker {

		private final ApplicationTerm mTerm;
		public Evaluator(ApplicationTerm term) {
			mTerm = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final ModelEvaluator eval = (ModelEvaluator) engine;
			final int[] args = eval.getConvertedArgs(mTerm.getParameters().length);
			eval.setResult(eval.getValue(mTerm.getFunction(), args, mTerm));
		}
		
	}
	
	private static class CachedEvaluator extends TermWalker {

		public CachedEvaluator(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker) {
			final ModelEvaluator eval = (ModelEvaluator) walker;
			final Integer cached = eval.mCache.get(mTerm);
			if (cached == null) {
				eval.enqueueWalker(new AddToCache(mTerm));
				super.walk(walker);
			} else {
				eval.setResult(cached);
			}	
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			if (!term.getSort().isNumericSort()) {
				throw new InternalError(
						"Don't know how to evaluate this: " + term);
			}
			final ModelEvaluator eval = (ModelEvaluator) walker;
			final NumericSortInterpretation numSorts =
					eval.mModel.getNumericSortInterpretation();
			Rational val;
			if (term.getValue() instanceof BigInteger) {
				val = Rational.valueOf(
						(BigInteger) term.getValue(), BigInteger.ONE); 
			} else if (term.getValue() instanceof BigDecimal) {
				final BigDecimal decimal = (BigDecimal) term.getValue();
				if (decimal.scale() <= 0) {
					final BigInteger num = decimal.toBigInteger();
					val = Rational.valueOf(num, BigInteger.ONE);
				} else {
					final BigInteger num = decimal.unscaledValue();
					final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					val = Rational.valueOf(num, denom);
				}
			} else {
				assert(term.getValue() instanceof Rational);
				val = (Rational) term.getValue();
			}
			eval.setResult(numSorts.extend(val));
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			final ModelEvaluator eval = (ModelEvaluator) walker;
			eval.enqueueWalker(new CachedEvaluator(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			final ModelEvaluator eval = (ModelEvaluator) walker;
			if (term.getFunction().getName().equals("ite")) {
				eval.enqueueWalker(new ITESelector(term));
				eval.pushTerm(term.getParameters()[0]);
			} else {
				eval.enqueueWalker(new Evaluator(term));
				eval.pushTerms(term.getParameters());			
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError(
					"Let-Terms should not be in model evaluation");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			throw new SMTLIBException(
					"Quantifiers not supported in model evaluation");
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			throw new SMTLIBException("Terms to evaluate must be closed");
		}
		
	}
	
	HashMap<Term, Integer> mCache = new HashMap<Term, Integer>();
	
	ArrayDeque<Integer> mEvaluated = new ArrayDeque<Integer>();
	
	private Integer getConverted() {
		return mEvaluated.removeLast();
	}
	
	public int getValue(FunctionSymbol fs, int[] args, ApplicationTerm term) {
		if (fs.isInterpreted()) {
			return interpret(fs, args, term);
		}
		return evalFunction(fs, args);
	}

	public void pushTerms(Term[] terms) {
		for (int i = terms.length - 1; i >= 0; i--) {
			pushTerm(terms[i]);
		}
	}

	public int[] getConvertedArgs(int length) {
		final int[] result = new int[length];
		while (--length >= 0) {
			result[length] = getConverted();
		}
		return result;
	}

	public void pushTerm(Term term) {
		enqueueWalker(new CachedEvaluator(term));
	}

	private void setResult(int res) {
		mEvaluated.addLast(res);
	}
	
	private final Model mModel;

	public ModelEvaluator(Model model) {
		mModel = model;
	}

	public Term evaluate(Term input) {
		try {
			run(new CachedEvaluator(input));
			final int res = getConverted();
			return mModel.toModelTerm(res, input.getSort());
		} finally {
			reset();
		}
	}
	
	private int evalFunction(FunctionSymbol fs, int... args) {
		FunctionValue val = mModel.getFunctionValue(fs);
		if (val == null) {
			val = mModel.map(fs, 0);
		}
		return val.get(args, mModel.isPartialModel());
	}
	
	private int interpret(FunctionSymbol fun, int[] args,
			ApplicationTerm term) {
		if (fun.isModelValue()) {
			return Integer.parseInt(fun.getName().substring(1));
		}
		final Theory theory = mModel.getTheory();
		if (fun == theory.mTrue.getFunction()) {
			return mModel.getTrueIdx();
		}
		if (fun == theory.mFalse.getFunction()) {
			return mModel.getFalseIdx();
		}
		if (fun == theory.mAnd) {
			int res = args[0];
			for (final int arg : args) {
				if (arg == -1) {
					res = -1;
				} else if (arg == mModel.getFalseIdx()) {
					return arg;
				}
				assert (arg == -1 || arg == mModel.getTrueIdx());
			}
			return res;
		}
		if (fun == theory.mOr) {
			int res = args[0];
			for (final int arg : args) {
				if (arg == -1) {
					res = arg;
				} else if (arg == mModel.getTrueIdx()) {
					return arg;
				}
				assert (arg == -1 || arg == mModel.getFalseIdx());
			}
			return res;
		}
		if (fun == theory.mImplies) {
			int val = args[args.length - 1];
			for (int i = args.length - 2; i >= 0; --i) {
				final int argi = args[i];
				if (val == mModel.getTrueIdx() || argi == mModel.getFalseIdx()) {
					val = mModel.getTrueIdx();
				} else if (!(argi == mModel.getTrueIdx()
						&& val == mModel.getFalseIdx()))
				 {
					val = -1; // There is at least one undefined
				}
			}
			return val;
		}
		// Propagate undefined
		for (final int arg : args) {
			if (arg == -1) {
				return arg;
			}
		}
		if (fun == theory.mNot) {
			return args[0] == mModel.getTrueIdx()
					? mModel.getFalseIdx() : mModel.getTrueIdx();
		}
		if (fun == theory.mXor) {
			int val = args[0];
			for (int i = 1; i < args.length; ++i) {
				final int argi = args[i];
				val = argi == val ? mModel.getFalseIdx() : mModel.getTrueIdx();
			}
			return val;
		}
		final String name = fun.getName();
		if (name.equals("=")) {
			for (int i = 1; i < args.length; ++i) {
				if (args[i] != args[0]) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals("distinct")) {
			final HashSet<Integer> vals = new HashSet<Integer>();
			for (final int arg : args) {
				if (!vals.add(arg)) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals("ite")) {
			assert(args.length == 3);// NOCHECKSTYLE since ite has 3 parameters
			final int selector = args[0];
			return args[selector + 1];
		}
		if (name.equals("+")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.add(rationalValue(args[i]));
			}
			return mModel.getNumericSortInterpretation().extend(val);
		}
		if (name.equals("-")) {
			Rational val = rationalValue(args[0]);
			if (args.length == 1) {
				return mModel.getNumericSortInterpretation().extend(val.negate());
			} else {
				for (int i = 1; i < args.length; ++i) {
					val = val.sub(rationalValue(args[i]));
				}
				return mModel.getNumericSortInterpretation().extend(val);
			}
		}
		if (name.equals("*")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.mul(rationalValue(args[i]));
			}
			return mModel.getNumericSortInterpretation().extend(val);
		}
		if (name.equals("/")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				final Rational divisor = rationalValue(args[i]);
				if (divisor.equals(Rational.ZERO)) {
					final FunctionSymbol div0 = theory.getFunction(
							"@/0", fun.getReturnSort());
					final int idx = mModel.getNumericSortInterpretation().extend(val);
					final int divval = evalFunction(div0, idx);
					if (divval == -1)
					{
						return -1; // Propagate undefined
					}
					val = rationalValue(divval);
				} else {
					val = val.div(divisor);
				}
			}
			return mModel.getNumericSortInterpretation().extend(val);
		}
		if (name.equals("<=")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) > 0) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals("<")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) >= 0) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals(">=")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) < 0) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals(">")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) <= 0) {
					return mModel.getFalseIdx();
				}
			}
			return mModel.getTrueIdx();
		}
		if (name.equals("div")) {
			// From the standard...
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				final Rational n = rationalValue(args[i]);
				if (n.equals(Rational.ZERO)) {
					final FunctionSymbol div0 = theory.getFunction(
							"@div0", fun.getReturnSort());
					final int idx = mModel.getNumericSortInterpretation().extend(val);
					final int divval = evalFunction(div0, idx);
					if (divval == -1)
					 {
						return -1; // Propagate undefined
					}
					val = rationalValue(divval);
				} else {
					final Rational div = val.div(n);
					val = n.isNegative() ? div.ceil() : div.floor();
				}
			}
			return mModel.getNumericSortInterpretation().extend(val);
		}
		if (name.equals("mod")) {
			assert(args.length == 2);
			final Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO)) {
				final FunctionSymbol div0 = theory.getFunction(
						"@mod0", fun.getReturnSort());
				return evalFunction(div0, args[0]);
			}
			final Rational m = rationalValue(args[0]);
			Rational div = m.div(n);
			div = n.isNegative() ? div.ceil() : div.floor();
			return mModel.getNumericSortInterpretation().extend(
					m.sub(div.mul(n)));
		}
		if (name.equals("abs")) {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return mModel.getNumericSortInterpretation().extend(arg.abs());
		}
		if (name.equals("divisible")) {
			assert(args.length == 1);
			final Rational arg = rationalValue(args[0]);
			final BigInteger[] indices = fun.getIndices();
			assert(indices.length == 1);
			final Rational rdiv = Rational.valueOf(indices[0], BigInteger.ONE);
			return arg.div(rdiv).isIntegral()
					? mModel.getTrueIdx() : mModel.getFalseIdx();
		}
		if (name.equals("to_int")) {
			assert (args.length == 1);
			final Rational arg = rationalValue(args[0]);
			return mModel.getNumericSortInterpretation().extend(arg.floor());
		}
		if (name.equals("to_real")) {
			assert (args.length == 1);
			return args[0];
		}
		if (name.equals("is_int")) {
			assert (args.length == 1);
			final Rational arg = rationalValue(args[0]);
			return arg.isIntegral()
					? mModel.getTrueIdx() : mModel.getFalseIdx();
		}
		// @...0 should not go here...
//		if (name.equals("@/0") || name.equals("@div0") || name.equals("@mod0"))
//			return evalExecTerm(term, fun, args);
		if (name.equals("store")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fun.getParameterSorts()[0]);
			ArrayValue storeVal = array.getValue(args[0]);
			if (storeVal.select(args[1]) == args[2]) {
				return args[0];
			}
			storeVal = storeVal.copy();
			storeVal.store(args[1], args[2]);
			return array.value2index(storeVal);
		}
		if (name.equals("const")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fun.getReturnSort());
			ArrayValue constVal = new ArrayValue();
			constVal.setDefaultValue(args[0]);
			return array.value2index(constVal);
		}
		if (name.equals("select")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fun.getParameterSorts()[0]);
			final ArrayValue val = array.getValue(args[0]);
			return val.select(args[1]);
		}
		if (name.equals("@diff")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fun.getParameterSorts()[0]);
			final ArrayValue left = array.getValue(args[0]);
			final ArrayValue right = array.getValue(args[1]);
			return left.computeDiff(args[1], right, array);
		}
		throw new AssertionError("Unknown internal function " + name);
	}

	private Rational rationalValue(int idx) {
		return mModel.getNumericSortInterpretation().get(idx);
	}
}

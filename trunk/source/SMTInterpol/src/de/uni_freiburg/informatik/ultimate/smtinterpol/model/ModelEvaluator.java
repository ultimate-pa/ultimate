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

import java.math.BigInteger;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * An evaluator for terms against the current model.
 *
 * @author Jochen Hoenicke, Juergen Christ
 */
public class ModelEvaluator extends TermTransformer {

	/**
	 * A helper to enqueue either the true or the false branch of an ite.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class ITESelector implements Walker {

		private final ApplicationTerm mIte;

		public ITESelector(final ApplicationTerm ite) {
			mIte = ite;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ModelEvaluator eval = (ModelEvaluator) engine;
			final ApplicationTerm condition = (ApplicationTerm) eval.getConverted();
			assert isBooleanValue(condition) : "condition must be 'true' or 'false'";
			eval.pushTerm(mIte.getParameters()[condition.getFunction().getName() == "true" ? 1 : 2]);
		}
	}

	/**
	 * A helper to enqueue either the true or the false branch of an ite.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class MatchSelector implements Walker {

		private final MatchTerm mMatch;

		public MatchSelector(final MatchTerm match) {
			mMatch = match;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final Theory theory = mMatch.getTheory();
			final ModelEvaluator eval = (ModelEvaluator) engine;
			final ApplicationTerm dataTerm = (ApplicationTerm) eval.getConverted();
			for (int i = 0; i < mMatch.getConstructors().length; i++) {
				final Constructor cons = mMatch.getConstructors()[i];
				if (cons == null) {
					// default value
					eval.pushTerm(theory.let(mMatch.getVariables()[i][0], dataTerm, mMatch.getCases()[i]));
					return;
				} else if (dataTerm.getFunction().getName() == cons.getName()) {
					eval.pushTerm(theory.let(mMatch.getVariables()[i], dataTerm.getParameters(), mMatch.getCases()[i]));
					return;
				}
			}
			throw new InternalError("Match term not total or data term not evaluated");
		}
	}

	/**
	 * The model where to evaluate in.
	 */
	private final Model mModel;

	/**
	 * The scoped let map. Each scope corresponds to a partially executed let or a quantifier on the todo stack. It
	 * gives the mapping for each term variable defined in that scope to the corresponding term.
	 */
	private final ScopedHashMap<TermVariable, Term> mLetMap = new ScopedHashMap<>(false);

	private static boolean isBooleanValue(final Term term) {
		final Theory theory = term.getTheory();
		return term == theory.mTrue || term == theory.mFalse;
	}

	@Override
	public void convert(Term term) {
		while (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm) term).getSubterm();
		}
		if (term instanceof ConstantTerm) {
			if (!term.getSort().isNumericSort()) {
				throw new InternalError("Don't know how to evaluate this: " + term);
			}
			final Term result = SMTAffineTerm.convertConstant((ConstantTerm) term).toTerm(term.getSort());
			setResult(result);
			return;
		}
		if (term instanceof TermVariable) {
			if (mLetMap.containsKey(term)) {
				setResult(mLetMap.get(term));
				return;
			}
			throw new SMTLIBException("Terms to evaluate must be closed");
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().isIntern() && appTerm.getFunction().getName() == "ite") {
				enqueueWalker(new ITESelector(appTerm));
				pushTerm(appTerm.getParameters()[0]);
				return;
			}
		} else if (term instanceof QuantifiedFormula) {
			throw new SMTLIBException("Quantifiers not supported in model evaluation");
		} else if (term instanceof MatchTerm) {
			final MatchTerm matchTerm = (MatchTerm) term;
			enqueueWalker(new MatchSelector(matchTerm));
			pushTerm(matchTerm.getDataTerm());
			return;
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final FunctionSymbol fs = appTerm.getFunction();
		if (fs.isIntern() || fs.isModelValue()) {
			setResult(interpret(fs, newArgs));
		} else if (fs.getDefinition() != null) {
			pushTerm(appTerm.getTheory().let(fs.getDefinitionVars(), newArgs, fs.getDefinition()));
		} else {
			setResult(lookupFunction(fs, newArgs));
		}
	}

	@Override
	public void preConvertLet(final LetTerm oldLet, final Term[] newValues) {
		mLetMap.beginScope();
		final TermVariable[] vars = oldLet.getVariables();
		for (int i = 0; i < vars.length; i++) {
			mLetMap.put(vars[i], newValues[i]);
		}
		super.preConvertLet(oldLet, newValues);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		setResult(newBody);
		mLetMap.endScope();
	}

	public ModelEvaluator(final Model model) {
		mModel = model;
	}

	public Term evaluate(final Term input) {
		return transform(input);
	}

	private Term lookupFunction(final FunctionSymbol fs, final Term[] args) {
		final FunctionValue val = mModel.getFunctionValue(fs);
		if (val == null) {
			final Sort sort = fs.getReturnSort();
			return mModel.getSomeValue(sort);
		}
		final Term value = val.values().get(new FunctionValue.Index(args));
		return value == null ? val.getDefault() : value;
	}

	private Term interpret(final FunctionSymbol fs, final Term[] args) {
		if (fs.isModelValue()) {
			final int idx = Integer.parseInt(fs.getName().substring(1));
			return mModel.getModelValue(idx, fs.getReturnSort());
		}
		final Theory theory = mModel.getTheory();
		if (fs == theory.mTrue.getFunction()) {
			return theory.mTrue;
		}
		if (fs == theory.mFalse.getFunction()) {
			return theory.mFalse;
		}
		if (fs == theory.mAnd) {
			for (final Term arg : args) {
				if (arg == theory.mFalse) {
					return arg;
				}
				assert arg == theory.mTrue;
			}
			return theory.mTrue;
		}
		if (fs == theory.mOr) {
			for (final Term arg : args) {
				assert isBooleanValue(arg);
				if (arg == theory.mTrue) {
					return arg;
				}
				assert arg == theory.mFalse;
			}
			return theory.mFalse;
		}
		if (fs == theory.mImplies) {
			for (int i = 0; i < args.length - 1; i++) {
				final Term argi = args[i];
				assert isBooleanValue(argi);
				if (argi == theory.mFalse) {
					return theory.mTrue;
				}
				assert argi == theory.mTrue;
			}
			return args[args.length - 1];
		}
		if (fs == theory.mNot) {
			assert isBooleanValue(args[0]);
			return theory.not(args[0]);
		}
		if (fs == theory.mXor) {
			boolean result = false;
			for (final Term arg : args) {
				assert isBooleanValue(arg);
				result ^= arg == theory.mTrue;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		final String name = fs.getName();
		if (name.equals("=")) {
			for (int i = 1; i < args.length; ++i) {
				if (args[i] != args[0]) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals("distinct")) {
			final HashSet<Term> vals = new HashSet<>();
			for (final Term arg : args) {
				if (!vals.add(arg)) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals("ite")) {
			// ite is handled else-where
			throw new InternalError("ITE not handled in convert?");
		}
		if (name.equals("+")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.add(rationalValue(args[i]));
			}
			return val.toTerm(fs.getReturnSort());
		}
		if (name.equals("-")) {
			Rational val = rationalValue(args[0]);
			if (args.length == 1) {
				val = val.negate();
			} else {
				for (int i = 1; i < args.length; ++i) {
					val = val.sub(rationalValue(args[i]));
				}
			}
			return val.toTerm(fs.getReturnSort());
		}
		if (name.equals("*")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.mul(rationalValue(args[i]));
			}
			return val.toTerm(fs.getReturnSort());
		}
		if (name.equals("/")) {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				final Rational divisor = rationalValue(args[i]);
				if (divisor.equals(Rational.ZERO)) {
					val = rationalValue(lookupFunction(fs, new Term[] { val.toTerm(args[0].getSort()), args[i] }));
				} else {
					val = val.div(divisor);
				}
			}
			return val.toTerm(fs.getReturnSort());
		}
		if (name.equals("<=")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) > 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals("<")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) >= 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals(">=")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) < 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals(">")) {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) <= 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}
		if (name.equals("div")) {
			// From the standard...
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				final Rational n = rationalValue(args[i]);
				if (n.equals(Rational.ZERO)) {
					val = rationalValue(lookupFunction(fs, new Term[] { val.toTerm(args[0].getSort()), args[i] }));
				} else {
					final Rational div = val.div(n);
					val = n.isNegative() ? div.ceil() : div.floor();
				}
			}
			return val.toTerm(fs.getReturnSort());
		}
		if (name.equals("mod")) {
			assert(args.length == 2);
			final Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO)) {
				return lookupFunction(fs, args);
			}
			final Rational m = rationalValue(args[0]);
			Rational div = m.div(n);
			div = n.isNegative() ? div.ceil() : div.floor();
			return m.sub(div.mul(n)).toTerm(fs.getReturnSort());
		}
		if (name.equals("abs")) {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return arg.abs().toTerm(fs.getReturnSort());
		}
		if (name.equals("divisible")) {
			assert(args.length == 1);
			final Rational arg = rationalValue(args[0]);
			final String[] indices = fs.getIndices();
			assert(indices.length == 1);
			BigInteger divisor;
			try {
				divisor = new BigInteger(indices[0]);
			} catch (final NumberFormatException e) {
				throw new SMTLIBException("index of divisible must be numeral", e);
			}
			final Rational rdivisor = Rational.valueOf(divisor, BigInteger.ONE);
			return arg.div(rdivisor).isIntegral() ? theory.mTrue : theory.mFalse;
		}
		if (name.equals("to_int")) {
			assert (args.length == 1);
			final Rational arg = rationalValue(args[0]);
			return arg.floor().toTerm(fs.getReturnSort());
		}
		if (name.equals("to_real")) {
			assert (args.length == 1);
			final Rational arg = rationalValue(args[0]);
			return arg.toTerm(fs.getReturnSort());
		}
		if (name.equals("is_int")) {
			assert (args.length == 1);
			final Rational arg = rationalValue(args[0]);
			return arg.isIntegral() ? theory.mTrue : theory.mFalse;
		}
		if (name.equals("store")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.normalizeStoreTerm(theory.term(fs, args));
		}
		if (name.equals("const")) {
			return theory.term(fs, args[0]);
		}
		if (name.equals("select")) {
			// we assume that the array parameter is a term of the form store(store(...(const v),...))
			ApplicationTerm array = (ApplicationTerm) args[0];
			final Term index = args[1];
			FunctionSymbol head = array.getFunction();
			// go through the store chain and check if we write to the index
			while (head.getName() == "store") {
				if (array.getParameters()[1] == index) {
					return array.getParameters()[2];
				}
				array = (ApplicationTerm) array.getParameters()[0];
				head = array.getFunction();
			}
			assert head.getName() == "const";
			return array.getParameters()[0];
		}
		if (name.equals("@diff")) {
			final ArraySortInterpretation array = (ArraySortInterpretation)
					mModel.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.computeDiff(args[0], args[1], fs.getReturnSort());
		}
		throw new AssertionError("Unknown internal function " + name);
	}

	private Rational rationalValue(final Term term) {
		return (Rational) ((ConstantTerm) term).getValue();
	}
}

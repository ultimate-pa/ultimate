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
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
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
	 * The scoped let map. Each scope corresponds to a partially executed let or a
	 * quantifier on the todo stack. It gives the mapping for each term variable
	 * defined in that scope to the corresponding term.
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
			if (term.getSort().isNumericSort()) {
				final Term result = SMTAffineTerm.convertConstant((ConstantTerm) term).toTerm(term.getSort());
				setResult(result);
				return;
			} else if (term.getSort().isBitVecSort()) {
				final Object value = ((ConstantTerm) term).getValue();
				if (value instanceof String) {
					BigInteger result;
					final String bitString = (String) value;
					if (bitString.startsWith("#b")) {
						result = new BigInteger(bitString.substring(2), 2);
					} else {
						assert bitString.startsWith("#x");
						result = new BigInteger(bitString.substring(2), 16);
					}
					setResult(createBitvectorTerm(result, term.getSort()));
				} else {
					assert value instanceof BigInteger;
					setResult(term);
				}
				return;
			}
			throw new InternalError("Don't know how to evaluate this: " + term);
		}
		if (term instanceof TermVariable) {
			if (mLetMap.containsKey(term)) {
				setResult(mLetMap.get(term));
				return;
			}
			throw new SMTLIBException("Terms to evaluate must be closed");
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().isIntern() && appTerm.getFunction().getName() == SMTLIBConstants.ITE) {
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
		switch (fs.getName()) {
		case SMTLIBConstants.TRUE:
			return theory.mTrue;

		case SMTLIBConstants.FALSE:
			return theory.mFalse;

		case SMTLIBConstants.AND:
			for (final Term arg : args) {
				if (arg == theory.mFalse) {
					return arg;
				}
				assert arg == theory.mTrue;
			}
			return theory.mTrue;

		case SMTLIBConstants.OR:
			for (final Term arg : args) {
				assert isBooleanValue(arg);
				if (arg == theory.mTrue) {
					return arg;
				}
				assert arg == theory.mFalse;
			}
			return theory.mFalse;

		case SMTLIBConstants.IMPLIES:
			for (int i = 0; i < args.length - 1; i++) {
				final Term argi = args[i];
				assert isBooleanValue(argi);
				if (argi == theory.mFalse) {
					return theory.mTrue;
				}
				assert argi == theory.mTrue;
			}
			return args[args.length - 1];

		case SMTLIBConstants.NOT:
			assert isBooleanValue(args[0]);
			return args[0] == theory.mTrue ? theory.mFalse : theory.mTrue;

		case SMTLIBConstants.XOR: {
			boolean result = false;
			for (final Term arg : args) {
				assert isBooleanValue(arg);
				result ^= arg == theory.mTrue;
			}
			return result ? theory.mTrue : theory.mFalse;
		}

		case SMTLIBConstants.EQUALS:
			for (int i = 1; i < args.length; ++i) {
				if (args[i] != args[0]) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;

		case SMTLIBConstants.DISTINCT: {
			final HashSet<Term> vals = new HashSet<>();
			for (final Term arg : args) {
				if (!vals.add(arg)) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}

		case SMTLIBConstants.ITE:
			return args[0] == theory.mTrue ? args[1] : args[2];

		case SMTLIBConstants.PLUS: {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.add(rationalValue(args[i]));
			}
			return val.toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.MINUS: {
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

		case SMTLIBConstants.MUL: {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.mul(rationalValue(args[i]));
			}
			return val.toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.DIVIDE: {
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

		case SMTLIBConstants.LEQ: {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) > 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}

		case SMTLIBConstants.LT: {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) >= 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}

		case SMTLIBConstants.GEQ: {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) < 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}

		case SMTLIBConstants.GT: {
			for (int i = 1; i < args.length; ++i) {
				final Rational arg1 = rationalValue(args[i - 1]);
				final Rational arg2 = rationalValue(args[i]);
				if (arg1.compareTo(arg2) <= 0) {
					return theory.mFalse;
				}
			}
			return theory.mTrue;
		}

		case SMTLIBConstants.DIV: {
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

		case SMTLIBConstants.MOD: {
			assert args.length == 2;
			final Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO)) {
				return lookupFunction(fs, args);
			}
			final Rational m = rationalValue(args[0]);
			Rational div = m.div(n);
			div = n.isNegative() ? div.ceil() : div.floor();
			return m.sub(div.mul(n)).toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.ABS: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return arg.abs().toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.DIVISIBLE: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			final String[] indices = fs.getIndices();
			assert indices.length == 1;
			BigInteger divisor;
			try {
				divisor = new BigInteger(indices[0]);
			} catch (final NumberFormatException e) {
				throw new SMTLIBException("index of divisible must be numeral", e);
			}
			final Rational rdivisor = Rational.valueOf(divisor, BigInteger.ONE);
			return arg.div(rdivisor).isIntegral() ? theory.mTrue : theory.mFalse;
		}

		case SMTLIBConstants.TO_INT: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return arg.floor().toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.TO_REAL: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return arg.toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.IS_INT: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return arg.isIntegral() ? theory.mTrue : theory.mFalse;
		}

		case SMTLIBConstants.STORE: {
			final ArraySortInterpretation array = (ArraySortInterpretation) mModel
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.normalizeStoreTerm(theory.term(fs, args));
		}

		case SMTLIBConstants.CONST:
			return theory.term(fs, args[0]);

		case SMTLIBConstants.SELECT: {
			// we assume that the array parameter is a term of the form
			// store(store(...(const v),...))
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
			assert head.getName() == SMTLIBConstants.CONST;
			return array.getParameters()[0];
		}

		case SMTInterpolConstants.DIFF: {
			final ArraySortInterpretation array = (ArraySortInterpretation) mModel
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.computeDiff(args[0], args[1], fs.getReturnSort());
		}

		case SMTInterpolConstants.NAT2BV: {
			assert args.length == 1;
			final Rational n = rationalValue(args[0]);
			assert n.isIntegral();
			final BigInteger mask = getBVModulo(fs.getReturnSort()).subtract(BigInteger.ONE);
			return createBitvectorTerm(n.numerator().and(mask), fs.getReturnSort());
		}

		case SMTInterpolConstants.BV2NAT: {
			assert args.length == 1;
			final BigInteger value = bitvectorValue(args[0]);
			return Rational.valueOf(value, BigInteger.ONE).toTerm(fs.getReturnSort());
		}

		case SMTLIBConstants.BVADD: {
			final BigInteger mask = getBVModulo(fs.getReturnSort()).subtract(BigInteger.ONE);
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				value = value.add(bitvectorValue(args[i]));
			}
			value = value.and(mask);
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVSUB: {
			final BigInteger mask = getBVModulo(fs.getReturnSort()).subtract(BigInteger.ONE);
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				value = value.add(bitvectorValue(args[i]).negate());
			}
			value = value.and(mask);
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVMUL: {
			final BigInteger mask = getBVModulo(fs.getReturnSort()).subtract(BigInteger.ONE);
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				value = value.multiply(bitvectorValue(args[i]));
				value = value.and(mask);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVUDIV: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			BigInteger value = bitvectorValue(args[0]);
			final BigInteger arg = bitvectorValue(args[1]);
			value = arg.signum() == 0 ? modulo.subtract(BigInteger.ONE) : value.divide(arg);
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVUREM: {
			assert args.length == 2;
			BigInteger value = bitvectorValue(args[0]);
			final BigInteger arg = bitvectorValue(args[1]);
			value = arg.signum() == 0 ? value : value.mod(arg);
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVSDIV: {
			assert args.length == 2;
			final int signBit = getBitVecSize(fs.getReturnSort()) - 1;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			BigInteger value = bitvectorValue(args[0]);
			boolean isNegative = value.testBit(signBit);
			if (isNegative) {
				value = modulo.subtract(value);
			}
			BigInteger arg = bitvectorValue(args[1]);
			if (arg.testBit(signBit)) {
				arg = modulo.subtract(arg);
				isNegative = !isNegative;
			}
			value = arg.signum() == 0 ? modulo.subtract(BigInteger.ONE) : value.divide(arg);
			if (isNegative && value.signum() != 0) {
				value = modulo.subtract(value);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVSREM: {
			assert args.length == 2;
			final int signBit = getBitVecSize(fs.getReturnSort()) - 1;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			BigInteger value = bitvectorValue(args[0]);
			final boolean isNegative = value.testBit(signBit);
			if (isNegative) {
				value = modulo.subtract(value);
			}
			BigInteger arg = bitvectorValue(args[1]);
			if (arg.testBit(signBit)) {
				arg = modulo.subtract(arg);
			}
			value = arg.signum() == 0 ? value : value.mod(arg);
			if (isNegative && value.signum() != 0) {
				value = modulo.subtract(value);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVSMOD: {
			assert args.length == 2;
			final int signBit = getBitVecSize(fs.getReturnSort()) - 1;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger origValue = bitvectorValue(args[0]);
			BigInteger value = origValue;
			if (value.testBit(signBit)) {
				value = value.subtract(modulo);
			}
			BigInteger arg = bitvectorValue(args[1]);
			final boolean isNegative = arg.testBit(signBit);
			if (isNegative) {
				arg = modulo.subtract(arg);
			}
			value = arg.signum() == 0 ? origValue : value.mod(arg);
			if (isNegative && value.signum() != 0) {
				value = value.add(modulo).subtract(arg);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVNOT: {
			assert args.length == 1;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = bitvectorValue(args[0]).xor(modulo.subtract(BigInteger.ONE));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVNEG: {
			assert args.length == 1;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			BigInteger value = bitvectorValue(args[0]);
			if (value.signum() != 0) {
				value = modulo.subtract(value);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVAND: {
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger arg = bitvectorValue(args[i]);
				value = value.and(arg);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVOR: {
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger arg = bitvectorValue(args[i]);
				value = value.or(arg);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVXOR: {
			BigInteger value = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger arg = bitvectorValue(args[i]);
				value = value.xor(arg);
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVNAND: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE).subtract(bitvectorValue(args[0]).and(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVNOR: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE).subtract(bitvectorValue(args[0]).or(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVXNOR: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE).subtract(bitvectorValue(args[0]).xor(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVCOMP: {
			assert args.length == 2;
			final BigInteger value = bitvectorValue(args[0]).equals(bitvectorValue(args[1])) ? BigInteger.ONE : BigInteger.ZERO;
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVULE: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) <= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVULT: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) < 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVUGE: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) >= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVUGT: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) > 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSLE: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) <= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSLT: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) < 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSGE: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) >= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSGT: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) > 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSHL: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value;
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				final BigInteger mask = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
				value = bitvectorValue(args[0]).shiftLeft(shiftArg.intValueExact()).and(mask);
			} else {
				value = BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVLSHR: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value;
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				value = bitvectorValue(args[0]).shiftRight(shiftArg.intValueExact());
			} else {
				value = BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVASHR: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value = bitvectorValue(args[0]);
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				final int shiftInt = shiftArg.intValueExact();
				final BigInteger signBits = value.testBit(size - 1)
						? BigInteger.ONE.shiftLeft(size - shiftInt).subtract(BigInteger.ONE).shiftLeft(shiftInt)
						: BigInteger.ZERO;
				value = value.shiftRight(shiftInt).or(signBits);
			} else {
				value = value.testBit(size - 1) ? BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE)
						: BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.CONCAT: {
			assert args.length == 2;
			final int size2 = getBitVecSize(args[1].getSort());
			final BigInteger value = bitvectorValue(args[0]).shiftLeft(size2).or(bitvectorValue(args[1]));
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.REPEAT: {
			assert args.length == 1;
			final int sizeIn = getBitVecSize(args[0].getSort());
			final int count = Integer.parseInt(fs.getIndices()[0]);
			final BigInteger multiplier = BigInteger.ONE.shiftLeft(sizeIn*count).subtract(BigInteger.ONE)
					.divide(BigInteger.ONE.shiftLeft(sizeIn).subtract(BigInteger.ONE));
			final BigInteger value = bitvectorValue(args[0]).multiply(multiplier);
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.EXTRACT: {
			assert args.length == 1;
			final int high = Integer.parseInt(fs.getIndices()[0]);
			final int low = Integer.parseInt(fs.getIndices()[1]);
			final BigInteger value = bitvectorValue(args[0]).shiftRight(low)
					.and(BigInteger.ONE.shiftLeft(high - low + 1).subtract(BigInteger.ONE));
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.ZERO_EXTEND: {
			return createBitvectorTerm(bitvectorValue(args[0]), fs.getReturnSort());
		}
		case SMTLIBConstants.SIGN_EXTEND: {
			assert args.length == 1;
			final int inputLen = getBitVecSize(args[0].getSort());
			BigInteger value = bitvectorValue(args[0]);
			if (value.testBit(inputLen - 1)) {
				final int outputLen = getBitVecSize(fs.getReturnSort());
				value = value.add(BigInteger.ONE.shiftLeft(outputLen).subtract(BigInteger.ONE.shiftLeft(inputLen)));
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.ROTATE_LEFT:
		case SMTLIBConstants.ROTATE_RIGHT: {
			assert args.length == 1;
			final int size = getBitVecSize(fs.getReturnSort());
			int rotateValue = Integer.parseInt(fs.getIndices()[0]);
			if (fs.getName().equals(SMTLIBConstants.ROTATE_RIGHT)) {
				rotateValue = size - rotateValue;
			}
			final BigInteger mask = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
			BigInteger value = bitvectorValue(args[0]);
			value = value.shiftLeft(rotateValue).or(value.shiftRight(size - rotateValue)).and(mask);
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case "@EQ": {
			return lookupFunction(fs, args);
		}
		default:
			if (fs.isConstructor()) {
				return theory.term(fs, args);
			} else if (fs.isSelector()) {
				final ApplicationTerm arg = (ApplicationTerm) args[0];
				final DataType dataType = (DataType) arg.getSort().getSortSymbol();
				assert arg.getFunction().isConstructor();
				final Constructor constr = dataType.getConstructor(arg.getFunction().getName());
				final String[] selectors = constr.getSelectors();
				for (int i = 0; i < selectors.length; i++) {
					if (selectors[i].equals(fs.getName())) {
						return arg.getParameters()[i];
					}
				}
				// undefined case for selector on wrong constructor. use model.
				return lookupFunction(fs, args);
			} else if (fs.getName().equals(SMTLIBConstants.IS)) {
				final ApplicationTerm arg = (ApplicationTerm) args[0];
				assert arg.getFunction().isConstructor();
				return arg.getFunction().getName().equals(fs.getIndices()[0]) ? theory.mTrue : theory.mFalse;
			}
			throw new AssertionError("Unknown internal function " + fs.getName());
		}
	}

	private Rational rationalValue(final Term term) {
		return (Rational) ((ConstantTerm) term).getValue();
	}

	private BigInteger bitvectorValue(Term t) {
		return (BigInteger) ((ConstantTerm) t).getValue();
	}

	private Term createBitvectorTerm(BigInteger value, Sort sort) {
		return BitVectorInterpretation.BV(value, sort);
	}

	private int getBitVecSize(Sort sort) {
		assert sort.isBitVecSort();
		return Integer.parseInt(sort.getIndices()[0]);
	}

	private BigInteger getBVModulo(Sort sort) {
		return BigInteger.ONE.shiftLeft(getBitVecSize(sort));
	}
}

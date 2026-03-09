package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.TermEvaluator.UnsupportedTermError;

public class ValueToTermStorage {
	private static ValueToTermStorage instance = null;

	public static ValueToTermStorage getInstance() {
		if (instance == null) {
			instance = new ValueToTermStorage();
		}
		return instance;
	}

	public static void emptyCache() {
		if (instance == null) {
			instance = new ValueToTermStorage();
			return;
		}
		instance.mTranslatedInts.clear();
		instance.mTranslatedSelects.clear();
		instance.mTranslatedConstants.clear();
		instance.mTranslatedBitVecs.clear();
		instance.mBVSorts.clear();
	}

	private ValueToTermStorage() {
	}

	private final HashMap<BigInteger, Term> mTranslatedInts = new HashMap<>();
	private final HashMap<Term, HashMap<List<Value>, Term>> mTranslatedSelects = new HashMap<>();
	private final HashMap<ConstantTerm, Value> mTranslatedConstants = new HashMap<>();
	private final HashMap<BitVecValue, Term> mTranslatedBitVecs = new HashMap<>();
	private final HashMap<Integer, Sort> mBVSorts = new HashMap<>();

	public Term getInteger(final Script script, final IntValue intValue) {
		final BigInteger value = intValue.getValue();
		Term valueTerm = mTranslatedInts.get(value);
		if (valueTerm == null) {
			valueTerm = SmtUtils.constructIntValue(script, value);
			mTranslatedInts.put(value, valueTerm);
		}
		return valueTerm;
	}

	public Term getSelect(final Script script, final Term var, final List<Value> keyList) {
		HashMap<List<Value>, Term> keyMap = mTranslatedSelects.get(var);
		if (keyMap == null) {
			keyMap = new HashMap<>();
			mTranslatedSelects.put(var, keyMap);
		}

		Term selectTerm = keyMap.get(keyList);
		if (selectTerm == null) {
			selectTerm = var;
			for (final Value key : keyList) {
				selectTerm = SmtUtils.select(script, selectTerm, key.toTerm(script, var).get(var));
			}

			keyMap.put(keyList, selectTerm);
		}

		return selectTerm;
	}

	public Term getBitVec(final Script script, final BitVecValue bvValue) {
		Term bitVecTerm = mTranslatedBitVecs.get(bvValue);

		if (bitVecTerm == null) {
			final int length = bvValue.getLength();
			Sort sort = mBVSorts.get(length);

			if (sort == null) {
				sort = script.getTheory().getSort(SMTLIBConstants.BITVEC, new String[] { String.valueOf(length) });
				mBVSorts.put(length, sort);
			}

			bitVecTerm = script.getTheory().constant(Rational.valueOf(bvValue.getValue(), BigInteger.ONE), sort);
		}

		return bitVecTerm;
	}

	public Value getConstant(final ConstantTerm termConst) {
		Value result = mTranslatedConstants.get(termConst);
		if (result != null) {
			return result;
		}

		final Object valueUnparsed = termConst.getValue();
		final Sort sort = termConst.getSort();

		switch (sort.getName()) {
		case SMTLIBConstants.INT:
			BigInteger value;
			if (valueUnparsed instanceof final Rational rat) {
				value = rat.numerator();
			} else if (valueUnparsed instanceof final BigInteger bi) {
				value = bi;
			} else {
				throw new AssertionError();
			}
			result = new IntValue(value);
			break;
		case SMTLIBConstants.BOOL:
			result = new BoolValue((boolean) valueUnparsed);
			break;
		case SMTLIBConstants.BITVEC:
			final int length = Integer.parseInt(sort.getIndices()[0]);
			result = new BitVecValue((BigInteger) valueUnparsed, length);
			break;
		default:
			throw new UnsupportedTermError();
		}

		mTranslatedConstants.put(termConst, result);
		return result;
	}
}

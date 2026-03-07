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
	private final HashMap<BigInteger, Term> mTranslatedInts = new HashMap<>();
	private final HashMap<Term, HashMap<List<Value>, Term>> mTranslatedSelects = new HashMap<>();
	private final HashMap<ConstantTerm, Value> constantStorage = new HashMap<>();

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
		} else {

			return selectTerm;
		}

		return selectTerm;
	}

	public Value getConstant(final ConstantTerm termConst) {
		Value result = constantStorage.get(termConst);
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

		constantStorage.put(termConst, result);
		return result;
	}
}

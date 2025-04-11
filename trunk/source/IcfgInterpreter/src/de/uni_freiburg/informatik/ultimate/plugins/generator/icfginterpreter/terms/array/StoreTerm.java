package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class StoreTerm extends ArrayTerm {
	private final ArrayTerm mArray;
	private final ExecutionTerm mIndex;
	private final ExecutionTerm mValue;

	public StoreTerm(final ArrayTerm array, final ExecutionTerm index, final ExecutionTerm value) {
		super(array.keyType, array.valueType, SMTLIBConstants.STORE);
		assert array.keyType == index.returnType;
		assert array.valueType == value.returnType;
		mArray = array;
		mIndex = index;
		mValue = value;
	}

	@Override
	public StoreTerm simplify() {
		final ExecutionTerm newIndex = mIndex.simplify();
		final ExecutionTerm newValue = mValue.simplify();
		// Store terms are also array terms, meaning we should pass on the simplify here.
		final ArrayTerm newArray = mArray.simplify();
		return new StoreTerm(newArray, newIndex, newValue);
	}

	@Override
	public ArrayList<ExecutionTerm> getSubTerms() {
		return Util.toList(mArray, mIndex, mValue);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(store ");
		mArray.toString(out, 0).append(" ");
		mIndex.toString(out, 0).append(" ");
		return mValue.toString(out, 0).append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof StoreTerm)) {
			return false;
		}
		final StoreTerm castB = (StoreTerm) b;

		return mArray.equals(castB.mArray) && mIndex.equals(castB.mIndex) && mValue.equals(castB.mValue);
	}

	@Override
	public int hashCode() {
		int result = 107 * 31 + mArray.hashCode();
		result = result * 31 + mIndex.hashCode();
		return result * 31 + mValue.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mArray.getVariables();
		out.addAll(mIndex.getVariables());
		out.addAll(mValue.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mArray.toSMTTerm(theory), mIndex.toSMTTerm(theory),
				mValue.toSMTTerm(theory));
	}

	@Override
	public SMTArray evaluate(final ProgramState currentState, final ProgramState nextState) {
		if (mArray instanceof StoreTerm) {
			// combine stacked store calls.
			final ArrayList<Object> values = new ArrayList<>();
			final ArrayList<Object> keys = new ArrayList<>();

			ArrayTerm currentArray = this;

			while (currentArray instanceof final StoreTerm store) {
				keys.add(store.mIndex.evaluate(currentState, nextState));
				values.add(store.mValue.evaluate(currentState, nextState));
				currentArray = store.mArray;
			}

			// get the SMTArray from the first non-store child term
			final SMTArray array = currentArray.evaluate(currentState, nextState);
			// The child store call should be executed before the parents, so we will reverse the order of key / value
			// pairs.
			return array.multiStore(keys.reversed(), values.reversed());
		}

		final SMTArray array = mArray.evaluate(currentState, nextState);
		return array.store(mIndex.evaluate(currentState, nextState), mValue.evaluate(currentState, nextState));
	}

	@Override
	public String toCode() {
		if (mArray instanceof StoreTerm) {
			// combine stacked store calls.
			final ArrayList<String> values = new ArrayList<>();
			final ArrayList<String> keys = new ArrayList<>();

			ArrayTerm currentArray = this;

			while (currentArray instanceof final StoreTerm store) {
				keys.add(store.mIndex.toCode());
				values.add(store.mValue.toCode());
				currentArray = store.mArray;
			}

			// The child store call should be executed before the parents, so we will reverse the order of key / value
			// pairs.
			final String keysCode = String.join(", ", keys.reversed());
			final String valuesCode = String.join(", ", values.reversed());

			return currentArray.toCode() + ".multiStore(Util.toList(" + keysCode + "), Util.toList(" + valuesCode
					+ "))";
		}
		return mArray.toCode() + ".store(" + mIndex.toCode() + ", " + mValue.toCode() + ")";
	}

	@Override
	protected StoreTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		final ArrayTerm array = mArray.replaceTerm(old, replacement);
		final ExecutionTerm index = mIndex.replaceTerm(old, replacement);
		final ExecutionTerm value = mValue.replaceTerm(old, replacement);
		return new StoreTerm(array, index, value);
	}
}

package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.BooleanDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

/**
 * This class should be deterministic for its seed. This ensures that the same "non-deterministic" values appear when
 * the same key is given, allowing users to isolate a specific case and recreate it later.<br>
 * There should be a constructor for this class that has no parameters. An instance created this way will be used to
 * make the instances that will actually be used via {@link #newInstance(long)}
 */
public interface NonDeterministicChoice {
	NonDeterministicChoice newInstance(long seed);

	<T> T chooseEdge(ArrayList<T> edges);

	/**
	 * Select a non-deterministic value in the range defined by the domain for the given variable.
	 *
	 * @param possibleValues
	 * @return
	 */
	default Object havoc(final Variable variable, final Domain<?> possibleValues) {
		switch (possibleValues.getType()) {
		case Array:
			final ArrayDomain<?, ?> arrayDomain = (ArrayDomain<?, ?>) possibleValues;
			return newArray((VariableArrayTerm) variable, arrayDomain);
		case BitVector:
			return havocBitVector(variable, possibleValues);
		case Boolean:
			final BooleanDomain booleanDomain = (BooleanDomain) possibleValues;
			return havocBool((VariableBooleanTerm) variable, booleanDomain);
		case Int:
			final IntegerDomain integerDomain = (IntegerDomain) possibleValues;
			return havocInt((VariableIntegerTerm) variable, integerDomain);
		}
		return null;
	}

	int havocInt(VariableIntegerTerm variable, IntegerDomain values);

	boolean havocBool(VariableBooleanTerm variable, BooleanDomain values);

	BitVector havocBitVector(Variable variable, Domain<?> values);

	SMTArray newArray(VariableArrayTerm variable, ArrayDomain<?, ?> values);

	/**
	 * Called when an array entry is read where no value has been {@link SMTArray#store(Object, Object)}d.<br>
	 * Return a value as indicated by {@link SMTArray#valueType}.<br>
	 * One instance of this class should always return the same value for the same (array, index) pair.
	 *
	 * @param type
	 * @return
	 */
	Object havocArrayEntry(SMTArray array, Object index);

	boolean areArraysEqual(SMTArray a, SMTArray b);
}
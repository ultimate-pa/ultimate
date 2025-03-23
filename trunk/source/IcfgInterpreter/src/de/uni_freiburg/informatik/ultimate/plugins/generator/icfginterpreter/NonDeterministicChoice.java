package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector.VariableBitVectorTerm;
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
	default Object havoc(final Variable variable, final Restriction<?> possibleValues) {
		switch (variable.getTerm().returnType) {
		case Array:
			return newArray((VariableArrayTerm) variable, (ArrayRestriction) possibleValues);
		case BitVector:
			return havocBitVector((VariableBitVectorTerm) variable, (BitVectorRestriction) possibleValues);
		case Boolean:
			return havocBool((VariableBooleanTerm) variable, (BooleanRestriction) possibleValues);
		case Int:
			return havocInt((VariableIntegerTerm) variable, (IntegerRestriction) possibleValues);
		}
		return null;
	}

	int havocInt(VariableIntegerTerm variable, IntegerRestriction values);

	boolean havocBool(VariableBooleanTerm variable, BooleanRestriction values);

	BitVector havocBitVector(VariableBitVectorTerm variable, BitVectorRestriction values);

	SMTArray newArray(VariableArrayTerm variable, ArrayRestriction values);

	/**
	 * Called when an array entry is read where no value has been stored with
	 * {@link SMTArray#store(Object, Object)}.<br>
	 * Return a value as indicated by {@link SMTArray#valueType}.<br>
	 * One instance (same seed) of this class should always return the same value for the same (array, index) pair.
	 *
	 * @param type
	 * @return
	 */
	Object havocArrayEntry(SMTArray array, Object index);

	boolean areArraysEqual(SMTArray a, SMTArray b);

	UltimatePreferenceItemGroup getImplementationSettings();
}
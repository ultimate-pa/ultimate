package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BitVecValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;

/**
 * This class should be deterministic for its seed. This ensures that the same "non-deterministic" values appear when
 * the same key is given, allowing users to isolate a specific case and recreate it later.<br>
 * There should be a constructor for this class that has no parameters. An instance created this way will be used to
 * make the instances that will actually be used via {@link #newInstance(long)}
 */
public interface NonDeterministicChoice {
	NonDeterministicChoice newInstance(long seed);

	<T> T chooseEdge(List<T> edges);

	/**
	 * Select a non-deterministic value in the range defined by the domain for the given variable.
	 *
	 * @param possibleValues
	 * @return
	 */
	default Value havoc(final Value previousValue, final Restriction<?> possibleValues) {
		switch (previousValue) {
		case final ArrayValue av:
			return newArray(av.getSort(), av.getUniqueIdentifier(), (ArrayRestriction) possibleValues);
		case final BitVecValue bv:
			return havocBitVector(bv.getLength(), (BitVectorRestriction) possibleValues);
		case final BoolValue bv:
			return havocBool((BooleanRestriction) possibleValues);
		case final IntValue iv:
			return havocInt((IntegerRestriction) possibleValues);
		default:
			return null;
		}
	}

	IntValue havocInt(IntegerRestriction values);

	BoolValue havocBool(BooleanRestriction values);

	BitVecValue havocBitVector(int length, BitVectorRestriction values);

	/**
	 * Called when an array entry is read where no value has been stored with
	 * {@link SMTArray#store(Object, Object)}.<br>
	 * Return a value as indicated by {@link SMTArray#valueType}.<br>
	 * One instance (same seed) of this class should always return the same value for the same (array, index) pair.
	 *
	 * @param type
	 * @return
	 */
	Value havocArrayEntry(ArrayValue smtArray, Value index);

	ArrayValue newArray(Sort sort, String uniqueIdentifier, ArrayRestriction values);

	UltimatePreferenceItemGroup getImplementationSettings();

	NonDeterministicChoice clone();
}

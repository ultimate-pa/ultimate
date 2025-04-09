package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;

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
	default Object havoc(final IProgramVar variable, final Restriction<?> possibleValues) {
		switch (variable.getSort().getName()) {
		case SMTLIBConstants.ARRAY:
			return newArray(variable, (ArrayRestriction) possibleValues);
		case SMTLIBConstants.BITVEC:
			return havocBitVector(variable, (BitVectorRestriction) possibleValues);
		case SMTLIBConstants.BOOL:
			return havocBool(variable, (BooleanRestriction) possibleValues);
		case SMTLIBConstants.INT:
			return havocInt(variable, (IntegerRestriction) possibleValues);
		}
		return null;
	}

	long havocInt(IProgramVar variable, IntegerRestriction values);

	boolean havocBool(IProgramVar variable, BooleanRestriction values);

	BitVector havocBitVector(IProgramVar variable, BitVectorRestriction values);

	/**
	 * Called when an array entry is read where no value has been stored with
	 * {@link SMTArray#store(Object, Object)}.<br>
	 * Return a value as indicated by {@link SMTArray#valueType}.<br>
	 * One instance (same seed) of this class should always return the same value for the same (array, index) pair.
	 *
	 * @param type
	 * @return
	 */
	Object havocArrayEntry(SMTArray smtArray, Object index);

	SMTArray newArray(IProgramVar programVar, ArrayRestriction values);

	boolean areArraysEqual(SMTArray a, SMTArray b);

	UltimatePreferenceItemGroup getImplementationSettings();

	NonDeterministicChoice clone();
}
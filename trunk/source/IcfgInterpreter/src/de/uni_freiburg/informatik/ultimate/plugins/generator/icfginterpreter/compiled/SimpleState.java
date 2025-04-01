package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled;

import java.util.HashMap;
import java.util.HashSet;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;

public class SimpleState {
	private final HashMap<IProgramVar, SMTArray> mArrayVars;
	private final HashMap<IProgramVar, Boolean> mBoolVars;
	private final HashMap<IProgramVar, BitVector> mBVVars;
	private final HashMap<IProgramVar, Integer> mIntVars;
	private final NonDeterministicChoice mNDC;

	public static Function<NonDeterministicChoice, SimpleState> getStateInitializer(
			final HashSet<IProgramVar> arrayEntries, final HashSet<IProgramVar> intEntries,
			final HashSet<IProgramVar> boolEntries, final HashSet<IProgramVar> bvEntries) {

		return (ndc) -> {
			final HashMap<IProgramVar, SMTArray> arrayVars = new HashMap<>();
			final HashMap<IProgramVar, Boolean> boolVars = new HashMap<>();
			final HashMap<IProgramVar, BitVector> bvVars = new HashMap<>();
			final HashMap<IProgramVar, Integer> intVars = new HashMap<>();

			for (final IProgramVar programVar : arrayEntries) {
				arrayVars.put(programVar, ndc.newArray(programVar, null));
			}
			for (final IProgramVar programVar : intEntries) {
				intVars.put(programVar, ndc.havocInt(programVar, null));
			}
			for (final IProgramVar programVar : boolEntries) {
				boolVars.put(programVar, ndc.havocBool(programVar, null));
			}
			for (final IProgramVar programVar : bvEntries) {
				bvVars.put(programVar, ndc.havocBitVector(programVar, null));
			}

			return new SimpleState(arrayVars, boolVars, bvVars, intVars, ndc);
		};
	}

	private SimpleState(final HashMap<IProgramVar, SMTArray> arrayVars, final HashMap<IProgramVar, Boolean> boolVars,
			final HashMap<IProgramVar, BitVector> bvVars, final HashMap<IProgramVar, Integer> intVars,
			final NonDeterministicChoice ndc) {
		mArrayVars = arrayVars;
		mBoolVars = boolVars;
		mBVVars = bvVars;
		mIntVars = intVars;
		mNDC = ndc;
	}

	public NonDeterministicChoice getNDC() {
		return mNDC;
	}

	@Override
	public SimpleState clone() {
		return new SimpleState(Util.copyMap(mArrayVars), Util.copyMap(mBoolVars), Util.copyMap(mBVVars),
				Util.copyMap(mIntVars), mNDC.clone());
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();
		for (final IProgramVar programVar : mArrayVars.keySet()) {
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mArrayVars.get(programVar)).append("\n");
		}
		for (final IProgramVar programVar : mIntVars.keySet()) {
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mIntVars.get(programVar)).append("\n");
		}
		for (final IProgramVar programVar : mBoolVars.keySet()) {
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mBoolVars.get(programVar)).append("\n");
		}
		for (final IProgramVar programVar : mBVVars.keySet()) {
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mBVVars.get(programVar)).append("\n");
		}
		return out.toString();
	}

	public int getInt(final IProgramVar var) {
		return mIntVars.get(var);
	}

	public Boolean getBool(final IProgramVar var) {
		return mBoolVars.get(var);
	}

	public BitVector getBitVec(final IProgramVar var) {
		return mBVVars.get(var);
	}

	public SMTArray getArray(final IProgramVar var) {
		return mArrayVars.get(var);
	}

	public void havocInt(final IProgramVar var, final IntegerRestriction restriction) {
		setInt(var, mNDC.havocInt(var, restriction));
	}

	public void havocBool(final IProgramVar var, final BooleanRestriction restriction) {
		setBool(var, mNDC.havocBool(var, restriction));
	}

	public void havocBitVec(final IProgramVar var, final BitVectorRestriction restriction) {
		setBitVec(var, mNDC.havocBitVector(var, restriction));
	}

	public void havocArray(final IProgramVar var, final ArrayRestriction restriction) {
		setArray(var, mNDC.newArray(var, restriction));
	}

	public void setInt(final IProgramVar var, final Integer value) {
		mIntVars.put(var, value);
	}

	public void setBool(final IProgramVar var, final Boolean value) {
		mBoolVars.put(var, value);
	}

	public void setBitVec(final IProgramVar var, final BitVector value) {
		mBVVars.put(var, value);
	}

	public void setArray(final IProgramVar var, final SMTArray value) {
		mArrayVars.put(var, value);
	}
}
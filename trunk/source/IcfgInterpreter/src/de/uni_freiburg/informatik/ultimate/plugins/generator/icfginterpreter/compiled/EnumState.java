package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled;

import java.util.EnumMap;
import java.util.HashSet;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class EnumState<T extends Enum<T> & IVariableName> {

	private final EnumMap<T, SMTArray> mArrayVars;
	private final EnumMap<T, Boolean> mBoolVars;
	private final EnumMap<T, BitVector> mBVVars;
	private final EnumMap<T, Integer> mIntVars;
	private final NonDeterministicChoice mNDC;

	public static <S extends Enum<S> & IVariableName> Function<NonDeterministicChoice, EnumState<S>> getStateInitializer(
			final HashSet<Variable> variables, final Class<S> varEnum) {
		final HashSet<S> arrayNames = new HashSet<>();
		final HashSet<S> intNames = new HashSet<>();
		final HashSet<S> boolNames = new HashSet<>();
		final HashSet<S> bvNames = new HashSet<>();

		for (final Variable variable : variables) {
			final IProgramVar programVar = variable.getVariableTerm().programVar;
			if (programVar == null) {
				continue;
			}
			switch (variable.getTerm().returnType) {
			case Array:
				arrayNames.add(Enum.valueOf(varEnum, programVar.getGloballyUniqueId()));
				break;
			case BitVector:
				bvNames.add(Enum.valueOf(varEnum, programVar.getGloballyUniqueId()));
				break;
			case Boolean:
				boolNames.add(Enum.valueOf(varEnum, programVar.getGloballyUniqueId()));
				break;
			case Int:
				intNames.add(Enum.valueOf(varEnum, programVar.getGloballyUniqueId()));
				break;
			}
		}

		return (ndc) -> {
			final EnumMap<S, SMTArray> arrayVars = new EnumMap<>(varEnum);
			final EnumMap<S, Boolean> boolVars = new EnumMap<>(varEnum);
			final EnumMap<S, BitVector> bvVars = new EnumMap<>(varEnum);
			final EnumMap<S, Integer> intVars = new EnumMap<>(varEnum);

			for (final S variable : arrayNames) {
				arrayVars.put(variable, ndc.newArray(variable.getProgramVar(), null));
			}
			for (final S variable : intNames) {
				intVars.put(variable, ndc.havocInt(variable.getProgramVar(), null));
			}
			for (final S variable : boolNames) {
				boolVars.put(variable, ndc.havocBool(variable.getProgramVar(), null));
			}
			for (final S variable : bvNames) {
				bvVars.put(variable, ndc.havocBitVector(variable.getProgramVar(), null));
			}

			return new EnumState<>(arrayVars, boolVars, bvVars, intVars, ndc);
		};
	}

	private EnumState(final EnumMap<T, SMTArray> arrayVars, final EnumMap<T, Boolean> boolVars,
			final EnumMap<T, BitVector> bvVars, final EnumMap<T, Integer> intVars, final NonDeterministicChoice ndc) {
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
	public EnumState<T> clone() {
		return new EnumState<>(mArrayVars.clone(), mBoolVars.clone(), mBVVars.clone(), mIntVars.clone(), mNDC.clone());
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder("{");
		for (final T variable : mArrayVars.keySet()) {
			final IProgramVar programVar = variable.getProgramVar();
			out.append("\n\t");
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mArrayVars.get(variable));
		}
		for (final T variable : mIntVars.keySet()) {
			final IProgramVar programVar = variable.getProgramVar();
			out.append("\n\t");
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mIntVars.get(variable));
		}
		for (final T variable : mBoolVars.keySet()) {
			final IProgramVar programVar = variable.getProgramVar();
			out.append("\n\t");
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mBoolVars.get(variable));
		}
		for (final T variable : mBVVars.keySet()) {
			final IProgramVar programVar = variable.getProgramVar();
			out.append("\n\t");
			out.append(programVar.getGloballyUniqueId()).append(" = ").append(mBVVars.get(variable));
		}
		return out.append("\n}").toString();
	}

	public int getInt(final T var) {
		return mIntVars.get(var);
	}

	public Boolean getBool(final T var) {
		return mBoolVars.get(var);
	}

	public BitVector getBitVec(final T var) {
		return mBVVars.get(var);
	}

	public SMTArray getArray(final T var) {
		return mArrayVars.get(var);
	}

	public void havocInt(final T var, final IntegerRestriction restriction) {
		setInt(var, mNDC.havocInt(var.getProgramVar(), restriction));
	}

	public void havocBool(final T var, final BooleanRestriction restriction) {
		setBool(var, mNDC.havocBool(var.getProgramVar(), restriction));
	}

	public void havocBitVec(final T var, final BitVectorRestriction restriction) {
		setBitVec(var, mNDC.havocBitVector(var.getProgramVar(), restriction));
	}

	public void havocArray(final T var, final ArrayRestriction restriction) {
		setArray(var, mNDC.newArray(var.getProgramVar(), restriction));
	}

	public void setInt(final T var, final Integer value) {
		mIntVars.put(var, value);
	}

	public void setBool(final T var, final Boolean value) {
		mBoolVars.put(var, value);
	}

	public void setBitVec(final T var, final BitVector value) {
		mBVVars.put(var, value);
	}

	public void setArray(final T var, final SMTArray value) {
		mArrayVars.put(var, value);
	}
}

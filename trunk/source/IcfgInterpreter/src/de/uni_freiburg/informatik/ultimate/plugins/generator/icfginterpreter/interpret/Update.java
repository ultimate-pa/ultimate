package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector.VariableBitVectorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public abstract class Update {
	protected final Variable mVariable;
	protected final IProgramVar mProgramVar;
	protected final ReturnType mReturnType;

	private static class AssignmentUpdate extends Update {
		private final ExecutionTerm mValueDefinition;

		protected AssignmentUpdate(final Variable variable, final ExecutionTerm equalTerm) {
			super(variable, variable.getVariableTerm().programVar);
			assert variable.getTerm().returnType.equals(equalTerm.returnType);
			mValueDefinition = equalTerm;
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState,
				final NonDeterministicChoice havoc) {
			return mValueDefinition.evaluate(currentState, nextState);
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := " + mValueDefinition;
		}
	}

	private static class HavocAnyUpdate extends Update {
		protected HavocAnyUpdate(final Variable variable) {
			super(variable, variable.getVariableTerm().programVar);
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState,
				final NonDeterministicChoice havoc) {
			switch (mReturnType) {
			case Array:
				return havoc.newArray((VariableArrayTerm) mVariable, null);
			case BitVector:
				return havoc.havocBitVector((VariableBitVectorTerm) mVariable, null);
			case Boolean:
				return havoc.havocBool((VariableBooleanTerm) mVariable, null);
			case Int:
				return havoc.havocInt((VariableIntegerTerm) mVariable, null);
			}
			return null;
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := havoc()";
		}
	}

	public static Update getAssignmentUpdate(final Variable variable, final ExecutionTerm equalTerm) {
		return new AssignmentUpdate(variable, equalTerm);
	}

	public static Update getHavocUpdate(final Variable variable, final HashSet<Constraint> constraints,
			final HashSet<Arc> arcs) {
		return null; // TODO make havoc updates for constraints (restrictions can be pre-calculated) and arcs
	}

	/**
	 * When a variable is undefined in the next state. Assigns any value of the given type.
	 */
	public static Update getHavocUpdateAny(final IProgramVar programVar, final ReturnType type) {

		final Sort mainSort = programVar.getSort();
		final Theory theory = programVar.getSort().getTheory();
		final TermVariable termVar = Util.makeVariable(programVar.getGloballyUniqueId() + "_Havoc", mainSort, theory);

		final VariableTerm variableTerm = new VariableTerm(false, true, false, true, programVar, termVar);

		final Variable replacementVar;
		switch (type) {
		case Array:
			final Sort[] keyValueSorts = mainSort.getArguments();
			final ReturnType keyType = Util.getType(keyValueSorts[0]);
			final ReturnType valueType = Util.getType(keyValueSorts[1]);
			replacementVar = new VariableArrayTerm(keyType, valueType, variableTerm);
			break;
		case BitVector:
			final int length = Integer.parseInt(programVar.getSort().getIndices()[0]);
			replacementVar = new VariableBitVectorTerm(length, variableTerm);
			break;
		case Boolean:
			replacementVar = new VariableBooleanTerm(variableTerm);
			break;
		case Int:
			replacementVar = new VariableIntegerTerm(variableTerm);
			break;
		default:
			return null;
		}

		return getHavocUpdateAny(replacementVar);
	}

	/**
	 * When a variable is undefined in the next state. Assigns any value of the given type.
	 */
	public static Update getHavocUpdateAny(final Variable variable) {
		return new HavocAnyUpdate(variable);
	}

	private Update(final Variable variable, final IProgramVar programVar) {
		assert !variable.getVariableTerm().isInVar && variable.getVariableTerm().isOutVar;
		mVariable = variable;
		mReturnType = mVariable.getTerm().returnType;
		mProgramVar = programVar;
	}

	protected abstract Object makeValue(final ProgramState currentState, final ProgramState nextState,
			final NonDeterministicChoice havoc);

	public void apply(final ProgramState currentState, final ProgramState nextState,
			final NonDeterministicChoice havoc) {
		putValue(nextState, makeValue(currentState, nextState, havoc));
	}

	private void putValue(final ProgramState state, final Object value) {
		switch (mReturnType) {
		case Array:
			state.setValue(mProgramVar, (SMTArray) value);
			break;
		case BitVector:
			state.setValue(mProgramVar, (BitVector) value);
			break;
		case Boolean:
			state.setValue(mProgramVar, (Boolean) value);
			break;
		case Int:
			state.setValue(mProgramVar, (Integer) value);
			break;
		}
	}
}

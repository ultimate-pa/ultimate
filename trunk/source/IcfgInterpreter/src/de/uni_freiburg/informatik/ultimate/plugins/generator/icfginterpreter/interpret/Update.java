package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
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

	/**
	 * An update that sets the variable value to a value defined by a term.
	 */
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

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				out.append("setArray(");
				break;
			case BitVector:
				out.append("setBitVec(");
				break;
			case Boolean:
				out.append("setBool(");
				break;
			case Int:
				out.append("setInt(");
				break;
			}
			out.append(DynamicLoader.getEnumClassName()).append(".").append(mProgramVar.getGloballyUniqueId());
			out.append(", ").append(mValueDefinition.toCode()).append(");");
			return out.toString();
		}
	}

	/**
	 * A havoc update that sets the variable value to any value of the same sort.
	 */
	private static class HavocAnyUpdate extends Update {
		protected HavocAnyUpdate(final Variable variable) {
			super(variable, variable.getVariableTerm().programVar);
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState,
				final NonDeterministicChoice havoc) {
			switch (mReturnType) {
			case Array:
				return havoc.newArray(mProgramVar, null);
			case BitVector:
				return havoc.havocBitVector(mProgramVar, null);
			case Boolean:
				return havoc.havocBool(mProgramVar, null);
			case Int:
				return havoc.havocInt(mProgramVar, null);
			}
			return null;
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := havoc()";
		}

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				out.append("havocArray(");
				break;
			case BitVector:
				out.append("havocBitVec(");
				break;
			case Boolean:
				out.append("havocBool(");
				break;
			case Int:
				out.append("havocInt(");
				break;
			}
			out.append(DynamicLoader.getEnumClassName()).append(".").append(mProgramVar.getGloballyUniqueId());
			out.append(", null);");
			return out.toString();
		}
	}

	/**
	 * A havoc update that sets the variable value to a value of the same sort in a range that does not depend on the
	 * state, and can therefore be defined by a pre-calculated restriction.
	 */
	private static class HavocLimitedUpdate extends Update {
		private final Function<NonDeterministicChoice, Object> func;
		private final Restriction<?> mRestriction;

		protected HavocLimitedUpdate(final Variable variable, final Restriction<?> restriction) {
			super(variable, variable.getVariableTerm().programVar);
			switch (restriction) {
			case final ArrayRestriction ar:
				func = (havoc) -> {
					return havoc.newArray(mProgramVar, ar);
				};
				break;
			case final BitVectorRestriction bvr:
				func = (havoc) -> {
					return havoc.havocBitVector(mProgramVar, bvr);
				};
				break;
			case final BooleanRestriction br:
				func = (havoc) -> {
					return havoc.havocBool(mProgramVar, br);
				};
				break;
			case final IntegerRestriction ir:
				func = (havoc) -> {
					return havoc.havocInt(mProgramVar, ir);
				};
				break;
			default:
				func = null;
				break;
			}
			mRestriction = restriction;
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState,
				final NonDeterministicChoice havoc) {
			return func.apply(havoc);
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := havoc()";
		}

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				out.append("havocArray(m");
				break;
			case BitVector:
				out.append("havocBitVec(m");
				break;
			case Boolean:
				out.append("havocBool(m");
				break;
			case Int:
				out.append("havocInt(m");
				break;
			}
			out.append(mProgramVar.getGloballyUniqueId());
			out.append(", ").append(mRestriction.toCode()).append(");");
			return out.toString();
		}
	}

	public static Update getAssignmentUpdate(final Variable variable, final ExecutionTerm equalTerm) {
		return new AssignmentUpdate(variable, equalTerm);
	}

	public static Update getHavocUpdate(final Variable variable, final HashSet<Constraint> constraints,
			final HashSet<Arc> arcs) {
		switch (variable.getTerm().returnType) {
		case Int:
			// Find the lowest constant value that the variable is bigger than, vice versa biggest constant
			int lowestConst = Integer.MIN_VALUE;
			int highestConst = Integer.MAX_VALUE;
			HashSet<Integer> inequals = new HashSet<>();
			for (final Constraint constraint : constraints) {
				int value = (int) constraint.getConstraint().evaluate(null, null);
				switch (constraint.relation) {
				case DISTINCT:
					inequals.add(value);
					break;
				case GEQ:
					// variable >= value
					// -> variable > value - 1
					value--;
					//$FALL-THROUGH$
				case GREATER:
					if (lowestConst < value) {
						// variable > value > lowestConst
						lowestConst = value;
					}
					break;
				case LEQ:
					// variable <= value
					// -> variable < value + 1
					value++;
					//$FALL-THROUGH$
				case LESS:
					if (highestConst > value) {
						// variable < value < highestConst
						highestConst = value;
					}
					break;
				default:
					break;
				}
			}

			// combine restrictions like variable > 4 and variable != 5 to variable > 5
			boolean changing = true;
			while (changing) {
				if (inequals.contains(lowestConst + 1)) {
					lowestConst++;
					inequals.remove(lowestConst);
					changing = true;
					continue;
				}
				if (inequals.contains(highestConst - 1)) {
					highestConst--;
					inequals.remove(highestConst);
					changing = true;
					continue;
				}
				changing = false;
			}

			final int finalHighest = highestConst;
			final int finalLowest = lowestConst;
			// remove any unequal values that are out of bounds anyways
			inequals = Util.filter(inequals, (value) -> {
				return finalHighest > value && value > finalLowest;
			});

			if (arcs.isEmpty()) {
				// only constraints, we can do most of the work at creation, as we are unaffected by state.
				return new HavocLimitedUpdate(variable, new IntegerRestriction(inequals, finalHighest, finalLowest));
			}

			// TODO make havoc Updates that depend on terms with variables
			break;
		default:
			break;
		}
		return null; // TODO make havoc updates for non-ints
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

	public abstract String toCode();

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

package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.function.BiFunction;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector.VariableBitVectorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AdditionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ConstIntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.SubtractionTerm;
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
			super(variable, variable.getVariableTerm().mProgramVar);
			assert variable.getTerm().returnType.equals(equalTerm.returnType);
			mValueDefinition = equalTerm;
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState) {
			return mValueDefinition.evaluate(currentState, nextState);
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mProgramVar.getGloballyUniqueId() + " := " + mValueDefinition;
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
			out.append(DynamicLoader.getVarLookup(mProgramVar));
			out.append(", ").append(mValueDefinition.toCode()).append(");");
			return out.toString();
		}
	}

	/**
	 * A havoc update that sets the variable value to any value of the same sort.
	 */
	private static class HavocAnyUpdate extends Update {
		private final Sort mSort;

		protected HavocAnyUpdate(final Variable variable) {
			super(variable, variable.getVariableTerm().mProgramVar);
			mSort = variable.getVariableTerm().mTermVar.getSort();
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState) {
			switch (mReturnType) {
			case Array:
				return nextState.getNDC().newArray(mSort, null);
			case BitVector:
				return nextState.getNDC().havocBitVector(Util.getBitVecLength(mSort), null);
			case Boolean:
				return nextState.getNDC().havocBool(null);
			case Int:
				return nextState.getNDC().havocInt(null);
			}
			return null;
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mProgramVar.getGloballyUniqueId() + " := havoc()";
		}

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				final String varName = DynamicLoader.getVarLookup(mProgramVar);
				out.append("setArray(").append(varName);
				out.append(", nextState.havocArray(").append(varName).append(".getProgramVar().getSort(), null));");
				break;
			case BitVector:
				out.append("setBitVec(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBitVec(").append(Util.getBitVecLength(mProgramVar.getSort()))
						.append(", null));");
				break;
			case Boolean:
				out.append("setBool(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBool(null));");
				break;
			case Int:
				out.append("setInt(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocInt(null));");
				break;
			}
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
			super(variable, variable.getVariableTerm().mProgramVar);
			final Sort sort = variable.getVariableTerm().mTermVar.getSort();
			switch (restriction) {
			case final ArrayRestriction ar:
				func = (havoc) -> {
					return havoc.newArray(sort, ar);
				};
				break;
			case final BitVectorRestriction bvr:
				final int length = Util.getBitVecLength(sort);
				func = (havoc) -> {
					return havoc.havocBitVector(length, bvr);
				};
				break;
			case final BooleanRestriction br:
				func = (havoc) -> {
					return havoc.havocBool(br);
				};
				break;
			case final IntegerRestriction ir:
				func = (havoc) -> {
					return havoc.havocInt(ir);
				};
				break;
			default:
				func = null;
				break;
			}
			mRestriction = restriction;
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState) {
			return func.apply(nextState.getNDC());
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mProgramVar.getGloballyUniqueId() + " := havoc(" + mRestriction + ")";
		}

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				final String varName = DynamicLoader.getVarLookup(mProgramVar);
				out.append("setArray(").append(varName);
				out.append(", nextState.havocArray(").append(varName).append(".getProgramVar().getSort(), ");
				break;
			case BitVector:
				out.append("setBitVec(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBitVec(").append(Util.getBitVecLength(mProgramVar.getSort())).append(", ");
				break;
			case Boolean:
				out.append("setBool(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBool(");
				break;
			case Int:
				out.append("setInt(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocInt(");
				break;
			}
			out.append(mRestriction.toCode()).append("));");
			return out.toString();
		}
	}

	private static class HavocDependentUpdate<T extends ExecutionTerm> extends Update {
		private final BiFunction<ProgramState, ProgramState, Object> func;

		protected HavocDependentUpdate(final Variable variable, final HashSet<T> InEqualTerms,
				final HashSet<T> lessThanTerms, final HashSet<T> greaterThanTerms) {
			super(variable, variable.getVariableTerm().mProgramVar);

			final Sort sort = variable.getVariableTerm().mTermVar.getSort();

			switch (Util.getType(sort)) {
			case ReturnType.Array:
				// TODO
				func = null;
				break;
			case ReturnType.BitVector:
				// TODO
				func = null;
				break;
			case ReturnType.Boolean:
				if (InEqualTerms.size() == 0) {
					func = (current, next) -> {
						return next.getNDC().havocBool(null);
					};
					return;
				}
				final T inEuqalTo = InEqualTerms.iterator().next();
				func = (current, next) -> {
					final HashSet<Boolean> inEqualBool = new HashSet<>();
					inEqualBool.add((Boolean) inEuqalTo.evaluate(current, next));
					return next.getNDC().havocBool(new BooleanRestriction(inEqualBool));
				};

				break;
			case ReturnType.Int:
				func = (current, next) -> {
					final HashSet<Long> inEquals = new HashSet<>();
					long lessThan = Long.MAX_VALUE;
					long greaterThan = Long.MIN_VALUE;

					for (final T lessThanTerm : lessThanTerms) {
						final Long newGreatestValue = (Long) lessThanTerm.evaluate(current, next);
						if (newGreatestValue < lessThan) {
							lessThan = newGreatestValue;
						}
					}

					for (final T greaterThanTerm : greaterThanTerms) {
						final Long newLowestValue = (Long) greaterThanTerm.evaluate(current, next);
						if (greaterThan < newLowestValue) {
							greaterThan = newLowestValue;
						}
					}

					for (final T inequalTerm : InEqualTerms) {
						final Long inEqual = (Long) inequalTerm.evaluate(current, next);
						if (inEqual > lessThan || inEqual < greaterThan) {
							continue;
						}
						inEquals.add(inEqual);
					}

					return next.getNDC().havocInt(new IntegerRestriction(inEquals, lessThan, greaterThan));
				};
				break;
			default:
				func = null;
				break;
			}
		}

		@Override
		protected Object makeValue(final ProgramState currentState, final ProgramState nextState) {

			return func.apply(currentState, nextState);
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mProgramVar.getGloballyUniqueId() + " := havoc(TODO)"; // TODO
		}

		@Override
		public String toCode() {
			final StringBuilder out = new StringBuilder("nextState.");
			switch (mReturnType) {
			case Array:
				final String varName = DynamicLoader.getVarLookup(mProgramVar);
				out.append("setArray(").append(varName);
				out.append(", nextState.havocArray(").append(varName).append(".getProgramVar().getSort(), null));");
				break;
			case BitVector:
				out.append("setBitVec(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBitVec(").append(Util.getBitVecLength(mProgramVar.getSort())).append(", ");
				break;
			case Boolean:
				out.append("setBool(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocBool(");
				break;
			case Int:
				out.append("setInt(");
				out.append(DynamicLoader.getVarLookup(mProgramVar));
				out.append(", nextState.havocInt(");
				break;
			}
			// TODO Restriction and its parts to code (like "new Restriction(\" + ...
			out.append("").append("));");
			return out.toString();
		}
	}

	public static Update getAssignmentUpdate(final Variable variable, final ExecutionTerm equalTerm) {
		return new AssignmentUpdate(variable, equalTerm);
	}

	public static Update getHavocUpdate(final Variable variable, final ArrayList<Constraint> constraints,
			final ArrayList<Arc> arcs) {
		HashSet<Long> inequals = new HashSet<>();
		switch (variable.getTerm().returnType) {
		case Int:
			// Find the lowest constant value that the variable is bigger than, vice versa biggest constant
			// As settings for min and max value are limited to int type, we can ignore any values that exceed ints.
			Long lowestConst = (long) Integer.MIN_VALUE;
			Long highestConst = (long) Integer.MAX_VALUE;
			for (final Constraint constraint : constraints) {
				Long value = (Long) constraint.getConstraint().evaluate(null, null);
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

			final Long finalHighest = highestConst;
			final Long finalLowest = lowestConst;
			// remove any unequal values that are out of bounds anyways
			inequals = Util.filter(inequals, (value) -> {
				return finalHighest > value && value > finalLowest;
			});

			if (arcs.isEmpty()) {
				// only constraints, we can do most of the work at creation, as we are unaffected by state.
				return new HavocLimitedUpdate(variable, new IntegerRestriction(inequals, finalHighest, finalLowest));
			}
			// TODO make havoc Updates that depend on terms with variables

			final HashSet<IntegerTerm> inequalTerms = new HashSet<>();
			final HashSet<IntegerTerm> lessTerms = new HashSet<>();
			final HashSet<IntegerTerm> greaterTerms = new HashSet<>();

			for (final Long inequal : inequals) {
				inequalTerms.add(new ConstIntegerTerm(inequal));
			}

			lessTerms.add(new ConstIntegerTerm(finalHighest));
			greaterTerms.add(new ConstIntegerTerm(finalLowest));

			for (final Arc arc : arcs) {
				switch (arc.relation) {
				case DISTINCT:
					inequalTerms.add((IntegerTerm) arc.getConstraint());
					break;
				case GEQ:
					// variable >= value
					// -> variable > value - 1
					greaterTerms.add(new SubtractionTerm((IntegerTerm) arc.getConstraint(), new ConstIntegerTerm(1L)));
					break;
				case GREATER:
					// variable > value
					greaterTerms.add((IntegerTerm) arc.getConstraint());
					break;
				case LEQ:
					// variable <= value
					// -> variable < value + 1

					lessTerms.add(new AdditionTerm((IntegerTerm) arc.getConstraint(), new ConstIntegerTerm(1L)));
					break;
				case LESS:
					// variable < value
					lessTerms.add((IntegerTerm) arc.getConstraint());
					break;
				default:
					break;
				}
			}

			return new HavocDependentUpdate<>(variable, inequalTerms, lessTerms, greaterTerms);
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

	protected abstract Object makeValue(final ProgramState currentState, final ProgramState nextState);

	public abstract String toCode();

	public void apply(final ProgramState currentState, final ProgramState nextState) {
		putValue(nextState, makeValue(currentState, nextState));
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
			state.setValue(mProgramVar, (Long) value);
			break;
		}
	}
}

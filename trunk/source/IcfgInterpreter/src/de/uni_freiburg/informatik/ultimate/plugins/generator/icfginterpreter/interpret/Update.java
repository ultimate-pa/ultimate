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
			return mVariable.getVariableTerm().mTermVar.getName() + " := " + mValueDefinition;
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
				return nextState.havocArray(mSort, null);
			case BitVector:
				return nextState.havocBitVec(Util.getBitVecLength(mSort), null);
			case Boolean:
				return nextState.havocBool(null);
			case Int:
				return nextState.havocInt(null);
			}
			return null;
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mTermVar.getName() + " := havoc()";
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
		private final Function<ProgramState, Object> func;
		private final Restriction<?> mRestriction;

		protected HavocLimitedUpdate(final Variable variable, final Restriction<?> restriction) {
			super(variable, variable.getVariableTerm().mProgramVar);
			final Sort sort = variable.getVariableTerm().mTermVar.getSort();
			switch (restriction) {
			case final ArrayRestriction ar:
				func = (state) -> {
					return state.havocArray(sort, ar);
				};
				break;
			case final BitVectorRestriction bvr:
				final int length = Util.getBitVecLength(sort);
				func = (state) -> {
					return state.havocBitVec(length, bvr);
				};
				break;
			case final BooleanRestriction br:
				func = (state) -> {
					return state.havocBool(br);
				};
				break;
			case final IntegerRestriction ir:
				func = (state) -> {
					return state.havocInt(ir);
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
			return func.apply(nextState);
		}

		@Override
		public String toString() {
			return mVariable.getVariableTerm().mTermVar.getName() + " := havoc(" + mRestriction + ")";
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
		private ArrayList<T> mInEqualTerms;
		private ArrayList<T> mMaximumTerms;
		private ArrayList<T> mMinimumTerms;

		protected HavocDependentUpdate(final Variable variable, final HashSet<T> InEqualTerms,
				final HashSet<T> maximumTerms, final HashSet<T> minimumTerms) {
			super(variable, variable.getVariableTerm().mProgramVar);
			assert maximumTerms.size() > 0 && minimumTerms.size() > 0;

			mInEqualTerms = new ArrayList<>(InEqualTerms);
			mMaximumTerms = new ArrayList<>(maximumTerms);
			mMinimumTerms = new ArrayList<>(minimumTerms);

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
						return next.havocBool(null);
					};
					return;
				}
				final T inEuqalTo = InEqualTerms.iterator().next();
				func = (currentState, nextState) -> {
					final HashSet<Boolean> inEqualBool = new HashSet<>();
					inEqualBool.add((Boolean) inEuqalTo.evaluate(currentState, nextState));
					return nextState.havocBool(new BooleanRestriction(inEqualBool));
				};

				break;
			case ReturnType.Int:
				func = (currentState, nextState) -> {
					final Long[] minimums = new Long[mMinimumTerms.size()];
					final Long[] maximums = new Long[mMaximumTerms.size()];
					final Long[] inequals = new Long[mInEqualTerms.size()];

					for (int i = 0; i < mMinimumTerms.size(); i++) {
						if (mMinimumTerms.get(i) instanceof final IntegerTerm minInt) {
							minimums[i] = minInt.evaluate(currentState, nextState);
						}
					}

					for (int i = 0; i < mMaximumTerms.size(); i++) {
						if (mMaximumTerms.get(i) instanceof final IntegerTerm maxInt) {
							maximums[i] = maxInt.evaluate(currentState, nextState);
						}
					}

					for (int i = 0; i < mInEqualTerms.size(); i++) {
						if (mInEqualTerms.get(i) instanceof final IntegerTerm neqInt) {
							inequals[i] = neqInt.evaluate(currentState, nextState);
						}
					}

					return nextState
							.havocInt(IntegerRestriction.makeRestriction(IntegerRestriction.findMinimum(minimums),
									IntegerRestriction.findMaximum(maximums), inequals));
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
			final StringBuilder out = new StringBuilder();
			out.append(mVariable.getVariableTerm().mTermVar.getName());
			out.append(" := havoc(");

			String connector = "";
			if (mMaximumTerms.size() > 0) {
				out.append("n <= {");
				for (final T maximum : mMaximumTerms) {
					maximum.toString(out, 0);
				}
				out.append("}");
				connector = ", ";
			}

			if (mMinimumTerms.size() > 0) {
				out.append(connector);
				out.append("n >= {");

				for (final T minimum : mMinimumTerms) {
					minimum.toString(out, 0);
				}
				out.append("}");

				connector = ", ";
			}

			if (mInEqualTerms.size() > 0) {
				out.append(connector);
				out.append("n != {");

				for (final T inEqual : mInEqualTerms) {
					inEqual.toString(out, 0);
				}
				out.append("}");
			}

			return out.toString() + ")";
		}

		@Override
		public String toCode() {
			final ArrayList<String> maxCode = new ArrayList<>();
			for (final T maximum : mMaximumTerms) {
				maxCode.add(maximum.toCode());
			}
			final ArrayList<String> minCode = new ArrayList<>();
			for (final T minimum : mMinimumTerms) {
				minCode.add(minimum.toCode());
			}
			final ArrayList<String> inEqualCode = new ArrayList<>();
			for (final T inEqualTerm : mInEqualTerms) {
				inEqualCode.add(inEqualTerm.toCode());
			}

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
				out.append(", nextState.havocInt(IntegerRestriction.makeRestriction(");

				if (minCode.size() > 1) {
					out.append("IntegerRestriction.findMinimum(");
					out.append(String.join(", ", minCode));
					out.append(")");
				} else {
					out.append(minCode.get(0));
				}
				out.append(", ");

				if (maxCode.size() > 1) {
					out.append("IntegerRestriction.findMaximum(");
					out.append(String.join(", ", maxCode));
					out.append(")");
				} else {
					out.append(maxCode.get(0));
				}

				if (inEqualCode.size() > 0) {
					out.append(", ");
					out.append(String.join(", ", inEqualCode));
				}
				out.append(")));");
				return out.toString();
			}

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
			// Find the lowest constant max such that variable <= max, vice versa biggest constant
			Long max = Long.MAX_VALUE;
			Long min = Long.MIN_VALUE;

			for (final Constraint constraint : constraints) {
				Long value = (Long) constraint.getConstraint().evaluate(null, null);
				switch (constraint.relation) {
				case DISTINCT:
					inequals.add(value);
					break;
				case GREATER:
					// variable > value
					// -> variable >= value + 1
					value++;
					//$FALL-THROUGH$
				case GEQ:
					// variable >= value && value > min
					if (value > min) {
						min = value;
					}
					break;
				case LESS:
					// variable < value
					// -> variable <= value - 1
					value--;
					//$FALL-THROUGH$
				case LEQ:
					// variable <= value && value < max
					if (max > value) {
						max = value;
					}
					break;
				default:
					break;
				}
			}

			// combine restrictions like variable >= 4 and variable != 4 to variable >= 5
			boolean changing = true;
			while (changing) {
				if (inequals.contains(max)) {
					inequals.remove(max);
					max--;
					changing = true;
					continue;
				}
				if (inequals.contains(min)) {
					inequals.remove(min);
					min++;
					changing = true;
					continue;
				}
				changing = false;
			}

			final Long finalMax = max;
			final Long finalMin = min;
			// remove any unequal values that are out of bounds anyways
			inequals = Util.filter(inequals, (value) -> {
				return finalMax >= value && value >= finalMin;
			});

			if (arcs.isEmpty()) {
				// only constraints, we can do most of the work at creation, as we are unaffected by state.
				return new HavocLimitedUpdate(variable, new IntegerRestriction(inequals, finalMin, finalMax));
			}

			final HashSet<IntegerTerm> inequalTerms = new HashSet<>();
			final HashSet<IntegerTerm> minimums = new HashSet<>();
			final HashSet<IntegerTerm> maximums = new HashSet<>();

			for (final Long inequal : inequals) {
				inequalTerms.add(new ConstIntegerTerm(inequal));
			}

			for (final Arc arc : arcs) {
				switch (arc.relation) {
				case DISTINCT:
					inequalTerms.add((IntegerTerm) arc.getConstraint());
					break;
				case GEQ:
					// variable >= value
					minimums.add((IntegerTerm) arc.getConstraint());
					break;
				case GREATER:
					// variable > value
					// -> variable >= value + 1
					minimums.add(new AdditionTerm((IntegerTerm) arc.getConstraint(), new ConstIntegerTerm(1L)));
					break;
				case LEQ:
					// variable <= value
					maximums.add((IntegerTerm) arc.getConstraint());
					break;
				case LESS:
					// variable < value
					// -> variable <= value - 1
					maximums.add(new SubtractionTerm((IntegerTerm) arc.getConstraint(), new ConstIntegerTerm(1L)));
					break;
				default:
					break;
				}
			}

			if (minimums.size() == 0 || finalMin != Long.MIN_VALUE) {
				minimums.add(new ConstIntegerTerm(finalMin));
			}
			if (maximums.size() == 0 || finalMax != Long.MAX_VALUE) {
				maximums.add(new ConstIntegerTerm(finalMax));
			}

			return new HavocDependentUpdate<>(variable, inequalTerms, maximums, minimums);
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

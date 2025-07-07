package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Triple;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;

public interface Update extends ITermProvider {
	void update(Map<Term, Value> state, NonDeterministicChoice ndc, Map<Term, Restriction<?>> havocRestrictions);

	TermVariable getVariable();

	/**
	 * Get the set of term variables that are used in the update.
	 *
	 * @return
	 */
	Set<TermVariable> getFreeVars();

	List<Triple<Term, TermVariable, List<Term>>> getArrayReads();

	public static class AssignmentUpdate implements Update {
		private final TermVariable mTermVar;
		private final Term mValue;
		private final Set<TermVariable> freeVars;
		private final List<Triple<Term, TermVariable, List<Term>>> mArrayReads;

		public AssignmentUpdate(final TermVariable programVar, final Term value) {
			assert programVar.getSort().equals(value.getSort());
			mTermVar = programVar;
			freeVars = Set.of(value.getFreeVars());

			final List<ApplicationTerm> selected = Util.extractSelects(value);
			mArrayReads = List.copyOf(selected.stream().map(select -> Util.selectToKeyTriple(select)).toList());
			mValue = value;
		}

		@Override
		public void update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			state.put(mTermVar, TermEvaluator.evaluate(state, mValue));
		}

		@Override
		public TermVariable getVariable() {
			return mTermVar;
		}

		@Override
		public Set<TermVariable> getFreeVars() {
			return freeVars;
		}

		@Override
		public String toString() {
			return mTermVar + " := " + mValue.toStringDirect();
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final AssignmentUpdate update) {
				return mTermVar.equals(update.mTermVar) && mValue.equals(update.mValue);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return mTermVar.hashCode() * 31 + mValue.hashCode();
		}

		@Override
		public Term toTerm(final Script script) {
			return SmtUtils.binaryEquality(script, mTermVar, mValue);
		}

		@Override
		public List<Triple<Term, TermVariable, List<Term>>> getArrayReads() {
			return mArrayReads;
		}
	}

	public static class HavocUpdate implements Update {
		private final TermVariable mTermVar;
		private Term mUpdatedTerm;
		private final HashSet<Term> mLessEq;
		private final HashSet<Term> mGreaterEq;
		private final HashSet<Term> mInEqual;
		private final Set<TermVariable> mFreeVars;
		private final boolean mRemovePrevious;
		private final List<Triple<Term, TermVariable, List<Term>>> mArrayReads;

		public HavocUpdate(final ApplicationTerm select, final TermVariable array, final List<SolvedEquation> equations,
				final boolean removePrevious) {
			this(array, equations, removePrevious);
			mUpdatedTerm = select;
		}

		/**
		 * @param termVar        Variable to receive a non-deterministic value
		 * @param equations      List of equation restricting the variable's value
		 * @param removePrevious True if this update removes previous restrictions (the variable was not an InVar)
		 */
		public HavocUpdate(final TermVariable termVar, final List<SolvedEquation> equations,
				final boolean removePrevious) {
			mUpdatedTerm = termVar;
			mTermVar = termVar;
			mLessEq = new HashSet<>();
			mGreaterEq = new HashSet<>();
			mInEqual = new HashSet<>();
			mFreeVars = Set.copyOf(equations.stream().map((eq) -> eq.getRhs().getFreeVars())
					.flatMap((arr) -> Arrays.stream(arr)).toList());
			mRemovePrevious = removePrevious;
			final Theory theory = mTermVar.getTheory();
			final Term one = theory.constant(BigInteger.ONE, theory.getNumericSort());
			final ArrayList<Triple<Term, TermVariable, List<Term>>> arrayReads = new ArrayList<>();

			for (final SolvedEquation equation : equations) {
				Term newTerm;

				switch (equation.getRelation()) {
				case BVUGE:
				case GEQ:
					newTerm = trySimplifyToConstant(equation.getRhs());
					mGreaterEq.add(newTerm);
					break;

				case BVUGT:
					// TODO make separate version with BitVec constant, BitVec - Int is undefined
				case GREATER:
					// x > y <==> x > y + 1 or x == y + 1 <==> x >= y + 1
					newTerm = trySimplifyToConstant(theory.term(SMTLIBConstants.PLUS, equation.getRhs(), one));
					mGreaterEq.add(newTerm);
					break;
				case BVULE:
				case LEQ:
					newTerm = trySimplifyToConstant(equation.getRhs());
					mLessEq.add(newTerm);
					break;
				case BVULT:
					// TODO make separate version with BitVec constant, BitVec + Int is undefined
				case LESS:
					// x < y <==> x < y - 1 or x == y - 1 <==> x <= y - 1
					newTerm = trySimplifyToConstant(theory.term(SMTLIBConstants.MINUS, equation.getRhs(), one));
					mLessEq.add(newTerm);
					break;
				case DISTINCT:
					newTerm = trySimplifyToConstant(equation.getRhs());
					mInEqual.add(newTerm);
					break;
				default:
					continue;
				}

				final List<ApplicationTerm> selected = Util.extractSelects(newTerm);
				arrayReads.addAll(selected.stream().map(select -> Util.selectToKeyTriple(select)).toList());
			}

			mArrayReads = List.copyOf(arrayReads);
		}

		/**
		 * True if this havoc update is on an edge where it's variable is not an InVar, meaning that this is a new
		 * instance of havocing this variable. If it is false, then the variable was previously havoced and this update
		 * only restricts the possible values (an assume statement).
		 *
		 * @return True if this is a havoc, false if this is an assume.
		 */
		public boolean overridesPrevious() {
			return mRemovePrevious;
		}

		private static Term trySimplifyToConstant(Term term) {
			if (term.getFreeVars().length > 0) {
				return term;
			}
			switch (term.getSort().getName()) {
			case SMTLIBConstants.BOOL:
				final BoolValue boolValue = (BoolValue) TermEvaluator.evaluate(null, term);
				term = term.getTheory().constant(boolValue.getValue(), term.getTheory().getBooleanSort());
				break;
			case SMTLIBConstants.INT:
				final IntValue intValue = (IntValue) TermEvaluator.evaluate(null, term);
				term = term.getTheory().constant(intValue.getValue(), term.getTheory().getNumericSort());
				break;
			case SMTLIBConstants.ARRAY:
				// No array constants
				break;
			case SMTLIBConstants.BITVEC:
				final BitVecValue bitVecValue = (BitVecValue) TermEvaluator.evaluate(null, term);
				term = term.getTheory().constant(bitVecValue.getValue(), term.getTheory().getNumericSort());
				break;
			}

			return term;
		}

		public Restriction<?> getRestriction(final Map<Term, Value> state, final NonDeterministicChoice ndc) {

			String returnSort;
			if (mUpdatedTerm instanceof final ApplicationTerm at) {
				returnSort = at.getFunction().getReturnSort().getName();
			} else {
				returnSort = mTermVar.getSort().getName();
			}

			switch (returnSort) {
			case SMTLIBConstants.BOOL:
				final HashSet<BoolValue> inEqualBools = new HashSet<>();

				for (final Term inEqual : mInEqual) {
					inEqualBools.add((BoolValue) TermEvaluator.evaluate(state, inEqual));
				}

				return new BooleanRestriction(inEqualBools);

			case SMTLIBConstants.INT:
			case SMTLIBConstants.BITVEC:
				if (mInEqual.size() + mLessEq.size() + mGreaterEq.size() == 0) {
					return null;
				}

				IntValue maximum = null;
				if (mLessEq.size() > 0) {
					final Iterator<Term> lessEqlIter = mLessEq.iterator();
					maximum = (IntValue) TermEvaluator.evaluate(state, lessEqlIter.next());
					while (lessEqlIter.hasNext()) {
						final IntValue nextValue = (IntValue) TermEvaluator.evaluate(state, lessEqlIter.next());
						if (nextValue.compareTo(maximum) < 0) {
							maximum = nextValue;
						}
					}
				}

				IntValue minimum = null;
				if (mGreaterEq.size() > 0) {
					final Iterator<Term> greaterEqlIter = mGreaterEq.iterator();
					minimum = (IntValue) TermEvaluator.evaluate(state, greaterEqlIter.next());
					while (greaterEqlIter.hasNext()) {
						final IntValue nextValue = (IntValue) TermEvaluator.evaluate(state, greaterEqlIter.next());
						if (minimum.compareTo(nextValue) < 0) {
							minimum = nextValue;
						}
					}
				}

				final Set<IntValue> inEqualInts = new HashSet<>();
				final Iterator<Term> inEqualIter = mInEqual.iterator();
				while (inEqualIter.hasNext()) {
					final IntValue nextValue = (IntValue) TermEvaluator.evaluate(state, inEqualIter.next());
					if ((minimum == null || minimum.compareTo(nextValue) <= 0)
							&& (maximum == null || nextValue.compareTo(maximum) <= 0)) {
						inEqualInts.add(nextValue);
					}
				}

				final IntegerRestriction restriction = new IntegerRestriction(inEqualInts, minimum, maximum);

				return restriction;
			default:
				return null;
			}
		}

		@Override
		public void update(final Map<Term, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			final Restriction<?> existingRestriction = havocRestrictions.remove(mUpdatedTerm);
			Restriction<?> newRestriction;

			if (existingRestriction != null && !mRemovePrevious) {
				newRestriction = existingRestriction.combine(getRestriction(state, ndc));
			} else {
				newRestriction = getRestriction(state, ndc);
			}

			// Is havoced when (and only if) variable is read
			havocRestrictions.put(mUpdatedTerm, newRestriction);
			if (mUpdatedTerm instanceof final TermVariable tv) {
				// We are havocing a specific variable, not an array entry. Arrays as a whole do not get havoced.
				state.remove(tv);
			}
		}

		@Override
		public TermVariable getVariable() {
			return mTermVar;
		}

		@Override
		public Set<TermVariable> getFreeVars() {
			return mFreeVars;
		}

		@Override
		public String toString() {
			final ArrayList<String> types = new ArrayList<>();

			if (!mInEqual.isEmpty()) {
				types.add("var != {" + String.join(", ", mInEqual.stream().map(neq -> neq.toStringDirect()).toList())
						+ "}");
			}

			if (!mGreaterEq.isEmpty()) {
				types.add("var >= {" + String.join(", ", mGreaterEq.stream().map(geq -> geq.toStringDirect()).toList())
						+ "}");
			}

			if (!mLessEq.isEmpty()) {
				types.add("var <= {" + String.join(", ", mLessEq.stream().map(leq -> leq.toStringDirect()).toList())
						+ "}");
			}

			final String type = mRemovePrevious ? "havoc" : "assume";
			return mUpdatedTerm + " := " + type + "(" + String.join("; ", types) + ")";
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final HavocUpdate update) {
				return mUpdatedTerm.equals(update.mUpdatedTerm) && mInEqual.equals(update.mInEqual)
						&& mGreaterEq.equals(update.mGreaterEq) && mLessEq.equals(update.mLessEq);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return (((mUpdatedTerm.hashCode() * 31 + mInEqual.hashCode()) * 31 + mGreaterEq.hashCode()) * 31
					+ mLessEq.hashCode()) * 31;
		}

		@Override
		public Term toTerm(final Script script) {
			final List<Term> equations = new ArrayList<>();

			for (final Term neq : mInEqual) {
				return SmtUtils.distinct(script, mUpdatedTerm, neq);
			}

			for (final Term geq : mGreaterEq) {
				return SmtUtils.geq(script, mUpdatedTerm, geq);
			}

			for (final Term leq : mLessEq) {
				return SmtUtils.leq(script, mUpdatedTerm, leq);
			}

			return SmtUtils.and(script, equations);
		}

		@Override
		public List<Triple<Term, TermVariable, List<Term>>> getArrayReads() {
			return mArrayReads;
		}
	}
}
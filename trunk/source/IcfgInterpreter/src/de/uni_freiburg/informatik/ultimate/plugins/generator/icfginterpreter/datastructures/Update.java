package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.RestrictionParser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.TermEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Equation.SolvedEquation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public interface Update {
	void update(Map<TermVariable, Value> state, NonDeterministicChoice ndc,
			Map<Term, Restriction<?>> havocRestrictions);

	TermVariable getVariable();

	/**
	 * Get the set of term variables that are used in the update.
	 *
	 * @return
	 */
	Set<TermVariable> getFreeVars();

	Map<Term, Pair<TermVariable, List<Term>>> getArrayReads();

	public static class AssignmentUpdate implements Update {
		private final TermVariable mTermVar;
		private final Term mValue;
		private final Set<TermVariable> mFreeVars;
		private final Map<Term, Pair<TermVariable, List<Term>>> mArrayReads;

		public AssignmentUpdate(final TermVariable programVar, final Term value) {
			assert programVar.getSort().equals(value.getSort());
			mTermVar = programVar;
			mFreeVars = Set.of(value.getFreeVars());

			final List<ApplicationTerm> selected = Util.extractSelects(value);
			mArrayReads = selected.stream().collect(Collectors.toMap(Term.class::cast, Util::selectToKeyPair));
			mValue = value;
		}

		@Override
		public void update(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			state.put(mTermVar, TermEvaluator.evaluate(state, mValue));
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
		public Map<Term, Pair<TermVariable, List<Term>>> getArrayReads() {
			return mArrayReads;
		}
	}

	public static class HavocUpdate implements Update {
		private final TermVariable mTermVar;
		private Term mUpdatedTerm;
		private final boolean mRemovePrevious;
		private final RestrictionParser mRestrictionParser;

		public HavocUpdate(final ApplicationTerm select, final TermVariable array, final List<SolvedEquation> equations,
				final boolean removePrevious) {
			this(array, equations, removePrevious);
			mUpdatedTerm = select;
		}

		/**
		 * @param termVar
		 *            Variable to receive a non-deterministic value
		 * @param equations
		 *            List of equation restricting the variable's value
		 * @param removePrevious
		 *            True if this update removes previous restrictions (the variable was not an InVar)
		 */
		public HavocUpdate(final TermVariable termVar, final List<SolvedEquation> equations,
				final boolean removePrevious) {
			mUpdatedTerm = termVar;
			mTermVar = termVar;
			mRemovePrevious = removePrevious;
			mRestrictionParser = new RestrictionParser(termVar, equations);
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

		@Override
		public void update(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			final Restriction<?> existingRestriction = havocRestrictions.remove(mUpdatedTerm);
			final Restriction<?> restriction;

			final Restriction<?> newRestriction = mRestrictionParser.getRestriction(state);
			if (existingRestriction != null && !mRemovePrevious) {
				restriction = existingRestriction.combine(newRestriction);
			} else {
				restriction = newRestriction;
			}

			if (mUpdatedTerm instanceof final TermVariable tv) {
				// We are havocing a specific variable, not an array entry. Arrays as a whole do not get havoced.
				state.remove(tv);
			}
			// TODO decide if we should check if array entry exists and not add restriction

			// Is havoced when (and only if) variable is read
			havocRestrictions.put(mUpdatedTerm, restriction);
		}

		@Override
		public TermVariable getVariable() {
			return mTermVar;
		}

		@Override
		public Set<TermVariable> getFreeVars() {
			return mRestrictionParser.getFreeVars();
		}

		@Override
		public String toString() {
			return mUpdatedTerm + " := " + (mRemovePrevious ? "havoc" : "assume") + mRestrictionParser.toString();
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final HavocUpdate update) {
				return mUpdatedTerm.equals(update.mUpdatedTerm) && mRestrictionParser.equals(update.mRestrictionParser);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return (mUpdatedTerm.hashCode() * 31 + mRestrictionParser.hashCode()) * 31;
		}

		@Override
		public Map<Term, Pair<TermVariable, List<Term>>> getArrayReads() {
			return mRestrictionParser.getArrayReads();
		}
	}
}
package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.ArrayDeque;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Pair;
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

	List<Pair<ArrayValue, List<Value>>> getArrayReads(Map<Term, Value> state);

	default List<ApplicationTerm> extractSelects(final Term term) {
		final List<ApplicationTerm> out = new ArrayList<>();
		final ArrayDeque<Term> terms = new ArrayDeque<>();
		terms.add(term);

		while (terms.size() > 0) {
			final Term subTerm = terms.pop();
			if (subTerm instanceof final ApplicationTerm at) {
				if (at.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
					out.add(at);
				} else {
					terms.addAll(List.of(at.getParameters()));
				}
			}
		}

		return out;
	}

	default Pair<Term, List<Term>> selectToKeyPair(ApplicationTerm select) {
		final ArrayDeque<Term> keys = new ArrayDeque<>();
		Term arrayTerm = null;

		while (select.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			keys.push(select.getParameters()[1]);

			final Term subTerm = select.getParameters()[0];
			if (subTerm instanceof final ApplicationTerm at) {
				select = at;
			} else {
				arrayTerm = subTerm;
				break;
			}
		}
		return new Pair<>(arrayTerm, List.of(keys.toArray(new Term[keys.size()])));
	}

	public static class AssignmentUpdate implements Update {
		private final TermVariable mTermVar;
		private final Term mValue;
		private final Set<TermVariable> freeVars;
		private final List<Pair<Term, List<Term>>> arrayReads;

		public AssignmentUpdate(final TermVariable programVar, final Term value) {
			assert programVar.getSort().equals(value.getSort());
			mTermVar = programVar;
			freeVars = Set.of(value.getFreeVars());

			final List<ApplicationTerm> selected = extractSelects(value);
			arrayReads = List.copyOf(selected.stream().map(select -> selectToKeyPair(select)).toList());
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
		public List<Pair<ArrayValue, List<Value>>> getArrayReads(final Map<Term, Value> state) {
			final List<Pair<ArrayValue, List<Value>>> out = new ArrayList<>();

			for (final Pair<Term, List<Term>> arrayPair : arrayReads) {
				final ArrayValue array = (ArrayValue) state.get(arrayPair.a());
				out.add(new Pair<>(array,
						arrayPair.b().stream().map(term -> TermEvaluator.evaluate(state, term)).toList()));
			}

			return out;
		}
	}

	public static class HavocUpdate implements Update {
		private final TermVariable mTermVar;
		private final HashSet<Term> mLessEq;
		private final HashSet<Term> mGreaterEq;
		private final HashSet<Term> mInEqual;
		private final Set<TermVariable> freeVars;

		public HavocUpdate(final TermVariable programVar, final List<SolvedEquation> equations) {
			mTermVar = programVar;
			mLessEq = new HashSet<>();
			mGreaterEq = new HashSet<>();
			mInEqual = new HashSet<>();
			freeVars = Set.copyOf(equations.stream().map((eq) -> eq.getRhs().getFreeVars())
					.flatMap((arr) -> Arrays.stream(arr)).toList());
			final Theory theory = mTermVar.getTheory();
			final Term one = theory.constant(BigInteger.ONE, theory.getNumericSort());

			for (final SolvedEquation equation : equations) {
				switch (equation.getRelation()) {
				case BVUGE:
				case GEQ:
					mGreaterEq.add(trySimplifyToConstant(equation.getRhs()));
					break;

				case BVUGT:
					// TODO make separate version with BitVec constant, BitVec - Int is undefined
				case GREATER:
					// x > y <==> x > y + 1 or x == y + 1 <==> x >= y + 1
					mGreaterEq.add(trySimplifyToConstant(theory.term(SMTLIBConstants.PLUS, equation.getRhs(), one)));
					break;
				case BVULE:
				case LEQ:
					mLessEq.add(trySimplifyToConstant(equation.getRhs()));
					break;
				case BVULT:
					// TODO make separate version with BitVec constant, BitVec + Int is undefined
				case LESS:
					// x < y <==> x < y - 1 or x == y - 1 <==> x <= y - 1
					mLessEq.add(trySimplifyToConstant(theory.term(SMTLIBConstants.MINUS, equation.getRhs(), one)));
					break;
				case DISTINCT:
					mInEqual.add(trySimplifyToConstant(equation.getRhs()));
					break;
				default:
					break;
				}
			}
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

		private Restriction<?> getRestriction(final Map<Term, Value> state, final NonDeterministicChoice ndc,
				final Map<Term, Restriction<?>> havocRestrictions) {
			switch (mTermVar.getSort().getName()) {
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
			final Restriction<?> existingRestriction = havocRestrictions.remove(mTermVar);
			Restriction<?> newRestriction;

			if (existingRestriction != null) {
				newRestriction = existingRestriction.combine(getRestriction(state, ndc, havocRestrictions));
			} else {
				newRestriction = getRestriction(state, ndc, havocRestrictions);
			}

			// Is havoced when (and only if) variable is read
			havocRestrictions.put(mTermVar, newRestriction);
			state.remove(mTermVar);
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

			return mTermVar + " := havoc(" + String.join("; ", types) + ")";
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final HavocUpdate update) {
				return mTermVar.equals(update.mTermVar) && mInEqual.equals(update.mInEqual)
						&& mGreaterEq.equals(update.mGreaterEq) && mLessEq.equals(update.mLessEq);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return (((mTermVar.hashCode() * 31 + mInEqual.hashCode()) * 31 + mGreaterEq.hashCode()) * 31
					+ mLessEq.hashCode()) * 31;
		}

		@Override
		public Term toTerm(final Script script) {
			final List<Term> equations = new ArrayList<>();

			for (final Term neq : mInEqual) {
				return SmtUtils.distinct(script, mTermVar, neq);
			}

			for (final Term geq : mGreaterEq) {
				return SmtUtils.geq(script, mTermVar, geq);
			}

			for (final Term leq : mLessEq) {
				return SmtUtils.leq(script, mTermVar, leq);
			}

			return SmtUtils.and(script, equations);
		}

		@Override
		public List<Pair<ArrayValue, List<Value>>> getArrayReads(final Map<Term, Value> state) {
			// TODO Auto-generated method stub
			return null;
		}
	}
}
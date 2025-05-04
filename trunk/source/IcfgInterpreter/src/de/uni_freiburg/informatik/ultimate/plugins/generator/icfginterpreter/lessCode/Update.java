package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;

public interface Update {
	Value makeValue(Map<Term, Value> state, NonDeterministicChoice ndc);

	TermVariable getVariable();

	public static class AssignmentUpdate implements Update {
		private final TermVariable mProgramVar;
		private final Term mValue;

		public AssignmentUpdate(final TermVariable programVar, final Term value) {
			assert programVar.getSort().equals(value.getSort());
			mProgramVar = programVar;
			mValue = value;
		}

		@Override
		public Value makeValue(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
			return TermEvaluator.evaluate(state, mValue, ndc);
		}

		@Override
		public TermVariable getVariable() {
			return mProgramVar;
		}

		@Override
		public String toString() {
			return mProgramVar + " := " + mValue.toStringDirect();
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final AssignmentUpdate update) {
				return mProgramVar.equals(update.mProgramVar) && mValue.equals(update.mValue);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return mProgramVar.hashCode() * 31 + mValue.hashCode();
		}
	}

	public static class HavocUpdate implements Update {
		private final TermVariable mProgramVar;
		private final HashSet<Term> mLessEq;
		private final HashSet<Term> mGreaterEq;
		private final HashSet<Term> mInEqual;

		public HavocUpdate(final TermVariable programVar, final List<SolvedEquation> equations) {
			mProgramVar = programVar;
			mLessEq = new HashSet<>();
			mGreaterEq = new HashSet<>();
			mInEqual = new HashSet<>();
			final Theory theory = mProgramVar.getTheory();
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
				final BoolValue boolValue = (BoolValue) TermEvaluator.evaluate(null, term, null);
				term = term.getTheory().constant(boolValue.getValue(), term.getTheory().getBooleanSort());
				break;
			case SMTLIBConstants.INT:
				final IntValue intValue = (IntValue) TermEvaluator.evaluate(null, term, null);
				term = term.getTheory().constant(intValue.getValue(), term.getTheory().getNumericSort());
				break;
			case SMTLIBConstants.ARRAY:
				// No array constants
				break;
			case SMTLIBConstants.BITVEC:
				final BitVecValue bitVecValue = (BitVecValue) TermEvaluator.evaluate(null, term, null);
				term = term.getTheory().constant(bitVecValue.getValue(), term.getTheory().getNumericSort());
				break;
			}

			return term;
		}

		@Override
		public Value makeValue(final Map<Term, Value> state, final NonDeterministicChoice ndc) {
			switch (mProgramVar.getSort().getName()) {
			// TODO Rewrite when NDC uses Value. Add Array and BitVec
			case SMTLIBConstants.BOOL:
				final HashSet<Boolean> inEqualBools = new HashSet<>();

				for (final Term inEqual : mInEqual) {
					final BoolValue eval = (BoolValue) TermEvaluator.evaluate(state, inEqual, ndc);
					inEqualBools.add(eval.getValue());
				}

				return new BoolValue(ndc.havocBool(new BooleanRestriction(inEqualBools)));
			case SMTLIBConstants.INT:
				if (mInEqual.size() + mLessEq.size() + mGreaterEq.size() == 0) {
					return new IntValue(BigInteger.valueOf(ndc.havocInt(null)));
				}
				final Long[] inEqualInts = new Long[mInEqual.size()];
				final Long[] maximumInts = new Long[mLessEq.size()];
				final Long[] minimumInts = new Long[mGreaterEq.size()];

				final Iterator<Term> inEqualIter = mInEqual.iterator();
				for (int i = 0; i < mInEqual.size(); i++) {
					final IntValue eval = (IntValue) TermEvaluator.evaluate(state, inEqualIter.next(), ndc);
					inEqualInts[i] = eval.getValue().longValue();
				}

				final Iterator<Term> lessEqlIter = mLessEq.iterator();
				for (int i = 0; i < mLessEq.size(); i++) {
					final IntValue eval = (IntValue) TermEvaluator.evaluate(state, lessEqlIter.next(), ndc);
					maximumInts[i] = eval.getValue().longValue();
				}

				final Iterator<Term> greaterEqlIter = mGreaterEq.iterator();
				for (int i = 0; i < mGreaterEq.size(); i++) {
					final IntValue eval = (IntValue) TermEvaluator.evaluate(state, greaterEqlIter.next(), ndc);
					minimumInts[i] = eval.getValue().longValue();
				}

				final IntegerRestriction restriction = IntegerRestriction.makeRestriction(
						IntegerRestriction.findMinimum(minimumInts), IntegerRestriction.findMaximum(maximumInts),
						inEqualInts);

				return new IntValue(BigInteger.valueOf(ndc.havocInt(restriction)));
			default:
				return null;
			}
		}

		@Override
		public TermVariable getVariable() {
			return mProgramVar;
		}

		@Override
		public String toString() {
			final ArrayList<String> types = new ArrayList<>();

			final ArrayList<String> inEquals = new ArrayList<>();
			for (final Term inEqual : mInEqual) {
				inEquals.add(inEqual.toStringDirect());
			}
			if (!inEquals.isEmpty()) {
				types.add("var != {" + String.join(", ", inEquals) + "}");
			}

			final ArrayList<String> maximums = new ArrayList<>();
			for (final Term lessEqual : mLessEq) {
				maximums.add(lessEqual.toStringDirect());
			}
			if (!maximums.isEmpty()) {
				types.add("var <= {" + String.join(", ", maximums) + "}");
			}

			final ArrayList<String> minimums = new ArrayList<>();
			for (final Term greaterEqual : mGreaterEq) {
				minimums.add(greaterEqual.toStringDirect());
			}
			if (!minimums.isEmpty()) {
				types.add("var >= {" + String.join(", ", minimums) + "}");
			}

			return mProgramVar + " := havoc(" + String.join("; ", types) + ")";
		}

		@Override
		public boolean equals(final Object b) {
			if (b instanceof final HavocUpdate update) {
				return mProgramVar.equals(update.mProgramVar) && mInEqual.equals(update.mInEqual)
						&& mGreaterEq.equals(update.mGreaterEq) && mLessEq.equals(update.mLessEq);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return (((mProgramVar.hashCode() * 31 + mInEqual.hashCode()) * 31 + mGreaterEq.hashCode()) * 31
					+ mLessEq.hashCode()) * 31;
		}
	}
}
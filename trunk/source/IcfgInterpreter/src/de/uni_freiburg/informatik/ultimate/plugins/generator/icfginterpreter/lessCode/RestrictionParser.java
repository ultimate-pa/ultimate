package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramExecutions.Pair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;

public class RestrictionParser {
	private final HashSet<Term> mLessEq;
	private final HashSet<Term> mGreaterEq;
	private final HashSet<Term> mInEqual;
	private final HashSet<Term> mEqual;
	private final TermVariable mVariable;
	private final Term mFullTerm;
	private final Map<Term, Pair<TermVariable, List<Term>>> mArrayReads;
	private final Set<TermVariable> mFreeVars;
	private final boolean mIsArray;

	public RestrictionParser(final TermVariable variable, final List<SolvedEquation> equations) {
		this(variable, variable, equations);
	}

	public RestrictionParser(final TermVariable variable, final Term fullTerm, final List<SolvedEquation> equations) {
		mVariable = variable;
		mFullTerm = fullTerm;
		final Theory theory = mVariable.getTheory();
		mLessEq = new HashSet<>();
		mGreaterEq = new HashSet<>();
		mInEqual = new HashSet<>();
		mEqual = new HashSet<>();

		mIsArray = variable.getSort().isArraySort();

		final Term one = theory.constant(BigInteger.ONE, theory.getNumericSort());
		final Map<Term, Pair<TermVariable, List<Term>>> arrayReads = new HashMap<>();

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

			case EQ:
				// Havoc turned out to be exactly one value
				newTerm = trySimplifyToConstant(equation.getRhs());
				mEqual.add(newTerm);
				break;
			default:
				continue;
			}

			final List<ApplicationTerm> selected = Util.extractSelects(newTerm);

			arrayReads.putAll(selected.stream()
					.collect(Collectors.toMap((select -> (Term) select), (select -> Util.selectToKeyPair(select)))));
		}

		mFreeVars = Set.copyOf(equations.stream().map((eq) -> eq.getRhs().getFreeVars())
				.flatMap((arr) -> Arrays.stream(arr)).toList());
		mArrayReads = Map.copyOf(arrayReads);
	}

	public Restriction<?> getRestriction(final Map<TermVariable, Value> state, final NonDeterministicChoice ndc) {
		if (mInEqual.size() + mLessEq.size() + mGreaterEq.size() == 0 && mEqual == null) {
			return new IntegerRestriction(Set.of(), null, null);
		}

		String returnSort;
		if (mFullTerm instanceof final ApplicationTerm at) {
			returnSort = at.getFunction().getReturnSort().getName();
		} else {
			returnSort = mFullTerm.getSort().getName();
		}

		if (mEqual.size() > 0) {
			// Try to get equivalent term
			for (final Term equals : mEqual) {
				final Value value;
				try {
					value = TermEvaluator.evaluate(state, equals);
				} catch (final Exception e) {
					continue;
				}
				switch (value) {
				case final BoolValue bv:
					// Var is unequal to !value => is equal to value
					return new BooleanRestriction(Set.of(bv.not()));
				default:
					// (Assumption: all non-integer / non-bit-vector cases are handled above)
					// The term is both at least and at most the value
					final IntValue valueParsed = parseIntValue(value);
					return new IntegerRestriction(Set.of(), valueParsed, valueParsed);
				}
			}
		}
		// Either no equals are known, or none could be resolved (depending on variables not in state)

		switch (returnSort) {
		case SMTLIBConstants.BOOL:
			final HashSet<BoolValue> inEqualBools = new HashSet<>();

			for (final Term inEqual : mInEqual) {
				try {
					inEqualBools.add((BoolValue) TermEvaluator.evaluate(state, inEqual));
				} catch (final Exception e) {
					continue;
				}
			}

			return new BooleanRestriction(inEqualBools);

		case SMTLIBConstants.INT:
		case SMTLIBConstants.BITVEC:
			IntValue maximum = null;
			if (mLessEq.size() > 0) {
				final Iterator<Term> lessEqlIter = mLessEq.iterator();
				while (maximum == null && lessEqlIter.hasNext()) {
					try {
						final Value value = TermEvaluator.evaluate(state, lessEqlIter.next());
						maximum = parseIntValue(value);
					} catch (final Exception e) {
						continue;
					}
				}

				while (lessEqlIter.hasNext()) {
					final IntValue nextValue;
					try {
						nextValue = parseIntValue(TermEvaluator.evaluate(state, lessEqlIter.next()));
					} catch (final Exception e) {
						continue;
					}
					if (nextValue.compareTo(maximum) < 0) {
						maximum = nextValue;
					}
				}
			}

			IntValue minimum = null;
			if (mGreaterEq.size() > 0) {
				final Iterator<Term> greaterEqlIter = mGreaterEq.iterator();

				while (minimum == null && greaterEqlIter.hasNext()) {
					try {
						final Value value = TermEvaluator.evaluate(state, greaterEqlIter.next());
						minimum = parseIntValue(value);
					} catch (final Exception e) {
						continue;
					}
				}

				while (greaterEqlIter.hasNext()) {
					final IntValue nextValue;
					try {
						nextValue = parseIntValue(TermEvaluator.evaluate(state, greaterEqlIter.next()));
					} catch (final Exception e) {
						continue;
					}
					if (minimum.compareTo(nextValue) < 0) {
						minimum = nextValue;
					}
				}
			}

			final Set<IntValue> inEqualInts = new HashSet<>();
			final Iterator<Term> inEqualIter = mInEqual.iterator();
			while (inEqualIter.hasNext()) {
				final IntValue nextValue;
				try {
					nextValue = parseIntValue(TermEvaluator.evaluate(state, inEqualIter.next()));
				} catch (final Exception e) {
					continue;
				}
				if ((minimum == null || minimum.compareTo(nextValue) <= 0)
						&& (maximum == null || nextValue.compareTo(maximum) <= 0)) {
					inEqualInts.add(nextValue);
				}
			}

			return new IntegerRestriction(inEqualInts, minimum, maximum);
		default:
			throw new TermEvaluator.UnsupportedTermError("Unsupported DataType: " + returnSort);
		}
	}

	public boolean isArray() {
		return mIsArray;
	}

	public Set<TermVariable> getFreeVars() {
		return mFreeVars;
	}

	public Map<Term, Pair<TermVariable, List<Term>>> getArrayReads() {
		return mArrayReads;
	}

	private static IntValue parseIntValue(final Value val) {
		switch (val) {
		case final BitVecValue bv:
			return bv.bv2nat();
		case final IntValue iv:
			return iv;
		default:
			break;
		}
		return null;
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

	@Override
	public String toString() {
		final ArrayList<String> types = new ArrayList<>();

		if (!mEqual.isEmpty()) {
			types.add("var = {" + String.join(", ", mEqual.stream().map(eq -> eq.toStringDirect()).toList()) + "}");
		}

		if (!mInEqual.isEmpty()) {
			types.add(
					"var != {" + String.join(", ", mInEqual.stream().map(neq -> neq.toStringDirect()).toList()) + "}");
		}

		if (!mGreaterEq.isEmpty()) {
			types.add("var >= {" + String.join(", ", mGreaterEq.stream().map(geq -> geq.toStringDirect()).toList())
					+ "}");
		}

		if (!mLessEq.isEmpty()) {
			types.add("var <= {" + String.join(", ", mLessEq.stream().map(leq -> leq.toStringDirect()).toList()) + "}");
		}

		return "(" + String.join("; ", types) + ")";
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final RestrictionParser parser) {
			return mVariable.equals(parser.mVariable) && mInEqual.equals(parser.mInEqual)
					&& mGreaterEq.equals(parser.mGreaterEq) && mLessEq.equals(parser.mLessEq)
					&& mEqual == parser.mEqual;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return ((((mVariable.hashCode() * 31 + mInEqual.hashCode()) * 31 + mGreaterEq.hashCode()) * 31
				+ mLessEq.hashCode()) * 31 + (mEqual != null ? mEqual.hashCode() : 0)) * 31;
	}
}
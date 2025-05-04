package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Equation implements ITermProvider {
	private final RelationSymbol mRelation;
	private final Term mLHS;
	private final Term mRHS;

	public Equation(final RelationSymbol relation, final Term lhs, final Term rhs) {
		mRelation = relation;
		mLHS = lhs;
		mRHS = rhs;
	}

	public Equation swapParameters() {
		return new Equation(mRelation.swapParameters(), mRHS, mLHS);
	}

	public Term getLhs() {
		return mLHS;
	}

	public Term getRhs() {
		return mRHS;
	}

	public RelationSymbol getRelation() {
		return mRelation;
	}

	public Equation negate() {
		return new Equation(mRelation.negate(), mLHS, mRHS);
	}

	@Override
	public Term toTerm(final Script script) {
		switch (getRelation()) {
		case DISTINCT:
			return SmtUtils.distinct(script, getLhs(), getRhs());
		case EQ:
			return SmtUtils.binaryEquality(script, getLhs(), getRhs());
		case GEQ:
			return SmtUtils.geq(script, getLhs(), getRhs());
		case GREATER:
			return SmtUtils.greater(script, getLhs(), getRhs());
		case LEQ:
			return SmtUtils.leq(script, getLhs(), getRhs());
		case LESS:
			return SmtUtils.less(script, getLhs(), getRhs());
		default:
			return null;
		}
	}

	public boolean isSolvedFor(final TermVariable subject) {
		return mLHS.equals(subject);
	}

	public SolvedEquation getSolvedEquation() {
		if (mLHS instanceof final TermVariable tv) {
			return new SolvedEquation(mRelation, tv, mRHS);
		}
		return null;
	}

	public Set<TermVariable> getFreeVars() {
		final HashSet<TermVariable> freeVars = new HashSet<>(Set.of(mLHS.getFreeVars()));
		freeVars.addAll(Set.of(mRHS.getFreeVars()));
		return freeVars;
	}

	public ArrayList<SolvedEquation> solveForVars(final Script script) {
		final ArrayList<SolvedEquation> out = new ArrayList<>();

		for (final TermVariable termVar : getFreeVars()) {
			final boolean leftContains = Arrays.asList(mLHS.getFreeVars()).contains(termVar);
			final boolean rightContains = Arrays.asList(mRHS.getFreeVars()).contains(termVar);

			if (!(leftContains ^ rightContains)) {
				// can't solve if variable appears on both sides (yet)
				continue;
			}

			Equation base = this;
			// make the side that contains the variable the left hand side
			if (!leftContains && rightContains) {
				base = base.swapParameters();
			}

			switch (base.getRelation()) {
			case DISTINCT:
			case EQ:
				SolvedEquation solvedEq;
				if (base.getLhs().getSort().isNumericSort()) {
					solvedEq = solveForSubjectInt(base, termVar, script);
				} else {
					solvedEq = solveForSubjectEquality(base, termVar);
				}
				if (solvedEq == null) {
					continue;
				}
				out.add(solvedEq);
				break;
			case GEQ:
			case GREATER:
			case LEQ:
			case LESS:
				final SolvedEquation solvedComp = solveForSubjectInt(base, termVar, script);
				if (solvedComp == null) {
					continue;
				}
				out.add(solvedComp);
				break;
			default:
				continue;
			}
		}

		return out;
	}

	private static SolvedEquation solveForSubjectEquality(final Equation equation, final TermVariable subject) {
		if (equation.isSolvedFor(subject)) {
			return equation.getSolvedEquation();
		}
		return null;
	}

	public PolynomialRelation toPolinomial(final Script script) {
		return PolynomialRelation.of(script, mRelation, mLHS, mRHS);
	}

	private static SolvedEquation solveForSubjectInt(Equation equation, final TermVariable subject,
			final Script script) {
		if (equation.isSolvedFor(subject)) {
			return equation.getSolvedEquation();
		}
		final PolynomialRelation polynomial = equation.toPolinomial(script);
		final SolvedBinaryRelation solved = polynomial.solveForSubject(script, subject);
		if (solved != null && solved.getLeftHandSide() instanceof final TermVariable tv) {
			return new SolvedEquation(solved.getRelationSymbol(), tv, solved.getRightHandSide());
		}

		final ApplicationTerm leftApp = (ApplicationTerm) equation.getLhs();

		final ArrayList<Term> lhsTerms = new ArrayList<>();
		final ArrayList<Term> rhsTerms = new ArrayList<>();
		switch (leftApp.getFunction().getName()) {
		case SMTLIBConstants.PLUS:
			final Term[] addedTerms = leftApp.getParameters();

			rhsTerms.add(equation.getRhs());

			for (final Term addedTerm : addedTerms) {
				if (Arrays.asList(addedTerm.getFreeVars()).contains(subject)) {
					lhsTerms.add(addedTerm);
				} else {
					rhsTerms.add(addedTerm);
				}
			}

			if (lhsTerms.size() > 1) {
				// more than one subTerm of the PlusTerm contained the subject
				return null;
			}

			equation = new Equation(equation.getRelation(), lhsTerms.get(0),
					script.term(SMTLIBConstants.MINUS, rhsTerms.toArray(new Term[rhsTerms.size()])));
			break;
		case SMTLIBConstants.MINUS:
			final Term[] subtractedTerms = leftApp.getParameters();
			if (subtractedTerms.length == 1) {
				// negation, -x = y becomes x = -y
				equation = new Equation(equation.getRelation(), subtractedTerms[0],
						script.term(SMTLIBConstants.MINUS, equation.getRhs()));
				break;
			}

			// turn ((x - y) - z) into ((x + (-y)) + (-z)) and use addition definition above

			for (int i = 1; i < subtractedTerms.length; i++) {
				subtractedTerms[i] = script.term(SMTLIBConstants.MINUS, subtractedTerms[i]);
			}

			equation = new Equation(equation.getRelation(), script.term(SMTLIBConstants.PLUS, subtractedTerms),
					equation.getRhs());
			break;
		default:
			return null;
		}

		return solveForSubjectInt(equation, subject, script);
	}

	@Override
	public String toString() {
		if (mRelation == null || mRHS == null) {
			return mLHS.toStringDirect() + " = any";
		}
		return mLHS.toStringDirect() + " " + mRelation.toString() + " " + mRHS.toStringDirect();
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final Equation eq) {
			boolean isEqual = true;
			if (getRelation() == null) {
				isEqual &= eq.getRelation() == null;
			} else {
				isEqual &= getRelation().equals(eq.getRelation());
			}

			if (getLhs() == null) {
				isEqual &= eq.getLhs() == null;
			} else {
				isEqual &= getLhs().equals(eq.getLhs());
			}

			if (getRhs() == null) {
				isEqual &= eq.getRhs() == null;
			} else {
				isEqual &= getRhs().equals(eq.getRhs());
			}
			return isEqual;
		}
		return false;
	}

	@Override
	public int hashCode() {
		int out = 0;
		if (getRelation() != null) {
			out += getRelation().hashCode();
			out *= 31;
		}
		if (getLhs() != null) {
			out += getLhs().hashCode();
			out *= 31;
		}
		if (getRhs() != null) {
			out += getRhs().hashCode();
			out *= 31;
		}
		return out;
	}

	public static class SolvedEquation extends Equation {
		private final TermVariable mVariable;

		public SolvedEquation(final RelationSymbol relation, final TermVariable lhs, final Term rhs) {
			super(relation, lhs, rhs);
			mVariable = lhs;
		}

		@Override
		public TermVariable getLhs() {
			return mVariable;
		}

		@Override
		public SolvedEquation negate() {
			return new SolvedEquation(getRelation().negate(), mVariable, getRhs());
		}

		@Override
		public SolvedEquation getSolvedEquation() {
			return this;
		}

		@Override
		public Set<TermVariable> getFreeVars() {
			final HashSet<TermVariable> freeVars = new HashSet<>(Set.of(getRhs().getFreeVars()));
			freeVars.add(mVariable);
			return freeVars;
		}
	}
}
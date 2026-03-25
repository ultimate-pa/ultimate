package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

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

	public boolean isSolvedFor(final Term subject) {
		return mLHS.equals(subject);
	}

	public SolvedEquation getSolvedEquation() {
		if (mLHS instanceof final TermVariable tv) {
			return new SolvedEquation(mRelation, tv, mRHS);
		}
		if (mLHS instanceof final ApplicationTerm at && at.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			return new SolvedEquation(mRelation, at, mRHS);
		}
		return null;
	}

	public Set<TermVariable> getFreeVars() {
		final HashSet<TermVariable> freeVars = new HashSet<>(Set.of(mLHS.getFreeVars()));
		freeVars.addAll(Set.of(mRHS.getFreeVars()));
		return freeVars;
	}

	public Set<Term> getSelects() {
		final HashSet<Term> selects = new HashSet<>(Util.extractSelects(mLHS));
		selects.addAll(Util.extractSelects(mRHS));
		return selects;
	}

	public List<SolvedEquation> solveForAllVars(final Script script) {
		final Set<Term> freeVars = new HashSet<>(getFreeVars());
		freeVars.addAll(getSelects());
		return solveForVars(script, freeVars);
	}

	public List<SolvedEquation> solveForVars(final Script script, final Collection<Term> variables) {
		final ArrayList<SolvedEquation> out = new ArrayList<>();

		for (final Term termVar : variables) {

			final boolean leftContains = SmtUtils.isSubterm(mLHS, termVar);
			final boolean rightContains = SmtUtils.isSubterm(mRHS, termVar);

			// variable is not in equation
			if (!(leftContains ^ rightContains)) {
				continue;
			}

			Equation base = this;
			// make the side that contains the variable the left hand side
			if (!leftContains && rightContains) {
				base = base.swapParameters();
			}

			switch (base.getRelation()) {
			case DISTINCT:
				if (base.getRhs().getSort().getName().equals(SMTLIBConstants.BOOL)) {
					// x != y for bools is equal to x = not(y)
					base = new Equation(RelationSymbol.EQ, base.getLhs(), SmtUtils.not(script, base.getRhs()));
				}
				//$FALL-THROUGH$
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

	private static SolvedEquation solveForSubjectEquality(final Equation equation, final Term subject) {
		if (equation.isSolvedFor(subject)) {
			return equation.getSolvedEquation();
		}
		return null;
	}

	public PolynomialRelation toPolinomial(final Script script) {
		return PolynomialRelation.of(script, mRelation, mLHS, mRHS);
	}

	private static SolvedEquation solveForSubjectInt(Equation equation, final Term subject, final Script script) {
		if (equation.isSolvedFor(subject)) {
			return equation.getSolvedEquation();
		}
		final PolynomialRelation polynomial = equation.toPolinomial(script);
		final SolvedBinaryRelation solved = polynomial.solveForSubject(script, subject);
		if (solved != null) {
			if (solved.getLeftHandSide() instanceof final TermVariable tv && tv.equals(subject)) {
				return new SolvedEquation(solved.getRelationSymbol(), tv, solved.getRightHandSide());
			}
			if (solved.getLeftHandSide() instanceof final ApplicationTerm at && at.equals(subject)) {
				return new SolvedEquation(solved.getRelationSymbol(), at, solved.getRightHandSide());
			}
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
		private final ApplicationTerm mSelect;
		private final boolean mIsSelect;

		public SolvedEquation(final RelationSymbol relation, final TermVariable lhs, final Term rhs) {
			super(relation, lhs, rhs);
			mVariable = lhs;
			mSelect = null;
			mIsSelect = false;
		}

		public SolvedEquation(final RelationSymbol relation, final ApplicationTerm lhs, final Term rhs) {
			super(relation, lhs, rhs);
			assert lhs.getFunction().getName().equals(SMTLIBConstants.SELECT);
			mSelect = lhs;
			mVariable = null;
			mIsSelect = true;
		}

		@Override
		public Term getLhs() {
			return mIsSelect ? mSelect : mVariable;
		}

		@Override
		public SolvedEquation negate() {
			if (mIsSelect) {
				return new SolvedEquation(getRelation().negate(), mSelect, getRhs());
			}
			return new SolvedEquation(getRelation().negate(), mVariable, getRhs());
		}

		public boolean isSelect() {
			return mIsSelect;
		}

		@Override
		public SolvedEquation getSolvedEquation() {
			return this;
		}
	}
}
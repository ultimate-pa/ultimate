package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Equation {
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

	public ApplicationTerm toTerm(final Script script) {
		return (ApplicationTerm) script.term(mRelation.toString(), mLHS, mRHS);
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

	@Override
	public String toString() {
		return mLHS.toStringDirect() + " " + mRelation.toString() + " " + mRHS.toStringDirect();
	}

	public static class SolvedEquation extends Equation {
		private final TermVariable variable;

		public SolvedEquation(final RelationSymbol relation, final TermVariable lhs, final Term rhs) {
			super(relation, lhs, rhs);
			variable = lhs;
		}

		@Override
		public TermVariable getLhs() {
			return variable;
		}
	}
}
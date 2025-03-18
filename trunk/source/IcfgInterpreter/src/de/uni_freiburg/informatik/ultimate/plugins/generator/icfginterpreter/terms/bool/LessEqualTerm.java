package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AdditionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.ConstIntegerTerm;

/**
 * Represents the binary function "X <= Y"
 */
public class LessEqualTerm extends BooleanTerm {
	private final IntegerTerm mX, mY;

	public LessEqualTerm(final IntegerTerm X, final IntegerTerm Y) {
		super(SMTLIBConstants.LEQ);
		mX = X;
		mY = Y;
	}

	/**
	 * Returns "X <= Y" with arguments simplified
	 */
	@Override
	public BooleanTerm simplify() {
		if (mX instanceof AdditionTerm) {
			// (1 + X) <= Y becomes X < Y
			final AdditionTerm xAddition = (AdditionTerm) mX;
			final ArrayList<IntegerTerm> subTerms = xAddition.getSubTerms();
			for (final IntegerTerm subTerm : subTerms) {
				if (subTerm instanceof ConstIntegerTerm && ((ConstIntegerTerm) subTerm).getValue() == 1) {
					subTerms.remove(subTerm);
					final IntegerTerm newSubTerm = subTerms.size() == 1 ? subTerms.get(0)
							: new AdditionTerm(Util.fillArray(subTerms, new IntegerTerm[subTerms.size()]));
					return new LessTerm(newSubTerm, mY).simplify();
				}
			}
		}

		return new LessEqualTerm(mX.simplify(), mY.simplify());
	}

	/**
	 * Returns "Y < X"
	 */
	@Override
	public LessTerm negate() {
		return new LessTerm(mY, mX);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return Util.toList(mX, mY);
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");

		mX.toString(out, 0);
		out.append(" <= ");
		mY.toString(out, 0);

		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof LessEqualTerm)) {
			return false;
		}
		final LessEqualTerm castB = (LessEqualTerm) b;

		return mX.equals(castB.mX) && mY.equals(castB.mY);
	}

	@Override
	public int hashCode() {
		final int result = 47 * 31 + mX.hashCode();
		return result * 31 + mY.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = mX.getVariables();
		out.addAll(mY.getVariables());

		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, mX.toSMTTerm(theory), mY.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { final IntegerTerm[] mSubTerms = new
	 * IntegerTerm[subTerms.length]; for (int i = 0; i < subTerms.length; i++) { mSubTerms[i] =
	 * subTerms[i].equals(current) ? (IntegerTerm) replacement : subTerms[i]; }
	 *
	 * return new LessEqualTerm(mSubTerms); }
	 */

	@Override
	public Boolean evaluate(final ProgramState state) {
		return mX.evaluate(state) <= mY.evaluate(state);
	}
}
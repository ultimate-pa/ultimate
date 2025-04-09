package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents a constant of integer sort.
 */
public class ConstIntegerTerm extends IntegerTerm {
	private final Long mValue;

	public ConstIntegerTerm(final Long value) {
		super(SMTLIBConstants.INT);
		mValue = value;
	}

	@Override
	public IntegerTerm simplify() {
		return this;
	}

	@Override
	public IntegerTerm negate() {
		return new ConstIntegerTerm(-mValue);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(mValue);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ConstIntegerTerm)) {
			return false;
		}
		final ConstIntegerTerm castB = (ConstIntegerTerm) b;
		return mValue == castB.mValue;
	}

	@Override
	public int hashCode() {
		return (int) ((19 * 31 + mValue) % Integer.MAX_VALUE);
	}

	public Long getValue() {
		return mValue;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return new HashSet<>();
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeConstant(Rational.valueOf(mValue, 1L), returnType, theory);
	}

	@Override
	public Long evaluate(final ProgramState currentState, final ProgramState nextState) {
		return mValue;
	}

	@Override
	public String toCode() {
		return String.valueOf(mValue) + "L";
	}

	@Override
	protected ConstIntegerTerm replaceSubterms(final ExecutionTerm old, final ExecutionTerm replacement) {
		return this;
	}
}
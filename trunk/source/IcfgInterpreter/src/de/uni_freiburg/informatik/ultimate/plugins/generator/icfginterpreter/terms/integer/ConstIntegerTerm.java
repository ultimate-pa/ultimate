package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents a constant of integer sort.
 */
public class ConstIntegerTerm extends IntegerTerm {
	private final int value;

	public ConstIntegerTerm(final int mValue) {
		super(SMTLIBConstants.INT);
		value = mValue;
	}

	@Override
	public IntegerTerm simplify() {
		return this;
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(value);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ConstIntegerTerm)) {
			return false;
		}
		final ConstIntegerTerm castB = (ConstIntegerTerm) b;
		return value == castB.value;
	}

	@Override
	public int hashCode() {
		return 19 * 31 + value;
	}

	/*
	 * @Override public IntegerDomain evaluate(final HashMap<Variable<?>, Domain<?>> variableDomains) { return new
	 * IntegerDomain(new Interval(value, value)); }
	 */

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return new HashSet<>();
	}

	@Override
	public Term toSMTTerm() {
		return Util.makeConstant(value, returnType);
	}

	@Override
	public Integer evaluate(final ProgramState state) {
		return value;
	}
}
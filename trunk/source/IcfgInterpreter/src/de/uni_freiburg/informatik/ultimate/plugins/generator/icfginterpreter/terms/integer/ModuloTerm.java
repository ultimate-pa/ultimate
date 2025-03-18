package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

/**
 * Represents the unary function "X % Y"
 */
public class ModuloTerm extends IntegerTerm {
	private final IntegerTerm X;
	private final IntegerTerm Y;

	public ModuloTerm(final IntegerTerm mX, final IntegerTerm mY) {
		super(SMTLIBConstants.MOD);
		X = mX;
		Y = mY;
	}

	/**
	 * Returns "X % Y" with X and Y simplified
	 */
	@Override
	public IntegerTerm simplify() {
		return new ModuloTerm(X.simplify(), Y.simplify());
	}

	@Override
	public IntegerTerm negate() {
		return new NegationTerm(this);
	}

	@Override
	public ArrayList<IntegerTerm> getSubTerms() {
		return new ArrayList<>(Arrays.asList(X, Y));
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		out.append(Util.getIndent(depth)).append("(");
		X.toString(out, 0);
		out.append(" % ");
		Y.toString(out, 0);
		return out.append(")");
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ModuloTerm)) {
			return false;
		}
		final ModuloTerm castB = (ModuloTerm) b;
		return X.equals(castB.X) && Y.equals(castB.Y);
	}

	@Override
	public int hashCode() {
		final int result = 67 * 31 + X.hashCode();
		return result * 31 + Y.hashCode();
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		final HashSet<Variable> out = X.getVariables();
		out.addAll(Y.getVariables());
		return out;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory, X.toSMTTerm(theory), Y.toSMTTerm(theory));
	}

	/*
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<IntegerDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { final IntegerTerm mX = X.equals(current) ?
	 * (IntegerTerm) replacement : X; final IntegerTerm mY = Y.equals(current) ? (IntegerTerm) replacement : Y; return
	 * new ModuloTerm(mX, mY); }
	 */

	@Override
	public Integer evaluate(final ProgramState state) {
		// a mod b := a - ((a div b) * b);
		final int a = X.evaluate(state);
		final int b = Y.evaluate(state);

		return a - ((Util.SMTDiv(a, b)) * b);
	}
}
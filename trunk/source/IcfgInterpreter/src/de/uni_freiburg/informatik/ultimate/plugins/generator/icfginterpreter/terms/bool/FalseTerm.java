package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class FalseTerm extends BooleanTerm {
	public FalseTerm() {
		super(SMTLIBConstants.FALSE);
	}

	@Override
	public BooleanTerm negate() {
		return new TrueTerm();
	}

	@Override
	public BooleanTerm simplify() {
		return this;
	}

	@Override
	public ArrayList<BooleanTerm> getSubTerms() {
		return new ArrayList<>();
	}

	@Override
	public StringBuilder toString(final StringBuilder out, final int depth) {
		return out.append(Util.getIndent(depth)).append(mSymbol);
	}

	@Override
	public boolean equals(final Object b) {
		return b instanceof FalseTerm;
	}

	@Override
	public int hashCode() {
		return 2 * 31;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return new HashSet<>();
	}

	/*
	 * @Override public BooleanDomain evaluate(final HashMap<Variable<?>, Domain<?>> variableDomains) { return new
	 * BooleanDomain(false, true); }
	 *
	 *
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { return this; }
	 */
	@Override
	public Boolean evaluate(final ProgramState state) {
		return false;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory);// return Util.makeConstant(false, returnType, theory);
	}
}
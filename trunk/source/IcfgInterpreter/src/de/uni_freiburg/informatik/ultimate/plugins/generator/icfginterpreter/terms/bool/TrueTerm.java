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

public class TrueTerm extends BooleanTerm {
	public TrueTerm() {
		super(SMTLIBConstants.TRUE);
	}

	@Override
	public BooleanTerm negate() {
		return new FalseTerm();
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
		return b instanceof TrueTerm;
	}

	@Override
	public int hashCode() {
		return 3 * 31;
	}

	@Override
	protected HashSet<Variable> getVariablesInternal() {
		return new HashSet<>();
	}

	/*
	 * @Override public BooleanDomain evaluate(final HashMap<Variable<?>, Domain<?>> variableDomains) { return new
	 * BooleanDomain(true, false); }
	 *
	 * @Override public <subT extends Domain<subT>> ExecutionTerm<BooleanDomain> replaceSubTerm(final
	 * ExecutionTerm<subT> current, final ExecutionTerm<subT> replacement) { return this; }
	 */
	@Override
	public Boolean evaluate(final ProgramState state) {
		return true;
	}

	@Override
	public Term toSMTTerm(final Theory theory) {
		return Util.makeTerm(mSymbol, theory);// .makeConstant(true, returnType, theory);
	}
}
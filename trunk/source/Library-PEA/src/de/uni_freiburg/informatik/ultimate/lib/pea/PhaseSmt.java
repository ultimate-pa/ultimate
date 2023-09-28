package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PhaseSmt extends Phase<Term> {

	private final Script mScript;

	public PhaseSmt(String name, Term stateInv, Term clockInv, Script script) {
		super(name, stateInv, clockInv);
		mScript = script;
	}

	@Override
	protected boolean isStrict(Term clockInv) {
		// TODO: check if clock invariant has only strict less or > oparators
		return false;
	}

	@Override
	protected Term computeOr(Term a, Term b) {
		return SmtUtils.or(mScript, Arrays.asList(new Term[] { (Term) a, (Term) b }));
	}

}

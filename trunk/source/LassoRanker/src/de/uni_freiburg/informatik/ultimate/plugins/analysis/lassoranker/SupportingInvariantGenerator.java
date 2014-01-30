package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


/**
 * Creates and extracts supporting invariants.
 * This class is the counterpart of the RankingFunctionTemplate classes for
 * supporting invariants.
 * 
 * @author Jan Leike
 */
public class SupportingInvariantGenerator extends AffineFunctionGenerator {
	private static final String s_prefix = "si";
	
	/**
	 * Whether the inequality is strict ("<") versus non-strict ("<=")
	 */
	public boolean strict;
	
	/**
	 * @param script The SMTLib script
	 * @param variables A collection of all variables that are relevant for
	 *                   the supporting invariant
	 * @param strict is this invariant a strict inequality?
	 */
	SupportingInvariantGenerator(Script script,
			Collection<BoogieVar> variables, boolean strict) {
		super(script, variables, s_prefix
				+ (new InstanceCounting()).m_instance);
		this.strict = strict;
	}
	
	/**
	 * Generate the linear inequality
	 * @param vars a mapping from Boogie variables to TermVariables to be used
	 * @return Linear inequality corresponding to si(x)
	 */
	public LinearInequality generate(Map<BoogieVar, TermVariable> vars) {
		LinearInequality li = super.generate(vars);
		li.needs_motzkin_coefficient = false;
		li.setStrict(this.strict);
		return li;
	}
	
	/**
	 * Extract the supporting invariant from a model
	 * @return supporting invariant
	 * @throws SMTLIBException
	 */
	public SupportingInvariant extractSupportingInvariant(Map<Term, Rational> val)
			throws SMTLIBException {
		AffineFunction f = super.extractAffineFunction(val);
		SupportingInvariant si = new SupportingInvariant(f);
		si.strict = this.strict;
		return si;
	}
}
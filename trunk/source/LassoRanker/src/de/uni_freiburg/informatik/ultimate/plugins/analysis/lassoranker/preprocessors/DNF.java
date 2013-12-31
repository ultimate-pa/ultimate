package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms.Dnf;


/**
 * Convert a formula into disjunctive normal form, i.e., a formula of the
 * form
 * 
 * <pre>OR ( AND ( NOT? inequality ) )</pre>
 * 
 * This includes a negation normal form (negations only occur before atoms).
 * 
 * @author Jan Leike
 */
public class DNF implements PreProcessor {
	@Override
	public String getDescription() {
		return "Transform the given term into disjunctive normal form.";
	}
	
	@Override
	public Term process(Script script, Term term) throws TermException {
		// Use the DNF transformer from RCFGBuilder
		Dnf dnf_transformer = new Dnf(script);
		return dnf_transformer.transform(term);
	}
	
//	@Override
//	public Collection<TermVariable> getAuxVars() {
//		return Collections.emptyList();
//	}
}
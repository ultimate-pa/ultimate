package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Subclass of {@link SafeSubstitution} were we apply a local simplification
 * when constructing new terms.
 * @author Matthias Heizmann
 *
 */
public class SafeSubstitutionWithLocalSimplification extends SafeSubstitution {
	
	public SafeSubstitutionWithLocalSimplification(Script script, 
			Map<Term, Term> substitutionMapping) {
		this(script, null, substitutionMapping);
	}
	
	public SafeSubstitutionWithLocalSimplification(Script script, 
			IFreshTermVariableConstructor freshTermVariableConstructor,
			Map<Term, Term> substitutionMapping) {
		super(script, freshTermVariableConstructor, substitutionMapping);
	}
	
	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final Term result;
		Term[] oldArgs = appTerm.getParameters();
		if (oldArgs == newArgs) {
			// no argument was changed, we can return the original term
			result = appTerm;
		} else {
			String funcname = appTerm.getFunction().getApplicationString();
			result = SmtUtils.termWithLocalSimplification(m_Script, funcname, newArgs);
		}
		setResult(result);
	}

}

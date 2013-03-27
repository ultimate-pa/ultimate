package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Try to eliminate existentially quantified variables in terms.
 * Use that the term ∃v.v=c∧φ[v] is equivalent to term φ[c].
 *
 */
public class NaiveDestructiveEqualityResolution {
	private final Script m_Script;
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	public NaiveDestructiveEqualityResolution(Script script) {
		m_Script = script;
	}
	
	/**
	 * Eliminate auxVars from input if possible. Let {x_1,...,x_n} be a subset 
	 * of auxVars. Returns a term that is equivalent to ∃x_1,...,∃x_n input and
	 * remove {x_1,...,x_n} from auxVars.
	 * The set {x_1,...,x_n} is determined by NaiveDestructiveEqualityResolution.
	 * 
	 * Returns term that is 
	 * equisatisfiable to input.  If a x is free variable 
	 * @param input
	 * @param auxVars set of free variables occurring in input
	 * @return 
	 */
	public Term eliminate(Set<TermVariable> vars, Term term) {
		Collection<TermVariable> eliminatedVars = new ArrayList<TermVariable>();
		Term resFormula = new FormulaUnLet().unlet(term);
		for (TermVariable tv : vars) {
			Term replacementTerm = equalTerms(tv, resFormula);
			if (replacementTerm != null) {
				s_Logger.debug("eliminated existentially quantifed variable " + tv);
				eliminatedVars.add(tv);
				TermVariable[] varsAux = { tv };
				Term[] valuesAux = { replacementTerm };
				resFormula = m_Script.let(varsAux, valuesAux, resFormula);
				resFormula = new FormulaUnLet().unlet(resFormula);
			}
			else {
				s_Logger.debug("unable to eliminated existentially quantifed variable " + tv);
			}
		}
		for (TermVariable tv : eliminatedVars) {
			vars.remove(tv);
		}
		return resFormula;
	}
	
	
	/**
	 * If Term t is returned tv=t is implied by Term term.
	 * If null is returned no such t exists or the algorithm is not intelligent
	 * enough to find such at t.
	 */
	private Term equalTerms(TermVariable tv, Term term) {
		if (term instanceof ApplicationTerm) {
			return computeEqualTerms(tv, (ApplicationTerm) term);
		}
		else if (term instanceof TermVariable) {
			return computeEqualTerms(tv, (TermVariable) term);
		}
		else if (term instanceof ConstantTerm) {
			return computeEqualTerms(tv, (ConstantTerm) term);
		}
		else {
			throw new UnsupportedOperationException();
		}
		
	}
	
	
	private Term computeEqualTerms(TermVariable tv, TermVariable term) {
		return null;
	}
	
	private Term computeEqualTerms(TermVariable tv, ConstantTerm term) {
		return null;
	}
	
	private Term computeEqualTerms(TermVariable tv, ApplicationTerm term) {
		FunctionSymbol sym = term.getFunction();
		Term[] params = term.getParameters();
		if (sym.getName().equals("=")) {
			int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params);
			return params[tvOnOneSideOfEquality];
		} else if (sym.getName().equals("and")) {
			for (Term param : params) {
				Term equalTerm = equalTerms(tv, param);
				if (equalTerm != null) {
					return equalTerm;
				}
			}
			return null;
		} else {
			return null;
		}
	}
	
	
	/**
     * return <ul>
	 * <li> 0 if right hand side of equality is tv and left hand side does not
	 *  contain tv
  	 * <li> 1 if left hand side of equality is tv and right hand side does not
	 *  contain tv
	 * <li> -1 otherwise
	 * </ul>
	 * 
	 */
	private int tvOnOneSideOfEquality(TermVariable tv, Term[] params) {
		if (params.length != 2) {
			s_Logger.warn("Equality of length " + params.length);
		}
		if (params[0] == tv) {
			final boolean rightHandSideContainsTv = 
					Arrays.asList(params[1].getFreeVars()).contains(tv);
			if (rightHandSideContainsTv) {
				return -1;
			}
			else {
				return 1;
			}
		} else if (params[1] == tv) {
			final boolean leftHandSideContainsTv = 
					Arrays.asList(params[0].getFreeVars()).contains(tv);
			if (leftHandSideContainsTv) {
				return -1;
			}
			else {
				return 0;
			}
		}
		return -1;
	}

}

package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
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
			Term replacementTerm = equalTerm(tv, resFormula);
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
	private Term equalTerm(TermVariable tv, Term term) {
		VarContext context = null;
		context = computeEqualTerms(tv, term);
		if (context.varOccurred == false) {
			throw new IllegalArgumentException("var does not appear: " + tv);
		}
		if (context.getVarEqualTo().isEmpty()) {
			return null;
		}
		return context.getVarEqualTo().iterator().next();
	}
	
	private VarContext computeEqualTerms(TermVariable tv, Term term) {
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
	
	
	private VarContext computeEqualTerms(TermVariable tv, TermVariable term) {
		if (term == tv) {
			return new VarContext(true);
		}
		else {
			return new VarContext(false);
		}
	}
	
	private VarContext computeEqualTerms(TermVariable tv, ConstantTerm term) {
		return new VarContext(false);
	}
	
	private VarContext computeEqualTerms(TermVariable tv, ApplicationTerm term) {
		FunctionSymbol sym = term.getFunction();
		Term[] params = term.getParameters();
		VarContext[] contexts = new VarContext[params.length];
		for (int i=0; i<params.length; i++) {
			contexts[i] = computeEqualTerms(tv, params[i]);
		}
		int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv,sym,params,contexts);
		if (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1) {
			Set<Term> equalTerms = new HashSet<Term>();
			equalTerms.add(params[tvOnOneSideOfEquality]);
			return new VarContext(true, equalTerms, new HashSet<Term>());
		}
		if (sym.getName().equals("and")) {
			boolean varOccurred = false;
			Set<Term> varEqualTo = new HashSet<Term>();
			Set<Term> varDifferentFrom = new HashSet<Term>();
			for (int i=0; i<contexts.length; i++) {
				varOccurred = varOccurred || contexts[i].hasVarOccurred();
				varEqualTo.addAll(contexts[i].getVarEqualTo());
				varDifferentFrom.addAll(contexts[i].getVarDifferentFrom());
			}
			return new VarContext(varOccurred,varEqualTo,varDifferentFrom);
		}
		else if (sym.getName().equals("or")) {
			boolean varOccurred = false;
			Set<Term> varEqualTo = new HashSet<Term>();
			Set<Term> varDifferentFrom = new HashSet<Term>();
			for (int i=0; i<contexts.length; i++) {
				if (varOccurred == true && contexts[i].hasVarOccurred()) {
					return new VarContext(true);
				}
				varOccurred = varOccurred || contexts[i].hasVarOccurred();
				varEqualTo.addAll(contexts[i].getVarEqualTo());
				varDifferentFrom.addAll(contexts[i].getVarDifferentFrom());
			}
			return new VarContext(varOccurred,varEqualTo,varDifferentFrom);
		}
		else if (sym.getName().equals("not")) {
			assert(params.length == 1);
			return new VarContext(contexts[0].hasVarOccurred(), 
					              contexts[0].getVarEqualTo(), 
					              contexts[0].getVarDifferentFrom());
		}

		
		boolean varOccurred = false;
		for (int i=0; i<contexts.length; i++) {
				varOccurred = varOccurred || contexts[i].hasVarOccurred();
		}
		return new VarContext(varOccurred);
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
	private int tvOnOneSideOfEquality(TermVariable tv, FunctionSymbol sym, 
										Term[] params, VarContext[] contexts) {
		if (!sym.getName().equals("=")) {
			return -1;
		}
		if (params.length != 2) {
			return -1;
		}
		if (params[0] == tv) {
			if (contexts[1].hasVarOccurred()) {
				return -1;
			}
			else {
				return 1;
			}
		}
		if (params[1] == tv) {
			if (contexts[0].hasVarOccurred()) {
				return -1;
			}
			else {
				return 0;
			}
		}
		return -1;
	}
	
	
	private class VarContext {
		boolean varOccurred;
		Set<Term> varEqualTo;
		Set<Term> varDifferentFrom;
		
		VarContext(boolean varOccurred) {
			this.varOccurred = varOccurred;
			this.varEqualTo = new HashSet<Term>(0);
			this.varDifferentFrom = new HashSet<Term>(0);
		}


		private VarContext(boolean varOccurred, Set<Term> varEqualTo,
				Set<Term> varDifferentFrom) {
			super();
			this.varOccurred = varOccurred;
			this.varEqualTo = varEqualTo;
			this.varDifferentFrom = varDifferentFrom;
		}


		private boolean hasVarOccurred() {
			return varOccurred;
		}

		private Set<Term> getVarEqualTo() {
			return varEqualTo;
		}

		private Set<Term> getVarDifferentFrom() {
			return varDifferentFrom;
		}
		
		
	}

}

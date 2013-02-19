package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;

/**
 * Represents the transition of a program or a transition system as an SMT
 * formula. The formula denotes a binary relation of this-state/next-state
 * pairs, where we consider a state as a variable assignment.
 * The variables that describe the "this-state"s are given as a BoogieVar,
 * stored as the keySet of the Map m_InVars. m_InVars maps to each of these
 * variables a corresponding TermVariable in the formula. 
 * The variables that describe the "next-state"s are given as a set of strings,
 * stored as the keySet of the Map m_OutVars. m_InVars maps to each of these
 * variables a corresponding TermVariable in the formula.
 * All TermVariables that occur in the formula are stored in the Set m_Vars.
 * The names of all variables that are assigned/updated by this transition are
 * stored in m_AssignedVars (this information is obtained from m_InVars and 
 * m_OutVars).
 * If a variable does not occur in the this-state, but in the next-state it may
 * have any value (think of a Havoc Statement).
 * <p>
 * A TransFormula represents the set of transitions denoted by the formula φ
 * over primed and unprimed variables where φ is obtained by
 * <ul> 
 * <li> first replacing for each x ∈ dom(invar) the TermVariable invar(x) in 
 * m_Formula by x
 * <li> then replacing for each x ∈ dom(outvar) the TermVariable onvar(x) in 
 * m_Formula by x'
 * <li> finally, adding the conjunct x=x' for each x∈(dom(invar)⋂dom(outvar)
 * such that invar(x)=outvar(x)
 * </ul>
 * 
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TransFormula implements Serializable {
	private static final long serialVersionUID = 7058102586141801399L;
	
	static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID); 
	
	private final Term m_Formula;
	private final Set<TermVariable> m_Vars;
	private final Map<BoogieVar, TermVariable> m_InVars;
	private final Map<BoogieVar, TermVariable> m_OutVars;
	private final Set<BoogieVar> m_AssignedVars;
	private final Set<TermVariable> m_auxVars;
	private final Set<TermVariable> m_BranchEncoders;
	private final Infeasibility m_Infeasibility;
	private final Term m_ClosedFormula;
	
	/**
	 * Was the solver able to prove infeasiblity of a TransFormula. UNPROVEABLE
	 * means that TransFormula could be infeasible but the solver is not able
	 * to prove the infeasibility.
	 */
	public enum Infeasibility { INFEASIBLE, UNPROVEABLE, NOT_DETERMINED }
	
	public TransFormula(Term formula,
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars,
			Set<TermVariable> auxVars,
			Set<TermVariable> branchEncoders,
			Infeasibility infeasibility,
			Term closedFormula) {
		m_Formula = formula;
		m_InVars = inVars;
		m_OutVars = outVars;
		m_auxVars = auxVars;
		m_BranchEncoders = branchEncoders;
		m_Infeasibility = infeasibility;
		m_ClosedFormula = closedFormula;
		assert (branchEncoders.size() > 0 || closedFormula.getFreeVars().length == 0);
		m_Vars = new HashSet<TermVariable>(Arrays.asList(m_Formula.getFreeVars()));
		assert (inOutAuxIsAll()) : "unnecessary many vars in TransFormula";
		
		// compute the assigned/updated variables. A variable is updated by this
		// transition if it occurs as outVar and 
		// - it does not occur as inVar 
		// - or the inVar is represented by a different TermVariable 
		m_AssignedVars = new HashSet<BoogieVar>();
		for (BoogieVar var: outVars.keySet()) {
			assert (outVars.get(var) != null);
			if (outVars.get(var) != inVars.get(var)) {
				m_AssignedVars.add(var);
			}
		}
	}
	
	
	/**
	 * Construct formula where
	 * <ul>
	 * <li> each inVar is replaced by default constant of corresponding 
	 * BoogieVar
	 * <li> and each outVar is replaced by primed constant of corresponding 
	 * BoogieVar
	 * <li> each auxVar is replaced by a fresh constant
	 * </ul>
	 * If formula contained no branch encoders the result is a closed formula 
	 * (does not contain free variables)  
	 * 
	 */
	public static Term computeClosedFormula(Term formula,
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars,
			Set<TermVariable> auxVars,
			Boogie2SMT boogie2smt) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		for (BoogieVar bv : inVars.keySet()) {
			replacees.add(inVars.get(bv));
			replacers.add(bv.getDefaultConstant());
		}
		for (BoogieVar bv : outVars.keySet()) {
			if (inVars.get(bv) == outVars.get(bv)) {
				// is assigned var
				continue;
			}
			replacees.add(outVars.get(bv));
			replacers.add(bv.getPrimedConstant());
		}
		for (TermVariable tv : auxVars) {
			replacees.add(tv);
			replacers.add(boogie2smt.getFreshConstant(tv));
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term closedTerm = boogie2smt.getScript().let( vars , values, formula);
		closedTerm = (new FormulaUnLet()).unlet(closedTerm);
		return closedTerm;
	}
	

	private static boolean allVarsContainsFreeVars(
										Set<TermVariable> allVars, Term term) {
		Set<TermVariable> freeVars = 
				new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (TermVariable tv : freeVars) {
			if (!allVars.contains(tv)) {
				s_Logger.error("not in allVars: " + tv);
				result = false;
			}
		}
		return result;
	}
	
	private static boolean freeVarsContainsAllVars(
			Set<TermVariable> allVars, Term term) {
		Set<TermVariable> freeVars = 
				new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (TermVariable tv : allVars) {
			if (!freeVars.contains(tv)) {
				s_Logger.error("not in allVars: " + tv);
				result = false;
			}
		}
		return result;
	}
	
	private static boolean freeVarsSubsetInOutAuxBranch(Term term, 
			Map<BoogieVar, TermVariable> inVars, 
			Map<BoogieVar, TermVariable> outVars, 
			Set<TermVariable> aux, Set<TermVariable> branchEncoders) {
		Set<TermVariable> freeVars = 
				new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		boolean result = true;
		for (TermVariable tv : freeVars) {
			if (inVars.containsValue(tv)) {
				continue;
			}
			if (outVars.containsValue(tv)) {
				continue;
			}
			if (aux.contains(tv)) {
				continue;
			}
			if (branchEncoders.contains(tv)) {
				continue;
			}
			s_Logger.error("neither in out aux: " + tv);
			result = false;
		}
		return result;
	}


	private boolean inOutAuxIsAll() {
		boolean result = true;
		for (TermVariable tv : m_Vars) {
			result &= (m_InVars.values().contains(tv) || 
					m_OutVars.values().contains(tv) || 
					m_auxVars.contains(tv)
					|| m_BranchEncoders.contains(tv));
			assert result;
		}
//		for (TermVariable tv : m_InVars.values()) {
//			result &= m_Vars.contains(tv);
//			assert result;
//		}
//		for (TermVariable tv : m_OutVars.values()) {
//			result &= m_Vars.contains(tv);
//			assert result;
//		}
		for (TermVariable tv : m_auxVars) {
			result &= m_Vars.contains(tv);
			assert result : "unnecessary many vars in TransFormula";
		}
		return result;
	}


	public Term getFormula() {
		return m_Formula;
	}

	public Set<TermVariable> getVars() {
		return m_Vars;
	}

	public Map<BoogieVar, TermVariable> getInVars() {
		return m_InVars;
	}

	public Map<BoogieVar, TermVariable> getOutVars() {
		return m_OutVars;
	}

	public Set<TermVariable> getAuxVars() {
		return m_auxVars;
	}
	
	public Set<TermVariable> getBranchEncoders() {
		return m_BranchEncoders;
	}

	public Term getClosedFormula() {
		return m_ClosedFormula;
	}

	/**
	 * @return the m_AssignedVars
	 */
	public Set<BoogieVar> getAssignedVars() {
		return m_AssignedVars;
	}

	@Override
	public String toString() {
		return "Formula: "+m_Formula + 
				"  Vars: " + m_Vars + 
				"  InVars " + m_InVars + 
				"  OutVars" + m_OutVars +
				"  AssignedVars" + m_AssignedVars;
	}
	
	

	
	/**
	 * @return the relational composition (concatenation) of transformula1 und
	 * transformula2 
	 */
	public static TransFormula sequentialComposition(TransFormula transFormula1, 
				TransFormula transFormula2, Boogie2SMT boogie2smt, int serialNumber) {
		Script script = boogie2smt.getScript();
	 	Term formula1 = transFormula1.getFormula();
		Map<BoogieVar, TermVariable> inVars1 = transFormula1.getInVars();
		Map<BoogieVar, TermVariable> outVars1 = transFormula1.getOutVars();
		Set<TermVariable> vars1 = transFormula1.getVars();

	 	Term formula2 = transFormula2.getFormula();
		Map<BoogieVar, TermVariable> inVars2 = transFormula2.getInVars();
		Map<BoogieVar, TermVariable> outVars2 = transFormula2.getOutVars();
		Set<TermVariable> vars2 = transFormula2.getVars();
	 	
		Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar, TermVariable>();
		Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar, TermVariable>();
		Set<TermVariable> allVars = new HashSet<TermVariable>();
		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
		Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
		
		inVars.putAll(inVars2);
		outVars.putAll(outVars2);
		newAuxVars.addAll(transFormula1.getAuxVars());
		newAuxVars.addAll(transFormula2.getAuxVars());
		newBranchEncoders.addAll(transFormula1.getBranchEncoders());
		newBranchEncoders.addAll(transFormula2.getBranchEncoders());
		allVars.addAll(vars1);
		allVars.addAll(vars2);
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();
		
		for (BoogieVar var :outVars1.keySet()) {
			TermVariable outVar2 = outVars2.get(var);
			TermVariable inVar2 = inVars2.get(var);
			TermVariable outVar1 = outVars1.get(var);
			TermVariable inVar1 = inVars1.get(var);
			
			if (inVar2 == null) {
				if (outVar2 == null) {
					//var does not occur in transFormula2
					if (outVar1 != null) {
						outVars.put(var, outVar1);
					}
					if (inVar1 != null) {
						inVars.put(var, inVar1);
					}
				} else {
					assert (outVar1 != outVar2 && inVar1 != outVar2) : 
						"accidently same tv is used twice, ask Matthias" +
						"to implement this case";
					//var is written but not read in transFormula2
					if (inVar1 != null) {
						inVars.put(var, inVar1);
					}
					if (inVar1 != outVar1) {
						newAuxVars.add(outVar1);
					}
				}
			} else {
				TermVariable newOutVar1 = inVar2;
				inVars.put(var, newOutVar1);
				replacees.add(outVar1);
				replacers.add(newOutVar1);
				if (inVar1 == null) {
					//var is written but not read in transFormula1
					inVars.remove(var);
					if (outVar2 != inVar2) {
						//var modified by both formulas
						newAuxVars.add(newOutVar1);
					}
					assert (outVar1 != inVar2 && outVar1 != outVar2) : 
						"accidently same tv is used twice, ask Matthias" +
						"to implement this case";
				} else if (inVar1 == outVar1) {
					//var not modified in transFormula1
					assert (outVar1 != inVar2 && outVar1 != outVar2) : 
						"accidently same tv is used twice, ask Matthias" +
						"to implement this case";
				} else {
					if (outVar2 != inVar2) {
						//var modified by both formulas
						newAuxVars.add(newOutVar1);
					}
					String name = var.getIdentifier() + "_In" + serialNumber;
					TermVariable newInVar = script.variable(
										name, outVar1.getSort());
					allVars.add(newInVar);
					allVars.add(newInVar);
					inVars.put(var, newInVar);
					replacees.add(inVar1);
					replacers.add(newInVar);
				}
				
			}
		}
		
		for (BoogieVar var : inVars1.keySet()) {
			if (outVars1.containsKey(var)) {
				// nothing do to, this var was already considered above 
			} else {
				TermVariable outVar2 = outVars2.get(var);
				TermVariable inVar2 = inVars2.get(var);
				TermVariable inVar1 = inVars1.get(var);
				assert (inVar1 != inVar2) : 
					"accidently same tv is used twice, ask Matthias" +
					"to implement this case";
				assert (inVar1 != outVar2) : 
					"accidently same tv is used twice, ask Matthias" +
					"to implement this case";
				if (inVar2 == null) {
					if (outVar2 == null) {
						//var does not occur in transFormula2
						inVars.put(var, inVar1);
					} else {
						//var is written but not read in transFormula2
						inVars.put(var, inVar1);
					}
				} else {
					if (outVar2 == inVar2) {
						//var not modified in transFormula2
						inVars.put(var, inVar1);
					} else {
						//var modified in transFormula2
						inVars.put(var, inVar1);
						newAuxVars.add(inVar2);
					}
				}
			}
		}
		
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term formula = script.let( vars , values, formula1);

		formula = Util.and(script, formula, formula2);
		formula = new FormulaUnLet().unlet(formula);
		NaiveDestructiveEqualityResolution der = 
								new NaiveDestructiveEqualityResolution(script);
		//remove auxVars that do not occur in the formula
		{
			Set<TermVariable> varsOccurInTerm = new HashSet<TermVariable>(
										Arrays.asList(formula.getFreeVars()));
			List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
			for (TermVariable tv : newAuxVars) {
				if (!varsOccurInTerm.contains(tv)) {
					superfluousAuxVars.add(tv);
				}
			}
			newAuxVars.removeAll(superfluousAuxVars);
		}
		formula = der.eliminate(newAuxVars, formula);
//		formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
		LBool isSat = Util.checkSat(script, formula);
		if (isSat == LBool.UNSAT) {
			s_Logger.warn("CodeBlock already infeasible");
			formula = script.term("false");
		}
		Infeasibility infeasibility;
		if (formula == script.term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}
		Set<TermVariable> occuringVars = new HashSet<TermVariable>(
										Arrays.asList(formula.getFreeVars()));
		{
			List<BoogieVar> superfluousInVars = new ArrayList<BoogieVar>();
			for (Entry<BoogieVar, TermVariable> entry  : inVars.entrySet()) {
				if (!occuringVars.contains(entry.getValue())) {
					superfluousInVars.add(entry.getKey());
				}
			}
			for (BoogieVar bv : superfluousInVars) {
				inVars.remove(bv);
			}
		}
		// we may not remove outVars e.g., if x is outvar and formula is true
		// this means that x is havoced.
		{
			List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
			for (TermVariable tv  : newAuxVars) {
				if (!occuringVars.contains(tv)) {
					superfluousAuxVars.add(tv);
				}
			}
			for (TermVariable tv : superfluousAuxVars) {
				newAuxVars.remove(tv);
			}
		}
		Term closedFormula = computeClosedFormula(formula, 
				inVars, outVars, newAuxVars, boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars,
				newAuxVars, newBranchEncoders, infeasibility, closedFormula);
		result.getAuxVars().addAll(newAuxVars);
		assert allVarsContainsFreeVars(allVars, formula);
		assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, newAuxVars, newBranchEncoders);
		return result;
	 
 }
 
	
	
	/**
	 * The parallel composition of transFormulas is the disjunction of the
	 * underlying relations.
	 * If we check satisfiability of a path which contains this transFormula
	 * we want know one disjuncts that is satisfiable. We use additional boolean
	 * variables called branchIndicators to encode this disjunction.
	 * Example: Assume we have two TransFormulas tf1 and tf2. Instead of the
	 * Formula tf1 || tf2 we use the following formula.
	 * (BI1 -> tf1) && (BI2 -> tf2) && (BI1 || BI2)
	 * The following holds
	 * <ul>
	 * <li> tf1 || tf2 is satisfiable iff 
	 * (BI1 -> tf1) && (BI2 -> tf2) && (BI1 || BI2) is satisfiable.
	 * <li> in a satisfying assignment BIi can only be true if tfi is true
	 * for i \in {1,2}
	 */
	public static TransFormula parallelComposition(int serialNumber, 
			Boogie2SMT boogie2smt, 
			TermVariable[] branchIndicators, TransFormula... transFormulas) {
		Script script = boogie2smt.getScript();
		boolean useBranchEncoders;
		if (branchIndicators == null) {
			useBranchEncoders = false;
		} else {
			useBranchEncoders = true;
			if (branchIndicators.length != transFormulas.length) {
				throw new IllegalArgumentException();
			}

		}
		
		Term[] renamedFormulas = new Term[transFormulas.length];
		Map<BoogieVar,TermVariable> newInVars = new HashMap<BoogieVar,TermVariable>();
		Map<BoogieVar,TermVariable> newOutVars = new HashMap<BoogieVar,TermVariable>();
		Set<TermVariable> auxVars = new HashSet<TermVariable>();
		Set<TermVariable> branchEncoders = new HashSet<TermVariable>();
		if (useBranchEncoders) {
			branchEncoders.addAll(Arrays.asList(branchIndicators));
		}
				
		Map<BoogieVar,Sort> assignedInSomeBranch = new HashMap<BoogieVar,Sort>();
		for (TransFormula tf : transFormulas) {
			for (BoogieVar bv : tf.getInVars().keySet()) {
				if (!newInVars.containsKey(bv)) {
					Sort sort = tf.getInVars().get(bv).getSort();
					String inVarName = bv.getIdentifier()+"_In"+ serialNumber;
					newInVars.put(bv, script.variable(inVarName, sort));
				}
			}
			for (BoogieVar bv : tf.getOutVars().keySet()) {
				
				// vars which are assigned in some but not all branches must
				// also occur as inVar
				// We could omit this step in the special case where the
				// variable is assigned in all branches, 
				// but we omitted this optimization in the current 
				// implementation.				
				if (!newInVars.containsKey(bv)) {
					Sort sort = tf.getOutVars().get(bv).getSort();
					String inVarName = bv.getIdentifier()+"_In"+ serialNumber;
					newInVars.put(bv, script.variable(inVarName, sort));
				}
				
				TermVariable outVar = tf.getOutVars().get(bv);
				TermVariable inVar = tf.getInVars().get(bv);
				boolean isAssignedVar = (outVar != inVar);
				if (isAssignedVar) {
					Sort sort = tf.getOutVars().get(bv).getSort();
					assignedInSomeBranch.put(bv, sort);
				}
				// auxilliary step, add all invars. Some will be overwritten by
				// outvars
				newOutVars.put(bv,newInVars.get(bv));
			}
		}
		
		// overwrite (see comment above) the outvars if the outvar does not 
		// coincide with the invar is some of the transFormulas
		for (BoogieVar bv : assignedInSomeBranch.keySet()) {
			Sort sort = assignedInSomeBranch.get(bv);
			String outVarName = bv.getIdentifier()+"_Out"+ serialNumber;
			newOutVars.put(bv, script.variable(outVarName, sort));
		}
		
		for (int i=0; i<transFormulas.length; i++) {
			auxVars.addAll(transFormulas[i].getAuxVars());
			branchEncoders.addAll(transFormulas[i].getBranchEncoders());
		
			ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
			ArrayList<Term> replacers = new ArrayList<Term>();
			for (BoogieVar bv : transFormulas[i].getInVars().keySet()) {
				TermVariable inVar = transFormulas[i].getInVars().get(bv);
				replacees.add(inVar);
				replacers.add(newInVars.get(bv));
			}
			for (BoogieVar bv : transFormulas[i].getOutVars().keySet()) {
				TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				TermVariable inVar = transFormulas[i].getInVars().get(bv);
				
				boolean isAssignedVar = (inVar != outVar);
				if (isAssignedVar) {
					replacees.add(outVar);
					replacers.add(newOutVars.get(bv));
				} else {
					assert replacees.contains(outVar);
					assert replacers.contains(newInVars.get(bv));
				}
			}
			TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
			Term[] values = replacers.toArray(new Term[replacers.size()]);
			Term originalFormula = transFormulas[i].getFormula();
			renamedFormulas[i] = script.let( vars , values, originalFormula);

			for (BoogieVar bv : assignedInSomeBranch.keySet()) {
				TermVariable inVar = transFormulas[i].getInVars().get(bv);
				TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				if (inVar == null && outVar == null) {
					//bv does not occur in transFormula
					assert newInVars.get(bv) != null;
					assert newOutVars.get(bv) != null;
					Term equality = script.term("=", newInVars.get(bv), newOutVars.get(bv));
					renamedFormulas[i] = Util.and(script, renamedFormulas[i], equality);
				}
				else if (inVar == outVar) {
					//bv is not modified in transFormula
					assert newInVars.get(bv) != null;
					assert newOutVars.get(bv) != null;
					Term equality = script.term("=", newInVars.get(bv), newOutVars.get(bv));
					renamedFormulas[i] = Util.and(script, renamedFormulas[i], equality);
					replacees.add(inVar);
					replacers.add(newInVars.get(bv));					
				}
			}

			if (useBranchEncoders) {
				renamedFormulas[i] = Util.implies(script, branchIndicators[i], renamedFormulas[i]);
			}
		}
		
		Term resultFormula;
		if (useBranchEncoders) {
			resultFormula = Util.and(script, renamedFormulas);
			Term atLeastOneBranchTaken = Util.or(script, branchIndicators);
			resultFormula = Util.and(script, resultFormula, atLeastOneBranchTaken);
		} else {
			resultFormula = Util.or(script, renamedFormulas);
		}
		LBool termSat = Util.checkSat(script, resultFormula);
		Infeasibility inFeasibility;
		if (termSat == LBool.UNSAT) {
			inFeasibility = Infeasibility.INFEASIBLE;
		} else {
			inFeasibility = Infeasibility.UNPROVEABLE;
		}
		Term closedFormula = computeClosedFormula(resultFormula, 
				newInVars, newOutVars, auxVars, boogie2smt);
		return new TransFormula(resultFormula, newInVars, newOutVars, auxVars, 
				branchEncoders, inFeasibility, closedFormula);
	}




	public Infeasibility isInfeasible() {
		return m_Infeasibility;
	}
	 

}
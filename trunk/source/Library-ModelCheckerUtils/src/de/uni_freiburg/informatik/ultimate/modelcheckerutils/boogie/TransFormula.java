package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

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
			UltimateServices.getInstance().getLogger(ModelCheckerUtils.sPluginID);

//	private static int s_FreshVarNumber = 10000; 
	
//	private final static boolean s_TransformToCNF = false;
	
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
			Term closedFormula, boolean allowSuperflousInVars) {
		m_Formula = formula;
		m_InVars = inVars;
		m_OutVars = outVars;
		m_auxVars = auxVars;
		m_BranchEncoders = branchEncoders;
		m_Infeasibility = infeasibility;
		m_ClosedFormula = closedFormula;
		assert (branchEncoders.size() > 0 || closedFormula.getFreeVars().length == 0);
		m_Vars = new HashSet<TermVariable>(Arrays.asList(m_Formula.getFreeVars()));
		assert allSubsetInOutAuxBranch() : "unexpected vars in TransFormula";
		assert InAuxSubsetAll(allowSuperflousInVars) : "superfluous vars in TransFormula";
//		assert m_OutVars.keySet().containsAll(m_InVars.keySet()) : " strange inVar";
		
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
	
	public TransFormula(Term formula,
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars,
			Set<TermVariable> auxVars,
			Set<TermVariable> branchEncoders,
			Infeasibility infeasibility,
			Term closedFormula) {
		this(formula, inVars, outVars, auxVars, branchEncoders, infeasibility, 
				closedFormula, false);
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
		Map<TermVariable,Term> substitutionMapping = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : inVars.keySet()) {
			assert !substitutionMapping.containsKey(inVars.get(bv));
			substitutionMapping.put(inVars.get(bv), bv.getDefaultConstant());
		}
		for (BoogieVar bv : outVars.keySet()) {
			if (inVars.get(bv) == outVars.get(bv)) {
				// is assigned var
				continue;
			}
			substitutionMapping.put(outVars.get(bv), bv.getPrimedConstant());
		}
		for (TermVariable tv : auxVars) {
			substitutionMapping.put(tv, boogie2smt.getVariableManager().constructConstant(tv));
		}
		Term closedTerm = (new Substitution(substitutionMapping, boogie2smt.getScript())).transform(formula);
		return closedTerm;
	}
	
	
	
	/**
	 * Remove inVars, outVars and auxVars that are not necessary.
	 * Remove auxVars if it does not occur in the formula.
	 * Remove inVars if it does not occur in the formula.
	 * Remove outVar if it does not occur in the formula and is also an inVar
	 * (case where the var is not modified).
	 * Note that we may not generally remove outVars that do not occur in the
	 * formula (e.g., TransFormula for havoc statement).  
	 */
	public static void removeSuperfluousVars(Term formula, 
			Map<BoogieVar, TermVariable> inVars, 
			Map<BoogieVar, TermVariable> outVars, 
			Set<TermVariable> auxVars) {
		Set<TermVariable> allVars = 
				new HashSet<TermVariable>(Arrays.asList(formula.getFreeVars()));
		auxVars.retainAll(allVars);
		List<BoogieVar> superfluousInVars = new ArrayList<BoogieVar>();
		List<BoogieVar> superfluousOutVars = new ArrayList<BoogieVar>();
		for (BoogieVar bv : inVars.keySet()) {
			TermVariable inVar = inVars.get(bv);
			if (!allVars.contains(inVar)) {
				superfluousInVars.add(bv);
			}
		}
		for (BoogieVar bv : outVars.keySet()) {
			TermVariable outVar = outVars.get(bv);
			if (!allVars.contains(outVar)) {
				TermVariable inVar = inVars.get(bv);
				if (outVar == inVar) {
					superfluousOutVars.add(bv);
				}
			}
		}
		for (BoogieVar bv : superfluousInVars) {
			inVars.remove(bv);
		}
		for (BoogieVar bv : superfluousOutVars) {
			outVars.remove(bv);
		}
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


	/**
	 * Returns true if each Term variable in m_Vars occurs as
	 * inVar, outVar, auxVar, or branchEncoder
	 */
	private boolean allSubsetInOutAuxBranch() {
		boolean result = true;
		for (TermVariable tv : m_Vars) {
			result &= (m_InVars.values().contains(tv) || 
					m_OutVars.values().contains(tv) || 
					m_auxVars.contains(tv)
					|| m_BranchEncoders.contains(tv));
			assert result : "unexpected variable in formula";
		}
		for (TermVariable tv : m_auxVars) {
			result &= m_Vars.contains(tv);
			assert result : "unnecessary many vars in TransFormula";
		}
		return result;
	}
	
	/**
	 * Returns true each auxVar is in allVars and 
	 * each inVar occurs in allVars. 
	 */
	private boolean InAuxSubsetAll(boolean allowSuperflousInVars) {
		boolean result = true;
		if (!allowSuperflousInVars) {
			for (BoogieVar bv : m_InVars.keySet()) {
				result &= (m_Vars.contains(m_InVars.get(bv)));
				assert result : "superfluous inVar";
			}
		}
		for (TermVariable tv : m_auxVars) {
			result &= m_Vars.contains(tv);
			assert result : "superfluous auxVar";
		}
		return result;
	}
	


	public Term getFormula() {
		return m_Formula;
	}

	public Map<BoogieVar, TermVariable> getInVars() {
		return Collections.unmodifiableMap(m_InVars);
	}

	public Map<BoogieVar, TermVariable> getOutVars() {
		return Collections.unmodifiableMap(m_OutVars);
	}

	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(m_auxVars);
	}
	
	public Set<TermVariable> getBranchEncoders() {
		return Collections.unmodifiableSet(m_BranchEncoders);
	}

	public Term getClosedFormula() {
		return m_ClosedFormula;
	}

	/**
	 * @return the m_AssignedVars
	 */
	public Set<BoogieVar> getAssignedVars() {
		return Collections.unmodifiableSet(m_AssignedVars);
	}

	@Override
	public String toString() {
		return "Formula: "+m_Formula + 
				"  Vars: " + m_Vars + 
				"  InVars " + m_InVars + 
				"  OutVars" + m_OutVars +
				"  AssignedVars" + m_AssignedVars;
	}
	
	public Infeasibility isInfeasible() {
		return m_Infeasibility;
	}
	
	
//	public static TermVariable getFreshAuxVariable(Boogie2SMT boogie2smt, String id, Sort sort) {
//		String name = id + "_" + s_FreshVarNumber++;
//		TermVariable newVar = boogie2smt.getScript().variable(name, sort);
//		return newVar;
//	}
	
//	public static TermVariable getFreshVariable(Boogie2SMT boogie2smt, BoogieVar var, Sort sort) {
//		String name;
//		if (var.isGlobal()) {
//			if (var.isOldvar()) {
//				name = "old(" + var.getIdentifier() + ")";
//			} else {
//				name = var.getIdentifier();
//			}
//		} else {
//			name = var.getProcedure() + "_" + var.getIdentifier();
//		}
//		name += "_" + s_FreshVarNumber++;
//		return boogie2smt.getScript().variable(name, sort);
//	}
	
	/**
	 * @return the relational composition (concatenation) of transformula1 und
	 * transformula2 
	 */
	public static TransFormula sequentialComposition(Boogie2SMT boogie2smt, 
			boolean simplify, boolean extPqe, boolean tranformToCNF,
			TransFormula... transFormula) {
		s_Logger.debug("sequential composition with" + (simplify ? "" : "out") +
				" formula simplification");
		Script script = boogie2smt.getScript();
		Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar, TermVariable>();
		Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar, TermVariable>();
		Set<TermVariable> auxVars = new HashSet<TermVariable>();
		Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
		Term formula = boogie2smt.getScript().term("true");

		Map<TermVariable,Term> subsitutionMapping = new HashMap<TermVariable, Term>();
		for (int i = transFormula.length-1; i>=0; i--) {
			for (BoogieVar var : transFormula[i].getOutVars().keySet()) {
				TermVariable outVar = transFormula[i].getOutVars().get(var);
				TermVariable newOutVar;
				if (inVars.containsKey(var)) {
					newOutVar = inVars.get(var);
				} else {
					Sort sort = outVar.getSort();
					newOutVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
				}
				subsitutionMapping.put(outVar, newOutVar);
				// add to outvars if var is not outvar
				if (!outVars.containsKey(var)) {
					outVars.put(var, newOutVar);
				}
				TermVariable inVar = transFormula[i].getInVars().get(var);
				if (inVar == null) {
					// case: var is assigned without reading or havoced
					if (outVars.get(var) != newOutVar) {
						//add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
					inVars.remove(var);
				} else if (inVar == outVar) {
					// case: var is not modified
					inVars.put(var, newOutVar);
				} else {
					// case: var is read and written
					Sort sort = outVar.getSort();
					TermVariable newInVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
					subsitutionMapping.put(inVar, newInVar);
					inVars.put(var, newInVar);
					if (outVars.get(var) != newOutVar) {
						//add to auxVars if not already outVar
						auxVars.add(newOutVar);
					}
				}
			}
			for (TermVariable auxVar : transFormula[i].getAuxVars()) {
				TermVariable newAuxVar = boogie2smt.getVariableManager().
						constructFreshTermVariable(auxVar.getName(), auxVar.getSort());
				subsitutionMapping.put(auxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
			newBranchEncoders.addAll(transFormula[i].getBranchEncoders());


			for (BoogieVar var : transFormula[i].getInVars().keySet()) {
				if (transFormula[i].getOutVars().containsKey(var)) {
					// nothing do to, this var was already considered above 
				} else {
					// case var occurs only as inVar: var is not modfied.
					TermVariable inVar = transFormula[i].getInVars().get(var);
					TermVariable newInVar;
					if (inVars.containsKey(var)) {
						newInVar = inVars.get(var);
					} else {
						Sort sort = inVar.getSort();
						newInVar = boogie2smt.getVariableManager().constructFreshTermVariable(var);
						inVars.put(var, newInVar);
					}
					subsitutionMapping.put(inVar, newInVar);
				}
			}
			Term originalFormula = transFormula[i].getFormula();
			Term updatedFormula = (new Substitution(subsitutionMapping, script)).transform(originalFormula);
			formula = Util.and(script, formula, updatedFormula);
			//formula = new FormulaUnLet().unlet(formula);
		
		}
		
		formula = new FormulaUnLet().unlet(formula);
		if (simplify) {
			s_Logger.debug(new DebugMessage(
					"simplifying formula of DAG size {0}", 
					new DagSizePrinter(formula)));
			Term simplified = (new SimplifyDDA(script)).getSimplifiedTerm(formula);
			s_Logger.debug(new DebugMessage(
					"DAG size before simplification {0}, DAG size after simplification {1}", 
					new DagSizePrinter(formula), new DagSizePrinter(simplified)));
			formula = simplified;
		}
		removesuperfluousVariables(inVars, outVars, auxVars, formula);
		
		if (extPqe) {
			Term eliminated = PartialQuantifierElimination.elim(script, QuantifiedFormula.EXISTS, auxVars, formula);
			s_Logger.debug(new DebugMessage(
					"DAG size before PQE {0}, DAG size after PQE {1}", 
					new DagSizePrinter(formula), new DagSizePrinter(eliminated)));
			formula = eliminated;
		} else {
			NaiveDestructiveEqualityResolution der = 
								new NaiveDestructiveEqualityResolution(script);
			formula = der.eliminate(auxVars, formula);
		}
		if (simplify) {
			formula = (new SimplifyDDA(script)).getSimplifiedTerm(formula);
		} else {
			LBool isSat = Util.checkSat(script, formula);
			if (isSat == LBool.UNSAT) {
				s_Logger.warn("CodeBlock already infeasible");
				formula = script.term("false");
			}
		}
		removesuperfluousVariables(inVars, outVars, auxVars, formula);
		
		Infeasibility infeasibility;
		if (formula == script.term("false")) {
			infeasibility = Infeasibility.INFEASIBLE;
		} else {
			infeasibility = Infeasibility.UNPROVEABLE;
		}
		
		if (tranformToCNF) {
			Term cnf = (new Cnf(script)).transform(formula);
			formula = cnf;
		}

		Term closedFormula = computeClosedFormula(formula, 
				inVars, outVars, auxVars, boogie2smt);
		TransFormula result = new TransFormula(formula, inVars, outVars,
				auxVars, newBranchEncoders, infeasibility, closedFormula);

//		assert allVarsContainsFreeVars(allVars, formula);
		assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, auxVars, newBranchEncoders);
		return result;
	 
 }
	
	private static void removesuperfluousVariables(Map<BoogieVar,TermVariable> inVars, Map<BoogieVar,TermVariable> outVars, Set<TermVariable> auxVars, Term formula) {
		Set<TermVariable> occuringVars = new HashSet<TermVariable>(
				Arrays.asList(formula.getFreeVars()));
		{
			List<BoogieVar> superfluousInVars = new ArrayList<BoogieVar>();
			for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
				if (!occuringVars.contains(entry.getValue())) {
					superfluousInVars.add(entry.getKey());
				}
			}
			for (BoogieVar bv : superfluousInVars) {
				TermVariable inVar = inVars.get(bv);
				TermVariable outVar = outVars.get(bv);
				if (inVar == outVar) {
					assert inVar != null;
					outVars.remove(bv);
				}
				inVars.remove(bv);
			}
		}
		// we may not remove outVars e.g., if x is outvar and formula is true
		// this means that x is havoced.
		{
			List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
			for (TermVariable tv : auxVars) {
				if (!occuringVars.contains(tv)) {
					superfluousAuxVars.add(tv);
				}
			}
			for (TermVariable tv : superfluousAuxVars) {
				auxVars.remove(tv);
			}
		}
	}

	
//	/**
//	 * @return the relational composition (concatenation) of transformula1 und
//	 * transformula2 
//	 */
//	public static TransFormula sequentialComposition(TransFormula transFormula1, 
//				TransFormula transFormula2, Boogie2SMT boogie2smt, int serialNumber) {
//		Script script = boogie2smt.getScript();
//	 	Term formula1 = transFormula1.getFormula();
//		Map<BoogieVar, TermVariable> inVars1 = transFormula1.getInVars();
//		Map<BoogieVar, TermVariable> outVars1 = transFormula1.getOutVars();
//		Set<TermVariable> vars1 = transFormula1.getVars();
//
//	 	Term formula2 = transFormula2.getFormula();
//		Map<BoogieVar, TermVariable> inVars2 = transFormula2.getInVars();
//		Map<BoogieVar, TermVariable> outVars2 = transFormula2.getOutVars();
//		Set<TermVariable> vars2 = transFormula2.getVars();
//	 	
//		Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar, TermVariable>();
//		Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar, TermVariable>();
//		Set<TermVariable> allVars = new HashSet<TermVariable>();
//		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
//		Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
//		
//		inVars.putAll(inVars2);
//		outVars.putAll(outVars2);
//		newAuxVars.addAll(transFormula1.getAuxVars());
//		newAuxVars.addAll(transFormula2.getAuxVars());
//		newBranchEncoders.addAll(transFormula1.getBranchEncoders());
//		newBranchEncoders.addAll(transFormula2.getBranchEncoders());
//		allVars.addAll(vars1);
//		allVars.addAll(vars2);
//		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
//		ArrayList<Term> replacers = new ArrayList<Term>();
//		
//		for (BoogieVar var :outVars1.keySet()) {
//			TermVariable outVar2 = outVars2.get(var);
//			TermVariable inVar2 = inVars2.get(var);
//			TermVariable outVar1 = outVars1.get(var);
//			TermVariable inVar1 = inVars1.get(var);
//			
//			if (inVar2 == null) {
//				if (outVar2 == null) {
//					//var does not occur in transFormula2
//					if (outVar1 != null) {
//						outVars.put(var, outVar1);
//					}
//					if (inVar1 != null) {
//						inVars.put(var, inVar1);
//					}
//				} else {
//					assert (outVar1 != outVar2 && inVar1 != outVar2) : 
//						"accidently same tv is used twice, ask Matthias" +
//						"to implement this case";
//					//var is written but not read in transFormula2
//					if (inVar1 != null) {
//						inVars.put(var, inVar1);
//					}
//					if (inVar1 != outVar1) {
//						newAuxVars.add(outVar1);
//					}
//				}
//			} else {
//				TermVariable newOutVar1 = inVar2;
//				inVars.put(var, newOutVar1);
//				replacees.add(outVar1);
//				replacers.add(newOutVar1);
//				if (inVar1 == null) {
//					//var is written but not read in transFormula1
//					inVars.remove(var);
//					if (outVar2 != inVar2) {
//						//var modified by both formulas
//						newAuxVars.add(newOutVar1);
//					}
//					assert (outVar1 != inVar2 && outVar1 != outVar2) : 
//						"accidently same tv is used twice, ask Matthias" +
//						"to implement this case";
//				} else if (inVar1 == outVar1) {
//					//var not modified in transFormula1
//					assert (outVar1 != inVar2 && outVar1 != outVar2) : 
//						"accidently same tv is used twice, ask Matthias" +
//						"to implement this case";
//				} else {
//					if (outVar2 != inVar2) {
//						//var modified by both formulas
//						newAuxVars.add(newOutVar1);
//					}
//					String name = var.getIdentifier() + "_In" + serialNumber;
//					TermVariable newInVar = script.variable(
//										name, outVar1.getSort());
//					allVars.add(newInVar);
//					allVars.add(newInVar);
//					inVars.put(var, newInVar);
//					replacees.add(inVar1);
//					replacers.add(newInVar);
//				}
//				
//			}
//		}
//		
//		for (BoogieVar var : inVars1.keySet()) {
//			if (outVars1.containsKey(var)) {
//				// nothing do to, this var was already considered above 
//			} else {
//				TermVariable outVar2 = outVars2.get(var);
//				TermVariable inVar2 = inVars2.get(var);
//				TermVariable inVar1 = inVars1.get(var);
//				assert (inVar1 != inVar2) : 
//					"accidently same tv is used twice, ask Matthias" +
//					"to implement this case";
//				assert (inVar1 != outVar2) : 
//					"accidently same tv is used twice, ask Matthias" +
//					"to implement this case";
//				if (inVar2 == null) {
//					if (outVar2 == null) {
//						//var does not occur in transFormula2
//						inVars.put(var, inVar1);
//					} else {
//						//var is written but not read in transFormula2
//						inVars.put(var, inVar1);
//					}
//				} else {
//					if (outVar2 == inVar2) {
//						//var not modified in transFormula2
//						inVars.put(var, inVar1);
//					} else {
//						//var modified in transFormula2
//						inVars.put(var, inVar1);
//						newAuxVars.add(inVar2);
//					}
//				}
//			}
//		}
//		
//		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
//		Term[] values = replacers.toArray(new Term[replacers.size()]);
//		Term formula = script.let( vars , values, formula1);
//
//		formula = Util.and(script, formula, formula2);
//		formula = new FormulaUnLet().unlet(formula);
//		NaiveDestructiveEqualityResolution der = 
//								new NaiveDestructiveEqualityResolution(script);
//		//remove auxVars that do not occur in the formula
//		{
//			Set<TermVariable> varsOccurInTerm = new HashSet<TermVariable>(
//										Arrays.asList(formula.getFreeVars()));
//			List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
//			for (TermVariable tv : newAuxVars) {
//				if (!varsOccurInTerm.contains(tv)) {
//					superfluousAuxVars.add(tv);
//				}
//			}
//			newAuxVars.removeAll(superfluousAuxVars);
//		}
//		formula = der.eliminate(newAuxVars, formula);
////		formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
//		LBool isSat = Util.checkSat(script, formula);
//		if (isSat == LBool.UNSAT) {
//			s_Logger.warn("CodeBlock already infeasible");
//			formula = script.term("false");
//		}
//		Infeasibility infeasibility;
//		if (formula == script.term("false")) {
//			infeasibility = Infeasibility.INFEASIBLE;
//		} else {
//			infeasibility = Infeasibility.UNPROVEABLE;
//		}
//		Set<TermVariable> occuringVars = new HashSet<TermVariable>(
//										Arrays.asList(formula.getFreeVars()));
//		{
//			List<BoogieVar> superfluousInVars = new ArrayList<BoogieVar>();
//			for (Entry<BoogieVar, TermVariable> entry  : inVars.entrySet()) {
//				if (!occuringVars.contains(entry.getValue())) {
//					superfluousInVars.add(entry.getKey());
//				}
//			}
//			for (BoogieVar bv : superfluousInVars) {
//				inVars.remove(bv);
//			}
//		}
//		// we may not remove outVars e.g., if x is outvar and formula is true
//		// this means that x is havoced.
//		{
//			List<TermVariable> superfluousAuxVars = new ArrayList<TermVariable>();
//			for (TermVariable tv  : newAuxVars) {
//				if (!occuringVars.contains(tv)) {
//					superfluousAuxVars.add(tv);
//				}
//			}
//			for (TermVariable tv : superfluousAuxVars) {
//				newAuxVars.remove(tv);
//			}
//		}
//		Term closedFormula = computeClosedFormula(formula, 
//				inVars, outVars, newAuxVars, boogie2smt);
//		TransFormula result = new TransFormula(formula, inVars, outVars,
//				newAuxVars, newBranchEncoders, infeasibility, closedFormula);
//		result.getAuxVars().addAll(newAuxVars);
//		assert allVarsContainsFreeVars(allVars, formula);
//		assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, newAuxVars, newBranchEncoders);
//		return result;
//	 
// }
 
	
	
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
			TermVariable[] branchIndicators,
			boolean tranformToCNF,
			TransFormula... transFormulas) {
		s_Logger.debug("parallel composition");
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
				// We can omit this step in the special case where the
				// variable is assigned in all branches.
				if (!newInVars.containsKey(bv) && !assignedInAll(bv, transFormulas)) {
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
		// coincide with the invar in some of the transFormulas
		for (BoogieVar bv : assignedInSomeBranch.keySet()) {
			Sort sort = assignedInSomeBranch.get(bv);
			String outVarName = bv.getIdentifier()+"_Out"+ serialNumber;
			newOutVars.put(bv, script.variable(outVarName, sort));
		}
		
		for (int i=0; i<transFormulas.length; i++) {
			branchEncoders.addAll(transFormulas[i].getBranchEncoders());
			Map<TermVariable,Term> subsitutionMapping = new HashMap<TermVariable, Term>();
			for (TermVariable oldAuxVar : transFormulas[i].getAuxVars()) {
				TermVariable newAuxVar = boogie2smt.getVariableManager().
						constructFreshTermVariable(oldAuxVar.getName(), oldAuxVar.getSort());
				subsitutionMapping.put(oldAuxVar, newAuxVar);
				auxVars.add(newAuxVar);
			}
			for (BoogieVar bv : transFormulas[i].getInVars().keySet()) {
				TermVariable inVar = transFormulas[i].getInVars().get(bv);
				subsitutionMapping.put(inVar, newInVars.get(bv));
			}
			for (BoogieVar bv : transFormulas[i].getOutVars().keySet()) {
				TermVariable outVar = transFormulas[i].getOutVars().get(bv);
				TermVariable inVar = transFormulas[i].getInVars().get(bv);
				
				boolean isAssignedVar = (inVar != outVar);
				if (isAssignedVar) {
					subsitutionMapping.put(outVar, newOutVars.get(bv));
				} else {
					assert subsitutionMapping.containsKey(outVar);
					assert subsitutionMapping.containsValue(newInVars.get(bv));
				}
			}
			Term originalFormula = transFormulas[i].getFormula();
			renamedFormulas[i] = (new Substitution(subsitutionMapping, script)).transform(originalFormula);

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
		TransFormula.removeSuperfluousVars(resultFormula, 
				newInVars, newOutVars, auxVars);
		
		if (tranformToCNF) {
			resultFormula = (new Cnf(script)).transform(resultFormula);
		}
		Term closedFormula = computeClosedFormula(resultFormula, 
				newInVars, newOutVars, auxVars, boogie2smt);
		return new TransFormula(resultFormula, newInVars, newOutVars, auxVars, 
				branchEncoders, inFeasibility, closedFormula);
	}
	
	
	/**
	 * Return true iff bv is assigned in all transFormulas. 
	 */
	private static boolean assignedInAll(BoogieVar bv, TransFormula... transFormulas) {
		for (TransFormula tf : transFormulas) {
			if (!tf.getAssignedVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}



//	/**
//	 * Returns a Transformula that can be seen as procedure summary of the input
//	 * transformula with respect to inParams and outParams.
//	 * We obtain the result by
//	 * - removing all inVars that are not global or not in inParams
//	 * - removing all outVars that are not global or not in outParams
//	 * - considering all oldVars as non-old inVars.
//	 */
//	public static TransFormula procedureSummary(Boogie2SMT boogie2smt, 
//			TransFormula transFormula, Set<BoogieVar> inArgument, Set<BoogieVar> outResult) {
//		Script script = boogie2smt.getScript();
//		Map<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar, TermVariable>();
//		Map<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar, TermVariable>();
//		Set<TermVariable> allVars = new HashSet<TermVariable>();
//		Set<TermVariable> auxVars = new HashSet<TermVariable>();
//		Set<TermVariable> newBranchEncoders = new HashSet<TermVariable>();
//
//		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
//		ArrayList<Term> replacers = new ArrayList<Term>();
//		
//		Set<BoogieVar> inAndOutVars = new HashSet<BoogieVar>();
//		inAndOutVars.addAll(transFormula.getOutVars().keySet());
//		inAndOutVars.addAll(transFormula.getInVars().keySet());
//		
//		for (BoogieVar var : inAndOutVars) {
//			TermVariable outVar = transFormula.getOutVars().get(var);
//			TermVariable inVar = transFormula.getInVars().get(var);
//			
//			if (var.isGlobal()) {
//				if (var.isOldvar()) {
//					BoogieVar nonOldVar = boogie2smt.getSmt2Boogie().
//							getGlobals().get(var.getIdentifier());
//					TermVariable nonOldVarTv;
//					// We use the TermVariable of the nonOld invar.
//					// If the nonOld BoogieVar does not occur we use a fresh
//					// TermVariable
//					if (inVars.containsKey(nonOldVar)) {
//						nonOldVarTv = inVar;
//					} else {
//						nonOldVarTv = getFreshVariable(boogie2smt,var, outVar.getSort()); 
//					}
//					if (transFormula.getInVars().containsKey(var)) {
//						replacees.add(inVar);
//						replacers.add(nonOldVarTv);
//						assert (outVar == null || outVar == inVar) : "oldvar can not be modified";
//					} else {
//						assert transFormula.getOutVars().containsKey(var);
//						replacees.add(outVar);
//						replacers.add(nonOldVarTv);
//					}
//					// Since oldvars may not be modified it is safe to add the
//					// TermVariable only as inVar.
//					assert (!inVars.containsKey(nonOldVar) || 
//							inVars.get(nonOldVarTv) == nonOldVarTv) : 
//								"oldVar should have been replaced by nonOldVar"; 
//					inVars.put(var, nonOldVarTv);
//				} else {
//					if (transFormula.getInVars().containsKey(var)) {
//						inVars.put(var, inVar);
//					}
//					if (transFormula.getOutVars().containsKey(var)) {
//						outVars.put(var, outVar);
//					}
//				}
//			} else {
//				if (outVar != null) {
//					if (outResult.contains(var)) {
//						assert (transFormula.getOutVars().containsKey(var));
//						outVars.put(var, outVar);
//					} else {
//						if (outVar == inVar && inArgument.contains(var)) {
//							// do nothing. special case where outVar does not
//							// become auxVar
//						} else {
//							auxVars.add(outVar);
//						}
//					}
//				}
//				if (inVar != null) {
//					if (inArgument.contains(var) && inVar != null) {
//						assert (transFormula.getInVars().containsKey(var));
//						inVars.put(var, inVar);
//					} else {
//						if (inVar == outVar && outResult.contains(var)) {
//							// do nothing. special case where inVar does not
//							// become
//							// auxVar
//						} else {
//							auxVars.add(inVar);
//						}
//					}
//				}
//			}
//		}
//
//		for (TermVariable auxVar : transFormula.getAuxVars()) {
//			TermVariable newAuxVar = getFreshAuxVariable(boogie2smt, auxVar.getName(), auxVar.getSort());
//			replacees.add(auxVar);
//			replacers.add(newAuxVar);
//			auxVars.add(newAuxVar);
//		}
//		//TODO: These have to be renamed?!?
//		//newBranchEncoders.addAll(transFormula.getBranchEncoders());
//
//
//		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
//		Term[] values = replacers.toArray(new Term[replacers.size()]);
//		Term formula = script.let( vars , values, transFormula.getFormula());
//		//formula = new FormulaUnLet().unlet(formula);
//		
//		
//		formula = new FormulaUnLet().unlet(formula);
//		formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
//		removesuperfluousVariables(inVars, outVars, auxVars, formula);
//		
//		NaiveDestructiveEqualityResolution der = 
//								new NaiveDestructiveEqualityResolution(script);
//		formula = der.eliminate(auxVars, formula);
//		formula = (new SimplifyDDA(script, s_Logger)).getSimplifiedTerm(formula);
//		removesuperfluousVariables(inVars, outVars, auxVars, formula);
//		
//		LBool isSat = Util.checkSat(script, formula);
//		if (isSat == LBool.UNSAT) {
//			s_Logger.warn("CodeBlock already infeasible");
//			formula = script.term("false");
//		}
//		Infeasibility infeasibility;
//		if (formula == script.term("false")) {
//			infeasibility = Infeasibility.INFEASIBLE;
//		} else {
//			infeasibility = Infeasibility.UNPROVEABLE;
//		}
//
//		Term closedFormula = computeClosedFormula(formula, 
//				inVars, outVars, auxVars, boogie2smt);
//		TransFormula result = new TransFormula(formula, inVars, outVars,
//				auxVars, newBranchEncoders, infeasibility, closedFormula);
//
////		assert allVarsContainsFreeVars(allVars, formula);
//		assert freeVarsSubsetInOutAuxBranch(formula, inVars, outVars, auxVars, newBranchEncoders);
//		return result;
//	 
// }
//	

	
	
	
	private void removeOutVar(BoogieVar var) {
		assert this.m_OutVars.containsKey(var) : "illegal to remove variable not that is contained"; 
		TermVariable inVar = m_InVars.get(var);
		TermVariable outVar = m_OutVars.get(var);
		m_OutVars.remove(var);
		if (inVar != outVar) {
			// outVar does not occurs already as inVar, we have to add outVar
			// to auxVars
			m_auxVars.add(outVar);
			boolean removed = m_AssignedVars.remove(var);
			assert (removed);
		} else {
			assert !m_AssignedVars.contains(var);
		}
	}
	
	private void removeInVar(BoogieVar var) {
		assert this.m_InVars.containsKey(var) : "illegal to remove variable not that is contained"; 
		TermVariable inVar = m_InVars.get(var);
		TermVariable outVar = m_OutVars.get(var);
		m_InVars.remove(var);
		if (inVar != outVar) {
			// inVar does not occurs already as outVar, we have to add inVar
			// to auxVars
			m_auxVars.add(inVar);
			assert outVar == null || m_AssignedVars.contains(var);
		} else {
			assert !m_AssignedVars.contains(var);
			if (outVar != null) {
				m_AssignedVars.add(var);
			}
		}
	}

	
	
	
//	/**
//	 * Replace all oldVars that occur in inVars or outVars by corresponding
//	 * non-old global Var. The corresponding non-old Var is the one that
//	 * occurs in the inVars. If inVars does not contain such a variable
//	 * we construct it.
//	 */
//	private static Term replaceOldVarsByInVars(Boogie2SMT boogie2smt, 
//			Map<BoogieVar,TermVariable> inVars, Map<BoogieVar,TermVariable> outVars, Term formula) {
//		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
//		ArrayList<Term> replacers = new ArrayList<Term>();
//		
//		Set<BoogieVar> inAndOutVars = new HashSet<BoogieVar>();
//		inAndOutVars.addAll(outVars.keySet());
//		inAndOutVars.addAll(inVars.keySet());
//		
//		for (BoogieVar var : inAndOutVars) {
//			if (var.isGlobal()) {
//				if (var.isOldvar()) {
//					TermVariable outVar = outVars.get(var);
//					TermVariable inVar = inVars.get(var);
//					BoogieVar nonOldVar = boogie2smt.getSmt2Boogie()
//							.getGlobals().get(var.getIdentifier());
//					TermVariable nonOldVarTv;
//					// We use the TermVariable of the nonOld invar.
//					// If the nonOld BoogieVar does not occur we use a fresh
//					// TermVariable
//					if (inVars.containsKey(nonOldVar)) {
//						nonOldVarTv = inVar;
//					} else {
//						nonOldVarTv = getFreshVariable(boogie2smt, var,
//								outVar.getSort());
//					}
//					if (inVars.containsKey(var)) {
//						replacees.add(inVar);
//						replacers.add(nonOldVarTv);
//						assert (outVar == null || outVar == inVar) : "oldvar can not be modified";
//					} else {
//						assert outVars.containsKey(var);
//						replacees.add(outVar);
//						replacers.add(nonOldVarTv);
//					}
//				}
//			}
//		}
//		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
//		Term[] values = replacers.toArray(new Term[replacers.size()]);
//		Term result = boogie2smt.getScript().let( vars , values, formula);
//		return result;
//	}
	

	/**
	 * Returns TransFormula that describes a sequence of code blocks that 
	 * contains a pending call.
	 * Note the the scope of inVars and outVars is different. Do not compose
	 * the result with the default/intraprocedural composition.
	 * @param beforeCall TransFormula that describes transition relation 
	 * before the call.
	 * @param callTf TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment TransFormula that assigns to oldVars of 
	 * 	modifiable globals the value of the global var.
	 * @param bfterCall TransFormula that describes the transition relation
	 * after the call.
	 */
	public static TransFormula sequentialCompositionWithPendingCall(
			Boogie2SMT boogie2smt, boolean simplify, boolean extPqe, 
			boolean transformToCNF, TransFormula[] beforeCall,
			TransFormula callTf, TransFormula oldVarsAssignment,
			TransFormula bfterCall) {
		s_Logger.debug("sequential composition (pending call) with" + 
				(simplify ? "" : "out") + " formula simplification");
		TransFormula callAndBeforeTF;
		{
			List<TransFormula> callAndBeforeList =  new ArrayList<TransFormula>(Arrays.asList(beforeCall));
			callAndBeforeList.add(callTf);
			TransFormula[] callAndBeforeArray = 
					callAndBeforeList.toArray(new TransFormula[0]);
			callAndBeforeTF = sequentialComposition(boogie2smt, simplify, 
					extPqe, transformToCNF, callAndBeforeArray);

			// remove outVars that relate to scope of caller
			// - local vars that are no inParams of callee
			// - oldVars of variables that can be modified by callee
			List<BoogieVar> varsToRemove = new ArrayList<BoogieVar>();
			for (BoogieVar bv : callAndBeforeTF.getOutVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar()
							&& oldVarsAssignment.getOutVars().containsKey(bv)) {
						varsToRemove.add(bv);
					}
				} else {
					if (!callTf.getOutVars().containsKey(bv)) {
						// bv is local but not inParam of called procedure
						varsToRemove.add(bv);
					}
				}
			}
			for (BoogieVar bv : varsToRemove) {
				callAndBeforeTF.removeOutVar(bv);
			}
		}

		TransFormula oldAssignAndAfterTF;
		{
			List<TransFormula> oldAssignAndAfterList = new ArrayList<TransFormula>(Arrays.asList(bfterCall));
			oldAssignAndAfterList.add(0, oldVarsAssignment);
			TransFormula[] oldAssignAndAfterArray = 
					oldAssignAndAfterList.toArray(new TransFormula[0]);
			oldAssignAndAfterTF = sequentialComposition(boogie2smt, simplify, 
					extPqe, transformToCNF, oldAssignAndAfterArray);

			// remove inVars that relate to scope of callee
			// - local vars that are no inParams of callee
			// - oldVars of variables that can be modified by callee
			List<BoogieVar> varsToRemove = new ArrayList<BoogieVar>();
			for (BoogieVar bv : oldAssignAndAfterTF.getInVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar()
							&& oldVarsAssignment.getOutVars().containsKey(bv)) {
						varsToRemove.add(bv);
					}
				} else {
					if (!callTf.getOutVars().containsKey(bv)) {
						// bv is local but not inParam of called procedure
						varsToRemove.add(bv);
					}
				}
			}
			for (BoogieVar bv : varsToRemove) {
				oldAssignAndAfterTF.removeInVar(bv);
			}
		}

		TransFormula result = sequentialComposition(boogie2smt, simplify, extPqe,
				transformToCNF,
				callAndBeforeTF, oldAssignAndAfterTF);
		return result;
	}
	
	

	/**
	 * Returns a Transformula that can be seen as procedure summary.
	 * @param callTf TransFormula that describes parameter assignment of call.
	 * @param oldVarsAssignment TransFormula that assigns to oldVars of 
	 * 	modifiable globals the value of the global var.
	 * @param procedureTf TransFormula that describes the procdure.
	 * @param returnTf TransFormula that assigns the result of the procedure call.
	 */
	public static TransFormula sequentialCompositionWithCallAndReturn(
			Boogie2SMT boogie2smt, boolean simplify, boolean extPqe, 
			boolean transformToCNF,
			TransFormula callTf,
			TransFormula oldVarsAssignment, TransFormula procedureTf,
			TransFormula returnTf) {
		s_Logger.debug("sequential composition (call/return) with" + 
			(simplify ? "" : "out") + " formula simplification");
		TransFormula result = sequentialComposition(boogie2smt, simplify, extPqe,
				transformToCNF,	callTf, oldVarsAssignment, procedureTf, returnTf);
		{
			List<BoogieVar> inVarsToRemove = new ArrayList<BoogieVar>();
			for (BoogieVar bv : result.getInVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar()
							&& oldVarsAssignment.getOutVars().containsKey(bv)) {
						inVarsToRemove.add(bv);
					}
				} else {
					if (!callTf.getInVars().containsKey(bv)) {
						// bv is local but not argument of procedure call
						inVarsToRemove.add(bv);
					}
				}
			}
			for (BoogieVar bv : inVarsToRemove) {
				result.removeInVar(bv);
			}
		}
		{
			List<BoogieVar> outVarsToRemove = new ArrayList<BoogieVar>();
			for (BoogieVar bv : result.getOutVars().keySet()) {
				if (bv.isGlobal()) {
					if (bv.isOldvar()
							&& oldVarsAssignment.getOutVars().containsKey(bv)) {
						outVarsToRemove.add(bv);
					}
				} else {
					if (!returnTf.getOutVars().containsKey(bv)) {
						// bv is local but not result of procedure call
						outVarsToRemove.add(bv);
					}
				}
			}
			for (BoogieVar bv : outVarsToRemove) {
				result.removeOutVar(bv);
			}
		}
		// Add all inVars (bv,tv) of the call to outVars of the result except 
		// if there already an outVar (bv,tv').
		// (Because in this case the variable bv was reassigned by the summary,
		// e.g. in the case where bv is a global variable that can be modified
		// by the procedure or is bv is a variable that is assigned by the
		// call. 
		{
			for (BoogieVar bv : callTf.getInVars().keySet()) {
				if (!result.getOutVars().containsKey(bv)) {
					result.m_OutVars.put(bv, result.getInVars().get(bv));
				}
				
			}
		}
		assert(isIntraprocedural(result));
		return result;
	}
	
	/**
	 * Returns true iff all local variables in tf belong to a single procedure.
	 */
	static boolean isIntraprocedural(final TransFormula tf) {
		final Set<String> procedures = new HashSet<String>();
		for (BoogieVar bv : tf.getInVars().keySet()) {
			if (!bv.isGlobal()) {
				procedures.add(bv.getProcedure());
			}
		}
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (!bv.isGlobal()) {
				procedures.add(bv.getProcedure());
			}
		}
		return procedures.size() <= 1;
	}
	
	
	
	 

}
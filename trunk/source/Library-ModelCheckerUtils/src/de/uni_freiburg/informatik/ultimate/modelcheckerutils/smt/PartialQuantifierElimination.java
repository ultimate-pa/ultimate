package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Cnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Dnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfIrd;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfUsr;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Try to eliminate existentially quantified variables in terms. Therefore we
 * use that the term ∃v.v=c∧φ[v] is equivalent to term φ[c]. Resp. we use that
 * the term ∀v.v!=c∨φ[v] is equivalent to term φ[c].
 */
public class PartialQuantifierElimination {

	static final boolean USE_UPD = true;
	static final boolean USE_IRD = true;
	static final boolean USE_SOS = true;
	static final boolean USE_USR = true;
	
	
	/**
	 * Compose term with outer operation of a XNF.
	 * For the case of existential quantification:
	 * Compose disjuncts to a disjunction.
	 */
	private static Term composeXjunctsOuter(Script script, int quantifier, Term[] xjunctsOuter) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = Util.or(script, xjunctsOuter);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = Util.and(script, xjunctsOuter);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}

	/**
	 * Compose term with inner operation of a XNF.
	 * For the case of existential quantification:
	 * Compose atoms to a conjunction.
	 */
	private static Term composeXjunctsInner(Script script, int quantifier, Term[] xjunctsInner) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = Util.and(script, xjunctsInner);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = Util.or(script, xjunctsInner);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}
	
	/**
	 * Get all parameters of the outer operation of a XNF
	 * For the case of existential quantification:
	 * Get all disjuncts of a formula in DNF. 
	 * (conjuncts of CNF for case of universal quantification)
	 */
	private static Term[] getXjunctsOuter(int quantifier, Term xnf) {
		Term[] xjunctsOuter;
		if (quantifier == QuantifiedFormula.EXISTS) {
			xjunctsOuter = SmtUtils.getDisjuncts(xnf);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			xjunctsOuter = SmtUtils.getConjuncts(xnf);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return xjunctsOuter;
	}
	
	/**
	 * Get all parameters of the inner operation of a XNF
	 * For the case of existential quantification:
	 * Get all conjuncts of a conjunction. 
	 * (disjuncts of disjunction in case of universal quantification)
	 */
	private static Term[] getXjunctsInner(int quantifier, Term xnf) {
		Term[] xjunctsOuter;
		if (quantifier == QuantifiedFormula.EXISTS) {
			xjunctsOuter = SmtUtils.getConjuncts(xnf);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			xjunctsOuter = SmtUtils.getDisjuncts(xnf);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return xjunctsOuter;
	}

	

	/**
	 * Returns equivalent formula. Quantifier is dropped if quantified variable
	 * not in formula. Quantifier is eliminated if this can be done by using a
	 * naive "destructive equality resolution".
	 * 
	 * @param services
	 * @param logger
	 */
	public static Term quantifier(IUltimateServiceProvider services, Logger logger, Script script, int quantifier,
			TermVariable[] vars, Term body, Term[]... patterns) {
		Set<TermVariable> varSet = new HashSet<TermVariable>(Arrays.asList(vars));
		body = elim(script, quantifier, varSet, body, services, logger);
		if (varSet.isEmpty()) {
			return body;
		} else {
			return script.quantifier(quantifier, varSet.toArray(new TermVariable[varSet.size()]), body, patterns);
		}

	}

	public static Term elim(Script script, int quantifier, final Set<TermVariable> eliminatees, final Term term,
			IUltimateServiceProvider services, Logger logger) {
		Set<TermVariable> occuringVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			TermVariable tv = it.next();
			if (!occuringVars.contains(tv)) {
				it.remove();
			}
		}
		if (eliminatees.isEmpty()) {
			return term;
		}
		Term result;

		// transform to DNF (resp. CNF)
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = (new Dnf(script, services)).transform(term);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = (new Cnf(script, services)).transform(term);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		if (result instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula) result;
			if (qf.getQuantifier() != quantifier) {
				throw new UnsupportedOperationException("quantifier alternation unsupported");
			}
			eliminatees.addAll(Arrays.asList(qf.getVariables()));
			result = qf.getSubformula();
		}

		// apply Destructive Equality Resolution
		Term termAfterDER;
		{
			XnfDer xnfDer = new XnfDer(script, services);
			Term[] oldParams = getXjunctsOuter(quantifier, result);
			Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				Set<TermVariable> eliminateesDER = new HashSet<TermVariable>(eliminatees);
				Term[] oldAtoms = getXjunctsInner(quantifier, oldParams[i]);
				newParams[i] = composeXjunctsInner(script, quantifier, 
						xnfDer.tryToEliminate(quantifier, oldAtoms, eliminateesDER));
			}
			termAfterDER = composeXjunctsOuter(script, quantifier, newParams);
			result = termAfterDER;
			Set<TermVariable> remainingAfterDER = new HashSet<TermVariable>(eliminatees);
			remainingAfterDER.retainAll(Arrays.asList(result.getFreeVars()));
			eliminatees.retainAll(remainingAfterDER);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// apply Infinity Restrictor Drop
		Term termAfterIRD;
		if (USE_IRD) {
			XnfIrd xnfIRD = new XnfIrd(script, services);
			Term[] oldParams = getXjunctsOuter(quantifier, result);
			Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				Set<TermVariable> eliminateesIRD = new HashSet<TermVariable>(eliminatees);
				Term[] oldAtoms = getXjunctsInner(quantifier, oldParams[i]);
				newParams[i] = composeXjunctsInner(script, quantifier, 
						xnfIRD.tryToEliminate(quantifier, oldAtoms, eliminateesIRD));
			}
			termAfterIRD = composeXjunctsOuter(script, quantifier, newParams);
			result = termAfterIRD;
			Set<TermVariable> remainingAfterIRD = new HashSet<TermVariable>(eliminatees);
			remainingAfterIRD.retainAll(Arrays.asList(result.getFreeVars()));
			eliminatees.retainAll(remainingAfterIRD);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// apply Unconnected Parameter Deletion
		Term termAfterUPD = null;
		if (USE_UPD) {
			Term[] oldParams = getXjunctsOuter(quantifier, result);
			Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				Set<TermVariable> eliminateesUPD = new HashSet<TermVariable>(eliminatees);
				newParams[i] = updSimple(script, quantifier, oldParams[i], eliminateesUPD, logger);
			}
			termAfterUPD = composeXjunctsOuter(script, quantifier, newParams);
			result = termAfterUPD;
			Set<TermVariable> remainingAfterUPD = new HashSet<TermVariable>(eliminatees);
			remainingAfterUPD.retainAll(Arrays.asList(result.getFreeVars()));
			eliminatees.retainAll(remainingAfterUPD);
		}

		if (eliminatees.isEmpty()) {
			return result;
		}
		final boolean sosChangedTerm;
		// apply Store Over Select
		if (USE_SOS) {
			Set<TermVariable> remainingAndNewAfterSOS = new HashSet<TermVariable>();
			Term termAfterSOS;
			Term[] oldParams = getXjunctsOuter(quantifier, result);
			Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				Set<TermVariable> eliminateesSOS = new HashSet<TermVariable>(eliminatees);
				newParams[i] = sos(script, quantifier, oldParams[i], eliminateesSOS, logger, services);
				remainingAndNewAfterSOS.addAll(eliminateesSOS);
			}
			termAfterSOS = composeXjunctsOuter(script, quantifier, newParams);
			sosChangedTerm = (result != termAfterSOS);
			result = termAfterSOS;
			eliminatees.retainAll(remainingAndNewAfterSOS);
			eliminatees.addAll(remainingAndNewAfterSOS);
		} else {
			sosChangedTerm = false;
		}

		if (eliminatees.isEmpty()) {
			return result;
		}

		// simplification
		result = SmtUtils.simplify(script, result, services);

		// (new SimplifyDDA(script)).getSimplifiedTerm(result);
		eliminatees.retainAll(Arrays.asList(result.getFreeVars()));

		// if (!eliminateesBeforeSOS.containsAll(eliminatees)) {
		// SOS introduced new variables that should be eliminated
		if (sosChangedTerm) {
			// if term was changed by SOS new elimination might be possible
			// Before the implementation of IRD we only retried elimination
			// if SOS introduced more quantified variables.
			result = elim(script, quantifier, eliminatees, result, services, logger);
		}
		
		if (eliminatees.isEmpty()) {
			return result;
		}
		
		assert Arrays.asList(result.getFreeVars()).containsAll(eliminatees) : "superficial variables";
		
		if (USE_USR) {
			XnfUsr xnfUsr = new XnfUsr(script, services);
			Term[] oldParams = getXjunctsOuter(quantifier, result);
			Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				Set<TermVariable> eliminateesUsr = new HashSet<TermVariable>(eliminatees);
				Term[] oldAtoms = getXjunctsInner(quantifier, oldParams[i]);
				newParams[i] = composeXjunctsInner(script, quantifier, 
						xnfUsr.tryToEliminate(quantifier, oldAtoms, eliminateesUsr));
			}
			Term termAfterUsr = composeXjunctsOuter(script, quantifier, newParams);
			result = termAfterUsr;
			if (!xnfUsr.getAffectedEliminatees().isEmpty()) {
				result = elim(script, quantifier, eliminatees, result, services, logger);
			}
		}
		
		return result;
	}





	public static Term sos(Script script, int quantifier, Term term, Set<TermVariable> eliminatees, Logger logger,
			IUltimateServiceProvider services) {
		Term result = term;
		Set<TermVariable> overallAuxVars = new HashSet<TermVariable>();
		Iterator<TermVariable> it = eliminatees.iterator();
		while (it.hasNext()) {
			TermVariable tv = it.next();
			if (tv.getSort().isArraySort()) {
				// if (quantifier != QuantifiedFormula.EXISTS) {
				// // return term;
				// throw new
				// UnsupportedOperationException("QE for universal quantified arrays not implemented yet.");
				// }
				Set<TermVariable> thisIterationAuxVars = new HashSet<TermVariable>();
				Term elim = (new ElimStore3(script, services)).elim(quantifier, tv, result, thisIterationAuxVars);
				logger.debug(new DebugMessage("eliminated quantifier via SOS for {0}, additionally introduced {1}", tv,
						thisIterationAuxVars));
				overallAuxVars.addAll(thisIterationAuxVars);
				// if (Arrays.asList(elim.getFreeVars()).contains(tv)) {
				// elim = (new ElimStore3(script)).elim(tv, result,
				// thisIterationAuxVars);
				// }
				assert !Arrays.asList(elim.getFreeVars()).contains(tv) : "var is still there";
				result = elim;
			}
		}
		eliminatees.addAll(overallAuxVars);
		return result;
	}

	/**
	 * Try to eliminate the variables vars = {x_1,...,x_n} in term φ_1∧...∧φ_m.
	 * Therefore we use the following approach, which we call Unconnected
	 * Parameter Drop. If X is a subset of {x_1,...,x_n} and Φ is a subset
	 * {φ_1,...,φ_m} such that - variables in X occur only in term of Φ, and -
	 * terms in Φ contain only variables of X, and - the conjunction of all term
	 * in Φ is satisfiable. Then we can remove the conjuncts Φ and the
	 * quantified variables X from φ_1∧...∧φ_m and obtain an equivalent formula.
	 * 
	 * Is only sound if there are no uninterpreted function symbols in the term
	 * TODO: extend this to uninterpreted function symbols (for soundness)
	 * 
	 * @param logger
	 */
	public static Term updSimple(Script script, int quantifier, Term term, Set<TermVariable> vars, Logger logger) {
		Set<TermVariable> occuringVars = new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
		vars.retainAll(occuringVars);
		Set<Term> parameters;
		if (quantifier == QuantifiedFormula.EXISTS) {
			parameters = new HashSet<Term>(Arrays.asList(SmtUtils.getConjuncts(term)));
		} else if (quantifier == QuantifiedFormula.FORALL) {
			parameters = new HashSet<Term>(Arrays.asList(SmtUtils.getDisjuncts(term)));
		} else {
			throw new AssertionError("unknown quantifier");
		}
		ConnectionPartition connection = new ConnectionPartition(parameters);
		List<TermVariable> removeableTvs = new ArrayList<TermVariable>();
		List<TermVariable> unremoveableTvs = new ArrayList<TermVariable>();
		List<Term> removeableTerms = new ArrayList<Term>();
		List<Term> unremoveableTerms = new ArrayList<Term>();
		for (Set<Term> connectedTerms : connection.getConnectedVariables()) {
			Set<TermVariable> connectedVars = SmtUtils.getFreeVars(connectedTerms);
			boolean isSuperfluous;
			if (quantifier == QuantifiedFormula.EXISTS) {
				isSuperfluous = isSuperfluousConjunction(script, connectedTerms, connectedVars, vars);
			} else if (quantifier == QuantifiedFormula.FORALL) {
				isSuperfluous = isSuperfluousDisjunction(script, connectedTerms, connectedVars, vars);
			} else {
				throw new AssertionError("unknown quantifier");
			}
			if (isSuperfluous) {
				removeableTvs.addAll(connectedVars);
				removeableTerms.addAll(connectedTerms);
			} else {
				unremoveableTvs.addAll(connectedVars);
				unremoveableTerms.addAll(connectedTerms);
			}
		}
		List<Term> termsWithoutTvs = connection.getTermsWithOutTvs();
		assert occuringVars.size() == removeableTvs.size() + unremoveableTvs.size();
		assert parameters.size() == removeableTerms.size() + unremoveableTerms.size() + termsWithoutTvs.size();
		for (Term termWithoutTvs : termsWithoutTvs) {
			LBool sat = Util.checkSat(script, termWithoutTvs);
			if (sat == LBool.UNSAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					vars.clear();
					return script.term("false");
				} else if (quantifier == QuantifiedFormula.FORALL) {
					// we drop this term its equivalent to false
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else if (sat == LBool.SAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					// we drop this term its equivalent to true
				} else if (quantifier == QuantifiedFormula.FORALL) {
					vars.clear();
					return script.term("true");
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				throw new AssertionError("expecting sat or unsat");
			}
		}
		if (removeableTerms.isEmpty()) {
			logger.debug(new DebugMessage("not eliminated quantifier via UPD for {0}", occuringVars));
			return term;
		} else {
			vars.removeAll(removeableTvs);
			logger.debug(new DebugMessage("eliminated quantifier via UPD for {0}", removeableTvs));
			Term result;
			if (quantifier == QuantifiedFormula.EXISTS) {
				result = Util.and(script, unremoveableTerms.toArray(new Term[unremoveableTerms.size()]));
			} else if (quantifier == QuantifiedFormula.FORALL) {
				result = Util.or(script, unremoveableTerms.toArray(new Term[unremoveableTerms.size()]));
			} else {
				throw new AssertionError("unknown quantifier");
			}
			return result;
		}
	}

	/**
	 * Return true if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is satisfiable.
	 */
	public static boolean isSuperfluousConjunction(Script script, Set<Term> terms, Set<TermVariable> connectedVars,
			Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			Term conjunction = Util.and(script, terms.toArray(new Term[terms.size()]));
			if (Util.checkSat(script, conjunction) == LBool.SAT) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Return true if connectedVars is a subset of quantifiedVars and the
	 * disjunction of terms is not valid.
	 */
	public static boolean isSuperfluousDisjunction(Script script, Set<Term> terms, Set<TermVariable> connectedVars,
			Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			Term disjunction = Util.or(script, terms.toArray(new Term[terms.size()]));
			if (Util.checkSat(script, Util.not(script, disjunction)) == LBool.SAT) {
				return true;
			}
		}
		return false;
	}











	/**
	 * Find term φ such that term implies tv == φ.
	 * 
	 * @param logger
	 */
	private static Term findEqualTermExists(TermVariable tv, Term term, Logger logger) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol sym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (sym.getName().equals("=")) {
				int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params, logger);
				if (tvOnOneSideOfEquality == -1) {
					return null;
				} else {
					assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
					return params[tvOnOneSideOfEquality];
				}
			} else if (sym.getName().equals("and")) {
				for (Term param : params) {
					Term equalTerm = findEqualTermExists(tv, param, logger);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
			} else {
				return null;
			}
		} else {
			return null;
		}
	}

	/**
	 * Find term φ such that tv != φ implies term
	 * 
	 * @param logger
	 */
	private static Term findEqualTermForall(TermVariable tv, Term term, Logger logger) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol sym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (sym.getName().equals("not")) {
				assert params.length == 1;
				if (params[0] instanceof ApplicationTerm) {
					appTerm = (ApplicationTerm) params[0];
					sym = appTerm.getFunction();
					params = appTerm.getParameters();
					if (sym.getName().equals("=")) {
						int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params, logger);
						if (tvOnOneSideOfEquality == -1) {
							return null;
						} else {
							assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
							return params[tvOnOneSideOfEquality];
						}
					} else {
						return null;
					}
				} else {
					return null;
				}
			} else if (sym.getName().equals("or")) {
				for (Term param : params) {
					Term equalTerm = findEqualTermForall(tv, param, logger);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
			} else {
				return null;
			}
		} else {
			return null;
		}
	}

	/**
	 * return
	 * <ul>
	 * <li>0 if right hand side of equality is tv and left hand side does not
	 * contain tv
	 * <li>1 if left hand side of equality is tv and right hand side does not
	 * contain tv
	 * <li>-1 otherwise
	 * </ul>
	 * 
	 * @param logger
	 * 
	 */
	private static int tvOnOneSideOfEquality(TermVariable tv, Term[] params, Logger logger) {
		if (params.length != 2) {
			logger.warn("Equality of length " + params.length);
		}
		if (params[0] == tv) {
			final boolean rightHandSideContainsTv = Arrays.asList(params[1].getFreeVars()).contains(tv);
			if (rightHandSideContainsTv) {
				return -1;
			} else {
				return 1;
			}
		} else if (params[1] == tv) {
			final boolean leftHandSideContainsTv = Arrays.asList(params[0].getFreeVars()).contains(tv);
			if (leftHandSideContainsTv) {
				return -1;
			} else {
				return 0;
			}
		}
		return -1;
	}
	
	
	
//	public static Term usr(Script script, int quantifier, Term term, Collection<TermVariable> eliminatees, Set<TermVariable> affectedEliminatees, Logger logger) {
//		Term[] oldParams;
//		if (quantifier == QuantifiedFormula.EXISTS) {
//			oldParams = SmtUtils.getConjuncts(term);
//		} else if (quantifier == QuantifiedFormula.FORALL) {
//			oldParams = SmtUtils.getDisjuncts(term);
//		} else {
//			throw new AssertionError("unknown quantifier");
//		}
//		HashRelation<TermVariable, Term> var2arrays = new HashRelation<TermVariable, Term>();
//		HashRelation<TermVariable, Term> var2parameters = new HashRelation<TermVariable, Term>();
//		for (Term param : oldParams) {
//			List<MultiDimensionalSelect> slects = MultiDimensionalSelect.extractSelectDeep(param, false);
//			for (MultiDimensionalSelect mds : slects) {
//				Set<TermVariable> indexFreeVars = mds.getIndex().getFreeVars();
//				for (TermVariable tv : indexFreeVars) {
//					if (eliminatees.contains(tv)) {
//						var2arrays.addPair(tv, mds.getArray());
//						var2parameters.addPair(tv, param);
//					}
//				}
//			}
//		}
//		Set<Term> superfluousParams = new HashSet<Term>();
//		for (TermVariable eliminatee : var2arrays.getDomain()) {
//			if (var2arrays.getImage(eliminatee).size() == 1 &&
//					var2parameters.getImage(eliminatee).size() == 1) {
//				superfluousParams.addAll(var2parameters.getImage(eliminatee));
//				affectedEliminatees.add(eliminatee);
//			}
//		}
//		ArrayList<Term> resultParams = new ArrayList<Term>();
//		for (Term oldParam : oldParams) {
//			if (!superfluousParams.contains(oldParam)) {
//				resultParams.add(oldParam);
//			}
//		}
//		return Util.and(script, resultParams.toArray(new Term[resultParams.size()]));
//	}
}

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IPredicateCoverageChecker;

public class SdHoareTripleChecker {
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	
	private final EdgeCheckerBenchmarkGenerator m_EdgeCheckerBenchmark;
	private final IPredicateCoverageChecker m_PredicateCoverageChecker;
	
	
	public SdHoareTripleChecker(ModifiableGlobalVariableManager modGlobVarManager, 
			IPredicateCoverageChecker predicateCoverageChecker) {
		m_ModifiableGlobalVariableManager = modGlobVarManager;
		m_EdgeCheckerBenchmark = new EdgeCheckerBenchmarkGenerator();
		m_PredicateCoverageChecker = predicateCoverageChecker;
	}
	
	public SdHoareTripleChecker(ModifiableGlobalVariableManager modGlobVarManager) {
		this(modGlobVarManager, null);
	}
	
	
	public EdgeCheckerBenchmarkGenerator getEdgeCheckerBenchmark() {
		return m_EdgeCheckerBenchmark;
	}
	
	
	
	private static boolean varSetDisjoint(Set<BoogieVar> set1, Set<BoogieVar> set2) {
		if (set1.size() < set2.size()) {
			for (BoogieVar bv : set1) {
				if (set2.contains(bv)) {
					return false;
				}
			}
		} else {
			for (BoogieVar bv : set2) {
				if (set1.contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	
	
	/**
	 * Idea: If the formula of the code block is satisfiable,
	 * the predecessor is satisfiable and the vars of predecessor are disjoint
	 * from the inVars of the code block, then a transition to false is not
	 * inductive.
	 * Idea with UNKNOWN: if the solver was unable to decide feasibility of cb, 
	 * the predecessor is satisfiable and the vars of predecessor are disjoint
	 * from the inVars of the code block, then the solver will be unable to
	 * show that a transition to false is inductive. 
	 *
	 * FIXME: Check for precondition false, not for precondition true.
	 */
	public Validity sdecInternalToFalse(IPredicate pre, CodeBlock cb) {
		Infeasibility infeasiblity = cb.getTransitionFormula().isInfeasible();
		if (infeasiblity == Infeasibility.UNPROVEABLE) {
			if (SmtUtils.isTrue(pre.getFormula())) {
				m_EdgeCheckerBenchmark.getSdCounter().incIn();
				return Validity.UNKNOWN;
			} else {
				if (varsDisjoinedFormInVars(pre, cb)) {
					m_EdgeCheckerBenchmark.getSdCounter().incIn();
					return Validity.INVALID;
				} else  {
					return null;
				}
			}
						
		} else if (infeasiblity == Infeasibility.INFEASIBLE) {
			m_EdgeCheckerBenchmark.getSdCounter().incIn();
			return Validity.VALID;
		} else if (infeasiblity == Infeasibility.NOT_DETERMINED) {
			return null;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	
	
	
	/**
	 * Returns true iff the variables occurring in state are disjoint from the
	 * inVars of CodeBlock letter.
	 * @param state
	 * @param symbol
	 * @return
	 */
	private boolean varsDisjoinedFormInVars(IPredicate state, CodeBlock letter) {
		for (BoogieVar bv : state.getVars()) {
			if (letter.getTransitionFormula().getInVars().containsKey(bv)) {
				return false;
			}
		}
		return true;
	}
	
	
	/**
	 * FIXME: Mention assumptions.
	 * Idea: If 
	 * <ul>
	 * <li> the formula of the code block is satisfiable, 
	 * <li> the predecessor is satisfiable,
	 * <li> the successor is not unsatisfiable,
	 * <li> the variables of the predecessor are disjoint from the invars
	 * of the code block, and
	 * <li> the variables of the successor are disjoint from the outvars of the
	 * code block, from the invars of the code block and from the vars of the
	 * predecessor,
	 * </ul>
	 * then a transition (pre, cb, post) is not inductive. 
	 *
	 * FIXME: Check for preconditions, postcondition? Check at least for
	 * infeasibility flag of TransFormula.
	 */
	public Validity sdecInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		if (m_PredicateCoverageChecker != null) {
			Validity sat = MonolithicHoareTripleChecker.lbool2httv(m_PredicateCoverageChecker.isCovered(pre, post));
			if (sat == Validity.VALID) {
				if (Collections.disjoint(pre.getVars(), cb.getTransitionFormula().getAssignedVars())) {
					return Validity.VALID;
				}
			}
		}
		for (BoogieVar bv : pre.getVars()) {
			if (cb.getTransitionFormula().getInVars().containsKey(bv)) {
				return null;
			}
		}
		for (BoogieVar bv : post.getVars()) {
//			if (pre.getVars().contains(bv)) {
//				return null;
//			} else 
			if (cb.getTransitionFormula().getInVars().containsKey(bv)) {
				return null;
			} else if (cb.getTransitionFormula().getOutVars().containsKey(bv)) {
				return null;
			}
		}
		// now, we know that vars of pre and post are both disjoint from the
		/// vars of cb. Edge is inductive iff pre implies post
		if (m_PredicateCoverageChecker != null) {
			Validity sat = MonolithicHoareTripleChecker.lbool2httv(m_PredicateCoverageChecker.isCovered(pre, post));
			if (sat == Validity.VALID) {
				return Validity.VALID;
			}
		} else {
			if (!Collections.disjoint(pre.getVars(), post.getVars())) {
				return null;
			}
		}
		m_EdgeCheckerBenchmark.getSdCounter().incIn();
		return Validity.INVALID;
	}
	
	
//	public boolean sdecSatAssured(Predicate pre, CodeBlock cb) {
//		Set<BoogieVar> inVars = cb.getTransitionFormula().getInVars().keySet();
//		 if (varSetDisjoint(pre.getVars(), inVars)) {
//			 return true;
//		 }
//		 else return false;
//	}
	
	
	public Validity sdLazyEcInteral(IPredicate pre, CodeBlock cb, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecInteral(pre, cb, post);
		}
		for (BoogieVar bv : post.getVars()) {
			if (pre.getVars().contains(bv)) {
				continue;
			} else if (cb.getTransitionFormula().getInVars().containsKey(bv)) {
				continue;
			} else if (cb.getTransitionFormula().getOutVars().containsKey(bv)) {
				continue;
			}
			// occurs neither in pre not in codeBlock, probably unsat
			m_EdgeCheckerBenchmark.getSdLazyCounter().incIn();
			return Validity.INVALID;
		}
		return null;
	}
	
	public Validity sdecCallToFalse(IPredicate pre, CodeBlock cb) {
		// TODO:
		// there could be a contradiction if the Call is not a simple call
		// but interprocedural sequential composition 			
		if (cb instanceof Call) {
			m_EdgeCheckerBenchmark.getSdCounter().incCa();
			return Validity.INVALID;
		} else {
			return null;
		}
	}
	
	public Validity sdecCall(IPredicate pre, CodeBlock cb, IPredicate post) {
		for (BoogieVar bv : post.getVars()) {
			if (bv.isOldvar()) {
				//if oldVar occurs this edge might be inductive since 
				// old(g)=g is true
				return null;
			} else if (bv.isGlobal()) {
				assert !bv.isOldvar();
				if (pre.getVars().contains(bv)) {
					return null;
				}
			}
		}
		//workaround see preHierIndependent()
		TransFormula locVarAssignTf = cb.getTransitionFormula();
		if (!varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return null;
		}
		if (preHierIndependent(post, pre, (Call) cb)) {
			m_EdgeCheckerBenchmark.getSdCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}
	
	public Validity sdLazyEcCall(IPredicate pre, Call cb, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecCall(pre, cb, post);
		}
		TransFormula locVarAssignTf = cb.getTransitionFormula();
		boolean argumentsRestrictedByPre = 
				!varSetDisjoint(locVarAssignTf.getInVars().keySet(), pre.getVars());
		for (BoogieVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				continue;
			} else {
				if (locVarAssignTf.getAssignedVars().contains(bv)) {
					if (argumentsRestrictedByPre) {
						continue;
					}
				}
			}
			m_EdgeCheckerBenchmark.getSdLazyCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}
	
	
	public Validity sdecReturn(IPredicate pre, IPredicate hier, CodeBlock cb, IPredicate post) {
		Return ret = (Return) cb;
		Call call = ret.getCorrespondingCall();
		if (hierPostIndependent(hier, ret, post) 
				&& preHierIndependent(pre, hier, call)
				&& prePostIndependent(pre, ret, post)) {
			m_EdgeCheckerBenchmark.getSdCounter().incRe();
			return Validity.INVALID;

		}
		return null;
	}
	
	
	public Validity sdLazyEcReturn(IPredicate pre, IPredicate hier, Return cb, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecReturn(pre, hier, cb, post);
		}
		Call call = cb.getCorrespondingCall();
		Set<BoogieVar> assignedVars = cb.getTransitionFormula().getAssignedVars();
		
		/*
		 * Old Version. Does not work if param set to constant.
		 * 
		// If there is an argument in post which is not assigned by return
		// and an parameter is in pre we have to return UNKNOWN
		Map<BoogieVar, TermVariable> arguments = call.getTransitionFormula().getInVars();
		Set<BoogieVar> parameters = call.getTransitionFormula().getAssignedVars();
		if (!varSetDisjoint(parameters, pre.getVars())) {
			for (BoogieVar bv : arguments.keySet()) {
				if (post.getVars().contains(bv) && !assignedVars.contains(bv)) {
					m_LazyEdgeCheckQueries++;
					return null;
				}
			}
		}
		 * 
		 */
		Set<BoogieVar> parameters = call.getTransitionFormula().getAssignedVars();
		if (!varSetDisjoint(parameters, pre.getVars())) {
			return null;
		}

		String proc = call.getCallStatement().getMethodName();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);
		boolean assignedVarsRestrictedByPre = 
				!varSetDisjoint(cb.getTransitionFormula().getInVars().keySet(), pre.getVars());
		for (BoogieVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (hier.getVars().contains(bv)) {
						continue;
					}
				} else {
					if (modifiableGlobals.contains(bv)) {
						if (pre.getVars().contains(bv)) {
							continue;
						}
					} else {
						if (hier.getVars().contains(bv)) {
							continue;
						}
						if (pre.getVars().contains(bv)) {
							continue;
						}

						
					}
					if (assignedVars.contains(bv)) {
						if (assignedVarsRestrictedByPre) {
							continue;
						}
					}
				}
				
			} else {
				if (assignedVars.contains(bv)) {
					if (assignedVarsRestrictedByPre) {
						continue;
					}
				} else {
					if (hier.getVars().contains(bv)) {
						continue;
					}
				}
			}
			m_EdgeCheckerBenchmark.getSdLazyCounter().incRe();
			return Validity.INVALID;
		}
		return null;
	}
	

	private boolean preHierIndependent(IPredicate pre, IPredicate hier, Call call) {
		TransFormula locVarAssignTf = call.getTransitionFormula();
		//TODO: Matthias 7.10.2012 I hoped following would be sufficient.
		// But this is not sufficient when constant assigned to invar
		// e.g. pre is x!=0 and call is x_Out=1. Might be solved with
		// dataflow map.
		// 8.10.2012 consider also case where inVar is non-modifiable global
		// which does not occur in hier, but in pre
//		if (!varSetDisjoint(hier.getVars(), locVarAssignTf.getInVars().keySet())
//				&& !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
//			return false;
//		}
		//workaround for preceding problem
		if (!varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return false;
		}
		
		// cases where pre and hier share non-modifiable var g, or
		// g occurs in hier, and old(g) occurs in pre.
		String proc = call.getCallStatement().getMethodName();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);

		
		for (BoogieVar bv : pre.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (hier.getVars().contains(((BoogieOldVar) bv).getNonOldVar())) {
						return false;
					}
				} else {
					if (!modifiableGlobals.contains(bv) 
							&& hier.getVars().contains(bv)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	private boolean prePostIndependent(IPredicate pre, Return ret, IPredicate post) {
		TransFormula returnAssignTf = ret.getTransitionFormula();
		if (!varSetDisjoint(pre.getVars(), returnAssignTf.getInVars().keySet())
				&& !varSetDisjoint(returnAssignTf.getAssignedVars(), post.getVars())) {
			return false;
		}
		Call call = ret.getCorrespondingCall();
		TransFormula locVarAssignTf = call.getTransitionFormula();
		if (!varSetDisjoint(post.getVars(), locVarAssignTf.getInVars().keySet())
				&& !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return false;
		}
		for (BoogieVar bv : pre.getVars()) {
			if (bv.isGlobal() && !bv.isOldvar()) {
				if (pre.getVars().contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	private boolean hierPostIndependent(IPredicate hier, Return ret, IPredicate post) {
		Call call = ret.getCorrespondingCall();
		Set<BoogieVar> assignedVars = ret.getTransitionFormula().getAssignedVars();
		
		String proc = call.getCallStatement().getMethodName();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);
		
		for (BoogieVar bv : post.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				//do nothing
				continue;
			}
			if (assignedVars.contains(bv)) {
				//do nothing
				continue;
			}
			if (hier.getVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}
	
	
	
	
	/**
	 * If the assigned vars of cb are disjoint from the variables in p the
	 * selfloop (p,cb,p) is trivially inductive.
	 * Returns HTTV.VALID if selfloop is inductive. Returns null if we are
	 * not able to determinie inductivity selfloop. 
	 */
	public Validity sdecInternalSelfloop(IPredicate p, CodeBlock cb) {
		Set<BoogieVar> assignedVars = cb.getTransitionFormula().getAssignedVars();
		Set<BoogieVar> occVars = p.getVars();
		for (BoogieVar occVar : occVars) {
			if (assignedVars.contains(occVar)) {
				return null;
			}
		}
		return Validity.VALID;
	}
	
	
	/**
	 * Returns UNSAT if p contains only non-old globals.
	 */
	public Validity sdecCallSelfloop(IPredicate p, CodeBlock cb) {
		for (BoogieVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				} 
			} else {
				return null;
			}
		}
		return Validity.VALID;
	}
	
	
	
	public Validity sdecReturnSelfloopPre(IPredicate p, Return ret) {
		Set<BoogieVar> assignedVars = ret.getTransitionFormula().getAssignedVars();
		for (BoogieVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				} else {
					if (assignedVars.contains(bv)) {
						return null;
					}
				}
			} else {
				return null;
			}
		}
		return Validity.VALID;
	}
	
	
	public Validity sdecReturnSelfloopHier(IPredicate p, Return ret) {
		Set<BoogieVar> assignedVars = ret.getTransitionFormula().getAssignedVars();
		String proc = ret.getCorrespondingCall().getCallStatement().getMethodName();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);

		for (BoogieVar bv : p.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				return null;
			}
			if (assignedVars.contains(bv)) {
				return null;
			}
		}
		return Validity.VALID;
	}
	

	/**
	 * Returns true if the formula of this predicate is an or-term or an
	 * ite-term.
	 */
	private boolean isOrIteFormula(IPredicate p) {
		Term formula = p.getFormula();
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) formula;
			FunctionSymbol symbol = appTerm.getFunction();
			boolean result = symbol.getName().equals("or") || 
					symbol.getName().equals("ite"); 
			return result;
		} else {
			return false;
		}
	}}

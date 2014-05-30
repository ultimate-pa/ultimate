package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.Substitution;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PredicateTransformer {
	private final SmtManager m_SmtManager;
	private final Script m_Script;
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;


	public PredicateTransformer(SmtManager smtManager, ModifiableGlobalVariableManager modifiableGlobalVariableManager) {
		m_SmtManager = smtManager;
		m_Script = smtManager.getScript();
		m_ModifiableGlobalVariableManager = modifiableGlobalVariableManager;
	}



	/**
	 * Compute the irrelevant variables of the given predicate p. 
	 * A variable is irrelevant, if it isn't contained in the given set of relevantVars.
	 * @see LiveVariables
	 */
	private Set<TermVariable> computeIrrelevantVariables(Set<BoogieVar> relevantVars, IPredicate p) {
		Set<TermVariable> result = new HashSet<TermVariable>();
		for (BoogieVar bv : p.getVars()) {
			if (!relevantVars.contains(bv)) {
				result.add(bv.getTermVariable());
			}
		}
		return result;
	}


	/**
	 * Computes a predicate from the given predicate p, such that all irrelevant variables are quantified by
	 * the given quantifier.
	 */
	private IPredicate computeRelevantPredicateHelper(IPredicate p,
			Set<BoogieVar> relevantVars,
			int quantifier) {
		Set<TermVariable> irrelevantVars = computeIrrelevantVariables(relevantVars, p);
		return m_SmtManager.constructPredicate(p.getFormula(), quantifier, irrelevantVars);
	}

	
	public IPredicate computeBackwardRelevantPredicate(IPredicate wp, Set<BoogieVar> relevantVars) {
		return computeRelevantPredicateHelper(wp, relevantVars, Script.FORALL);
	}

	

	public IPredicate computeForwardRelevantPredicate(IPredicate sp, Set<BoogieVar> relevantVars) {
		return computeRelevantPredicateHelper(sp, relevantVars,
				Script.EXISTS);
	}

	/**
	 * Computes the strongest postcondition of the given predicate p and
	 * the TransFormula tf.
	 * - invars of the given transformula, which don't occur in the outvars
	 * or are mapped to different values are renamed to fresh variables. The corresponding 
	 * term variables in the given predicate p, are renamed to the same fresh variables.
	 * - outvars are renamed to corresponding term variables. If an outvar doesn't occur in the invars, its occurrence
	 * in the given predicate is substituted by a fresh variable.
	 * All fresh variables are existentially quantified.
	 */
	public IPredicate strongestPostcondition(IPredicate p, TransFormula tf) {
		// Check if p is false
		if (p.getFormula() == m_SmtManager.newFalsePredicate()) {
			return p;
		}

		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		Term tf_term = tf.getFormula();		

		for (BoogieVar bv : tf.getInVars().keySet()) {
			if (!tf.getOutVars().containsKey(bv) || 
					tf.getOutVars().get(bv) != tf.getInVars().get(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				substitution.put(tf.getInVars().get(bv), freshVar);
				varsToQuantify.add(freshVar);
			}
		}

		Term TFInvarsRenamed = new Substitution(substitution, m_Script).transform(tf_term);

		substitution.clear();
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			substitution.put(tf.getOutVars().get(bv), bv.getTermVariable());
			if (tf.getInVars().isEmpty() && tf.getFormula() == m_SmtManager.newTruePredicate()) {
				varsToQuantify.add(bv.getTermVariable());
			} else if (!tf.getInVars().containsKey(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
		}

		Term TFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(TFInvarsRenamed);

		Term predicateRenamed = new Substitution(varsToRenameInPred, m_Script).transform(p.getFormula());

		// Remove the superflous quantified variables. These are variables, which don't occur neither in
		// the predicate nor in the Transformula
		Set<TermVariable> freeVarsOfPredicate = new HashSet<TermVariable>();
		Set<TermVariable> freeVarsOfTF = new HashSet<TermVariable>();
		Collections.addAll(freeVarsOfPredicate, predicateRenamed.getFreeVars());
		Collections.addAll(freeVarsOfTF, TFInVarsOutVarsRenamed.getFreeVars());
		Set<TermVariable> superflousQuantifiedVars = new HashSet<TermVariable>();
		for (TermVariable tv : varsToQuantify) {
			if (!freeVarsOfPredicate.contains(tv) && !freeVarsOfTF.contains(tv)) {
				superflousQuantifiedVars.add(tv);
			}
		}
		varsToQuantify.removeAll(superflousQuantifiedVars);

		Term result = Util.and(m_Script, TFInVarsOutVarsRenamed, predicateRenamed);

		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());

		//		if (varsToQuantify.size() > 0) {
		//			result = PartialQuantifierElimination.quantifier(m_Script, Script.EXISTS,
		//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]), result, (Term[][]) null);
		//		}
		return m_SmtManager.constructPredicate(result, Script.EXISTS, varsToQuantify);
	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 */
	@Deprecated
	public IPredicate strongestPostcondition(IPredicate p, Call call, boolean isPendingCall) {

		return strongestPostcondition(p, call.getTransitionFormula(),
				m_ModifiableGlobalVariableManager.getGlobalVarsAssignment(call.getCallStatement().getMethodName()), 
				m_ModifiableGlobalVariableManager.getOldVarsAssignment(call.getCallStatement().getMethodName()),
				isPendingCall);
	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 * TODO: How do we compute the SP of a Call Statement?
	 */
	public IPredicate strongestPostcondition(IPredicate p, TransFormula localVarAssignments, 
			TransFormula globalVarAssignments,
			TransFormula oldVarAssignments,
			boolean isPendingCall) {

		// VarsToQuantify contains the local Vars and  the global vars of the calling proc, for a non-pending call.
		Set<TermVariable> varsToQuantifyNonPendingCall = new HashSet<TermVariable>();
		// Variables, which should be quantified if we have a pending call.
		Set<TermVariable> varsToQuantifyPendingCall = new HashSet<TermVariable>();
		// We rename oldvars of non-modifiable global variables to freshvars and quantify them.
		Set<TermVariable> varsToQuantifyNonModOldVars = new HashSet<TermVariable>();
		// In Pred we rename oldvars of non-modifiable global variables to freshvars.
		Map<TermVariable, Term> varsToRenameInPredInBoth = new HashMap<TermVariable, Term>();
		// Union Set of auxvars occurring in each transformula
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(localVarAssignments.getAuxVars());
		allAuxVars.addAll(globalVarAssignments.getAuxVars());
		allAuxVars.addAll(oldVarAssignments.getAuxVars());

		Map<TermVariable, Term> varsToRenameInPredPendingCall = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInPredNonPendingCall = new HashMap<TermVariable, Term>();
		// 1.1 Rename the invars in global variable assignments.Invars are {old(g) --> old(g)_23}
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		//		for (BoogieVar bv : globalVarAssignments.getInVars().keySet()) {
		//			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
		//			substitution.put(globalVarAssignments.getInVars().get(bv), bv.getTermVariable());
		//			varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
		//			varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
		//			varsToQuantifyNonPendingCall.add(freshVar);
		//			varsToQuantifyPendingCall.add(freshVar);
		//		}
		//		Term globalVarsInvarsRenamed = new Substitution(substitution, m_Script).transform(globalVarAssignments.getFormula());
		Term globalVarsInvarsRenamed = substituteToRepresantativesAndAddToQuantify(globalVarAssignments.getInVars(),
				globalVarAssignments.getFormula(), varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		varsToQuantifyPendingCall.addAll(varsToQuantifyNonPendingCall);
		varsToRenameInPredPendingCall.putAll(varsToRenameInPredNonPendingCall);

		// 1.2 Rename the outvars in global variable assignments.
		//		substitution.clear();
		//		for (BoogieVar bv : globalVarAssignments.getOutVars().keySet()) {
		//			substitution.put(globalVarAssignments.getOutVars().get(bv), bv.getTermVariable());
		//			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
		//			varsToQuantifyNonPendingCall.add(freshVar);
		//			varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
		//		}
		//		
		//		Term globalVarsInVarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsInvarsRenamed);
		Term globalVarsInVarsRenamedOutVarsRenamed = substituteToRepresantativesAndAddToQuantify(restrictMap(globalVarAssignments.getOutVars(), GlobalType.NONOLDVAR),
				globalVarsInvarsRenamed, varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		substitution.clear();
		if (globalVarAssignments.getFormula() == m_SmtManager.newTruePredicate().getFormula()) {
			for (BoogieVar bv : oldVarAssignments.getInVars().keySet()) {
				substitution.put(oldVarAssignments.getInVars().get(bv), bv.getTermVariable());
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToQuantifyNonPendingCall.add(freshVar);
				varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
			}
			globalVarsInvarsRenamed = new Substitution(substitution, m_Script).transform(oldVarAssignments.getFormula());
			substitution.clear();

			for (BoogieVar bv : oldVarAssignments.getOutVars().keySet()) {
				if (bv.isOldvar()) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					substitution.put(oldVarAssignments.getOutVars().get(bv), bv.getTermVariable());
					varsToQuantifyPendingCall.add(freshVar);
					varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
					varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
					varsToQuantifyNonPendingCall.add(freshVar);
				}
			}
			globalVarsInVarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsInvarsRenamed);
		}
		// Collect the local and the non-modifiable global variables of the calling proc.
		for (BoogieVar bv : p.getVars()) {
			// Procedure is null, if it is a global variable
			if (bv.getProcedure() != null) {
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				// Ensure that variable doesn't occur in call
				if (!localVarAssignments.getInVars().containsKey(bv)
						&& !localVarAssignments.getOutVars().containsKey(bv)) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
					varsToQuantifyPendingCall.add(freshVar);
					varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				}
			}

			if (bv.isGlobal() &&
					!globalVarAssignments.getInVars().containsKey(bv) && 
					!globalVarAssignments.getOutVars().containsKey(bv)) {
				if (bv.isOldvar()) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInPredInBoth.put(bv.getTermVariable(), freshVar);
					varsToQuantifyNonModOldVars.add(freshVar);
				}
			}
		}
		substitution.clear();

		// 2.1 Rename the invars of the term of Call-Statement.
		for (BoogieVar bv : localVarAssignments.getInVars().keySet()) {

			if (globalVarAssignments.getOutVars().containsKey(bv)) {
				// If it is a global var, then we substitute it through its oldvar
				substitution.put(localVarAssignments.getInVars().get(bv), m_SmtManager.getOldVar(bv).getTermVariable());
			} else {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(),
						bv.getTermVariable().getSort());
				substitution.put(localVarAssignments.getInVars().get(bv), freshVar);
				varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
			}
		}
		Term call_Term_InVarsRenamed = new Substitution(substitution, m_Script).transform(localVarAssignments.getFormula());
		substitution.clear();

		Term predNonModOldVarsRenamed = new Substitution(varsToRenameInPredInBoth, m_Script).transform(p.getFormula());


		if (isPendingCall) {
			// 2.2 Rename the outvars of the term of the Call-Statement.
			for (BoogieVar bv : localVarAssignments.getOutVars().keySet()) {
				substitution.put(localVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			Term callTermInvarsRenamedOutVarsRenamed = new Substitution(substitution, m_Script).transform(call_Term_InVarsRenamed);
			// Rename the invars of CAll, local Vars and old version of global variables.
			Term predRenamed = new Substitution(varsToRenameInPredPendingCall, m_Script).transform(predNonModOldVarsRenamed);
			Term predANDCallANDGlobalVars = Util.and(m_Script, predRenamed, callTermInvarsRenamedOutVarsRenamed,
					globalVarsInVarsRenamedOutVarsRenamed);
			varsToQuantifyPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyPendingCall.addAll(allAuxVars);
			//			Term result = PartialQuantifierElimination.quantifier(m_Script,
			//					Script.EXISTS,
			//					varsToQuantifyPendingCall.toArray(new TermVariable[varsToQuantifyPendingCall.size()]),
			//					predANDCallANDGlobalVars, (Term[][])null);

			return m_SmtManager.constructPredicate(predANDCallANDGlobalVars, Script.EXISTS, varsToQuantifyPendingCall);
		} else {
			Term predRenamed = new Substitution(varsToRenameInPredNonPendingCall, m_Script).transform(predNonModOldVarsRenamed);
			varsToQuantifyNonPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyNonPendingCall.addAll(allAuxVars);
			//			Term result = PartialQuantifierElimination.quantifier(m_Script, 
			//					Script.EXISTS,
			//					varsToQuantifyNonPendingCall.toArray(new TermVariable[varsToQuantifyNonPendingCall.size()]),
			//					Util.and(m_Script, predRenamed, globalVarsInVarsRenamedOutVarsRenamed),
			//					(Term[][])null);
			return m_SmtManager.constructPredicate(Util.and(m_Script, predRenamed, globalVarsInVarsRenamedOutVarsRenamed), Script.EXISTS, varsToQuantifyNonPendingCall);
		}
	}




	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return 
	 * statement and callerPred is the predicate that held in the calling 
	 * procedure before the corresponding call.
	 * TODO: How is it computed? 
	 */
	public IPredicate strongestPostcondition(IPredicate calleePred, 
			IPredicate callerPred, TransFormula ret_TF, 
			TransFormula callTF,
			TransFormula globalVarsAssignment,
			TransFormula oldVarsAssignment) {
		// VarsToQuantify contains local vars of called procedure, and it may contain
		// some invars, if it was a recursive call, i.e. callingProc = calledProc.
		Set<TermVariable> varsToQuantifyOverAll = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCalleePred = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCallerPredAndCallTF = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInCalleePred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInCallerPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> outVarsToRenameInCallTF = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> inVarsToRenameInReturnTF = new HashMap<TermVariable, Term>();
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(ret_TF.getAuxVars());
		allAuxVars.addAll(callTF.getAuxVars());
		allAuxVars.addAll(globalVarsAssignment.getAuxVars());


		// Substitute oldvars of modifiable global vars by fresh vars in calleePred
		// and substitue their non-oldvar by the same fresh var in callerPred.
		for (BoogieVar bv : globalVarsAssignment.getInVars().keySet()) {
			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
			varsToRenameInCallerPred.put(m_SmtManager.getNonOldVar(bv).getTermVariable(), freshVar);
			varsToQuantifyOverAll.add(freshVar);
		}
		// Note: We have to take also the outvars into account, because sometimes it may be the case,
		// that a invar does not occur in the outvars.
		for (BoogieVar bv : globalVarsAssignment.getOutVars().keySet()) {
			// We have only to check the vars, that are not contained in the map varsToRenameInCallerPred,
			// because otherwise it is already treated in the case above.
			if (!bv.isOldvar() && !varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
			}

		}


		// Collect the local variables of called proc
		for (BoogieVar bv : calleePred.getVars()) {
			if (bv.isGlobal() || bv.isOldvar()) {
				continue;
			}
			if (ret_TF.getOutVars().containsKey(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callTF.getInVars().containsKey(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callerPred.getVars().contains(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (!ret_TF.getInVars().containsKey(bv) && 
					!callTF.getOutVars().containsKey(bv)) {
				if (!m_ModifiableGlobalVariableManager.getGlobals().containsKey(bv.getIdentifier())) {
					varsToQuantifyInCalleePred.add(bv.getTermVariable());
				}
			}

		}


		// 1.1 We doesn't rename the invars of the TransFormula Return,
		// because we quantify them out.
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : ret_TF.getInVars().keySet()) {
			if (!inVarsToRenameInReturnTF.containsKey(ret_TF.getInVars().get(bv))) {
				TermVariable substitutor = ret_TF.getInVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}
		//1.2 Rename outvars of Return statement
		for (BoogieVar bv : ret_TF.getOutVars().keySet()) {
			if (calleePred.getVars().contains(bv)) {
				if (!varsToRenameInCalleePred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
					varsToQuantifyOverAll.add(freshVar);
				} 
			}
			substitution.put(ret_TF.getOutVars().get(bv), bv.getTermVariable());
			varsToQuantifyInCallerPredAndCallTF.add(bv.getTermVariable());
		}
		Term retTermRenamed = new Substitution(inVarsToRenameInReturnTF, m_Script).transform(ret_TF.getFormula());
		retTermRenamed = new Substitution(substitution, m_Script).transform(retTermRenamed);
		// 2.1 Rename invars of TransFormula of corresponding Call statement
		substitution.clear();
		for (BoogieVar bv : callTF.getInVars().keySet()) {
			if (ret_TF.getOutVars().containsKey(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(callTF.getInVars().get(bv), freshVar);
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyInCallerPredAndCallTF.add(freshVar);
			} else if (globalVarsAssignment.getOutVars().containsKey(bv)) {
				Term freshVar = varsToRenameInCallerPred.get(bv.getTermVariable());
				assert freshVar != null : "added null to substitution mapping";
				substitution.put(callTF.getInVars().get(bv), freshVar);
			} else {
				substitution.put(callTF.getInVars().get(bv), bv.getTermVariable());
			}
		}
		Term callTermRenamed = new Substitution(outVarsToRenameInCallTF, m_Script).transform(callTF.getFormula());
		callTermRenamed = new Substitution(substitution, m_Script).transform(callTermRenamed);
		// 2.2 We doesn't rename the outvars, because the outvars are the localvars
		// of the called procedure, therefore we want to quantify them out.
		for (BoogieVar bv : callTF.getOutVars().keySet()) {
			if (!outVarsToRenameInCallTF.containsKey(callTF.getOutVars().get(bv))) {
				TermVariable substitutor = callTF.getOutVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}


		// 3. Rename the vars in calleePred, which occur as an outvar in the TransFormula of Return Statement, or
		// which occur as an invar in the TransFormula of the corresponding Call statement.
		// This substitution is only necessary, if we have a recursive call.
		Term calleePredVarsRenamed = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePred.getFormula());



		// 5. Substitute oldvars through fresh variables in calleePredicate.
		Term calleePredVarsRenamedOldVarsToFreshVars = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePredVarsRenamed);


		// 6. Substitute the global variables in callerPred through the fresh Vars computed in (4).
		Term callerPredVarsRenamedToFreshVars = new Substitution(varsToRenameInCallerPred, m_Script).transform(callerPred.getFormula());

		// 1. CalleePredRenamed and loc vars quantified
		Term calleePredRenamedQuantified = PartialQuantifierElimination.quantifier(m_Script,
				Script.EXISTS,
				varsToQuantifyInCalleePred.toArray(new TermVariable[varsToQuantifyInCalleePred.size()]),
				calleePredVarsRenamedOldVarsToFreshVars,(Term[][])null);
		// 2. CallTF and callerPred
		Term calleRPredANDCallTFRenamedQuantified = PartialQuantifierElimination.quantifier(m_Script,
				Script.EXISTS,
				varsToQuantifyInCallerPredAndCallTF.toArray(new TermVariable[varsToQuantifyInCallerPredAndCallTF.size()]),
				Util.and(m_Script, callerPredVarsRenamedToFreshVars, callTermRenamed),(Term[][])null);
		// 3. Result
		varsToQuantifyOverAll.addAll(allAuxVars);

		return m_SmtManager.constructPredicate(Util.and(m_Script, calleePredRenamedQuantified, retTermRenamed,
				calleRPredANDCallTFRenamedQuantified), Script.EXISTS, varsToQuantifyOverAll);
	}

	

	public IPredicate weakestPrecondition(IPredicate p, TransFormula tf) {
		// If the given predicate p is true, then return true, since wp(true, st) = true for every statement st.
		if (p.getFormula() == m_SmtManager.newTruePredicate()) {
			return p;
		}
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		Map<TermVariable, Term> varsToRenameInPred = new HashMap<TermVariable, Term>();
		Term tf_term = tf.getFormula();
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		// 1 Rename the invars of the TransFormula of the given CodeBlock cb into TermVariables
		//		for (BoogieVar bv : tf.getInVars().keySet()) {
		//			substitution.put(tf.getInVars().get(bv), bv.getTermVariable());
		//		}
		//		Term TFInVarsRenamed = new Substitution(substitution, m_Script).transform(tf_term);

		Term TFInVarsRenamed = substituteToRepresantativesAndAddToQuantify(tf.getInVars(), tf_term, null, null);

		substitution.clear();
		// 2 Rename the outvars of the TransFormula of the given CodeBlock cb into TermVariables
		for (BoogieVar bv : tf.getOutVars().keySet()) {
			if (tf.getAssignedVars().contains(bv)) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToRenameInPred.put(bv.getTermVariable(), freshVar);
				substitution.put(tf.getOutVars().get(bv), freshVar);
				varsToQuantify.add(freshVar);
			}
		}
		Term TFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(TFInVarsRenamed);

		// 3. Rename the necessary vars in the given predicate
		Term predicateRenamed = new Substitution(varsToRenameInPred, m_Script).transform(p.getFormula());

		// Remove the superflous quantified variables. These are variables, which don't occur neither in
		// the predicate nor in the transformula
		Set<TermVariable> freeVarsOfPredicate = new HashSet<TermVariable>();
		Set<TermVariable> freeVarsOfTF = new HashSet<TermVariable>();
		Collections.addAll(freeVarsOfPredicate, predicateRenamed.getFreeVars());
		Collections.addAll(freeVarsOfTF, TFInVarsOutVarsRenamed.getFreeVars());
		Set<TermVariable> superflousQuantifiedVars = new HashSet<TermVariable>();
		for (TermVariable tv : varsToQuantify) {
			if (!freeVarsOfPredicate.contains(tv) && !freeVarsOfTF.contains(tv)) {
				superflousQuantifiedVars.add(tv);
			}
		}
		varsToQuantify.removeAll(superflousQuantifiedVars);

		Term result = Util.or(m_Script, Util.not(m_Script, TFInVarsOutVarsRenamed), predicateRenamed);
		// Add aux-vars to quantified vars
		varsToQuantify.addAll(tf.getAuxVars());
		//		if (varsToQuantify.size() > 0) {
		//			result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
		//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
		//					result, (Term[][]) null);
		//		} 
		return m_SmtManager.constructPredicate(result, Script.FORALL, varsToQuantify);
	}


	/**
	 * Responsible for computing WP of a Call statement.
	 * 
	 */
	public IPredicate weakestPrecondition(IPredicate calleePred, 
			TransFormula call_TF, 
			TransFormula globalVarsAssignments,
			TransFormula oldVarsAssignments,
			boolean isPendingCall) {

		if (isPendingCall) {
			Map<TermVariable, Term> varsToRenameInCalleePred = new HashMap<TermVariable, Term>();
			Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
			Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();

			// 1. Rename oldvars of global vars to fresh vars
			for (BoogieVar bv : globalVarsAssignments.getInVars().keySet()) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(globalVarsAssignments.getInVars().get(bv), freshVar);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
			Term globalVarsInVarsRenamed = new Substitution(substitution, m_Script).transform(globalVarsAssignments.getFormula());

			substitution.clear();
			// 2. Rename global vars to fresh vars
			for (BoogieVar bv : globalVarsAssignments.getOutVars().keySet()) {
				if (!bv.isOldvar()) {
					substitution.put(globalVarsAssignments.getOutVars().get(bv), bv.getTermVariable());
				}
				//				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				
				//				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				//				varsToQuantify.add(freshVar);
			}
			Term globalVarsInVarsOutVarsRenamed  = new Substitution(substitution, m_Script).transform(globalVarsInVarsRenamed);
			substitution.clear();
			if (globalVarsAssignments.getFormula() == m_SmtManager.newTruePredicate().getFormula()) {
				for (BoogieVar bv : oldVarsAssignments.getInVars().keySet()) {
					//					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					substitution.put(oldVarsAssignments.getInVars().get(bv), bv.getTermVariable());
					//					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
					//					varsToQuantify.add(freshVar);
				}
				globalVarsInVarsRenamed = new Substitution(substitution, m_Script).transform(oldVarsAssignments.getFormula());
				substitution.clear();
				for (BoogieVar bv : oldVarsAssignments.getOutVars().keySet()) {
					if (bv.isOldvar()) {
						TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
						substitution.put(oldVarsAssignments.getOutVars().get(bv), freshVar);
						varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
						varsToQuantify.add(freshVar);
					}
				}
				globalVarsInVarsOutVarsRenamed  = new Substitution(substitution, m_Script).transform(globalVarsInVarsRenamed);
			}

			substitution.clear();
			// 3. Rename invars of Call to its correspondent termvariables
			for (BoogieVar bv : call_TF.getInVars().keySet()) {
				substitution.put(call_TF.getInVars().get(bv), bv.getTermVariable());
			}
			Term callTFInVarsRenamed = new Substitution(substitution, m_Script).transform(call_TF.getFormula());
			// 4. Rename outvars of Call to fresh vars
			substitution.clear();
			for (BoogieVar bv : call_TF.getOutVars().keySet()) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				substitution.put(call_TF.getOutVars().get(bv), freshVar);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantify.add(freshVar);
			}
			Term callTFInVarsOutVarsRenamed = new Substitution(substitution, m_Script).transform(callTFInVarsRenamed);

			Term calleePredRenamed = new Substitution(varsToRenameInCalleePred, m_Script).transform(calleePred.getFormula());

			Term result = Util.or(m_Script, 
					Util.not(m_Script, 
							Util.and(m_Script, callTFInVarsOutVarsRenamed,
									globalVarsInVarsOutVarsRenamed)),
									calleePredRenamed);
			varsToQuantify.addAll(call_TF.getAuxVars());
			//			if (varsToQuantify.size() > 0) {
			//				result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
			//						varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
			//						result, (Term[][])null);
			//			}
			return m_SmtManager.constructPredicate(result, Script.FORALL, varsToQuantify);
		} else {
			throw new UnsupportedOperationException("WP for non-pending Call is not implemented yet!");
		}
	}


	/**
	 * Computes weakest precondition of a Return statement.
	 * 	oldvars of modifiable global variables are renamed to their representatives, and they are
	 * 		substituted in caller predicate and returner predicate to same fresh variables
	 * 	modifiable global variables are renamed to fresh variables and their occurrence in the caller predicate
	 * 		is substituted by the same fresh variables.
	 *  InVars of returnTF are renamed to representatives, their occurrence in ..
	 * 
	 */
	public IPredicate weakestPrecondition(IPredicate returnerPred, IPredicate callerPred, 
			TransFormula returnTF,
			TransFormula callTF,
			TransFormula globalVarsAssignments,
			TransFormula oldVarAssignments,
			Set<BoogieVar> modifiableGlobals) {

		Map<TermVariable, Term> varsToRenameInCallerAndReturnPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInReturnPred = new HashMap<TermVariable, Term>();
		Map<TermVariable, Term> varsToRenameInCallerPred = new HashMap<TermVariable, Term>();
		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>();
		// Appropriately rename global var assignments
		Term globalVarsRenamed = null;
		if (globalVarsAssignments != null) {
			// 1.1 Rename the invars in global variable assignments (old_vars) to representative term variables.
			// Rename old vars in callerPred and returnerPred to same fresh variable.
			globalVarsRenamed = substituteToRepresantativesAndAddToQuantify(
					globalVarsAssignments.getInVars(),globalVarsAssignments.getFormula(), varsToRenameInCallerAndReturnPred,
					varsToQuantify);
			// 1.2 Rename the outvars in global variable assignments to fresh variables.
			// Rename the global vars in callerPred to same fresh variables.
			globalVarsRenamed = substituteToFreshVarsAndAddToQuantify(
					restrictMap(globalVarsAssignments.getOutVars(), GlobalType.NONOLDVAR),
					globalVarsRenamed,
					varsToRenameInCallerPred, varsToQuantify);
		} else {
			// 1.1 Rename the outvars in global variable assignments (old_vars) to representative term variables.
			globalVarsRenamed = substituteToRepresantativesAndAddToQuantify(
					restrictMap(oldVarAssignments.getOutVars(), GlobalType.OLDVAR),
					oldVarAssignments.getFormula(),
					varsToRenameInCallerAndReturnPred,
					varsToQuantify);
			// 1.2 Rename the outvars in global variable assignments to fresh variables.
			// Rename the global vars in callerPred to same fresh variables. 
			globalVarsRenamed = substituteToFreshVarsAndAddToQuantify(
					oldVarAssignments.getInVars(),
					globalVarsRenamed,
					varsToRenameInCallerPred,
					varsToQuantify);
		}
		
		
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		// 2.1 Rename the invars of Return-Statement to representative term variables.
		// Rename the representative term variables of invars, which don't occur in the outvars in caller predicate
		// and in returner predicate to same fresh variables.
		// Representatives of invars, which occur also in
		for (BoogieVar bv : returnTF.getInVars().keySet()) {
			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			varsToQuantify.add(freshVar);
			substitution.put(returnTF.getInVars().get(bv), bv.getTermVariable());
			// Note: Variables which occur in the invars as well as in the outvars of the return transformula are
			// renamed in caller predicate and returner predicate to different fresh variables.
			if (returnTF.getOutVars().containsKey(bv)) {
				varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
			} else {
				varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
			}
		}
		Term returnTermRenamed = new Substitution(substitution, m_Script).transform(returnTF.getFormula());
		//		Term returnTermRenamed = substituteToRepresantativesAndAddToQuantify(returnTF.getInVars(), returnTF.getFormula(), 
		//				varsToRenameInCallerPred, varsToQuantify);
		substitution.clear();
		// 2.2 We rename the outvars to freshvars and quantify them
		//		for (BoogieVar bv : returnTF.getOutVars().keySet()) {
		//			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
		//			varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
		//			substitution.put(returnTF.getOutVars().get(bv), freshVar);
		//			varsToQuantify.add(freshVar);
		//		}
		//		returnTermRenamed = new Substitution(substitution, m_Script).transform(returnTermRenamed);
		// 2.2 We rename the outvars to fresh variables and quantify them.
		// The representative of the outvars in the returnerPred are renamed to same fresh variables.
		// The representative of the invars in the returnerPred are renamed to same fresh variables as in the callerPred.
		returnTermRenamed = substituteToFreshVarsAndAddToQuantify(returnTF.getOutVars(), returnTermRenamed, varsToRenameInReturnPred, varsToQuantify);


		// Rename the invars of the Call and quantify them
		// InVars are renamed to fresh variables.
		substitution.clear();
		for (BoogieVar bv : callTF.getInVars().keySet()) {
			if (varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
				substitution.put(callTF.getInVars().get(bv), varsToRenameInCallerAndReturnPred.get(bv.getTermVariable()));
			} else {
				TermVariable freshVar = null; 
				if (varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					freshVar = (TermVariable) varsToRenameInCallerPred.get(bv.getTermVariable());
				} else {
					freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				}
				substitution.put(callTF.getInVars().get(bv), freshVar);
				// Local variables, which aren't assigned by the return transformula (don't occur in the outvars)
				// are renamed in the caller and in the returner predicate to same fresh variables.
				if (!bv.isGlobal() && !returnTF.getOutVars().containsKey(bv)) {
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
					varsToRenameInCallerPred.remove(bv.getTermVariable());
				}
				varsToQuantify.add(freshVar);
			}
		}
		Term callTermRenamed = new Substitution(substitution, m_Script).transform(callTF.getFormula());
		substitution.clear();
		// Rename the outvars of the Call transformula to their representative term variables.
		// If an outvar isn't marked to be substituted by a fresh variable in the caller and returner predicate,
		// then mark such an outvar to be substituted by a new fresh variable.
		for (BoogieVar bv : callTF.getOutVars().keySet()) {
			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
				if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
				} else {
					varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
				}
			}
			substitution.put(callTF.getOutVars().get(bv), bv.getTermVariable());
			varsToQuantify.add(freshVar);
		}
		callTermRenamed = new Substitution(substitution, m_Script).transform(callTermRenamed);

		// Variables from the returner predicate, which aren't treated by any of the steps before, are
		// treated in this step as follows: 
		// oldvars are substituted by fresh variables
		// local variables (non global variables) are substituted by fresh variables and marked to be
		// substituted in the caller predicate by the same fresh variables.
		for (BoogieVar bv : returnerPred.getVars()) {
			//			if (bv.isOldvar()) {
			//				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable()) &&
			//						!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
			//					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			//					varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
			//					varsToQuantify.add(freshVar);
			//				}
			//			} else if (!bv.isGlobal()){
			//				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())		
			//						&& !varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
			//					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			//					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
			//					varsToQuantify.add(freshVar);
			//				}
			//			}
			if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable()) &&
					!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
				TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				varsToQuantify.add(freshVar);
				if (!bv.isGlobal() || bv.isOldvar()) {
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
				}
			}
		}
		// Appropriately rename and quantify local vars in the caller predicate (i.e. the variables that do not occur in the called procedure)
		// local variables (which aren't already affected by the previous steps) are renamed to fresh variables, and
		// also marked to be substituted in the returner predicate by the same fresh variables.
		// old vars are renamed to fresh variables.
		// global variables
		for (BoogieVar bv : callerPred.getVars()) {
			if (!bv.isGlobal()) {
				// 1.case: bv is a local var
				if (!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())&&
						!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerAndReturnPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
			} else if (bv.isOldvar()) {
				// 2.case: bv is an oldvar
				// TODO(Betim) Fix this bad condition!
				if (!varsToRenameInReturnPred.containsKey(bv.getTermVariable()) || 
						!varsToRenameInCallerAndReturnPred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
					varsToQuantify.add(freshVar);
				}
			} else {
				// 3.case: bv is a global var
				// If a global variable isn't modifiable by the returned proc. and it doesn't occur in the returner
				// predicate, then skip this variable (it isn't renamed or quantified).
				//				if (!modifiableGlobals.contains(bv) && returnerPred.getVars().contains(bv)) {
				//					continue;	
				//				} else if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
				//					TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
				//					varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
				//					varsToQuantify.add(freshVar);
				//					if (returnerPred.getVars().contains(bv) && 
				//							!globalVarsAssignments.getOutVars().containsKey(bv)) {
				//						if (!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
				//							varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
				//						}
				//					}
				//				}
				// 3.case: bv is a global var
				if (modifiableGlobals.contains(bv) || !returnerPred.getVars().contains(bv)) {
					if (!varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
						TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
						varsToRenameInCallerPred.put(bv.getTermVariable(), freshVar);
						varsToQuantify.add(freshVar);
						// This is not necessary!
						//						if (returnerPred.getVars().contains(bv) && 
						//								!globalVarsAssignments.getOutVars().containsKey(bv)) {
						//							if (!varsToRenameInReturnPred.containsKey(bv.getTermVariable())) {
						//								varsToRenameInReturnPred.put(bv.getTermVariable(), freshVar);
						//							}
						//						}
					}
				}
			}
		}

		Term returnPredRenamed = new Substitution(varsToRenameInCallerAndReturnPred, m_Script).transform(returnerPred.getFormula());
		returnPredRenamed = new Substitution(varsToRenameInReturnPred, m_Script).transform(returnPredRenamed);
		Term callerPredRenamed = new Substitution(varsToRenameInCallerAndReturnPred, m_Script).transform(callerPred.getFormula());
		callerPredRenamed = new Substitution(varsToRenameInCallerPred, m_Script).transform(callerPredRenamed);

		// Add aux vars to quantify them
		varsToQuantify.addAll(callTF.getAuxVars());
		varsToQuantify.addAll(returnTF.getAuxVars());
		varsToQuantify.addAll(globalVarsAssignments.getAuxVars());

		Term callerPredANDCallANDReturnAndGlobalVars = Util.and(m_Script, callerPredRenamed,
				returnTermRenamed, callTermRenamed,
				globalVarsRenamed);

		Term result = Util.or(m_Script, Util.not(m_Script, callerPredANDCallANDReturnAndGlobalVars), returnPredRenamed);

		//		if (varsToQuantify.size() > 0) {
		//			result = PartialQuantifierElimination.quantifier(m_Script, Script.FORALL,
		//					varsToQuantify.toArray(new TermVariable[varsToQuantify.size()]),
		//					result, (Term[][])null);
		//		}
		return m_SmtManager.constructPredicate(result, Script.FORALL, varsToQuantify);
	}


	private enum GlobalType {OLDVAR, NONOLDVAR}
	/**
	 * Returns copy of map restricted to keys that are of the given GlobalType
	 * (oldVar or nonOldVar).
	 */
	private Map<BoogieVar, TermVariable> restrictMap(
			Map<BoogieVar,TermVariable> map, GlobalType globalType) {
		Map<BoogieVar, TermVariable> result = new HashMap<BoogieVar, TermVariable>();
		for (Entry<BoogieVar, TermVariable> entry : map.entrySet()) {
			if ((globalType == GlobalType.OLDVAR) == (entry.getKey().isOldvar())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return result;
	}

	/** Substitutes in the given formula the values of the given map by fresh variables,
	 * and puts the substitution from the term variable to the same fresh variable into the
	 * second given map. It also adds the fresh variable to the given set. 
	 * @param varsToBeSubstituted - the occurrence of the values of this map in the given formula are renamed to fresh variables
	 * @param formulaToBeSubstituted - the formula in which the variables should be substituted 
	 * @param varsToBeSubstitutedByFreshVars - map to which the substitutions from corresponding term variables to fresh variables should be added
	 * @param varsToQuantify - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by fresh variables
	 */
	private Term substituteToFreshVarsAndAddToQuantify(
			Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted,
			Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			substitution.put(varsToBeSubstituted.get(bv), freshVar);
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new Substitution(substitution, m_Script).transform(formulaToBeSubstituted);
	}

	/**
	 * Substitutes in the given formula the values of the given map by the keys of the given map.
	 * It also puts a substitution from the keys of the given map to fresh variables into the
	 * second given map and adds the fresh variables to the given set. 
	 * @param varsToBeSubstituted - the occurrence of the values of this map in the given formula are substituted by the keys of this map
	 * @param formulaToBeSubstituted - the formula in which the variables should be substituted 
	 * @param varsToBeSubstitutedByFreshVars - map to which the substitutions from the keys of the map "varsToBeSubstituted" to fresh variables should be added
	 * @param varsToQuantify - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by the corresponding term variables
	 */
	private Term substituteToRepresantativesAndAddToQuantify(
			Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted,
			Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<TermVariable, Term> substitution = new HashMap<TermVariable, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = m_SmtManager.getFreshTermVariable(bv.getIdentifier(), bv.getTermVariable().getSort());
			substitution.put(varsToBeSubstituted.get(bv), bv.getTermVariable());
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new Substitution(substitution, m_Script).transform(formulaToBeSubstituted);
	}


}

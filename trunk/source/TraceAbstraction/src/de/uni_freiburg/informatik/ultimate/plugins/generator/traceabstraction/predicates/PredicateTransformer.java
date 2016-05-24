/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * @author musab@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * 
 */
public class PredicateTransformer {
	private final Script mScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	private final VariableManager mVariableManager;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	public PredicateTransformer(VariableManager variableManager, Script script, 
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mScript = script;
		mModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		mVariableManager = variableManager;
	}


	/**
	 * Computes the strongest postcondition of the given predicate p and the
	 * TransFormula tf. - invars of the given transformula, which don't occur in
	 * the outvars or are mapped to different values are renamed to fresh
	 * variables. The corresponding term variables in the given predicate p, are
	 * renamed to the same fresh variables. - outvars are renamed to
	 * corresponding term variables. If an outvar doesn't occur in the invars,
	 * its occurrence in the given predicate is substituted by a fresh variable.
	 * All fresh variables are existentially quantified.
	 */
	public Term strongestPostcondition(IPredicate p, TransFormula tf) {
		if (SmtUtils.isFalse(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		IValueConstruction<BoogieVar, TermVariable> substituentConstruction = new IValueConstruction<BoogieVar, TermVariable>() {

			@Override
			public TermVariable constructValue(BoogieVar bv) {
				final TermVariable result = mVariableManager.constructFreshTermVariable(bv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		ConstructionCache<BoogieVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		Map<Term, Term> substitutionForPredecessor = new HashMap<Term, Term>();
		for (Entry<BoogieVar, TermVariable> entry : tf.getInVars().entrySet()) {
			BoogieVar bv = entry.getKey();
			if (entry.getValue() == tf.getOutVars().get(bv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				TermVariable substituent = termVariablesForPredecessor.getOrConstuct(bv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(bv)) {
					substitutionForPredecessor.put(bv.getTermVariable(), substituent);
				}
			}
		}

		for (Entry<BoogieVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getInVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				TermVariable substituent = termVariablesForPredecessor.getOrConstuct(entry.getKey());
				substitutionForPredecessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedPredecessor = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForPredecessor).transform(p.getFormula());
			
		final Term result = Util.and(mScript, renamedTransFormula, renamedPredecessor);

		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;
	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 */
	@Deprecated
	public Term strongestPostcondition(IPredicate p, Call call, boolean isPendingCall) {
		return strongestPostcondition(p, call.getTransitionFormula(),
				mModifiableGlobalVariableManager.getGlobalVarsAssignment(call.getCallStatement().getMethodName()),
				mModifiableGlobalVariableManager.getOldVarsAssignment(call.getCallStatement().getMethodName()),
				isPendingCall);
	}
	
	
	public Term weakLocalPostconditionCall(IPredicate p, TransFormula globalVarAssignments, final Set<BoogieVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		
		final Term renamedOldVarsAssignment;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (BoogieVar bv : globalVarAssignments.getAssignedVars()) {
				assert (bv instanceof BoogieNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			for (Entry<BoogieVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof BoogieOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedOldVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(globalVarAssignments.getFormula());
		}

		final Term renamedPredicate;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			TermVariable substituent;
			for (BoogieVar bv : p.getVars()) {
				if (bv instanceof BoogieNonOldVar) {
					if (modifiableGlobals.contains(bv)) {
						substituent = mVariableManager.constructFreshTermVariable(bv);
						varsToQuantify.add(substituent);
						substitutionMapping.put(bv.getTermVariable(), substituent);
					} else {
						// do nothing
					}
				} else if (bv instanceof BoogieOldVar) {
					substituent = mVariableManager.constructFreshTermVariable(bv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(bv.getTermVariable(), substituent);
				} else if (bv instanceof LocalBoogieVar) {
					substituent = mVariableManager.constructFreshTermVariable(bv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(bv.getTermVariable(), substituent);
				} else {
					throw new AssertionError();
				}
			}
			renamedPredicate = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(p.getFormula());
		}
		Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedOldVarsAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;

	}
	
	
	public Term strongestPostconditionCall(IPredicate p, TransFormula localVarAssignments,
			TransFormula globalVarAssignments, TransFormula oldVarAssignments, final Set<BoogieVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		IValueConstruction<BoogieVar, TermVariable> substituentConstruction = new IValueConstruction<BoogieVar, TermVariable>() {

			@Override
			public TermVariable constructValue(BoogieVar bv) {
				final TermVariable result;
				if (bv instanceof BoogieNonOldVar) {
					if (modifiableGlobals.contains(bv)) {
						result = mVariableManager.constructFreshTermVariable(bv);
						varsToQuantify.add(result);
					} else {
						result = bv.getTermVariable();
					}
				} else if (bv instanceof BoogieOldVar) {
					result = mVariableManager.constructFreshTermVariable(bv);
					varsToQuantify.add(result);
				} else if (bv instanceof LocalBoogieVar) {
					result = mVariableManager.constructFreshTermVariable(bv);
					varsToQuantify.add(result);
				} else {
					throw new AssertionError();
				}
				return result;
			}
			
		};
		ConstructionCache<BoogieVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		final Term renamedGlobalVarAssignment;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (BoogieVar bv : globalVarAssignments.getAssignedVars()) {
				assert (bv instanceof BoogieNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			for (Entry<BoogieVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof BoogieOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedGlobalVarAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(globalVarAssignments.getFormula());
		}
		
		final Term renamedOldVarsAssignment;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (BoogieVar bv : oldVarAssignments.getAssignedVars()) {
				assert (bv instanceof BoogieOldVar);
				substitutionMapping.put(oldVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			for (Entry<BoogieVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof BoogieNonOldVar);
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstuct(entry.getKey()));
			}
			renamedOldVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(oldVarAssignments.getFormula());
		}
		
		final Term renamedLocalVarsAssignment;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (BoogieVar bv : localVarAssignments.getAssignedVars()) {
				assert (bv instanceof LocalBoogieVar);
				substitutionMapping.put(localVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			for (Entry<BoogieVar, TermVariable> entry : localVarAssignments.getInVars().entrySet()) {
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstuct(entry.getKey()));
			}
			renamedLocalVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(localVarAssignments.getFormula());
		}
		
		final Term renamedPredicate;
		{
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (BoogieVar bv : p.getVars()) {
				substitutionMapping.put(bv.getTermVariable(), termVariablesForPredecessor.getOrConstuct(bv));
			}
			renamedPredicate = new SafeSubstitutionWithLocalSimplification(mScript, mVariableManager, substitutionMapping).transform(p.getFormula());
		}
		Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedLocalVarsAssignment, renamedOldVarsAssignment,
				renamedGlobalVarAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;

	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way. TODO: How do we compute
	 * the SP of a Call Statement?
	 */
	@Deprecated
	private Term strongestPostcondition(IPredicate p, TransFormula localVarAssignments,
			TransFormula globalVarAssignments, TransFormula oldVarAssignments, boolean isPendingCall) {

		// VarsToQuantify contains the local Vars and the global vars of the
		// calling proc, for a non-pending call.
		Set<TermVariable> varsToQuantifyNonPendingCall = new HashSet<TermVariable>();
		// Variables, which should be quantified if we have a pending call.
		Set<TermVariable> varsToQuantifyPendingCall = new HashSet<TermVariable>();
		// We rename oldvars of non-modifiable global variables to freshvars and
		// quantify them.
		Set<TermVariable> varsToQuantifyNonModOldVars = new HashSet<TermVariable>();
		// In Pred we rename oldvars of non-modifiable global variables to
		// freshvars.
		Map<Term, Term> varsToRenameInPredInBoth = new HashMap<Term, Term>();
		// Union Set of auxvars occurring in each transformula
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(localVarAssignments.getAuxVars());
		allAuxVars.addAll(globalVarAssignments.getAuxVars());
		allAuxVars.addAll(oldVarAssignments.getAuxVars());

		Map<Term, Term> varsToRenameInPredPendingCall = new HashMap<Term, Term>();
		Map<Term, Term> varsToRenameInPredNonPendingCall = new HashMap<Term, Term>();
		// 1.1 Rename the invars in global variable assignments.Invars are
		// {old(g) --> old(g)_23}
		Map<Term, Term> substitution = new HashMap<Term, Term>();
		Term globalVarsInvarsRenamed = substituteToRepresantativesAndAddToQuantify(globalVarAssignments.getInVars(),
				globalVarAssignments.getFormula(), varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		varsToQuantifyPendingCall.addAll(varsToQuantifyNonPendingCall);
		varsToRenameInPredPendingCall.putAll(varsToRenameInPredNonPendingCall);

		Term globalVarsInVarsRenamedOutVarsRenamed = substituteToRepresantativesAndAddToQuantify(
				restrictMap(globalVarAssignments.getOutVars(), GlobalType.NONOLDVAR), globalVarsInvarsRenamed,
				varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		substitution.clear();
		if (SmtUtils.isTrue(globalVarAssignments.getFormula())) {
			for (BoogieVar bv : oldVarAssignments.getInVars().keySet()) {
				substitution.put(oldVarAssignments.getInVars().get(bv), bv.getTermVariable());
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				varsToQuantifyNonPendingCall.add(freshVar);
				varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
			}
			globalVarsInvarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(oldVarAssignments.getFormula());
			substitution.clear();

			for (BoogieVar bv : oldVarAssignments.getOutVars().keySet()) {
				if (bv.isOldvar()) {
					TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
					substitution.put(oldVarAssignments.getOutVars().get(bv), bv.getTermVariable());
					varsToQuantifyPendingCall.add(freshVar);
					varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
					varsToRenameInPredNonPendingCall.put(bv.getTermVariable(), freshVar);
					varsToQuantifyNonPendingCall.add(freshVar);
				}
			}
			globalVarsInVarsRenamedOutVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(globalVarsInvarsRenamed);
		}
		// Collect the local and the non-modifiable global variables of the
		// calling proc.
		for (BoogieVar bv : p.getVars()) {
			// Procedure is null, if it is a global variable
			if (bv.getProcedure() != null) {
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				/*
				 * On 2014-06-25 Matthias commented the following two lines of
				 * code: This lead to a problem with recursive programs where a
				 * variable occurred in p and also in the call. I do not know if
				 * commenting these lines is a proper solution (or is the reason
				 * for other bugs).
				 */
				// Ensure that variable doesn't occur in call
				// if (!localVarAssignments.getInVars().containsKey(bv)
				// && !localVarAssignments.getOutVars().containsKey(bv)) {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
				// }
			} else {
				// if is global var of modifiable oldvar we rename var to oldvar
				if (!bv.isOldvar() && oldVarAssignments.getInVars().containsKey(bv)) {
					varsToRenameInPredInBoth.put(bv.getTermVariable(), ((BoogieNonOldVar) bv).getOldVar().getTermVariable());
				}
				
				if (!globalVarAssignments.getInVars().containsKey(bv)
						&& !globalVarAssignments.getOutVars().containsKey(bv)) {
					if (bv.isOldvar()) {
						TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
						varsToRenameInPredInBoth.put(bv.getTermVariable(), freshVar);
						varsToQuantifyNonModOldVars.add(freshVar);
					}
				}
			}
		}
		substitution.clear();

		// 2.1 Rename the invars of the term of Call-Statement.
		for (BoogieVar bv : localVarAssignments.getInVars().keySet()) {

			if (globalVarAssignments.getOutVars().containsKey(bv)) {
				// If it is a global var, then we substitute it through its
				// oldvar
				substitution.put(localVarAssignments.getInVars().get(bv), ((BoogieNonOldVar) bv).getOldVar()
						.getTermVariable());
			} else {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				substitution.put(localVarAssignments.getInVars().get(bv), freshVar);
				varsToRenameInPredPendingCall.put(bv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(bv.getTermVariable());
			}
		}
		Term call_TermInVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(localVarAssignments
				.getFormula());
		substitution.clear();

		Term predNonModOldVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredInBoth).transform(p.getFormula());

		final Term quantified;
		if (isPendingCall) {
			// 2.2 Rename the outvars of the term of the Call-Statement.
			for (BoogieVar bv : localVarAssignments.getOutVars().keySet()) {
				substitution.put(localVarAssignments.getOutVars().get(bv), bv.getTermVariable());
			}
			Term callTermInvarsRenamedOutVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(call_TermInVarsRenamed);
			// Rename the invars of CAll, local Vars and old version of global
			// variables.
			Term predRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredPendingCall)
					.transform(predNonModOldVarsRenamed);
			Term predANDCallANDGlobalVars = Util.and(mScript, predRenamed, callTermInvarsRenamedOutVarsRenamed,
					globalVarsInVarsRenamedOutVarsRenamed);
			varsToQuantifyPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyPendingCall.addAll(allAuxVars);

			quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyNonPendingCall, predANDCallANDGlobalVars);
		} else {
			Term predRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredNonPendingCall)
					.transform(predNonModOldVarsRenamed);
			varsToQuantifyNonPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyNonPendingCall.addAll(allAuxVars);
			
			Term result = Util.and(mScript, predRenamed, globalVarsInVarsRenamedOutVarsRenamed);
			quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyNonPendingCall, result);
		}
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;

	}

	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return
	 * statement and callerPred is the predicate that held in the calling
	 * procedure before the corresponding call. TODO: How is it computed?
	 */
	public Term strongestPostcondition(IPredicate calleePred, IPredicate callerPred, TransFormula ret_TF,
			TransFormula callTF, TransFormula globalVarsAssignment, TransFormula oldVarsAssignment) {
		// VarsToQuantify contains local vars of called procedure, and it may
		// contain
		// some invars, if it was a recursive call, i.e. callingProc =
		// calledProc.
		Set<TermVariable> varsToQuantifyOverAll = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCalleePred = new HashSet<TermVariable>();
		Set<TermVariable> varsToQuantifyInCallerPredAndCallTF = new HashSet<TermVariable>();
		Map<Term, Term> varsToRenameInCalleePred = new HashMap<Term, Term>();
		Map<Term, Term> varsToRenameInCallerPred = new HashMap<Term, Term>();
		Map<Term, Term> outVarsToRenameInCallTF = new HashMap<Term, Term>();
		Map<Term, Term> inVarsToRenameInReturnTF = new HashMap<Term, Term>();
		Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(ret_TF.getAuxVars());
		allAuxVars.addAll(callTF.getAuxVars());
		allAuxVars.addAll(globalVarsAssignment.getAuxVars());

		// Substitute oldvars of modifiable global vars by fresh vars in
		// calleePred
		// and substitue their non-oldvar by the same fresh var in callerPred.
		for (BoogieVar bv : globalVarsAssignment.getInVars().keySet()) {
			TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
			varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
			varsToRenameInCallerPred.put((((BoogieOldVar) bv).getNonOldVar()).getTermVariable(), freshVar);
			varsToQuantifyOverAll.add(freshVar);
		}
		// Note: We have to take also the outvars into account, because
		// sometimes it may be the case,
		// that a invar does not occur in the outvars.
		for (BoogieVar bv : globalVarsAssignment.getOutVars().keySet()) {
			// We have only to check the vars, that are not contained in the map
			// varsToRenameInCallerPred,
			// because otherwise it is already treated in the case above.
			if (!bv.isOldvar() && !varsToRenameInCallerPred.containsKey(bv.getTermVariable())) {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
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
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callTF.getInVars().containsKey(bv)) {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (callerPred.getVars().contains(bv)) {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(bv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(bv), freshVar);
				}
				if (callTF.getOutVars().containsKey(bv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(bv), freshVar);
				}
			} else if (!ret_TF.getInVars().containsKey(bv) && !callTF.getOutVars().containsKey(bv)) {
				if (!mModifiableGlobalVariableManager.getGlobals().containsKey(bv.getIdentifier())) {
					varsToQuantifyInCalleePred.add(bv.getTermVariable());
				}
			}

		}

		// 1.1 We doesn't rename the invars of the TransFormula Return,
		// because we quantify them out.
		Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (BoogieVar bv : ret_TF.getInVars().keySet()) {
			if (!inVarsToRenameInReturnTF.containsKey(ret_TF.getInVars().get(bv))) {
				TermVariable substitutor = ret_TF.getInVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}
		// 1.2 Rename outvars of Return statement
		for (BoogieVar bv : ret_TF.getOutVars().keySet()) {
			if (calleePred.getVars().contains(bv)) {
				if (!varsToRenameInCalleePred.containsKey(bv.getTermVariable())) {
					TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
					varsToRenameInCalleePred.put(bv.getTermVariable(), freshVar);
					varsToQuantifyOverAll.add(freshVar);
				}
			}
			substitution.put(ret_TF.getOutVars().get(bv), bv.getTermVariable());
			varsToQuantifyInCallerPredAndCallTF.add(bv.getTermVariable());
		}
		Term retTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, inVarsToRenameInReturnTF).transform(ret_TF.getFormula());
		retTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(retTermRenamed);
		// 2.1 Rename invars of TransFormula of corresponding Call statement
		substitution.clear();
		for (BoogieVar bv : callTF.getInVars().keySet()) {
			if (ret_TF.getOutVars().containsKey(bv)) {
				TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
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
		Term callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, outVarsToRenameInCallTF).transform(callTF.getFormula());
		callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callTermRenamed);
		// 2.2 We doesn't rename the outvars, because the outvars are the
		// localvars
		// of the called procedure, therefore we want to quantify them out.
		for (BoogieVar bv : callTF.getOutVars().keySet()) {
			if (!outVarsToRenameInCallTF.containsKey(callTF.getOutVars().get(bv))) {
				TermVariable substitutor = callTF.getOutVars().get(bv);
				varsToRenameInCalleePred.put(bv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}

		// 3. Rename the vars in calleePred, which occur as an outvar in the
		// TransFormula of Return Statement, or
		// which occur as an invar in the TransFormula of the corresponding Call
		// statement.
		// This substitution is only necessary, if we have a recursive call.
		Term calleePredVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCalleePred).transform(calleePred
				.getFormula());

		// 5. Substitute oldvars through fresh variables in calleePredicate.
		Term calleePredVarsRenamedOldVarsToFreshVars = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCalleePred)
				.transform(calleePredVarsRenamed);

		// 6. Substitute the global variables in callerPred through the fresh
		// Vars computed in (4).
		Term callerPredVarsRenamedToFreshVars = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCallerPred)
				.transform(callerPred.getFormula());

		// 1. CalleePredRenamed and loc vars quantified
		Term calleePredRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger, mScript, mVariableManager,
				Script.EXISTS, varsToQuantifyInCalleePred,
				calleePredVarsRenamedOldVarsToFreshVars, (Term[][]) null);
		// 2. CallTF and callerPred
		Term calleRPredANDCallTFRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger,
				mScript, mVariableManager, Script.EXISTS, varsToQuantifyInCallerPredAndCallTF, 
				Util.and(mScript,
						callerPredVarsRenamedToFreshVars, callTermRenamed), (Term[][]) null);
		// 3. Result
		varsToQuantifyOverAll.addAll(allAuxVars);

		final Term result = Util.and(mScript, calleePredRenamedQuantified, retTermRenamed, calleRPredANDCallTFRenamedQuantified);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyOverAll, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;

	}
	

	public Term weakestPrecondition(IPredicate p, TransFormula tf) {
		if (SmtUtils.isTrue(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		IValueConstruction<BoogieVar, TermVariable> substituentConstruction = new IValueConstruction<BoogieVar, TermVariable>() {

			@Override
			public TermVariable constructValue(BoogieVar bv) {
				final TermVariable result = mVariableManager.constructFreshTermVariable(bv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		ConstructionCache<BoogieVar, TermVariable> termVariablesForSuccessor = new ConstructionCache<>(substituentConstruction);
		
		Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		Map<Term, Term> substitutionForSuccessor = new HashMap<Term, Term>();
		
		for (Entry<BoogieVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			BoogieVar bv = entry.getKey();
			if (entry.getValue() == tf.getInVars().get(bv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				TermVariable substituent = termVariablesForSuccessor.getOrConstuct(bv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(bv)) {
					substitutionForSuccessor.put(bv.getTermVariable(), substituent);
				}
			}
		}

		for (Entry<BoogieVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getOutVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				TermVariable substituent = termVariablesForSuccessor.getOrConstuct(entry.getKey());
				substitutionForSuccessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedSuccessor = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForSuccessor).transform(p.getFormula());
			
		final Term result = Util.or(mScript, SmtUtils.not(mScript, renamedTransFormula), renamedSuccessor);
		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;
	}

	/**
	 * Responsible for computing WP of a Call statement.
	 * 
	 */
	public Term weakestPrecondition(IPredicate calleePred, TransFormula call_TF,
			TransFormula globalVarsAssignments, TransFormula oldVarsAssignments, 
			Set<BoogieVar> modifiableGlobals) {
		
		InstanceProviderWpCall ip = new InstanceProviderWpCall(modifiableGlobals);
		
		Term calleePredRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (BoogieVar bv : calleePred.getVars()) {
				substitution.put(bv.getTermVariable(), ip.getOrConstuctAfterCallInstance(bv));
			}
			calleePredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(calleePred.getFormula());
		}
		
		final Term call_TFrenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (Entry<BoogieVar, TermVariable> entry : call_TF.getInVars().entrySet()) {
				TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (Entry<BoogieVar, TermVariable> entry : call_TF.getOutVars().entrySet()) {
				TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), afterCallInstance);
			}
			call_TFrenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(call_TF.getFormula());
		}
		
		final Term globalVarsAssignmentsRenamed;
		{
			// for the global vars assignment, we use only "after call instances"
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (Entry<BoogieVar, TermVariable> entry : globalVarsAssignments.getInVars().entrySet()) {
				assert entry.getKey().isOldvar();
				TermVariable beforeCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (Entry<BoogieVar, TermVariable> entry : globalVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					// do nothing
				} else {
					TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				}
			}
			globalVarsAssignmentsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(globalVarsAssignments.getFormula());
		}
		
		final Term oldVarsAssignmentsRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (Entry<BoogieVar, TermVariable> entry : oldVarsAssignments.getInVars().entrySet()) {
				assert !entry.getKey().isOldvar();
				TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (Entry<BoogieVar, TermVariable> entry : oldVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				} else {
					// do nothing
				}
			}
			oldVarsAssignmentsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(oldVarsAssignments.getFormula());
		}

		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ip.getFreshTermVariables());
		Term result = Util.or(mScript,
				SmtUtils.not(mScript, Util.and(mScript, call_TFrenamed, globalVarsAssignmentsRenamed, oldVarsAssignmentsRenamed)),
				calleePredRenamed);
		varsToQuantify.addAll(call_TF.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mVariableManager).transform(quantified);
		return pushed;

	}

	/**
	 * Computes weakest precondition of a Return statement. oldvars of
	 * modifiable global variables are renamed to their representatives, and
	 * they are substituted in caller predicate and returner predicate to same
	 * fresh variables modifiable global variables are renamed to fresh
	 * variables and their occurrence in the caller predicate is substituted by
	 * the same fresh variables. InVars of returnTF are renamed to
	 * representatives, their occurrence in ..
	 * @param varsOccurringBetweenCallAndReturn 
	 * 
	 */
	public Term weakestPrecondition(IPredicate returnerPred, IPredicate callerPred, TransFormula returnTF,
			TransFormula callTF, TransFormula globalVarsAssignments, TransFormula oldVarAssignments,
			Set<BoogieVar> modifiableGlobals, Set<BoogieVar> varsOccurringBetweenCallAndReturn) {
		InstanceProviderWpReturn ir = new InstanceProviderWpReturn(modifiableGlobals, varsOccurringBetweenCallAndReturn, returnTF.getAssignedVars());
		
		
		final Term globalVarsRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			if (globalVarsAssignments != null) {
				for (Entry<BoogieVar, TermVariable> entry : globalVarsAssignments.getInVars().entrySet()) {
					BoogieOldVar oldVar = (BoogieOldVar) entry.getKey(); 
					substitution.put(entry.getValue(), oldVar.getTermVariable());
				}
				for (Entry<BoogieVar, TermVariable> entry : globalVarsAssignments.getOutVars().entrySet()) {
					if (entry.getKey() instanceof BoogieNonOldVar) {
						TermVariable beforeCallInstance = 
								ir.getOrConstuctBeforeCallInstance(entry.getKey());
						substitution.put(entry.getValue(), beforeCallInstance);
					} else {
						assert (entry.getKey() instanceof BoogieOldVar);
					}
				}
				globalVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(globalVarsAssignments.getFormula());
			} else {
				for (Entry<BoogieVar, TermVariable> entry : oldVarAssignments.getOutVars().entrySet()) {
					BoogieOldVar oldVar = (BoogieOldVar) entry.getKey(); 
					substitution.put(entry.getValue(), oldVar.getTermVariable());
				}
				for (Entry<BoogieVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
					if (entry.getKey() instanceof BoogieNonOldVar) {
						TermVariable beforeCallInstance = 
								ir.getOrConstuctBeforeCallInstance(entry.getKey());
						substitution.put(entry.getValue(), beforeCallInstance);
					} else {
						assert (entry.getKey() instanceof BoogieOldVar);
					}
				}
				globalVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(oldVarAssignments.getFormula());
			}
		}
		
		final Term returnTermRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (Entry<BoogieVar, TermVariable> entry : returnTF.getInVars().entrySet()) {
				TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			for (Entry<BoogieVar, TermVariable> entry : returnTF.getOutVars().entrySet()) {
				TermVariable afterReturnInstance = 
						ir.getOrConstuctAfterReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), afterReturnInstance);
			}
			returnTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(returnTF.getFormula());
		}
		
		final Term callTermRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (Entry<BoogieVar, TermVariable> entry : callTF.getInVars().entrySet()) {
				TermVariable beforeCallInstance = 
						ir.getOrConstuctBeforeCallInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (Entry<BoogieVar, TermVariable> entry : callTF.getOutVars().entrySet()) {
				TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callTF.getFormula());
		}
		
		Term callerPredRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (BoogieVar bv : callerPred.getVars()) {
				substitution.put(bv.getTermVariable(), ir.getOrConstuctBeforeCallInstance(bv));
			}
			callerPredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callerPred.getFormula());
		}
		
		Term returnPredRenamed;
		{
			Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (BoogieVar bv : returnerPred.getVars()) {
				substitution.put(bv.getTermVariable(), ir.getOrConstuctAfterReturnInstance(bv));
			}
			returnPredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(returnerPred.getFormula());
		}

		Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ir.getFreshTermVariables());
		assert(callTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		assert(returnTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		assert(globalVarsAssignments.getAuxVars().isEmpty()) : "no auxvars allowed";
		if (callerPredRenamed instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula) callerPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.EXISTS) {
//			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				mLogger.warn("universally quantified caller pred");
//				throw new UnsupportedOperationException("only existentially quantified callerPred supported, but obtained " + callerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			callerPredRenamed = ((QuantifiedFormula) callerPredRenamed).getSubformula();
		}
		if (returnPredRenamed instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedFormula = (QuantifiedFormula) returnPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				throw new UnsupportedOperationException("only universally quantified returnPred supported, but obtained " + returnerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			returnPredRenamed = ((QuantifiedFormula) returnPredRenamed).getSubformula();
		}

		Term callerPredANDCallANDReturnAndGlobalVars = Util.and(mScript, callerPredRenamed, returnTermRenamed,
				callTermRenamed, globalVarsRenamed);

		Term result = Util.or(mScript, SmtUtils.not(mScript, callerPredANDCallANDReturnAndGlobalVars), returnPredRenamed);
		return SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
	}
	

	/**
	 * return true if varsOccurringBetweenCallAndReturn contains bv or 
	 * varsOccurringBetweenCallAndReturn is null (which means that the return
	 * is a pending return and possibly all vars may occur before return)
	 * @param bv
	 * @return
	 */
	private boolean varOccursBetweenCallAndReturn(
			Set<BoogieVar> varsOccurringBetweenCallAndReturn, BoogieVar bv) {
		if (varsOccurringBetweenCallAndReturn == null) {
			return true;
		} else {
			return varsOccurringBetweenCallAndReturn.contains(bv);
		}
	}
	
	/**
	 * Return instances of BoogieVars for computation of weakest precondition
	 * for call statements.
	 * Each instance is represented by a TermVariable.
	 * Each BoogieVar can have up to two instances: "before call" and 
	 * "after call".
	 * An instance can be the representative TermVariable for this BoogieVar
	 * of a fresh auxiliary variable. 
	 *  Objects of this class construct the fresh variables on demand and return
	 * the correct instances (which means it checks that for coinciding 
	 * instances a common TermVariable is returned). 
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	private class InstanceProviderWpCall {
		private final Set<BoogieVar> mModifiableGlobals;
		private final IValueConstruction<BoogieVar, TermVariable> mValueConstruction = new IValueConstruction<BoogieVar, TermVariable>() {
			@Override
			public TermVariable constructValue(BoogieVar bv) {
				return mVariableManager.constructFreshTermVariable(bv);
			}
		};
		private final ConstructionCache<BoogieVar, TermVariable> mFreshVariables = new ConstructionCache<>(mValueConstruction);
		
		public InstanceProviderWpCall(Set<BoogieVar> modifiableGlobals) {
			super();
			mModifiableGlobals = modifiableGlobals;
		}

		public TermVariable getOrConstuctBeforeCallInstance(BoogieVar bv) {
			return bv.getTermVariable();
		}

		public TermVariable getOrConstuctAfterCallInstance(BoogieVar bv) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return mFreshVariables.getOrConstuct(bv);
				} else {
					if (mModifiableGlobals.contains(bv)) {
						return mFreshVariables.getOrConstuct(bv);
					} else {
						return bv.getTermVariable();
					}
				}
			} else {
				return mFreshVariables.getOrConstuct(bv);
			}
		}
		
		public Collection<TermVariable> getFreshTermVariables() {
			return mFreshVariables.getMap().values();
		}
	}
	
	/**
	 * Return instances of BoogieVars for computation of weakest precondition
	 * for return statements.
	 * Each instance is represented by a TermVariable.
	 * Each BoogieVar can have up to three instances: "Before call", (directly)
	 * "before return", and "after return".
	 * An instance can be the representative TermVariable for this BoogieVar
	 * of a fresh auxiliary variable. In some cases these instances 
	 * (fresh auxiliary variable) coincide.
	 * Objects of this class construct the fresh variables on demand and return
	 * the correct instances (which means it checks that for coinciding 
	 * instances a common TermVariable is returned). 
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	private class InstanceProviderWpReturn {
		private final Map<BoogieVar, TermVariable> mBeforeCall = new HashMap<BoogieVar, TermVariable>();
		private final Map<BoogieVar, TermVariable> mAfterReturn = new HashMap<BoogieVar, TermVariable>();
		private final Map<BoogieVar, TermVariable> mBeforeAfterCallCoincide = new HashMap<BoogieVar, TermVariable>();
		private final Set<BoogieVar> mModifiableGlobals;
		private final Set<BoogieVar> mVarsOccurringBetweenCallAndReturn;
		private final Set<BoogieVar> mAssignedOnReturn;
		private final Set<TermVariable> mFreshTermVariables = new HashSet<TermVariable>();
		
		public InstanceProviderWpReturn(Set<BoogieVar> modifiableGlobals,
				Set<BoogieVar> varsOccurringBetweenCallAndReturn,
				Set<BoogieVar> assignedOnReturn) {
			super();
			mModifiableGlobals = modifiableGlobals;
			mVarsOccurringBetweenCallAndReturn = varsOccurringBetweenCallAndReturn;
			mAssignedOnReturn = assignedOnReturn;
		}

		public TermVariable getOrConstuctBeforeCallInstance(BoogieVar bv) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, bv);
				} else {
					if (mModifiableGlobals.contains(bv)) {
						return getOrConstructTermVariable(mBeforeCall, bv);
					} else {
						if (doesVarOccurBetweenCallAndReturn((BoogieNonOldVar) bv)) {
							return bv.getTermVariable();
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(bv, mBeforeCall);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(bv, mBeforeCall);
			}
		}

		public TermVariable getOrConstuctBeforeReturnInstance(BoogieVar bv) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return bv.getTermVariable();
				} else {
					throw new AssertionError("illegal case");
				}
			} else {
				return bv.getTermVariable();
			}
		}
		
		public TermVariable getOrConstuctAfterReturnInstance(BoogieVar bv) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, bv);
				} else {
					if (mModifiableGlobals.contains(bv)) {
						if (mAssignedOnReturn.contains(bv)) {
							return getOrConstructTermVariable(mAfterReturn, bv);
						} else {
							return bv.getTermVariable();
						}
					} else {
						if (doesVarOccurBetweenCallAndReturn((BoogieNonOldVar) bv)) {
							if (mAssignedOnReturn.contains(bv)) {
								return getOrConstructTermVariable(mAfterReturn, bv);
							} else {
								return bv.getTermVariable();
							}
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(bv, mAfterReturn);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(bv, mAfterReturn);
			}
		}
		
		public Set<TermVariable> getFreshTermVariables() {
			return mFreshTermVariables;
		}

		private boolean doesVarOccurBetweenCallAndReturn(
				BoogieNonOldVar nonOld) {
			return mVarsOccurringBetweenCallAndReturn.contains(nonOld);
		}

		/**
		 * getOrConstructTermVariable for map if bv is assigned on return
		 * (which means instance before call and after return is different)
		 * and getOrConstructTermVariable for the mBeforeAfterCallCoincide map
		 * if the variable is not assigned on return.
		 */
		private TermVariable getOrConstructTermVariable_BeforeAndAfterIfNecessary(BoogieVar bv, Map<BoogieVar, TermVariable> map) {
			assert map == mBeforeCall || map == mAfterReturn;
			if (mAssignedOnReturn.contains(bv)) {
				return getOrConstructTermVariable(map, bv); 
			} else {
				return getOrConstructTermVariable(mBeforeAfterCallCoincide, bv);
			}
		}
		
		private TermVariable getOrConstructTermVariable(
				Map<BoogieVar, TermVariable> map, BoogieVar bv) {
			TermVariable tv = map.get(bv);
			if (tv == null) {
				tv = mVariableManager.constructFreshTermVariable(bv);
				mFreshTermVariables.add(tv);
				map.put(bv, tv);
			}
			return tv;
		}
		
	}


	private enum GlobalType {
		OLDVAR, NONOLDVAR
	}

	/**
	 * Returns copy of map restricted to keys that are of the given GlobalType
	 * (oldVar or nonOldVar).
	 */
	private Map<BoogieVar, TermVariable> restrictMap(Map<BoogieVar, TermVariable> map, GlobalType globalType) {
		Map<BoogieVar, TermVariable> result = new HashMap<BoogieVar, TermVariable>();
		for (Entry<BoogieVar, TermVariable> entry : map.entrySet()) {
			if ((globalType == GlobalType.OLDVAR) == (entry.getKey().isOldvar())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return result;
	}

	/**
	 * Substitutes in the given formula the values of the given map by fresh
	 * variables, and puts the substitution from the term variable to the same
	 * fresh variable into the second given map. It also adds the fresh variable
	 * to the given set.
	 * 
	 * @param varsToBeSubstituted
	 *            - the occurrence of the values of this map in the given
	 *            formula are renamed to fresh variables
	 * @param formulaToBeSubstituted
	 *            - the formula in which the variables should be substituted
	 * @param varsToBeSubstitutedByFreshVars
	 *            - map to which the substitutions from corresponding term
	 *            variables to fresh variables should be added
	 * @param varsToQuantify
	 *            - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by
	 *         fresh variables
	 */
	private Term substituteToFreshVarsAndAddToQuantify(Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted, Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
			substitution.put(varsToBeSubstituted.get(bv), freshVar);
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(formulaToBeSubstituted);
	}

	/**
	 * Substitutes in the given formula the values of the given map by the keys
	 * of the given map. It also puts a substitution from the keys of the given
	 * map to fresh variables into the second given map and adds the fresh
	 * variables to the given set.
	 * 
	 * @param varsToBeSubstituted
	 *            - the occurrence of the values of this map in the given
	 *            formula are substituted by the keys of this map
	 * @param formulaToBeSubstituted
	 *            - the formula in which the variables should be substituted
	 * @param varsToBeSubstitutedByFreshVars
	 *            - map to which the substitutions from the keys of the map
	 *            "varsToBeSubstituted" to fresh variables should be added
	 * @param varsToQuantify
	 *            - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by
	 *         the corresponding term variables
	 */
	private Term substituteToRepresantativesAndAddToQuantify(Map<BoogieVar, TermVariable> varsToBeSubstituted,
			Term formulaToBeSubstituted, Map<Term, Term> varsToBeSubstitutedByFreshVars,
			Set<TermVariable> varsToQuantify) {
		Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (BoogieVar bv : varsToBeSubstituted.keySet()) {
			TermVariable freshVar = mVariableManager.constructFreshTermVariable(bv);
			substitution.put(varsToBeSubstituted.get(bv), bv.getTermVariable());
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(bv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(formulaToBeSubstituted);
	}

}

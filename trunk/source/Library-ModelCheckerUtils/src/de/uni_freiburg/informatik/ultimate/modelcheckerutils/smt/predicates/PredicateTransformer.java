/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * @author musab@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * 
 */
public class PredicateTransformer {
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public PredicateTransformer(final IUltimateServiceProvider services, final ManagedScript mgdScript, 
			final SimplicationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
	}
	
	private static TermVariable constructFreshTermVariable(final ManagedScript freshVarConstructor, final IProgramVar pv) {
		return freshVarConstructor.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
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
	public Term strongestPostcondition(final IPredicate p, final UnmodifiableTransFormula tf) {
		if (SmtUtils.isFalse(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result = constructFreshTermVariable(mMgdScript, pv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		final Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		final Map<Term, Term> substitutionForPredecessor = new HashMap<Term, Term>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (entry.getValue() == tf.getOutVars().get(pv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				final TermVariable substituent = termVariablesForPredecessor.getOrConstruct(pv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(pv)) {
					substitutionForPredecessor.put(pv.getTermVariable(), substituent);
				}
			}
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getInVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				final TermVariable substituent = termVariablesForPredecessor.getOrConstruct(entry.getKey());
				substitutionForPredecessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SubstitutionWithLocalSimplification(mMgdScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedPredecessor = new SubstitutionWithLocalSimplification(mMgdScript, substitutionForPredecessor).transform(p.getFormula());
			
		final Term result = Util.and(mScript, renamedTransFormula, renamedPredecessor);

		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
		return pushed;
	}

	public Term weakLocalPostconditionCall(final IPredicate p, final UnmodifiableTransFormula globalVarAssignments, final Set<IProgramVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		
		final Term renamedOldVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : globalVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedOldVarsAssignment = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(globalVarAssignments.getFormula());
		}

		final Term renamedPredicate;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			TermVariable substituent;
			for (final IProgramVar pv : p.getVars()) {
				if (pv instanceof IProgramNonOldVar) {
					if (modifiableGlobals.contains(pv)) {
						substituent = constructFreshTermVariable(mMgdScript, pv);
						varsToQuantify.add(substituent);
						substitutionMapping.put(pv.getTermVariable(), substituent);
					} else {
						// do nothing
					}
				} else if (pv instanceof IProgramOldVar) {
					substituent = constructFreshTermVariable(mMgdScript, pv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(pv.getTermVariable(), substituent);
				} else if (pv instanceof ILocalProgramVar) {
					substituent = constructFreshTermVariable(mMgdScript, pv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(pv.getTermVariable(), substituent);
				} else {
					throw new AssertionError();
				}
			}
			renamedPredicate = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(p.getFormula());
		}
		final Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedOldVarsAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
		return pushed;

	}
	
	
	public Term strongestPostconditionCall(final IPredicate p, final UnmodifiableTransFormula localVarAssignments,
			final UnmodifiableTransFormula globalVarAssignments, final UnmodifiableTransFormula oldVarAssignments, final Set<IProgramVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result;
				if (pv instanceof IProgramNonOldVar) {
					if (modifiableGlobals.contains(pv)) {
						result = constructFreshTermVariable(mMgdScript, pv);
						varsToQuantify.add(result);
					} else {
						result = pv.getTermVariable();
					}
				} else if (pv instanceof IProgramOldVar) {
					result = constructFreshTermVariable(mMgdScript, pv);
					varsToQuantify.add(result);
				} else if (pv instanceof ILocalProgramVar) {
					result = constructFreshTermVariable(mMgdScript, pv);
					varsToQuantify.add(result);
				} else {
					throw new AssertionError();
				}
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		final Term renamedGlobalVarAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : globalVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedGlobalVarAssignment = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(globalVarAssignments.getFormula());
		}
		
		final Term renamedOldVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : oldVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramOldVar);
				substitutionMapping.put(oldVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramNonOldVar);
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstruct(entry.getKey()));
			}
			renamedOldVarsAssignment = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(oldVarAssignments.getFormula());
		}
		
		final Term renamedLocalVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : localVarAssignments.getAssignedVars()) {
				assert (pv instanceof ILocalProgramVar);
				substitutionMapping.put(localVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : localVarAssignments.getInVars().entrySet()) {
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstruct(entry.getKey()));
			}
			renamedLocalVarsAssignment = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(localVarAssignments.getFormula());
		}
		
		final Term renamedPredicate;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : p.getVars()) {
				substitutionMapping.put(pv.getTermVariable(), termVariablesForPredecessor.getOrConstruct(pv));
			}
			renamedPredicate = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(p.getFormula());
		}
		final Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedLocalVarsAssignment, renamedOldVarsAssignment,
				renamedGlobalVarAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
		return pushed;

	}

	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return
	 * statement and callerPred is the predicate that held in the calling
	 * procedure before the corresponding call. TODO: How is it computed?
	 */
	public Term strongestPostcondition(final IPredicate calleePred, final IPredicate callerPred, final UnmodifiableTransFormula ret_TF,
			final UnmodifiableTransFormula callTF, final UnmodifiableTransFormula globalVarsAssignment, final UnmodifiableTransFormula oldVarsAssignment) {
		// VarsToQuantify contains local vars of called procedure, and it may
		// contain
		// some invars, if it was a recursive call, i.e. callingProc =
		// calledProc.
		final Set<TermVariable> varsToQuantifyOverAll = new HashSet<TermVariable>();
		final Set<TermVariable> varsToQuantifyInCalleePred = new HashSet<TermVariable>();
		final Set<TermVariable> varsToQuantifyInCallerPredAndCallTF = new HashSet<TermVariable>();
		final Map<Term, Term> varsToRenameInCalleePred = new HashMap<Term, Term>();
		final Map<Term, Term> varsToRenameInCallerPred = new HashMap<Term, Term>();
		final Map<Term, Term> outVarsToRenameInCallTF = new HashMap<Term, Term>();
		final Map<Term, Term> inVarsToRenameInReturnTF = new HashMap<Term, Term>();
		final Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(ret_TF.getAuxVars());
		allAuxVars.addAll(callTF.getAuxVars());
		allAuxVars.addAll(globalVarsAssignment.getAuxVars());

		// Substitute oldvars of modifiable global vars by fresh vars in
		// calleePred
		// and substitute their non-oldvar by the same fresh var in callerPred.
		for (final IProgramVar pv : globalVarsAssignment.getInVars().keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
			varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
			varsToRenameInCallerPred.put((((IProgramOldVar) pv).getNonOldVar()).getTermVariable(), freshVar);
			varsToQuantifyOverAll.add(freshVar);
		}
		// Note: We have to take also the outvars into account, because
		// sometimes it may be the case,
		// that a invar does not occur in the outvars.
		for (final IProgramVar pv : globalVarsAssignment.getOutVars().keySet()) {
			// We have only to check the vars, that are not contained in the map
			// varsToRenameInCallerPred,
			// because otherwise it is already treated in the case above.
			if (!pv.isOldvar() && !varsToRenameInCallerPred.containsKey(pv.getTermVariable())) {
				final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
				varsToRenameInCallerPred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
			}

		}

		// Collect the local variables of called proc
		for (final IProgramVar pv : calleePred.getVars()) {
			if (pv.isGlobal() || pv.isOldvar()) {
				continue;
			}
			if (ret_TF.getOutVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (callTF.getInVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (callerPred.getVars().contains(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (!ret_TF.getInVars().containsKey(pv) && !callTF.getOutVars().containsKey(pv)) {
				final boolean isGlobal = pv.isGlobal();
				if (!isGlobal) {
					varsToQuantifyInCalleePred.add(pv.getTermVariable());
				}
			}

		}

		// 1.1 We doesn't rename the invars of the TransFormula Return,
		// because we quantify them out.
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : ret_TF.getInVars().keySet()) {
			if (!inVarsToRenameInReturnTF.containsKey(ret_TF.getInVars().get(pv))) {
				final TermVariable substitutor = ret_TF.getInVars().get(pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}
		// 1.2 Rename outvars of Return statement
		for (final IProgramVar pv : ret_TF.getOutVars().keySet()) {
			if (calleePred.getVars().contains(pv)) {
				if (!varsToRenameInCalleePred.containsKey(pv.getTermVariable())) {
					final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
					varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
					varsToQuantifyOverAll.add(freshVar);
				}
			}
			substitution.put(ret_TF.getOutVars().get(pv), pv.getTermVariable());
			varsToQuantifyInCallerPredAndCallTF.add(pv.getTermVariable());
		}
		Term retTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, inVarsToRenameInReturnTF).transform(ret_TF.getFormula());
		retTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(retTermRenamed);
		// 2.1 Rename invars of TransFormula of corresponding Call statement
		substitution.clear();
		for (final IProgramVar pv : callTF.getInVars().keySet()) {
			if (ret_TF.getOutVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
				substitution.put(callTF.getInVars().get(pv), freshVar);
				varsToRenameInCallerPred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyInCallerPredAndCallTF.add(freshVar);
			} else if (globalVarsAssignment.getOutVars().containsKey(pv)) {
				final Term freshVar = varsToRenameInCallerPred.get(pv.getTermVariable());
				assert freshVar != null : "added null to substitution mapping";
				substitution.put(callTF.getInVars().get(pv), freshVar);
			} else {
				substitution.put(callTF.getInVars().get(pv), pv.getTermVariable());
			}
		}
		Term callTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, outVarsToRenameInCallTF).transform(callTF.getFormula());
		callTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(callTermRenamed);
		// 2.2 We doesn't rename the outvars, because the outvars are the
		// localvars
		// of the called procedure, therefore we want to quantify them out.
		for (final IProgramVar pv : callTF.getOutVars().keySet()) {
			if (!outVarsToRenameInCallTF.containsKey(callTF.getOutVars().get(pv))) {
				final TermVariable substitutor = callTF.getOutVars().get(pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}

		// 3. Rename the vars in calleePred, which occur as an outvar in the
		// TransFormula of Return Statement, or
		// which occur as an invar in the TransFormula of the corresponding Call
		// statement.
		// This substitution is only necessary, if we have a recursive call.
		final Term calleePredVarsRenamed = new SubstitutionWithLocalSimplification(mMgdScript, varsToRenameInCalleePred).transform(calleePred
				.getFormula());

		// 5. Substitute oldvars through fresh variables in calleePredicate.
		final Term calleePredVarsRenamedOldVarsToFreshVars = new SubstitutionWithLocalSimplification(mMgdScript, varsToRenameInCalleePred)
				.transform(calleePredVarsRenamed);

		// 6. Substitute the global variables in callerPred through the fresh
		// Vars computed in (4).
		final Term callerPredVarsRenamedToFreshVars = new SubstitutionWithLocalSimplification(mMgdScript, varsToRenameInCallerPred)
				.transform(callerPred.getFormula());

		// 1. CalleePredRenamed and loc vars quantified
		final Term calleePredRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger, mMgdScript, mSimplificationTechnique,
				mXnfConversionTechnique, Script.EXISTS, varsToQuantifyInCalleePred, calleePredVarsRenamedOldVarsToFreshVars,
				(Term[][]) null);
		// 2. CallTF and callerPred
		final Term calleRPredANDCallTFRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger,
				mMgdScript, mSimplificationTechnique, mXnfConversionTechnique, Script.EXISTS, varsToQuantifyInCallerPredAndCallTF, Util.and(mScript,
						callerPredVarsRenamedToFreshVars, callTermRenamed), 
				(Term[][]) null);
		// 3. Result
		varsToQuantifyOverAll.addAll(allAuxVars);

		final Term result = Util.and(mScript, calleePredRenamedQuantified, retTermRenamed, calleRPredANDCallTFRenamedQuantified);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyOverAll, result);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
		return pushed;

	}
	

	public Term weakestPrecondition(final IPredicate p, final UnmodifiableTransFormula tf) {
		if (SmtUtils.isTrue(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result = constructFreshTermVariable(mMgdScript, pv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForSuccessor = new ConstructionCache<>(substituentConstruction);
		
		final Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		final Map<Term, Term> substitutionForSuccessor = new HashMap<Term, Term>();
		
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (entry.getValue() == tf.getInVars().get(pv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				final TermVariable substituent = termVariablesForSuccessor.getOrConstruct(pv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(pv)) {
					substitutionForSuccessor.put(pv.getTermVariable(), substituent);
				}
			}
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getOutVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				final TermVariable substituent = termVariablesForSuccessor.getOrConstruct(entry.getKey());
				substitutionForSuccessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SubstitutionWithLocalSimplification(mMgdScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedSuccessor = new SubstitutionWithLocalSimplification(mMgdScript, substitutionForSuccessor).transform(p.getFormula());
			
		final Term result = Util.or(mScript, SmtUtils.not(mScript, renamedTransFormula), renamedSuccessor);
		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
		return pushed;
	}

	/**
	 * Responsible for computing WP of a Call statement.
	 * 
	 */
	public Term weakestPrecondition(final IPredicate calleePred, final UnmodifiableTransFormula call_TF,
			final UnmodifiableTransFormula globalVarsAssignments, final UnmodifiableTransFormula oldVarsAssignments, 
			final Set<IProgramVar> modifiableGlobals) {
		
		final InstanceProviderWpCall ip = new InstanceProviderWpCall(modifiableGlobals);
		
		Term calleePredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : calleePred.getVars()) {
				substitution.put(pv.getTermVariable(), ip.getOrConstuctAfterCallInstance(pv));
			}
			calleePredRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(calleePred.getFormula());
		}
		
		final Term call_TFrenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : call_TF.getInVars().entrySet()) {
				final TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : call_TF.getOutVars().entrySet()) {
				final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), afterCallInstance);
			}
			call_TFrenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(call_TF.getFormula());
		}
		
		final Term globalVarsAssignmentsRenamed;
		{
			// for the global vars assignment, we use only "after call instances"
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getInVars().entrySet()) {
				assert entry.getKey().isOldvar();
				final TermVariable beforeCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					// do nothing
				} else {
					final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				}
			}
			globalVarsAssignmentsRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(globalVarsAssignments.getFormula());
		}
		
		final Term oldVarsAssignmentsRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : oldVarsAssignments.getInVars().entrySet()) {
				assert !entry.getKey().isOldvar();
				final TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				} else {
					// do nothing
				}
			}
			oldVarsAssignmentsRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(oldVarsAssignments.getFormula());
		}

		final Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ip.getFreshTermVariables());
		final Term result = Util.or(mScript,
				SmtUtils.not(mScript, Util.and(mScript, call_TFrenamed, globalVarsAssignmentsRenamed, oldVarsAssignmentsRenamed)),
				calleePredRenamed);
		varsToQuantify.addAll(call_TF.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mMgdScript, mServices).transform(quantified);
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
	public Term weakestPrecondition(final IPredicate returnerPred, final IPredicate callerPred, 
			final UnmodifiableTransFormula returnTF, final UnmodifiableTransFormula callTF, 
			final UnmodifiableTransFormula globalVarsAssignments, final UnmodifiableTransFormula oldVarAssignments,
			final Set<IProgramVar> modifiableGlobals, final Set<IProgramVar> varsOccurringBetweenCallAndReturn) {
		assert(callTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		assert(returnTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		
		final InstanceProviderWpReturn ir = new InstanceProviderWpReturn(
				modifiableGlobals, varsOccurringBetweenCallAndReturn, returnTF.getAssignedVars());
		
		final Term oldVarsRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getOutVars().entrySet()) {
				if (entry.getKey() instanceof IProgramNonOldVar) {
					assert oldVarAssignments.getInVars().containsKey(entry.getKey());
				} else if (entry.getKey() instanceof IProgramOldVar) {
					assert oldVarAssignments.getAssignedVars().contains(entry.getKey());
					final IProgramOldVar oldVar = (IProgramOldVar) entry.getKey(); 
					substitution.put(entry.getValue(), oldVar.getTermVariable());
				} else {
					throw new AssertionError("invalid structure of oldVars assignment");
				}
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
				if (entry.getKey() instanceof IProgramNonOldVar) {
					final TermVariable beforeCallInstance = 
							ir.getOrConstuctBeforeCallInstance(entry.getKey());
					substitution.put(entry.getValue(), beforeCallInstance);
				} else {
					throw new AssertionError("invalid structure of oldVars assignment");
				}
			}
			oldVarsRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(oldVarAssignments.getFormula());
		}
		
		final Term returnTermRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : returnTF.getInVars().entrySet()) {
				final TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : returnTF.getOutVars().entrySet()) {
				final TermVariable afterReturnInstance = 
						ir.getOrConstuctAfterReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), afterReturnInstance);
			}
			returnTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(returnTF.getFormula());
		}
		
		final Term callTermRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : callTF.getInVars().entrySet()) {
				final TermVariable beforeCallInstance = 
						ir.getOrConstuctBeforeCallInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : callTF.getOutVars().entrySet()) {
				final TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			callTermRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(callTF.getFormula());
		}
		
		Term callerPredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : callerPred.getVars()) {
				substitution.put(pv.getTermVariable(), ir.getOrConstuctBeforeCallInstance(pv));
			}
			callerPredRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(callerPred.getFormula());
		}
		
		Term returnPredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : returnerPred.getVars()) {
				substitution.put(pv.getTermVariable(), ir.getOrConstuctAfterReturnInstance(pv));
			}
			returnPredRenamed = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(returnerPred.getFormula());
		}

		if (callerPredRenamed instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) callerPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.EXISTS) {
//			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				mLogger.warn("universally quantified caller pred");
//				throw new UnsupportedOperationException("only existentially quantified callerPred supported, but obtained " + callerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			callerPredRenamed = ((QuantifiedFormula) callerPredRenamed).getSubformula();
		}
		if (returnPredRenamed instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) returnPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				throw new UnsupportedOperationException("only universally quantified returnPred supported, but obtained " + returnerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			returnPredRenamed = ((QuantifiedFormula) returnPredRenamed).getSubformula();
		}

		final Term callerPredANDCallANDReturnAndGlobalVars = Util.and(mScript, callerPredRenamed, returnTermRenamed,
				callTermRenamed, oldVarsRenamed);

		final Term result = Util.or(mScript, SmtUtils.not(mScript, callerPredANDCallANDReturnAndGlobalVars), returnPredRenamed);
		final Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ir.getFreshTermVariables());
		return SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
	}
	

	/**
	 * return true if varsOccurringBetweenCallAndReturn contains pv or 
	 * varsOccurringBetweenCallAndReturn is null (which means that the return
	 * is a pending return and possibly all vars may occur before return)
	 * @param pv
	 * @return
	 */
	private boolean varOccursBetweenCallAndReturn(
			final Set<IProgramVar> varsOccurringBetweenCallAndReturn, final IProgramVar pv) {
		if (varsOccurringBetweenCallAndReturn == null) {
			return true;
		} else {
			return varsOccurringBetweenCallAndReturn.contains(pv);
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
		private final Set<IProgramVar> mModifiableGlobals;
		private final IValueConstruction<IProgramVar, TermVariable> mValueConstruction = new IValueConstruction<IProgramVar, TermVariable>() {
			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				return constructFreshTermVariable(mMgdScript, pv);
			}
		};
		private final ConstructionCache<IProgramVar, TermVariable> mFreshVariables = new ConstructionCache<>(mValueConstruction);
		
		public InstanceProviderWpCall(final Set<IProgramVar> modifiableGlobals) {
			super();
			mModifiableGlobals = modifiableGlobals;
		}

		public TermVariable getOrConstuctBeforeCallInstance(final IProgramVar pv) {
			return pv.getTermVariable();
		}

		public TermVariable getOrConstuctAfterCallInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return mFreshVariables.getOrConstruct(pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						return mFreshVariables.getOrConstruct(pv);
					} else {
						return pv.getTermVariable();
					}
				}
			} else {
				return mFreshVariables.getOrConstruct(pv);
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
		private final Map<IProgramVar, TermVariable> mBeforeCall = new HashMap<IProgramVar, TermVariable>();
		private final Map<IProgramVar, TermVariable> mAfterReturn = new HashMap<IProgramVar, TermVariable>();
		private final Map<IProgramVar, TermVariable> mBeforeAfterCallCoincide = new HashMap<IProgramVar, TermVariable>();
		private final Set<IProgramVar> mModifiableGlobals;
		private final Set<IProgramVar> mVarsOccurringBetweenCallAndReturn;
		private final Set<IProgramVar> mAssignedOnReturn;
		private final Set<TermVariable> mFreshTermVariables = new HashSet<TermVariable>();
		
		public InstanceProviderWpReturn(final Set<IProgramVar> modifiableGlobals,
				final Set<IProgramVar> varsOccurringBetweenCallAndReturn,
				final Set<IProgramVar> assignedOnReturn) {
			super();
			mModifiableGlobals = modifiableGlobals;
			mVarsOccurringBetweenCallAndReturn = varsOccurringBetweenCallAndReturn;
			mAssignedOnReturn = assignedOnReturn;
		}

		public TermVariable getOrConstuctBeforeCallInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						return getOrConstructTermVariable(mBeforeCall, pv);
					} else {
						if (doesVarOccurBetweenCallAndReturn((IProgramNonOldVar) pv)) {
							return pv.getTermVariable();
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mBeforeCall);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mBeforeCall);
			}
		}

		public TermVariable getOrConstuctBeforeReturnInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return pv.getTermVariable();
				} else {
					throw new AssertionError("illegal case");
				}
			} else {
				return pv.getTermVariable();
			}
		}
		
		public TermVariable getOrConstuctAfterReturnInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						if (mAssignedOnReturn.contains(pv)) {
							return getOrConstructTermVariable(mAfterReturn, pv);
						} else {
							return pv.getTermVariable();
						}
					} else {
						if (doesVarOccurBetweenCallAndReturn((IProgramNonOldVar) pv)) {
							if (mAssignedOnReturn.contains(pv)) {
								return getOrConstructTermVariable(mAfterReturn, pv);
							} else {
								return pv.getTermVariable();
							}
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mAfterReturn);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mAfterReturn);
			}
		}
		
		public Set<TermVariable> getFreshTermVariables() {
			return mFreshTermVariables;
		}

		private boolean doesVarOccurBetweenCallAndReturn(
				final IProgramNonOldVar nonOld) {
			return mVarsOccurringBetweenCallAndReturn.contains(nonOld);
		}

		/**
		 * getOrConstructTermVariable for map if pv is assigned on return
		 * (which means instance before call and after return is different)
		 * and getOrConstructTermVariable for the mBeforeAfterCallCoincide map
		 * if the variable is not assigned on return.
		 */
		private TermVariable getOrConstructTermVariable_BeforeAndAfterIfNecessary(final IProgramVar pv, final Map<IProgramVar, TermVariable> map) {
			assert map == mBeforeCall || map == mAfterReturn;
			if (mAssignedOnReturn.contains(pv)) {
				return getOrConstructTermVariable(map, pv); 
			} else {
				return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
			}
		}
		
		private TermVariable getOrConstructTermVariable(
				final Map<IProgramVar, TermVariable> map, final IProgramVar pv) {
			TermVariable tv = map.get(pv);
			if (tv == null) {
				tv = constructFreshTermVariable(mMgdScript, pv);
				mFreshTermVariables.add(tv);
				map.put(pv, tv);
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
	private Map<IProgramVar, TermVariable> restrictMap(final Map<IProgramVar, TermVariable> map, final GlobalType globalType) {
		final Map<IProgramVar, TermVariable> result = new HashMap<IProgramVar, TermVariable>();
		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
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
	private Term substituteToFreshVarsAndAddToQuantify(final Map<IProgramVar, TermVariable> varsToBeSubstituted,
			final Term formulaToBeSubstituted, final Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			final Set<TermVariable> varsToQuantify) {
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : varsToBeSubstituted.keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
			substitution.put(varsToBeSubstituted.get(pv), freshVar);
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(pv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(formulaToBeSubstituted);
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
	private Term substituteToRepresantativesAndAddToQuantify(final Map<IProgramVar, TermVariable> varsToBeSubstituted,
			final Term formulaToBeSubstituted, final Map<Term, Term> varsToBeSubstitutedByFreshVars,
			final Set<TermVariable> varsToQuantify) {
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : varsToBeSubstituted.keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mMgdScript, pv);
			substitution.put(varsToBeSubstituted.get(pv), pv.getTermVariable());
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(pv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(formulaToBeSubstituted);
	}
}

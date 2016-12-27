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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.CallReturnPyramideInstanceProvider.Instance;
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
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public PredicateTransformer(final IUltimateServiceProvider services, final ManagedScript mgdScript, 
			final SimplificationTechnique simplificationTechnique,
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

	public Term weakLocalPostconditionCall(final IPredicate p, final UnmodifiableTransFormula globalVarAssignments, final Set<IProgramNonOldVar> modifiedGlobals) {
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
					if (modifiedGlobals.contains(pv)) {
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
	
	
	public Term strongestPostconditionCall(final IPredicate callPred, final UnmodifiableTransFormula localVarAssignments,
			final UnmodifiableTransFormula globalVarAssignments, final UnmodifiableTransFormula oldVarAssignments, 
			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure) {
		
		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript, 
				Collections.emptySet(), localVarAssignments.getAssignedVars(), modifiableGlobalsOfCalledProcedure, Instance.AFTER_CALL);
		final Term callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final Term localVarAssignmentsTerm = renameTransFormulaToInstances(localVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term oldVarsAssignmentTerm = renameTransFormulaToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term globalVarsAssignmentTerm = renameTransFormulaToInstances(globalVarAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final Term result = Util.and(mScript,
				localVarAssignmentsTerm,
				oldVarsAssignmentTerm,
				globalVarsAssignmentTerm,
				callPredTerm);
		
		final Set<TermVariable> varsToQuantify = new HashSet<>(crpip.getFreshTermVariables());
		return SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, result);

	}
	
	public Term strongestPreconditionReturn(final IPredicate returnPred, final IPredicate callPred,  
			final UnmodifiableTransFormula returnTF, final UnmodifiableTransFormula callTF, 
			final UnmodifiableTransFormula oldVarAssignments,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		
		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript, 
				returnTF.getAssignedVars(), callTF.getAssignedVars(), modifiableGlobals, Instance.AFTER_RETURN);
		final Term callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final Term returnPredTerm = renamePredicateToInstance(returnPred, Instance.BEFORE_RETURN, crpip);
		final Term callTfTerm = renameTransFormulaToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term oldVarsAssignmentTerm = renameTransFormulaToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term returnTfTerm = renameTransFormulaToInstances(returnTF, Instance.BEFORE_RETURN, Instance.AFTER_RETURN, crpip);

		final Term result = Util.and(mScript,
				callTfTerm,
				oldVarsAssignmentTerm,
				returnTfTerm,
				callPredTerm,
				returnPredTerm);
		
		final Set<TermVariable> varsToQuantify = new HashSet<>(crpip.getFreshTermVariables());
		return SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, result);
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
			final Set<IProgramNonOldVar> modifiableGlobals) {
		
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

	
	

	
	
	
	
	public Term weakestPreconditionCall(final IPredicate callSucc, final UnmodifiableTransFormula callTF, 
			final UnmodifiableTransFormula globalVarsAssignments, final UnmodifiableTransFormula oldVarAssignments,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		
		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript, 
				Collections.emptySet(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_CALL);
		final Term callSuccTerm = renamePredicateToInstance(callSucc, Instance.AFTER_CALL, crpip);
		final Term callTfTerm = renameTransFormulaToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term oldVarsAssignmentTerm = renameTransFormulaToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term globalVarsAssignmentTerm = renameTransFormulaToInstances(globalVarsAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final Term result = Util.or(mScript,
				SmtUtils.not(mScript, callTfTerm),
				SmtUtils.not(mScript, oldVarsAssignmentTerm),
				SmtUtils.not(mScript, globalVarsAssignmentTerm),
				callSuccTerm); 
		
		final Set<TermVariable> varsToQuantify = new HashSet<>(crpip.getFreshTermVariables());
		return SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
	}
	
	
	public Term weakestPreconditionReturn(final IPredicate returnSucc, final IPredicate callPred, 
			final UnmodifiableTransFormula returnTF, final UnmodifiableTransFormula callTF, 
			final UnmodifiableTransFormula oldVarAssignments,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		
		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript, 
				returnTF.getAssignedVars(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_RETURN);
		final Term callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final Term returnSuccTerm = renamePredicateToInstance(returnSucc, Instance.AFTER_RETURN, crpip);
		final Term callTfTerm = renameTransFormulaToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term oldVarsAssignmentTerm = renameTransFormulaToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final Term returnTfTerm = renameTransFormulaToInstances(returnTF, Instance.BEFORE_RETURN, Instance.AFTER_RETURN, crpip);

		final Term result = Util.or(mScript,
				SmtUtils.not(mScript, callTfTerm),
				SmtUtils.not(mScript, oldVarsAssignmentTerm),
				SmtUtils.not(mScript, returnTfTerm),
				SmtUtils.not(mScript, callPredTerm),
				returnSuccTerm);
		
		final Set<TermVariable> varsToQuantify = new HashSet<>(crpip.getFreshTermVariables());
		return SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
	}
	
	
	
	private Term renamePredicateToInstance(final IPredicate p, final Instance instance, final CallReturnPyramideInstanceProvider crpip) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final IProgramVar pv : p.getVars()) {
			substitution.put(pv.getTermVariable(), crpip.getInstance(pv, instance));
		}
		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(p.getFormula());
		return result;
	}
	
	private Term renameTransFormulaToInstances(final TransFormula tf, final Instance preInstance, final Instance succInstance, final CallReturnPyramideInstanceProvider crpip) {
		
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitution.put(entry.getValue(), crpip.getInstance(entry.getKey(), succInstance));
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitution.put(entry.getValue(), crpip.getInstance(entry.getKey(), preInstance));
		}
		final Term result = new SubstitutionWithLocalSimplification(mMgdScript, substitution).transform(tf.getFormula());
		return result;
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
		private final Set<IProgramNonOldVar> mModifiableGlobals;
		private final IValueConstruction<IProgramVar, TermVariable> mValueConstruction = new IValueConstruction<IProgramVar, TermVariable>() {
			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				return constructFreshTermVariable(mMgdScript, pv);
			}
		};
		private final ConstructionCache<IProgramVar, TermVariable> mFreshVariables = new ConstructionCache<>(mValueConstruction);
		
		public InstanceProviderWpCall(final Set<IProgramNonOldVar> modifiableGlobals) {
			super();
			mModifiableGlobals = modifiableGlobals;
		}

		public TermVariable getOrConstuctBeforeCallInstance(final IProgramVar pv) {
			return pv.getTermVariable();
		}

		public TermVariable getOrConstuctAfterCallInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv instanceof IProgramConst) {
					return pv.getTermVariable();
				} else if (pv instanceof IProgramOldVar) {
					return mFreshVariables.getOrConstruct(pv);
				} else if (pv instanceof IProgramNonOldVar) {
					if (mModifiableGlobals.contains(pv)) {
						return mFreshVariables.getOrConstruct(pv);
					} else {
						return pv.getTermVariable();
					}
				} else {
					throw new AssertionError("illegal IProgramVar " + pv.getClass().getSimpleName());
				}
			} else {
				assert (pv instanceof ILocalProgramVar) : "illegal IProgramVar " + pv.getClass().getSimpleName();
				return mFreshVariables.getOrConstruct(pv);
			}
		}
		
		public Collection<TermVariable> getFreshTermVariables() {
			return mFreshVariables.getMap().values();
		}
	}
	

}

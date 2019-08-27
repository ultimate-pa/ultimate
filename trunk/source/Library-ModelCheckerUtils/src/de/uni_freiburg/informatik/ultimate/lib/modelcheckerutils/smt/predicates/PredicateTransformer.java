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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ITransitionRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.CallReturnPyramideInstanceProvider.Instance;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * Computes SP, WP and Pre.
 *
 * @param <C>
 *            The type of constraint the various methods produce, e.g., {@link Term}
 * @param <P>
 *            The type of predicates the various methods expect, e.g., {@link IPredicate}
 * @param <R>
 *            The type of transition the various methods expect, e.g., {@link TransFormula}
 *
 * @author musab@informatik.uni-freiburg.de
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class PredicateTransformer<C, P extends IAbstractPredicate, R extends ITransitionRelation> {
	private final ManagedScript mMgdScript;
	private final IDomainSpecificOperationProvider<C, P, R> mOperationProvider;

	public PredicateTransformer(final ManagedScript mgdScript,
			final IDomainSpecificOperationProvider<C, P, R> operationProvider) {
		mMgdScript = mgdScript;
		mOperationProvider = operationProvider;
	}

	/**
	 * Computes the strongest postcondition of the given predicate p and the {@link ITransitionRelation} transRel. -
	 * invars of the given relation, which don't occur in the outvars or are mapped to different values are renamed to
	 * fresh variables. The corresponding term variables in the given predicate p, are renamed to the same fresh
	 * variables. - outvars are renamed to corresponding term variables. If an outvar doesn't occur in the invars, its
	 * occurrence in the given predicate is substituted by a fresh variable. All fresh variables are existentially
	 * quantified.
	 */
	public C strongestPostcondition(final P p, final R transRel) {
		final C constraint = mOperationProvider.getConstraint(p);
		if (mOperationProvider.isConstraintUnsatisfiable(constraint)) {
			return constraint;
		}
		final Set<TermVariable> varsToProject = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = pv -> {
			final TermVariable result = constructFreshTermVariable(mMgdScript, pv);
			varsToProject.add(result);
			return result;
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor =
				new ConstructionCache<>(substituentConstruction);

		final Map<Term, Term> substitutionForTransFormula = new HashMap<>();
		final Map<Term, Term> substitutionForPredecessor = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : transRel.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (entry.getValue() == transRel.getOutVars().get(pv)) {
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

		for (final Entry<IProgramVar, TermVariable> entry : transRel.getOutVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!transRel.getInVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				final TermVariable substituent = termVariablesForPredecessor.getOrConstruct(entry.getKey());
				substitutionForPredecessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}

		final C renamedRelationConstraint = mOperationProvider.renameVariables(substitutionForTransFormula,
				mOperationProvider.getConstraintFromTransitionRelation(transRel));
		final C renamedPredecessor = mOperationProvider.renameVariables(substitutionForPredecessor, constraint);

		final C conjunction =
				mOperationProvider.constructConjunction(toList(renamedRelationConstraint, renamedPredecessor));

		// Add aux vars to varsToQuantify
		varsToProject.addAll(transRel.getAuxVars());
		return mOperationProvider.projectExistentially(varsToProject, conjunction);
	}

	public C strongestPostconditionCall(final P callPred, final R localVarAssignments, final R globalVarAssignments,
			final R oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure) {
		if (!globalVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip =
				new CallReturnPyramideInstanceProvider(mMgdScript, Collections.emptySet(),
						localVarAssignments.getAssignedVars(), modifiableGlobalsOfCalledProcedure, Instance.AFTER_CALL);
		final C callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final C localVarAssignmentsTerm =
				renameRelationToInstances(localVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C globalVarsAssignmentTerm =
				renameRelationToInstances(globalVarAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final C result = mOperationProvider.constructConjunction(
				toList(localVarAssignmentsTerm, oldVarsAssignmentTerm, globalVarsAssignmentTerm, callPredTerm));
		return mOperationProvider
				.projectExistentially(addAuxVarsOfCall(localVarAssignments, crpip.getFreshTermVariables()), result);
	}

	/**
	 * Special post operator that we use to obtain a modular (interprocedural) sequence of inductive interpolants.
	 */
	public C modularPostconditionCall(final P callPred, final R globalVarAssignments,
			final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure) {

		if (!globalVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip =
				new CallReturnPyramideInstanceProvider(mMgdScript, Collections.emptySet(), Collections.emptySet(),
						modifiableGlobalsOfCalledProcedure, Instance.AFTER_CALL);
		final C callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final C globalVarsAssignmentTerm =
				renameRelationToInstances(globalVarAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final C result = mOperationProvider.constructConjunction(toList(globalVarsAssignmentTerm, callPredTerm));
		return mOperationProvider.projectExistentially(crpip.getFreshTermVariables(), result);
	}

	public C strongestPostconditionReturn(final P returnPred, final P callPred, final R returnTF, final R callTF,
			final R oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobals) {
		if (!returnTF.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.TRANS_FORMULA_OF_RETURN_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript,
				returnTF.getAssignedVars(), callTF.getAssignedVars(), modifiableGlobals, Instance.AFTER_RETURN);
		final C callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final C returnPredTerm = renamePredicateToInstance(returnPred, Instance.BEFORE_RETURN, crpip);
		final C callTfTerm = renameRelationToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C returnTfTerm =
				renameRelationToInstances(returnTF, Instance.BEFORE_RETURN, Instance.AFTER_RETURN, crpip);

		final C result = mOperationProvider.constructConjunction(
				toList(callTfTerm, oldVarsAssignmentTerm, returnTfTerm, callPredTerm, returnPredTerm));
		return mOperationProvider.projectExistentially(addAuxVarsOfCall(callTF, crpip.getFreshTermVariables()), result);
	}



	public C weakestPrecondition(final P p, final R tf) {
		final C constraint = mOperationProvider.getConstraint(p);
		if (mOperationProvider.isConstraintValid(constraint)) {
			return constraint;
		}

		final PreRenaming pRename = new PreRenaming(p, tf);

		final C renamedRelationConstraint = mOperationProvider.renameVariables(pRename.getSubstitutionForRelation(),
				mOperationProvider.getConstraintFromTransitionRelation(tf));
		final C renamedPredecessor =
				mOperationProvider.renameVariables(pRename.getSubstitutionForSuccessor(), constraint);

		final C disjunction = mOperationProvider.constructDisjunction(
				toList(mOperationProvider.constructNegation(renamedRelationConstraint), renamedPredecessor));

		return mOperationProvider.projectUniversally(pRename.getVarsToProject(), disjunction);
	}

	public C weakestPreconditionCall(final P callSucc, final R callTF, final R globalVarsAssignments,
			final R oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobals) {
		if (!globalVarsAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}


		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript,
				Collections.emptySet(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_CALL);
		final C callSuccTerm = renamePredicateToInstance(callSucc, Instance.AFTER_CALL, crpip);
		final C callTfTerm = renameRelationToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C globalVarsAssignmentTerm =
				renameRelationToInstances(globalVarsAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final C result =
				mOperationProvider.constructDisjunction(toList(mOperationProvider.constructNegation(callTfTerm),
						mOperationProvider.constructNegation(oldVarsAssignmentTerm),
						mOperationProvider.constructNegation(globalVarsAssignmentTerm), callSuccTerm));
		return mOperationProvider.projectUniversally(addAuxVarsOfCall(callTF, crpip.getFreshTermVariables()), result);
	}

	public C weakestPreconditionReturn(final P returnSucc, final P callPred, final R returnTF, final R callTF,
			final R oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobals) {
		if (!returnTF.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.TRANS_FORMULA_OF_RETURN_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript,
				returnTF.getAssignedVars(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_RETURN);
		final C callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final C returnSuccTerm = renamePredicateToInstance(returnSucc, Instance.AFTER_RETURN, crpip);
		final C callTfTerm = renameRelationToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C returnTfTerm =
				renameRelationToInstances(returnTF, Instance.BEFORE_RETURN, Instance.AFTER_RETURN, crpip);

		final C result =
				mOperationProvider.constructDisjunction(toList(mOperationProvider.constructNegation(callTfTerm),
						mOperationProvider.constructNegation(oldVarsAssignmentTerm),
						mOperationProvider.constructNegation(returnTfTerm),
						mOperationProvider.constructNegation(callPredTerm), returnSuccTerm));
		return mOperationProvider.projectUniversally(addAuxVarsOfCall(callTF, crpip.getFreshTermVariables()), result);
	}

	public C pre(final P p, final R tf) {
		final C constraint = mOperationProvider.getConstraint(p);
		if (mOperationProvider.isConstraintUnsatisfiable(constraint)) {
			return constraint;
		}

		final PreRenaming pRename = new PreRenaming(p, tf);

		final C renamedRelationConstraint = mOperationProvider.renameVariables(pRename.getSubstitutionForRelation(),
				mOperationProvider.getConstraintFromTransitionRelation(tf));
		final C renamedPredecessor =
				mOperationProvider.renameVariables(pRename.getSubstitutionForSuccessor(), constraint);

		final C conjunction =
				mOperationProvider.constructConjunction(toList(renamedRelationConstraint, renamedPredecessor));

		return mOperationProvider.projectExistentially(pRename.getVarsToProject(), conjunction);
	}

	public C preCall(final P callSucc, final R callTF, final R globalVarsAssignments, final R oldVarAssignments,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		if (!globalVarsAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.GLOBAL_VARS_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript,
				Collections.emptySet(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_CALL);
		final C callSuccTerm = renamePredicateToInstance(callSucc, Instance.AFTER_CALL, crpip);
		final C callTfTerm = renameRelationToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C globalVarsAssignmentTerm =
				renameRelationToInstances(globalVarsAssignments, Instance.AFTER_CALL, Instance.AFTER_CALL, crpip);

		final C result = mOperationProvider.constructConjunction(
				toList(callTfTerm, oldVarsAssignmentTerm, globalVarsAssignmentTerm, callSuccTerm));
		return mOperationProvider.projectExistentially(addAuxVarsOfCall(callTF, crpip.getFreshTermVariables()), result);
	}

	public C preReturn(final P returnSucc, final P callPred, final R returnTF, final R callTF,
			final R oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobals) {
		if (!returnTF.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.TRANS_FORMULA_OF_RETURN_MUST_NOT_CONTAIN_AUX_VARS);
		}
		if (!oldVarAssignments.getAuxVars().isEmpty()) {
			throw new AssertionError(TransFormulaUtils.OLD_VAR_ASSIGNMENTS_MUST_NOT_CONTAIN_AUX_VARS);
		}

		final CallReturnPyramideInstanceProvider crpip = new CallReturnPyramideInstanceProvider(mMgdScript,
				returnTF.getAssignedVars(), callTF.getAssignedVars(), modifiableGlobals, Instance.BEFORE_RETURN);
		final C callPredTerm = renamePredicateToInstance(callPred, Instance.BEFORE_CALL, crpip);
		final C returnSuccTerm = renamePredicateToInstance(returnSucc, Instance.AFTER_RETURN, crpip);
		final C callTfTerm = renameRelationToInstances(callTF, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C oldVarsAssignmentTerm =
				renameRelationToInstances(oldVarAssignments, Instance.BEFORE_CALL, Instance.AFTER_CALL, crpip);
		final C returnTfTerm =
				renameRelationToInstances(returnTF, Instance.BEFORE_RETURN, Instance.AFTER_RETURN, crpip);

		final C result = mOperationProvider.constructConjunction(
				toList(callTfTerm, oldVarsAssignmentTerm, returnTfTerm, callPredTerm, returnSuccTerm));
		return mOperationProvider.projectExistentially(addAuxVarsOfCall(callTF, crpip.getFreshTermVariables()), result);
	}

	private C renamePredicateToInstance(final P p, final Instance instance,
			final CallReturnPyramideInstanceProvider crpip) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final IProgramVar pv : p.getVars()) {
			substitution.put(pv.getTermVariable(), crpip.getInstance(pv, instance));
		}
		final C result = mOperationProvider.renameVariables(substitution, mOperationProvider.getConstraint(p));
		return result;
	}

	private C renameRelationToInstances(final R tf, final Instance preInstance, final Instance succInstance,
			final CallReturnPyramideInstanceProvider crpip) {

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), crpip.getInstance(entry.getKey(), succInstance));
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionMapping.put(entry.getValue(), crpip.getInstance(entry.getKey(), preInstance));
		}
		final C result = mOperationProvider.renameVariables(substitutionMapping,
				mOperationProvider.getConstraintFromTransitionRelation(tf));
		return result;
	}

	private Set<TermVariable> addAuxVarsOfCall(final R callTF, final Set<TermVariable> inputVarsToProjectAway) {
		Set<TermVariable> resultingVarsToProjectAway;
		if (callTF.getAuxVars().isEmpty()) {
			resultingVarsToProjectAway = inputVarsToProjectAway;
		} else {
			resultingVarsToProjectAway = new HashSet<>(inputVarsToProjectAway);
			resultingVarsToProjectAway.addAll(callTF.getAuxVars());
		}
		return resultingVarsToProjectAway;
	}

	@SafeVarargs
	private static <E> List<E> toList(final E... elems) {
		return Arrays.asList(elems);
	}

	private static TermVariable constructFreshTermVariable(final ManagedScript freshVarConstructor,
			final IProgramVar pv) {
		return freshVarConstructor.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
	}

	/**
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 *
	 */
	private final class PreRenaming {

		private final Set<TermVariable> mVarsToProject;
		private final Map<Term, Term> mSubstitutionForRelation;
		private final Map<Term, Term> mSubstitutionForSuccessor;

		private PreRenaming(final P p, final R tf) {
			mVarsToProject = new HashSet<>();
			final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = pv -> {
				final TermVariable result = constructFreshTermVariable(mMgdScript, pv);
				mVarsToProject.add(result);
				return result;
			};

			final ConstructionCache<IProgramVar, TermVariable> termVariablesForSuccessor =
					new ConstructionCache<>(substituentConstruction);

			mSubstitutionForRelation = new HashMap<>();
			mSubstitutionForSuccessor = new HashMap<>();

			for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
				final IProgramVar pv = entry.getKey();
				if (entry.getValue() == tf.getInVars().get(pv)) {
					// special case, variable unchanged will be renamed when
					// considering outVars
				} else {
					final TermVariable substituent = termVariablesForSuccessor.getOrConstruct(pv);
					mSubstitutionForRelation.put(entry.getValue(), substituent);
					if (p.getVars().contains(pv)) {
						mSubstitutionForSuccessor.put(pv.getTermVariable(), substituent);
					}
				}
			}

			for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
				mSubstitutionForRelation.put(entry.getValue(), entry.getKey().getTermVariable());
				if (!tf.getOutVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
					final TermVariable substituent = termVariablesForSuccessor.getOrConstruct(entry.getKey());
					mSubstitutionForSuccessor.put(entry.getKey().getTermVariable(), substituent);
				}
			}
			mVarsToProject.addAll(tf.getAuxVars());
		}

		public Set<TermVariable> getVarsToProject() {
			return mVarsToProject;
		}

		public Map<Term, Term> getSubstitutionForRelation() {
			return mSubstitutionForRelation;
		}

		public Map<Term, Term> getSubstitutionForSuccessor() {
			return mSubstitutionForSuccessor;
		}

	}
}

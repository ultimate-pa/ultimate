/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class HeapSepTransFormulaTransformer implements ITransformulaTransformer {

	/**
	 * arrayId before separation --> pointerId --> arrayId after separation
	 */
	NestedMap2<Term, Term, Term> moldArrayToPointerToNewArray;
	/**
	 * arrayId before separation --> arrayId after separation--> Set of pointerIds
	 */
	private final ManagedScript mMgdScript;
	private NewArrayIdProvider mNewArrayIdProvider;
	
	private final IIcfgSymbolTable mOldSymbolTable;
	private IIcfgSymbolTable mNewSymbolTable;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> mEqualityProvider;
	private final HeapSeparatorBenchmark mStatistics;
	
	public HeapSepTransFormulaTransformer(final CfgSmtToolkit csToolkit, IUltimateServiceProvider services, 
			IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
		mMgdScript = csToolkit.getManagedScript();
		mOldSymbolTable = csToolkit.getSymbolTable();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(IcfgTransformer.class);
		mCsToolkit = csToolkit;
		mEqualityProvider = equalityProvider;
		mStatistics = new HeapSeparatorBenchmark();
	}

	public static IProgramVar getBoogieVarFromTermVar(final TermVariable tv, final Map<IProgramVar, TermVariable> map1,
			final Map<IProgramVar, TermVariable> map2) {
		for (final Entry<IProgramVar, TermVariable> en : map1.entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		for (final Entry<IProgramVar, TermVariable> en : map2.entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		assert false : "did not find " + tv + " in the given maps";
		return null;
	}

	private UnmodifiableTransFormula splitArraysInTransFormula(final UnmodifiableTransFormula tf) {
		mStatistics.incrementTransformulaCounter();

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		
		Term intermediateFormula = tf.getFormula();

		mMgdScript.lock(this);
		intermediateFormula = substituteArrayUpdates(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteArrayEqualites(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteRemainingStoresAndSelects(tf, newInVars, newOutVars, intermediateFormula);
		mMgdScript.unlock(this);
		
		boolean newEmptyNonTheoryConsts = false;
		Set<IProgramConst> newNonTheoryConsts = null;
		boolean newEmptyBranchEncoders = false;
		Collection<TermVariable> newBranchEncoders = null; // TODO: deal with these for working LBE, right?..
		boolean newEmptyAuxVars = false;
		TransFormulaBuilder tfBuilder = new TransFormulaBuilder(
				newInVars, 
				newOutVars, 
				newEmptyNonTheoryConsts, 
				newNonTheoryConsts, 
				newEmptyBranchEncoders, 
				newBranchEncoders, 
				newEmptyAuxVars);
		
		tfBuilder.setFormula(intermediateFormula);
		
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		
		return tfBuilder.finishConstruction(mMgdScript);
	}



	/**
	 * update selects and stores
	 * 
	 * details:
	 *  select case:
	 *   the result depends on the accessed index
	 *   simple example:
	 *  assume p != q;  mem -> p -> mem1, mem -> q -> mem2 are in the corresponding map from old to new array ids
	 *   old: mem[p]
	 *   new: mem1[p]
	 *   
	 *   less simple example (select over store):
	 *  assume p != q;  mem -> p -> mem1, mem -> q -> mem2 are in the corresponding map from old to new array ids
	 *   old: mem[p:=i][q]
	 *   new: mem2[q]
	 *   
	 *   alternative new: mem2[p:=i][q]
	 *     --> the store does not hurt us here, as we're not accessing at q anyway.. 
	 *        (but the above is better, of course, and we may only omit the store for (must) non-aliasing pointers ..)
	 *   
	 * @param tf
	 * @param newInVars
	 * @param newOutVars
	 * @param intermediateFormula
	 * @return
	 */
	private Term substituteRemainingStoresAndSelects(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			Term intermediateFormula) {
		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();
		
		List<MultiDimensionalSelect> mdSelects = 
				MultiDimensionalSelect.extractSelectShallow(intermediateFormula, true);//TODO allowArrayValues??
		List<MultiDimensionalSelect> mdSelectsInOriginalTf = 
				MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), true);//TODO allowArrayValues??
		for (MultiDimensionalSelect mds : mdSelects) {
			if (!mdSelectsInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or ArrayEquality-handling)
				continue;
			}
			if (!isArrayTracked(
					getInnerMostArray(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				continue;
			}

			final Term oldArray = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mMgdScript);

			final List<Term> pointers = mds.getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mMgdScript))
					.collect(Collectors.toList());
	

			Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc, tf);
		}
		intermediateFormula = new Substitution(mMgdScript, substitutionMapPvoc).transform(intermediateFormula);	

		final Map<Term, Term> substitutionMapPvoc2 = new HashMap<>();
		final List<MultiDimensionalStore> mdStores = 
				MultiDimensionalStore.extractArrayStoresShallow(intermediateFormula);
		final List<MultiDimensionalStore> mdStoresInOriginalTf = 
				MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula());
		for (MultiDimensionalStore mds : mdStores) {
			if (!mdStoresInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or ArrayEquality-handling)
				continue;
			}
			if (!isArrayTracked(
					getInnerMostArray(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				continue;
			}
			
			assert false : "TODO"; // TODO

//			final Term oldArray = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript);
//
//			final List<Term> pointers = mds.getIndex().stream()
//					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
//					.collect(Collectors.toList());
//					
//			final Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);
//
//			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc2);
		}
		intermediateFormula = new Substitution(mMgdScript, substitutionMapPvoc2).transform(intermediateFormula);	
		return intermediateFormula;
	}



	/**
	 * The conversion of an array update depends on which indices are written.
	 * 
	 * simplest case: 
	 *  assume p != q;  mem -> p -> mem1, mem -> q -> mem2 are in the corresponding map from old to new array ids
	 *  old: mem := mem[p:=i]
	 *  new: mem1 := mem1[p:=i]
	 *  
	 * less simple case: (TODO: implement)
	 *  assume p != q;  mem -> p -> mem1, mem -> q -> mem2 are in the corresponding map from old to new array ids
	 *  old: mem := mem[p:=i][q:=j]
	 *  new: mem1 := mem1[p:=i] ; mem2 := mem2[q:=j]  (this conversion is correct because of p!=q, mem1 will never be 
	 *  				read at q, and mem2 never at p)
	 *  
	 *  new': mem1 := mem1[p:=i][q:=j] ; mem2 := mem2[p:=i][q:=j] 
	 *   			(contracting the stores could be an additional optimization)
	 * 
	 * @param tf
	 * @param newInVars
	 * @param newOutVars
	 * @param formula
	 * @return
	 */
	private Term substituteArrayUpdates(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			Term formula) {
		
		/*
		 * algorithmic plan:
		 *  - the rhs is the one that is accessed according to the pointers
		 *   --> the pointers determine the rhs version(s), many pointers may correspond to the same new rhs version/part
		 *  - the lhs array has to have compatible partitions to the rhs versions (by convention/construction)
		 *   --> it may or may not be the same array
		 *   --> for the lhs, we have to look up the corresponding version according to the rhs version
		 */

		/*
		 * substitution from old to new array updates
		 */
		final Map<Term, Term> equalitySubstitution = new HashMap<>();

		List<ArrayUpdate> arrayUpdates = ArrayUpdate.extractArrayUpdates(formula, false);
		for (ArrayUpdate au : arrayUpdates) {
			mStatistics.incrementArrayUpdateCounter();

			final Term rhsStoreTerm = au.getMultiDimensionalStore().getStoreTerm();
			final TermVariable oldRhsVar = (TermVariable) getInnerMostArray(rhsStoreTerm);

			// we get a list of indices according to the store chain; 
			final List<ArrayIndex> pointers = computeAccessingIndicesInStoreChain(rhsStoreTerm);

			final List<Term> newEqualities = new ArrayList<>();
			
			Set<Term> alreadySeenNewArrayRhs = new HashSet<>();
			
			// for each of the pointers we have to determine the corresponding new array and update it
			for (ArrayIndex pointer : pointers) {
				
				// rhs is chosen according to pointerGroup
				final Term newArrayRhsVarNorm = mNewArrayIdProvider.getNewArrayId(
						VPDomainHelpers.normalizeTerm(oldRhsVar, tf, mMgdScript),
						VPDomainHelpers.normalizeArrayIndex(pointer, tf, mMgdScript));

				if (alreadySeenNewArrayRhs.contains(newArrayRhsVarNorm)) {
					continue;
				}
				mStatistics.incrementNewlyIntroducedArrayUpdateCounter();

				alreadySeenNewArrayRhs.add(newArrayRhsVarNorm);
				
				/*
				 *  lhs is chosen according to rhs 
				 *  --> but actually the outcome is the same as chosing it by pointer group, right?
				 */
				final Term newArrayLhsNorm = mNewArrayIdProvider.getNewArrayId(
						VPDomainHelpers.normalizeTerm(au.getNewArray(), tf, mMgdScript), 
						VPDomainHelpers.normalizeArrayIndex(pointer, tf, mMgdScript));

				
				final IProgramVar oldArrayLhsPvoc = mOldSymbolTable.getProgramVar(
						(TermVariable) VPDomainHelpers.normalizeTerm(au.getNewArray(), tf, mMgdScript));
				final IProgramVar oldArrayRhsVarPvoc = mOldSymbolTable.getProgramVar(
						(TermVariable) VPDomainHelpers.normalizeTerm(oldRhsVar, tf, mMgdScript));

				final IProgramVar newArrayLhsPvoc = mNewSymbolTable.getProgramVar((TermVariable) newArrayLhsNorm);
				final IProgramVar newArrayRhsVarPvoc = mNewSymbolTable.getProgramVar((TermVariable) newArrayRhsVarNorm);

				TermVariable newArrayLhs = newOutVars.get(newArrayLhsPvoc);
				if (newArrayLhs == null) {
					newArrayLhs = mMgdScript.constructFreshCopy(au.getNewArray());
					newOutVars.put(newArrayLhsPvoc, newArrayLhs);
					newOutVars.remove(oldArrayLhsPvoc);
				}

				TermVariable newArrayRhsVar = newInVars.get(newArrayRhsVarPvoc);
				if (newArrayRhsVar == null) {
					newArrayRhsVar = mMgdScript.constructFreshCopy(au.getNewArray());
					newInVars.put(newArrayRhsVarPvoc, newArrayRhsVar);
					newInVars.remove(oldArrayRhsVarPvoc);
					
					if (newOutVars.containsKey(oldArrayRhsVarPvoc)) {
						newOutVars.remove(oldArrayRhsVarPvoc);
						newOutVars.put(newArrayRhsVarPvoc, newArrayLhs);
					}
				}
				
				if (newArrayLhs == null || newArrayRhsVar == null) {
					assert !isArrayTracked(newArrayLhs, tf) 
						|| !isArrayTracked(newArrayRhsVar, tf);
					continue;
				}
				
				final Term newArrayRhs = new Substitution(mMgdScript, Collections.singletonMap(oldRhsVar, newArrayRhsVar))
						.transform(rhsStoreTerm);

				final Term newEquality = mMgdScript.term(this, "=", newArrayLhs, newArrayRhs);
				newEqualities.add(newEquality);
	
			}

			final Term newConjunctionOfEquations = SmtUtils.and(mMgdScript.getScript(), newEqualities);
			equalitySubstitution.put(au.getArrayUpdateTerm(), newConjunctionOfEquations);
		}
		
		final Term newTerm = new Substitution(mMgdScript, equalitySubstitution).transform(formula);
//		Term newTerm = new Substitution(mScript, substitutionMapPvoc).transform(formula);
		return newTerm;
	}

	private Term substituteArrayEqualites(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, 
			final Map<IProgramVar, TermVariable> newOutVars, 
			final Term intermediateFormula) {
		final List<ArrayEquality> arrayEqualities = ArrayEquality.extractArrayEqualities(intermediateFormula);
		final Map<Term, Term> equalitySubstitution = new HashMap<>();
//		mScript.lock(this);
		for (ArrayEquality ae : arrayEqualities) {
			/*
			 * plan:
			 *  (- check compatibility --> should be guaranteed by NewArrayIdProvider)
			 *  - make an assignment between all the partitions
			 */
			if (!isArrayTracked(ae.getLhs(), 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))
					|| !isArrayTracked(ae.getRhs(), 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				continue;
			}
			
			
			List<Term> newEqualities = new ArrayList<>();
			
			final Term oldLhs = ae.getLhs();
			final List<Term> newLhss = mNewArrayIdProvider.getAllNewArrayIds(
					VPDomainHelpers.normalizeTerm(oldLhs, tf, mMgdScript));

			final Term oldRhs = ae.getRhs();
			final List<Term> newRhss = mNewArrayIdProvider.getAllNewArrayIds(
					VPDomainHelpers.normalizeTerm(oldRhs, tf, mMgdScript));
			
			
			assert newLhss.size() == newRhss.size();
			for (int i = 0; i < newLhss.size(); i++) {
				final Term newLhs = newLhss.get(i);
				final Term newRhs = newRhss.get(i);
				final Term newEquality = mMgdScript.term(this, "=", newLhs, newRhs);
				newEqualities.add(newEquality);
				
				// TODO
//				updateNewInVarsAndNewOutVars(tf, newInVars, newOutVars, oldLhs, oldRhs, newLhs, newRhs);

			}
			assert newEqualities.size() > 0;
			final Term newConjunctionOfEquations = SmtUtils.and(mMgdScript.getScript(), newEqualities);
			equalitySubstitution.put(ae.getOriginalTerm(), newConjunctionOfEquations);
		}
//		mScript.unlock(this);
		final Term newTerm = new Substitution(mMgdScript, equalitySubstitution).transform(intermediateFormula);
		return newTerm;
	}

	private void updateNewInVarsAndNewOutVars(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			final IProgramVar oldLhsPvoc, final IProgramVar oldRhsPvoc, 
			final IProgramVar newLhsPvoc, final IProgramVar newRhsPvoc,
			final Term newLhs, final Term newRhs) {
//		if (tf.getInVars().containsKey(oldLhsPvoc)) {
//			newInVars.remove(oldLhsPvoc);
//			newInVars.put((IProgramVar) newLhsPvoc, (TermVariable) newLhs);
//		}
		if (tf.getInVars().containsKey(oldRhsPvoc)) {
			newInVars.remove(oldRhsPvoc);
			newInVars.put((IProgramVar) newRhsPvoc, (TermVariable) newRhs);
		}
		if (tf.getOutVars().containsKey(oldLhsPvoc)) {
			newOutVars.remove(oldLhsPvoc);
			newOutVars.put((IProgramVar) newLhsPvoc, (TermVariable) newLhs);
		}
//		if (tf.getOutVars().containsKey(oldRhsPvoc)) {
//			newOutVars.remove(oldRhsPvoc);
//			newOutVars.put((IProgramVar) newRhsPvoc, (TermVariable) newRhs);
//		}
	}



	/**
	 * 
	 * - updates the maps newInVars and newOutVars
	 * - updates the map substitutionMap
	 * 
	 * This method is for the simple cases, where we just need to replace the arrayIdentifer "one-by-one".
	 * (not like the ArrayEquality, where we replace one-by-many)
	 * 
	 * @param oldArray
	 * @param newArray
	 * @param tf
	 * @param newInVars
	 * @param newOutVars
	 * @param substitutionMap
	 * @param tf 
	 */
	private void updateMappingsForSubstitution(Term oldArrayTerm, Term newArrayTerm,
			final Map<IProgramVar, TermVariable> newInVars,
			final Map<IProgramVar, TermVariable> newOutVars,
			final Map<Term, Term> substitutionMap, UnmodifiableTransFormula tf) {
		if (oldArrayTerm instanceof TermVariable) {
			assert newArrayTerm instanceof TermVariable;

			final IProgramVar oldArray = mOldSymbolTable.getProgramVar((TermVariable) oldArrayTerm);
			final IProgramVar newArray = mNewSymbolTable.getProgramVar((TermVariable) newArrayTerm);
		
			final TermVariable invOld = newInVars.get(oldArray);
			final TermVariable outvOld = newOutVars.get(oldArray);
			
			final TermVariable invNew = newInVars.get(newArray);
			final TermVariable outvNew = newOutVars.get(newArray);

			
			TermVariable versionedInTvNew = newInVars.get(newArray);
			if (versionedInTvNew == null) {
				versionedInTvNew = mMgdScript.constructFreshCopy((TermVariable) newArrayTerm);
				newInVars.remove(oldArray);
				newInVars.put((IProgramVar) newArray, versionedInTvNew);
			}
			TermVariable versionedInTvOld = tf.getInVars().get(oldArray);
			substitutionMap.put(versionedInTvOld, versionedInTvNew);
			
			
			TermVariable versionedOutTvNew = newOutVars.get(newArray);
			if (versionedOutTvNew == null) {
				if (tf.getAssignedVars().contains(oldArray)) {
					versionedOutTvNew = mMgdScript.constructFreshCopy((TermVariable) newArrayTerm);
				} else {
					versionedOutTvNew = newInVars.get(newArray);
					assert versionedOutTvNew != null;
				}
				newOutVars.remove(oldArray);
				newOutVars.put((IProgramVar) newArray, versionedOutTvNew);
			}
			TermVariable versionedOutTvOld = tf.getOutVars().get(oldArray);
			substitutionMap.put(versionedOutTvOld, versionedOutTvNew);
	
			
//			TermVariable invNewTv = null;
//			if (invOld != null) {
//				invNewTv = mScript.constructFreshCopy((TermVariable) newArrayTerm);
//				newInVars.remove(oldArray);
//				newInVars.put((IProgramVar) newArray, invNewTv);
//				substitutionMap.put(inv, invNewTv);
//			}
//		
//			if (outv != null) {
//				TermVariable newTv;
//				if (inv == outv) {
//					newTv = invNewTv;
//				} else {
//					newTv = mScript.constructFreshCopy((TermVariable) newArrayTerm);
//				}
//				newOutVars.remove(oldArray);
//				newOutVars.put((IProgramVar) newArray, newTv);
//				substitutionMap.put(outv, newTv);
//			}
			
		} else if (SmtUtils.isConstant(oldArrayTerm)) {
			/*
			 * the array id is a constant (or literal)
			 *  --> there are no changes to the invar/outvar mappings, only to the substitution
			 */
			substitutionMap.put(oldArrayTerm, newArrayTerm);
		} else {
			throw new AssertionError("did not see this case coming..");
		}
	}
	
	/**
	 * Computes the ArrayIndexes that are used in a store chain. The result is ordered from the outside in.
	 * @param arrayUpdateTerm
	 * @return
	 */
	private List<ArrayIndex> computeAccessingIndicesInStoreChain(Term arrayUpdateTerm) {
		final List<ArrayIndex> result = new ArrayList<>();

		Term currentTerm = arrayUpdateTerm;
		while (SmtUtils.isFunctionApplication(currentTerm, "store")) {
			result.add(new MultiDimensionalStore(currentTerm).getIndex());
			currentTerm = ((ApplicationTerm) currentTerm).getParameters()[0];
		}
		return result;
	}

	public static Term getInnerMostArray(Term arrayTerm) {
		assert arrayTerm.getSort().isArraySort();
		Term innerArray = arrayTerm;
		while (SmtUtils.containsFunctionApplication(innerArray, "store")) {
			innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
		}
		assert innerArray instanceof TermVariable;
		return innerArray;
	}



	@Override
	public void preprocessIcfg(IIcfg<?> icfg) {
//		// run equality domain
//AbsIntEqualityProvider aiep = new AbsIntEqualityProvider(mServices);
//		final IAbstractInterpretationResult<EqState<IcfgEdge>, IcfgEdge, IProgramVarOrConst, ?> 
//			abstractInterpretationResult =
//				AbstractInterpreter.runFutureEqualityDomain(icfg, 
//						mServices.getProgressMonitorService().getChildTimer(0.2), 
//						mServices, 
//						false, 
//						mLogger);
//		mVpDomain = (VPDomain<IcfgEdge>) abstractInterpretationResult.getUsedDomain();
		
		/* 
		 * run a preanalysis that finds out necessary information for the (heap) array partitioning, in particular:
		 *  <li> which arrays are equated in the program
		 *  <li> at which indices each array is accessed
		 */
		HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger, 
				icfg.getCfgSmtToolkit().getManagedScript());
		new IcfgEdgeIterator(icfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));
		
		
		mEqualityProvider.preprocess(icfg);

		/* 
		 * compute the partitioning from the above results, in particular compute which array will translate to which
		 *  new array for which accessing expression
		 */
		mNewArrayIdProvider = 
//				new NewArrayIdProvider(mCsToolkit, abstractInterpretationResult, heapSepPreanalysis);
				new NewArrayIdProvider(mCsToolkit, mEqualityProvider, heapSepPreanalysis, mStatistics);
		mNewSymbolTable = mNewArrayIdProvider.getNewSymbolTable();
		
		mLogger.info("IcfgTransformer_HeapSeparator: Computed the following array partitioning from the given"
				+ "equality information:");
		mLogger.info(mNewArrayIdProvider.toString());
	}



	@Override
	public TransforumlaTransformationResult transform(final UnmodifiableTransFormula tf) {
		/*
		 * The question if the HeapSeparator computes an overapproximation ("false" flag we give below) is a bit more 
		 * complicated:
		 *  <li> we introduce fresh program variables, so strictly speaking the transformed program's behaviour is 
		 *    incomparable to the input program's
		 *  <li> if we view the TransFormula just by itself, and restrict ourselves to the unchanged program variables,
		 *      the HeapSeparator should produce an overapproximation
		 *  <li> if we view the whole program, including the constraints about the reachable states computed by the
		 *   equality domain, the transformation should be exact
		 *  <li> some TransFormulas it does not change at all, so there we could say "false" (TODO recognize that)
		 */
		return new TransforumlaTransformationResult(splitArraysInTransFormula(tf), false);
	}



	@Override
	public String getName() {
		return this.getClass().getName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	private boolean isArrayTracked(Term rhs, Map<TermVariable, IProgramVar> computeProgramVarMappingFromTransFormula) {
		// TODO Auto-generated method stub
		// also look into neighboring classes -- we have that method there, too..
		return true;
	}

	private boolean isArrayTracked(TermVariable newArrayLhs, UnmodifiableTransFormula tf) {
		// TODO Auto-generated method stub
		// also look into neighboring classes -- we have that method there, too..
		return true;
	}

	public HeapSeparatorBenchmark getStatistics() {
		return mStatistics;
	}
}

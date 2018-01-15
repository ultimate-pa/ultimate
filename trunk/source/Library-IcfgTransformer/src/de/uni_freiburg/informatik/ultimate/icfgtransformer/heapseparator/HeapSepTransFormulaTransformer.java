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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.VPDomainHelpers;
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

	public HeapSepTransFormulaTransformer(final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider) {
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

		final NewTermVariableProvider newTvProvider = new NewTermVariableProvider(tf);

		Term intermediateFormula = tf.getFormula();

//		/*
//		 *  we need this because the mapping oldTermVariable -> ProgramVar -> newTermVariables is sound
//		 *  example: a := a becomes a_1 = a_2, where both that the same ProgramVar
//		 */
		mMgdScript.lock(this);
		intermediateFormula = substituteArrayUpdates(tf, intermediateFormula, newTvProvider);

		intermediateFormula = substituteArrayEqualites(tf, intermediateFormula, newTvProvider);

		intermediateFormula = substituteRemainingStoresAndSelects(tf, intermediateFormula, newTvProvider);
		mMgdScript.unlock(this);

		final boolean newEmptyNonTheoryConsts = false;
		final Set<IProgramConst> newNonTheoryConsts = null;
		final boolean newEmptyBranchEncoders = false;
		final Collection<TermVariable> newBranchEncoders = null; // TODO: deal with these for working LBE, right?..
		final boolean newEmptyAuxVars = false;
		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(
				newTvProvider.getNewInVars(),
				newTvProvider.getNewOutVars(),
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
	 * @param newTvProvider
	 * @return
	 */
	private Term substituteRemainingStoresAndSelects(final UnmodifiableTransFormula tf,
//			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			final Term intermediateFormula, final NewTermVariableProvider newTvProvider) {
		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();

		final List<MultiDimensionalSelect> mdSelects =
				MultiDimensionalSelect.extractSelectShallow(intermediateFormula, true);//TODO allowArrayValues??
		final List<MultiDimensionalSelect> mdSelectsInOriginalTf =
				MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), true);//TODO allowArrayValues??
		for (final MultiDimensionalSelect mds : mdSelects) {
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

//			final List<Term> pointers = mds.getIndex().stream()
//					.map(t -> VPDomainHelpers.normalizeTerm(t, newTvProvider.getNewInVars(),
//							newTvProvider.getNewOutVars(), mMgdScript))
//					.collect(Collectors.toList());
			final ArrayIndex pointers = VPDomainHelpers.normalizeArrayIndex(mds.getIndex(),  newTvProvider.getNewInVars(),
							newTvProvider.getNewOutVars(), mMgdScript);


			final Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(mds.getArray(), newArray, substitutionMapPvoc, newTvProvider, tf);
		}
		Term result = new Substitution(mMgdScript, substitutionMapPvoc).transform(intermediateFormula);

		final Map<Term, Term> substitutionMapPvoc2 = new HashMap<>();
		final List<MultiDimensionalStore> mdStores =
				MultiDimensionalStore.extractArrayStoresShallow(result);
		final List<MultiDimensionalStore> mdStoresInOriginalTf =
				MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula());
		for (final MultiDimensionalStore mds : mdStores) {
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
		result = new Substitution(mMgdScript, substitutionMapPvoc2).transform(result);
		return result;
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
	 * @param newTvProvider
	 * @return
	 */
	private Term substituteArrayUpdates(final UnmodifiableTransFormula tf,
			final Term formula, final NewTermVariableProvider newTvProvider) {

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

		final List<ArrayUpdate> arrayUpdates = ArrayUpdate.extractArrayUpdates(formula, false);
		for (final ArrayUpdate au : arrayUpdates) {
			mStatistics.incrementArrayUpdateCounter();

			final Term rhsStoreTerm = au.getMultiDimensionalStore().getStoreTerm();
			final TermVariable oldRhsVar = (TermVariable) getInnerMostArray(rhsStoreTerm);

			// we get a list of indices according to the store chain;
			final List<ArrayIndex> pointers = computeAccessingIndicesInStoreChain(rhsStoreTerm);

			final List<Term> newEqualities = new ArrayList<>();

			final Set<Term> alreadySeenNewArrayRhs = new HashSet<>();

			// for each of the pointers we have to determine the corresponding new array and update it
			for (final ArrayIndex pointer : pointers) {

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

				final IProgramVar newArrayLhsPvoc = mNewSymbolTable.getProgramVar((TermVariable) newArrayLhsNorm);
				final IProgramVar newArrayRhsVarPvoc = mNewSymbolTable.getProgramVar((TermVariable) newArrayRhsVarNorm);

				/*
				 * update the new inVar/outVar maps
				 */

				/*
				 *  check if we already have an entry for the new lhs, because we have an update we only check in
				 *  outVars
				 */

				final TermVariable newArrayLhs = newTvProvider.getOrConstructNewTermVariable(newArrayLhsPvoc,
						au.getNewArray(), tf);

				/*
				 *  check if we already have an entry for the new rhs, because we have an update we only check in
				 *  inVars --> the rhs may be only in (for instance a := a[i:=x]) or both in and out with the same
				 *   (for instance b := a[i:=x]) variables
				 */
				final TermVariable newArrayRhsVar = newTvProvider.getOrConstructNewTermVariable(newArrayRhsVarPvoc,
						oldRhsVar, tf);

				if (newArrayLhs == null || newArrayRhsVar == null) {
					assert !isArrayTracked(newArrayLhs, tf)
						|| !isArrayTracked(newArrayRhsVar, tf);
					continue;
				}

				final Term newArrayRhs = new Substitution(mMgdScript,
						Collections.singletonMap(oldRhsVar, newArrayRhsVar))
						.transform(rhsStoreTerm);

				final Term newEquality = mMgdScript.term(this, "=", newArrayLhs, newArrayRhs);
				newEqualities.add(newEquality);

			}

			final Term newConjunctionOfEquations = SmtUtils.and(mMgdScript.getScript(), newEqualities);
			equalitySubstitution.put(au.getArrayUpdateTerm(), newConjunctionOfEquations);
		}

		final Term newTerm = new Substitution(mMgdScript, equalitySubstitution).transform(formula);
		return newTerm;
	}

	private Term substituteArrayEqualites(final UnmodifiableTransFormula tf,
			final Term intermediateFormula,
			final NewTermVariableProvider newTvProvider) {
		final List<ArrayEquality> arrayEqualities = ArrayEquality.extractArrayEqualities(intermediateFormula);
		final Map<Term, Term> equalitySubstitution = new HashMap<>();
		for (final ArrayEquality ae : arrayEqualities) {
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


			final List<Term> newEqualities = new ArrayList<>();

			final Term oldLhsNorm = VPDomainHelpers.normalizeTerm(ae.getLhs(), tf, mMgdScript);
			final List<Term> newLhss = mNewArrayIdProvider.getAllNewArrayIds(oldLhsNorm);

			final Term oldRhsNorm = VPDomainHelpers.normalizeTerm(ae.getRhs(), tf, mMgdScript);
			final List<Term> newRhss = mNewArrayIdProvider.getAllNewArrayIds(oldRhsNorm);

			assert newLhss.size() == newRhss.size();
			for (int i = 0; i < newLhss.size(); i++) {
				final Term newLhs = newLhss.get(i);
				final Term newRhs = newRhss.get(i);

				final IProgramVar newLhsPvoc = mNewSymbolTable.getProgramVar((TermVariable) newLhs);
				final IProgramVar newRhsPvoc = mNewSymbolTable.getProgramVar((TermVariable) newRhs);

				/*
				 * update the new invar/outvar maps
				 */
				final TermVariable newArrayLhs = newTvProvider.getOrConstructNewTermVariable(newLhsPvoc,
						ae.getLhsTermVariable(), tf);
				final TermVariable newArrayRhs = newTvProvider.getOrConstructNewTermVariable(newRhsPvoc,
						ae.getRhsTermVariable(), tf);

				assert newArrayLhs != null && newArrayRhs != null;

				final Term newEquality = mMgdScript.term(this, "=", newArrayLhs, newArrayRhs);
				newEqualities.add(newEquality);
			}
			assert newEqualities.size() > 0;
			final Term newConjunctionOfEquations = SmtUtils.and(mMgdScript.getScript(), newEqualities);
			equalitySubstitution.put(ae.getOriginalTerm(), newConjunctionOfEquations);
		}
		final Term newTerm = new Substitution(mMgdScript, equalitySubstitution).transform(intermediateFormula);
		return newTerm;
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
	private void updateMappingsForSubstitution(final Term versionedTermInOrigTf, final Term newArrayTerm,
			final Map<Term, Term> substitutionMap,
			final NewTermVariableProvider newTvProvider,
			final UnmodifiableTransFormula tf) {
		if (versionedTermInOrigTf instanceof TermVariable) {
			assert newArrayTerm instanceof TermVariable;

			final IProgramVar newArray = mNewSymbolTable.getProgramVar((TermVariable) newArrayTerm);

			final TermVariable versionedInTvNew = newTvProvider.getOrConstructNewTermVariable(newArray,
					(TermVariable) versionedTermInOrigTf, tf);
			substitutionMap.put(versionedTermInOrigTf, versionedInTvNew);
		} else if (SmtUtils.isConstant(versionedTermInOrigTf)) {
			/*
			 * the array id is a constant (or literal)
			 *  --> there are no changes to the invar/outvar mappings, only to the substitution
			 */
			assert false : "check this case";
			substitutionMap.put(versionedTermInOrigTf, newArrayTerm);
		} else {
			throw new AssertionError("did not see this case coming..");
		}
	}

	/**
	 * Computes the ArrayIndexes that are used in a store chain. The result is ordered from the outside in.
	 * @param arrayUpdateTerm
	 * @return
	 */
	private List<ArrayIndex> computeAccessingIndicesInStoreChain(final Term arrayUpdateTerm) {
		final List<ArrayIndex> result = new ArrayList<>();

		Term currentTerm = arrayUpdateTerm;
		while (SmtUtils.isFunctionApplication(currentTerm, "store")) {
			result.add(new MultiDimensionalStore(currentTerm).getIndex());
			currentTerm = ((ApplicationTerm) currentTerm).getParameters()[0];
		}
		return result;
	}

	public static Term getInnerMostArray(final Term arrayTerm) {
		assert arrayTerm.getSort().isArraySort();
		Term innerArray = arrayTerm;
		while (SmtUtils.containsFunctionApplication(innerArray, "store")) {
			innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
		}
		assert innerArray instanceof TermVariable;
		return innerArray;
	}



	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		/*
		 * run a preanalysis that finds out necessary information for the (heap) array partitioning, in particular:
		 *  <li> which arrays are equated in the program
		 *  <li> at which indices each array is accessed
		 */
		final HeapSepPreAnalysis heapSepPreanalysis = new HeapSepPreAnalysis(mLogger,
				icfg.getCfgSmtToolkit().getManagedScript());
		new IcfgEdgeIterator(icfg).forEachRemaining(edge -> heapSepPreanalysis.processEdge(edge));


		mEqualityProvider.preprocess(icfg);

		/*
		 * compute the partitioning from the above results, in particular compute which array will translate to which
		 *  new array for which accessing expression
		 */

//		mNewArrayIdProvider =
//				new NewArrayIdProvider(mCsToolkit, mEqualityProvider, heapSepPreanalysis, mStatistics);
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

	private boolean isArrayTracked(final Term rhs, final Map<TermVariable, IProgramVar> computeProgramVarMappingFromTransFormula) {
		// TODO Auto-generated method stub
		// also look into neighboring classes -- we have that method there, too..
		return true;
	}

	private boolean isArrayTracked(final TermVariable newArrayLhs, final UnmodifiableTransFormula tf) {
		// TODO Auto-generated method stub
		// also look into neighboring classes -- we have that method there, too..
		return true;
	}

	public HeapSeparatorBenchmark getStatistics() {
		return mStatistics;
	}


	/**
	 * Provides Terms that substitute the old array-representing Terms in the new TransFormulas we build.
	 *
	 * We probably only need this for TermVariables because constants are much simpler to replace (because they don't have
	 *  many versions within one TransFormula).
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class NewTermVariableProvider {

		private final NestedMap2<IProgramVar, TermVariable, TermVariable> mNewPvocToVersionedTvToNewVersionedTv =
				new NestedMap2<>();

		private final Map<IProgramVar, TermVariable> mNewInVars;
		private final Map<IProgramVar, TermVariable> mNewOutVars;

		public NewTermVariableProvider(final UnmodifiableTransFormula tf) {
			mNewInVars = new HashMap<>(tf.getInVars());
			mNewOutVars = new HashMap<>(tf.getOutVars());
		}

		TermVariable getOrConstructNewTermVariable(final IProgramVar newPvoc, final TermVariable versionedTvInOrigTf,
				final UnmodifiableTransFormula origTf) {
			TermVariable result = mNewPvocToVersionedTvToNewVersionedTv.get(newPvoc, versionedTvInOrigTf);
			if (result == null) {
				result = mMgdScript.constructFreshCopy(versionedTvInOrigTf);
				mNewPvocToVersionedTvToNewVersionedTv.put(newPvoc, versionedTvInOrigTf, result);

				if (origTf.getInVars().values().contains(versionedTvInOrigTf)) {
					mNewInVars.put(newPvoc, result);
				}
				if (origTf.getOutVars().values().contains(versionedTvInOrigTf)) {
					mNewOutVars.put(newPvoc, result);
				}
			}
			return result;
		}

		public Map<IProgramVar, TermVariable> getNewInVars() {
			return mNewInVars;
		}

		public Map<IProgramVar, TermVariable> getNewOutVars() {
			return mNewOutVars;
		}
	}


	/**
	 * Make a summary of what the HeapSeparator did, for reporting a GenericResult.
	 * @return
	 */
	public String getHeapSeparationSummary() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Heap separation summary: \n");
		sb.append(mNewArrayIdProvider.toString());
		return sb.toString();
	}
}



/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.MemlocArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreIndexInfo;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Applies the "memloc-array transformation"
 * Performs the following steps:
 * <ul>
 *  <li> introduce a fresh array-type variable, called the memloc-array
 *  <li> at each write to an array in the program, at location l with index variable i:
 *   <ul>
 *    <li> introduce a fresh memloc-literal "(l, i)" that represents this write location
 *    <li> update the memloc array like this: memloc[i] := (l,i);
 *   </ul>
 *  <li> make sure that all memloc-literals are assumed as distinct by the solver (may be done outside this class)
 * </ul>
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class MemlocArrayUpdaterIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements ITransformulaTransformer {

	private final Map<StoreIndexInfo, IProgramConst> mStoreIndexInfoToLocLiteral;

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;

	private final static boolean TRACK_CONSTANTS = false;
	private final Set<ConstantTerm> mAllConstantTerms;


	private int mMemLocLitCounter = 0;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final MemlocArrayManager mMemlocArrayManager;

	ManagedScript mMgdScript;

	private final DefaultIcfgSymbolTable mNewSymbolTable;

	/**
	 * info must be queried after all transform calls have been made
	 */
	private boolean mQueriedStoreAndLitInfo;

	private final HashRelation<String, IProgramNonOldVar> mNewModifiableGlobals;

	public MemlocArrayUpdaterIcfgTransformer(final ILogger logger,
			final CfgSmtToolkit oldCsToolkit,
			final MemlocArrayManager memlocArrayManager,
			final List<IProgramVarOrConst> heapArrays,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo) {
		mMgdScript = oldCsToolkit.getManagedScript();
		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
		mAllConstantTerms = TRACK_CONSTANTS ? new HashSet<>() : null;
		mMemlocArrayManager = memlocArrayManager;
		mStoreIndexInfoToLocLiteral = new HashMap<>();
		mHeapArrays = heapArrays;

		mNewSymbolTable = new DefaultIcfgSymbolTable(oldCsToolkit.getSymbolTable(), oldCsToolkit.getProcedures());
		mNewModifiableGlobals = new HashRelation<>(oldCsToolkit.getModifiableGlobalsTable().getProcToGlobals());
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		assert !mQueriedStoreAndLitInfo;

		final EdgeInfo edgeInfo = new EdgeInfo((IcfgEdge) oldEdge);

		if (TRACK_CONSTANTS) {
			/* update the all constants tracking */
			mAllConstantTerms.addAll(new SubTermFinder(t -> t instanceof ConstantTerm)
					.findMatchingSubterms(tf.getFormula())
					.stream().map(t -> (ConstantTerm) t)
					.collect(Collectors.toList()));
		}

		if (mEdgeToIndexToStoreIndexInfo.get(edgeInfo) == null) {
			// edge does not have any array writes --> return it unchanged
			return new TransformulaTransformationResult(tf);
		}

		/*
		 * core business from here on..
		 */

		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();
		final Set<IProgramConst> extraConstants = new HashSet<>();

		mMgdScript.lock(this);

		final NestedMap2<Integer, Term, Term> memlocUpdatesPerDim = new NestedMap2<>();

		for (final Entry<Term, StoreIndexInfo> en : mEdgeToIndexToStoreIndexInfo.get(edgeInfo).entrySet()) {

			final StoreIndexInfo storeIndexInfo = en.getValue();

			final Term indexTerm = storeIndexInfo.getIndexTerm();

			final IProgramConst locLit = getLocationLiteral(storeIndexInfo);
			extraConstants.add(locLit);

//			/*
//			 * updated the memloc array
//			 *  in Boogie we would add memloc_int[indexTerm] := locLit
//			 *  note that just adding the conjunct "memloc_int' = (store memloc_int indexTerm locLit)" is wrong here,
//			 *   because if we add several of these constraints (always with the same in/outvar), then the overall
//			 *    constraint has a much narrower meaning than intended!
//			 *    (describing this because the first implementation did it wrong..)
//			 */
//			memlocUpdates.put(indexTerm, locLit.getTerm());

			// TODO: think again about the store chain business..
			for (final Entry<ArrayGroup, Integer> en2 : storeIndexInfo.getArrayToAccessDimensions().entrySet()) {
				memlocUpdatesPerDim.put(en2.getValue(), indexTerm, locLit.getTerm());
			}
		}

		// construct a store chain for the memlocUpdates
		final List<Term> memlocUpdateConjuncts = new ArrayList<>();
		for (int dim = 0; memlocUpdatesPerDim.get(dim) != null; dim++) {
//		{
			final TermVariable memlocIntInVar;
			final TermVariable memlocIntOutVar;
			{
				// TODO not nice, with the locking..
				mMgdScript.unlock(this);
				final IProgramNonOldVar currentMemlocArrayInt = mMemlocArrayManager.getMemlocArray(dim);
				mMgdScript.lock(this);

				assert !extraOutVars.containsKey(mMemlocArrayManager.getMemlocArray(dim));
				memlocIntInVar = mMgdScript.constructFreshCopy(currentMemlocArrayInt.getTermVariable());
				memlocIntOutVar = mMgdScript.constructFreshCopy(currentMemlocArrayInt.getTermVariable());
				extraInVars.put(currentMemlocArrayInt, memlocIntInVar);
				extraOutVars.put(currentMemlocArrayInt, memlocIntOutVar);

				assert oldEdge.getPrecedingProcedure().equals(oldEdge.getSucceedingProcedure());
				mNewModifiableGlobals.addPair(oldEdge.getPrecedingProcedure(), currentMemlocArrayInt);
			}

			Term storeChain = memlocIntInVar;
			for (final Entry<Term, Term> en : memlocUpdatesPerDim.get(dim).entrySet()) {
				storeChain = SmtUtils.store(mMgdScript.getScript(), storeChain, en.getKey(), en.getValue());
			}
			memlocUpdateConjuncts.add(SmtUtils.binaryEquality(mMgdScript.getScript(), memlocIntOutVar, storeChain));
		}

		mMgdScript.unlock(this);

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		newInVars.putAll(extraInVars);
		for (final IProgramVar iv : extraInVars.keySet()) {
			if (iv instanceof IProgramOldVar) {
				continue;
			}
			mNewSymbolTable.add(iv);
		}

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		newOutVars.putAll(extraOutVars);
		for (final IProgramVar ov : extraOutVars.keySet()) {
			if (ov instanceof IProgramOldVar) {
				continue;
			}
			mNewSymbolTable.add(ov);
		}

		final Set<IProgramConst> newNonTheoryConsts = new HashSet<>(tf.getNonTheoryConsts());
		newNonTheoryConsts.addAll(extraConstants);
		for (final IProgramConst pc : extraConstants) {
			mNewSymbolTable.add(pc);
		}

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars,
				newNonTheoryConsts.isEmpty(), newNonTheoryConsts, tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());



		final List<Term> newFormulaConjuncts = new ArrayList<>();
		newFormulaConjuncts.add(tf.getFormula());
		newFormulaConjuncts.addAll(memlocUpdateConjuncts);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));
		tfBuilder.setInfeasibility(tf.isInfeasible());
		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);

		final UnmodifiableTransFormula newTf = tfBuilder.finishConstruction(mMgdScript);
		return new TransformulaTransformationResult(newTf);
	}

	private IProgramConst getLocationLiteral(final StoreIndexInfo storeIndexInfo) {
		IProgramConst result = mStoreIndexInfoToLocLiteral.get(storeIndexInfo);
		if (result == null) {
			assert mMgdScript.isLocked();
			final String locLitName = getLocationLitName(storeIndexInfo);
//			mMgdScript.declareFun(this, locLitName, new Sort[0], mMemLocSort);

			// any dim should work as the index sort must be the same at all dimensions accessted via that index
			final int sampleDim = storeIndexInfo.getArrayToAccessDimensions().entrySet().iterator().next().getValue();
			final Sort sort = mMemlocArrayManager.getMemlocSort(sampleDim);

			mMgdScript.declareFun(this, locLitName, new Sort[0], sort);
			final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);
			result = new HeapSepProgramConst(locLitTerm);
			mStoreIndexInfoToLocLiteral.put(storeIndexInfo, result);
		}
		return result;
	}

	private String getLocationLitName(final StoreIndexInfo storeIndexInfo) {
		return "mll_" + storeIndexInfo.getEdgeInfo().getSourceLocation() + "_" + mMemLocLitCounter ++;
	}

	/**
	 * Not this class's core concern but it also picks up all ConstantTerms in the program.
	 * @return
	 */
	public Set<ConstantTerm> getAllConstantTerms() {
		if (!TRACK_CONSTANTS) {
			throw new IllegalStateException();
		}
		return mAllConstantTerms;
	}

	public Set<IProgramConst> getLocationLiterals() {
		return new HashSet<>(getStoreIndexInfoToLocLiteral().values());
	}

	public Map<StoreIndexInfo, IProgramConst> getStoreIndexInfoToLocLiteral() {
		mQueriedStoreAndLitInfo = true;
		return mStoreIndexInfoToLocLiteral;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// do nothing
	}


	@Override
	public String getName() {
		return "withMemlocArrayUpdates";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mNewModifiableGlobals;
	}
}




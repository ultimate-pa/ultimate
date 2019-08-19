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

import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.ComputeStoreInfosAndArrayGroups;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.HeapSeparatorBenchmark;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.SubArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayCellAccess;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreLocationBlock;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class PartitionProjectionTransitionTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements ITransformulaTransformer {

	/**
	 * Manager for the separated subarrays.
	 */
	private final SubArrayManager mSubArrayManager;

	private final HashRelation3<ArrayGroup, Integer, StoreLocationBlock> mArrayGroupToDimensionToLocationBlocks;

//	private final NestedMap2<EdgeInfo, Term, StoreInfo> mEdgeToIndexToStoreIndexInfo;
//	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	private final ComputeStoreInfosAndArrayGroups<?> mCsiag;

	/**
	 * Map holding the partitioning information.
	 */
	private final NestedMap3<EdgeInfo, ArrayCellAccess, Integer, StoreLocationBlock>
		mEdgeInfoToArrayCellAccessToDimensionToLocationBlock;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final HeapSeparatorBenchmark mStatistics;

	ManagedScript mMgdScript;

	DefaultIcfgSymbolTable mNewSymbolTable;

	private final ILogger mLogger;

	private final CfgSmtToolkit mOldCsToolkit;

	private final HashRelation<String, IProgramNonOldVar> mNewModifiableGlobals;

	/**
	 *
	 * @param logger
	 * @param resultName
	 * @param outLocClazz
	 * @param inputCfg
	 * @param funLocFac
	 * @param backtranslationTracker
	 * @param selectInfoToDimensionToLocationBlock
	 * 			Maps each array read at some dimension in the program to its LocationBlock (i.e. set of all array writes
	 * 			 that may impact the value of the array at the read cell).
	 * 			This is the processed result of our alias analysis.
	 * @param edgeToIndexToStoreIndexInfo
	 * 			enables us to find all StoreIndexInfos by their key members
	 * @param arrayToArrayGroup
	 * 			enables us to find all array groups by their elements
	 * @param heapArrays
	 * @param statistics
	 */
	public PartitionProjectionTransitionTransformer(final ILogger logger,
			final NestedMap2<SelectInfo, Integer, StoreLocationBlock> selectInfoToDimensionToLocationBlock,
//			final NestedMap2<EdgeInfo, Term, StoreInfo> edgeToIndexToStoreIndexInfo,
//			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final ComputeStoreInfosAndArrayGroups<?> csiag,
			final List<IProgramVarOrConst> heapArrays,
			final HeapSeparatorBenchmark statistics,
			final CfgSmtToolkit inputCfgCsToolkit) {

		mMgdScript = inputCfgCsToolkit.getManagedScript();

		mOldCsToolkit = inputCfgCsToolkit;

		logger.info("executing heap partitioning transformation");
		mLogger = logger;

		mHeapArrays = heapArrays;

		mStatistics = statistics;

		/*
		 * We build two maps each a different view on the input map selectInfoToDimensionToLocationBlock
		 * <li> we split up the select infos from the input map into their two components: EdgeInfo and ArrayCellAccess
		 * <li> we combine it with arrayToArrayGroup to group the LocationBlocks by arrayGroup and dimension
		 *   (for the step in the projection operator when we project an array equation and build a big conjunction with
		 *    a conjunct for each fitting LocationBlock tuple)
		 */
		mEdgeInfoToArrayCellAccessToDimensionToLocationBlock = new NestedMap3<>();
		mArrayGroupToDimensionToLocationBlocks = new HashRelation3<>();
		for (final Triple<SelectInfo, Integer, StoreLocationBlock> triple
				: selectInfoToDimensionToLocationBlock.entrySet()) {
			mEdgeInfoToArrayCellAccessToDimensionToLocationBlock.put(triple.getFirst().getEdgeInfo(),
					triple.getFirst().getArrayCellAccess(), triple.getSecond(), triple.getThird());

//			final IProgramVarOrConst array = triple.getFirst().getArrayPvoc();
//			final ArrayGroup arrayGroup = arrayToArrayGroup.get(array);
			final Integer dim = triple.getSecond();
			assert dim == triple.getThird().getDimension();
			mArrayGroupToDimensionToLocationBlocks.addTriple(triple.getFirst().getArrayGroup(), dim, triple.getThird());
		}

//		mArrayToArrayGroup = arrayToArrayGroup;

		mSubArrayManager = new SubArrayManager(inputCfgCsToolkit, mStatistics, csiag);

//		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
		mCsiag = csiag;

		mNewSymbolTable = new DefaultIcfgSymbolTable();

		mNewModifiableGlobals = new HashRelation<>(mOldCsToolkit.getModifiableGlobalsTable().getProcToGlobals());
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {

		final EdgeInfo edgeInfo = new EdgeInfo((IcfgEdge) oldEdge);

		final NestedMap2<ArrayCellAccess, Integer, StoreLocationBlock> arrayCellAccessToDimensionToLocationBlock =
				mEdgeInfoToArrayCellAccessToDimensionToLocationBlock.get(edgeInfo);

		final Term transformedFormula;
		final Map<IProgramVar, TermVariable> inVars;
		final Map<IProgramVar, TermVariable> outVars;
		{
			final PartitionProjectionTermTransformer ppttf =
					new PartitionProjectionTermTransformer(mLogger, mMgdScript, mSubArrayManager,
							arrayCellAccessToDimensionToLocationBlock,
							edgeInfo, mArrayGroupToDimensionToLocationBlocks,
							mCsiag,
							mHeapArrays);
			final Term transformedFormulaRaw = ppttf.transform(tf.getFormula());
			ppttf.finish();

			final Map<Term, Term> substitutionMapping = new IdentityHashMap<>();
			/*
			 * do an extra post processing that eliminates trivial array updates
			 * Collect pairs of termVariables, equations between which should be replaced by "true".
			 */
			for (final Entry<IProgramVar, TermVariable> ov : ppttf.getNewOutVars().entrySet()) {
				if (!mSubArrayManager.isSubArray(ov.getKey())) {
					// not one of the partitioned arrays
					continue;
				}

				if (ppttf.getUpdatedSubarrays().contains(ov.getKey())) {
					// the array is actually updated in the transformula, do nothing
					continue;
				}

				final TermVariable inTv = ppttf.getNewInVars().get(ov.getKey());
				final TermVariable outTv = ov.getValue();
				assert outTv != null;

				if (inTv == null) {
					/* outvar has no corresponding invar --> there are no "neutral" terms like a1' = a1,
					 *  --> current equation is definitely an actual update */
					  continue;
				}

				if (inTv.equals(outTv)) {
					// not an assigned var
					continue;
				}
				/*
				 * ov is an assigned var belonging to one of the partitioned arrays that only has pseudo updates in
				 *  the transformula --> drop the update
				 */

				// don't use SMTUtils.binaryEquality here because it sorts the arguments!
				final Term eq1 = mMgdScript.getScript().term("=", inTv, outTv);
				substitutionMapping.put(eq1, mMgdScript.getScript().term("true"));
				final Term eq2 = mMgdScript.getScript().term("=", outTv, inTv);
				substitutionMapping.put(eq2, mMgdScript.getScript().term("true"));

			}
			final SubstitutionWithLocalSimplification subs =
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping);
			transformedFormula = subs.transform(transformedFormulaRaw);

			inVars = new HashMap<>(ppttf.getNewInVars());
			// filter invars and out vars such that only those which have a TermVariable in the formula are left
			for (final Entry<IProgramVar, TermVariable> iv : ppttf.getNewInVars().entrySet()) {
				if (!mSubArrayManager.isSubArray(iv.getKey())) {
					// not one of the partitioned arrays
					continue;
				}

				if (!Arrays.asList(transformedFormula.getFreeVars()).contains(iv.getValue())) {
					inVars.remove(iv.getKey());
				}
			}
			outVars = new HashMap<>(ppttf.getNewOutVars());
			for (final Entry<IProgramVar, TermVariable> ov : ppttf.getNewOutVars().entrySet()) {
				if (!mSubArrayManager.isSubArray(ov.getKey())) {
					// not one of the partitioned arrays
					continue;
				}

				if (!Arrays.asList(transformedFormula.getFreeVars()).contains(ov.getValue())) {
					outVars.remove(ov.getKey());
				}
			}
			// add outvars for invars that remain (case: an array with a pseudo-update is also read)
			for (final Entry<IProgramVar, TermVariable> iv : inVars.entrySet()) {
				if (!mSubArrayManager.isSubArray(iv.getKey())) {
					// not one of the partitioned arrays
					continue;
				}


				if (!outVars.containsKey(iv.getKey())) {
					outVars.put(iv.getKey(), iv.getValue());
				}
			}
		}


		{
			for (final Entry<IProgramVar, TermVariable> en : inVars.entrySet()) {
				if (en.getKey() instanceof IProgramOldVar) {
					// only add non-oldvar (oldvar is added implicitly, then)
					continue;
				}
				mNewSymbolTable.add(en.getKey());
			}
			for (final Entry<IProgramVar, TermVariable> en : outVars.entrySet()) {
				if (en.getKey() instanceof IProgramOldVar) {
					// only add non-oldvar (oldvar is added implicitly, then)
					continue;
				}
				mNewSymbolTable.add(en.getKey());

				if (oldEdge.getPrecedingProcedure().equals(oldEdge.getSucceedingProcedure())
						&& en.getKey() instanceof IProgramNonOldVar
						&& !en.getValue().equals(inVars.get(en.getKey()))) {
					/*
					 * we have and internal transition or summary and a global assigned var
					 * --> make sure it is tracked in modifiable globals
					 */
					mNewModifiableGlobals.addPair(oldEdge.getPrecedingProcedure(), (IProgramNonOldVar) en.getKey());
				}
			}
			for (final IProgramConst ntc : tf.getNonTheoryConsts()) {
				mNewSymbolTable.add(ntc);
			}

		}


		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(inVars, outVars,
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());

		tfBuilder.setFormula(transformedFormula);
		tfBuilder.setInfeasibility(tf.isInfeasible());
		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);

		final UnmodifiableTransFormula newTransformula = tfBuilder.finishConstruction(mMgdScript);


		assert oldEdge.getPrecedingProcedure().equals(oldEdge.getSucceedingProcedure())
				|| newTransformula.getAssignedVars().stream().allMatch(pv -> (pv instanceof ILocalProgramVar))
				: "how to deal with a call or return transition that modifies a global variable??";

		log(tf, newTransformula);

		return new TransformulaTransformationResult(newTransformula);
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// nothing to do
	}

	@Override
	public String getName() {
		return "HeapPartitionedCfg";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	private void log(final UnmodifiableTransFormula oldTf, final UnmodifiableTransFormula newTf) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}

		final boolean formulaHasChanged = !oldTf.getFormula().equals(newTf.getFormula());
		final boolean inVarsHaveChanged = !oldTf.getInVars().equals(newTf.getInVars());
		final boolean outVarsHaveChanged = !oldTf.getOutVars().equals(newTf.getOutVars());

		mLogger.debug("transformed transition");
		mLogger.debug("\t " + newTf);

		if (!formulaHasChanged && !inVarsHaveChanged && !outVarsHaveChanged) {
			mLogger.debug("\t transformula unchanged");
		}

		if (formulaHasChanged) {
			mLogger.debug("\t formula has changed");
			mLogger.debug("\t old formula:");
			mLogger.debug(oldTf.getFormula());
			mLogger.debug("\t new formula:");
			mLogger.debug(newTf.getFormula());
		}

		if (inVarsHaveChanged) {
			mLogger.debug("\t invars have changed");
			mLogger.debug("\t old invars:");
			mLogger.debug(oldTf.getInVars());
			mLogger.debug("\t new invars:");
			mLogger.debug(newTf.getInVars());
		}

		if (outVarsHaveChanged) {
			mLogger.debug("\t outvars have changed");
			mLogger.debug("\t old outvars:");
			mLogger.debug(oldTf.getOutVars());
			mLogger.debug("\t new outvars:");
			mLogger.debug(newTf.getOutVars());
		}
		mLogger.debug("");
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mNewModifiableGlobals;
	}

}

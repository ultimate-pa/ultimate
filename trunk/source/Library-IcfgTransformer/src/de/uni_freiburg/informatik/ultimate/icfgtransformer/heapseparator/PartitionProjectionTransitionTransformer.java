package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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
//		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

	/**
	 * Manager for the separated subarrays.
	 */
	private final SubArrayManager mSubArrayManager;

	private final HashRelation3<ArrayGroup, Integer, LocationBlock> mArrayGroupToDimensionToLocationBlocks;

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;
	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	/**
	 * Map holding the partitioning information.
	 */
	private final NestedMap3<EdgeInfo, ArrayCellAccess, Integer, LocationBlock>
		mEdgeInfoToArrayCellAccessToDimensionToLocationBlock;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final HeapSeparatorBenchmark mStatistics;

//	private final Map<StoreIndexInfo, LocationBlock> mStoreIndexInfoToLocationBlock;

	ManagedScript mMgdScript;

	DefaultIcfgSymbolTable mNewSymbolTable;

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
//			final String resultName,
//			final Class<OUTLOC> outLocClazz,
//			final IIcfg<INLOC> inputCfg,
//			final ILocationFactory<INLOC, OUTLOC> funLocFac,
//			final IBacktranslationTracker backtranslationTracker,
			final NestedMap2<SelectInfo, Integer, LocationBlock> selectInfoToDimensionToLocationBlock,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final List<IProgramVarOrConst> heapArrays,
			final HeapSeparatorBenchmark statistics,
			final CfgSmtToolkit inputCfgCsToolkit) {
//			final ManagedScript mgdScript) {
//			final Map<StoreIndexInfo, LocationBlock> storeIndexInfoToLocationBlock) {
//		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);

		mMgdScript = inputCfgCsToolkit.getManagedScript();

		logger.info("executing heap partitioning transformation");

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
		for (final Triple<SelectInfo, Integer, LocationBlock> triple
				: selectInfoToDimensionToLocationBlock.entrySet()) {
			mEdgeInfoToArrayCellAccessToDimensionToLocationBlock.put(triple.getFirst().getEdgeInfo(),
					triple.getFirst().getArrayCellAccess(), triple.getSecond(), triple.getThird());

			final IProgramVarOrConst array = triple.getFirst().getArrayPvoc();
			final ArrayGroup arrayGroup = arrayToArrayGroup.get(array);
			final Integer dim = triple.getSecond();
			assert dim == triple.getThird().getDimension();
			mArrayGroupToDimensionToLocationBlocks.addTriple(arrayGroup, dim, triple.getThird());
		}

//		mStoreIndexInfoToLocationBlock = storeIndexInfoToLocationBlock;

		mArrayToArrayGroup = arrayToArrayGroup;

//		mSubArrayManager = new SubArrayManager(mInputCfgCsToolkit, mStatistics, arrayToArrayGroup);
		mSubArrayManager = new SubArrayManager(inputCfgCsToolkit, mStatistics, arrayToArrayGroup);

		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;

		mNewSymbolTable = new DefaultIcfgSymbolTable();
	}

//	@Override
//	public IcfgEdge transform(final IcfgEdge edge, final OUTLOC newSource, final OUTLOC newTarget) {
	@Override
	public TransforumlaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
//		return new TransforumlaTransformationResult(transformedTransformula);
//	}

//		final UnmodifiableTransFormula tf = edge.getTransformula();

//		final EdgeInfo edgeInfo = new EdgeInfo(edge);
		final EdgeInfo edgeInfo = new EdgeInfo((IcfgEdge) oldEdge);

		final NestedMap2<ArrayCellAccess, Integer, LocationBlock> arrayCellAccessToDimensionToLocationBlock =
				mEdgeInfoToArrayCellAccessToDimensionToLocationBlock.get(edgeInfo);

		final PartitionProjectionTermTransformer ppttf =
				new PartitionProjectionTermTransformer(mMgdScript, mSubArrayManager,
						arrayCellAccessToDimensionToLocationBlock,
						edgeInfo, mArrayGroupToDimensionToLocationBlocks, mArrayToArrayGroup,
						mEdgeToIndexToStoreIndexInfo, mHeapArrays);//,
		final Term transformedFormula = ppttf.transform(tf.getFormula());
		ppttf.finish();

		final Map<IProgramVar, TermVariable> inVars = ppttf.getNewInVars();
		final Map<IProgramVar, TermVariable> outVars = ppttf.getNewOutVars();

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

//		return transform(edge, newSource, newTarget, newTransformula);
		return new TransforumlaTransformationResult(newTransformula);
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// TODO Auto-generated method stub

	}



	@Override
	public String getName() {
		return "HeapPartitionedCfg";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

}

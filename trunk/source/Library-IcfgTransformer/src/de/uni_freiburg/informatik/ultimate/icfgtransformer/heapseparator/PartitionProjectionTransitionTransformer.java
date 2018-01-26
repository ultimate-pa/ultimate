package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransitionTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class PartitionProjectionTransitionTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

//	NestedMap2<EdgeInfo, Term, LocationBlock> mEdgeInfoToTermVariableToPartitionBlock;

//	/**
//	 * Map holding the partitioning information.
//	 */
//	private final NestedMap2<IcfgEdge, Term, LocationBlock> mEdgeToTermVariableToPartitionBlock;


	/**
	 * Manager for the separated subarrays.
	 */
	final SubArrayManager mSubArrayManager;


//	private final Map<ArrayGroup, List<Set<LocationBlock>>> mArrayGroupToDimensionToLocationBlocks;
//	private final NestedMap2<ArrayGroup, Integer, Set<LocationBlock>> mArrayGroupToDimensionToLocationBlocks;
	private final HashRelation3<ArrayGroup, Integer, LocationBlock> mArrayGroupToDimensionToLocationBlocks;


	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;
	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	/**
	 * Map holding the partitioning information.
	 */
	private final NestedMap3<EdgeInfo, ArrayCellAccess, Integer, LocationBlock>
		mEdgeInfoToArrayCellAccessToDimensionToLocationBlock;

	/**
	 *
	 * @param logger
	 * @param resultName
	 * @param outLocClazz
	 * @param inputCfg
	 * @param funLocFac
	 * @param backtranslationTracker
//	 * @param selectInfoToLocationBlock
//	 * 			Maps each array read in the program to its LocationBlock (i.e. set of all array writes that may impact
//	 *           the value of the array at the read cell).
//	 * 			This is the processed result of our alias analysis.
	 * @param selectInfoToDimensionToLocationBlock
	 * 			Maps each array read at some dimension in the program to its LocationBlock (i.e. set of all array writes
	 * 			 that may impact the value of the array at the read cell).
	 * 			This is the processed result of our alias analysis.
	 * @param edgeToIndexToStoreIndexInfo
	 * 			enables us to find all StoreIndexInfos by their key members
	 * @param arrayToArrayGroup
	 * 			enables us to find all array groups by their elements
	 */
	public PartitionProjectionTransitionTransformer(final ILogger logger, final String resultName,
			final Class<OUTLOC> outLocClazz,
			final IIcfg<INLOC> inputCfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker,
//			final Map<SelectInfo, LocationBlock> selectInfoToLocationBlock,
			final NestedMap2<SelectInfo, Integer, LocationBlock> selectInfoToDimensionToLocationBlock,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup) {
		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);

//		mEdgeToTermVariableToPartitionBlock = new NestedMap2<>();
//		for (final Entry<SelectInfo, LocationBlock> en : selectInfoToLocationBlock.entrySet()) {
//			mEdgeToTermVariableToPartitionBlock.put(
//					en.getKey().getEdgeInfo().getEdge(),
//					en.getKey().getArrayCellAccess().getIndex(),
//					en.getValue());
//		}
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

//			aca = triple.getFirst().getArrayCellAccess();
			final IProgramVarOrConst array = triple.getFirst().getArrayPvoc();
			final ArrayGroup arrayGroup = arrayToArrayGroup.get(array);
			final Integer dim = triple.getSecond();
			assert dim == triple.getThird().getDimension();
			mArrayGroupToDimensionToLocationBlocks.addTriple(arrayGroup, dim, triple.getThird());
		}

		mArrayToArrayGroup = arrayToArrayGroup;

		// for this map we group the
//		mArrayGroupToDimensionToLocationBlocks = null;
//				computeArrayGroupToDimensionToLocationBlocks(
//						selectInfoToLocationBlock.values());

		mSubArrayManager = new SubArrayManager(mInputCfgCsToolkit, null);

		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
	}

//	private Map<ArrayGroup, List<Set<LocationBlock>>> computeArrayGroupToDimensionToLocationBlocks(
//			final Collection<LocationBlock> values) {
//		final Map<ArrayGroup, List<Set<LocationBlock>>> result = new HashMap<>();
//
//		for (final LocationBlock locationBlock : values) {
////			locationBlock.
//		}
//
//		return result;
//	}

	@Override
	public IcfgEdge transform(final IcfgEdge edge, final OUTLOC newSource, final OUTLOC newTarget) {

		final UnmodifiableTransFormula tf = edge.getTransformula();

		// essentially split up the SelectInfos

//		final Map<Term, LocationBlock> termToLocationBlock = mEdgeToTermVariableToPartitionBlock.get(edge);
//				mEdgeInfoToTermVariableToPartitionBlock.get(new EdgeInfo(edge));

		final EdgeInfo edgeInfo = new EdgeInfo(edge);

		final NestedMap2<ArrayCellAccess, Integer, LocationBlock> arrayCellAccessToDimensionToLocationBlock =
				mEdgeInfoToArrayCellAccessToDimensionToLocationBlock.get(edgeInfo);

		final PartitionProjectionTermTransformer ppttf =
//				new PartitionProjectionTermTransformer(mSubArrayManager, termToLocationBlock, edgeInfo,
				new PartitionProjectionTermTransformer(mMgdScript, mSubArrayManager,
						arrayCellAccessToDimensionToLocationBlock,
						edgeInfo, mArrayGroupToDimensionToLocationBlocks, mArrayToArrayGroup,
						mEdgeToIndexToStoreIndexInfo);
		final Term transformedFormula = ppttf.transform(tf.getFormula());

		final Map<IProgramVar, TermVariable> inVars = ppttf.getNewInVars();
		final Map<IProgramVar, TermVariable> outVars = ppttf.getNewOutVars();

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(inVars, outVars,
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());

		tfBuilder.setFormula(transformedFormula);
		tfBuilder.setInfeasibility(tf.isInfeasible());

		final UnmodifiableTransFormula newTransformula = tfBuilder.finishConstruction(mMgdScript);

		return transform(edge, newSource, newTarget, newTransformula);
	}

}

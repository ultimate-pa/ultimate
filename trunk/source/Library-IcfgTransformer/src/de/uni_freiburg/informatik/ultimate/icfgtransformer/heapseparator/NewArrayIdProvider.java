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
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IntraproceduralReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class NewArrayIdProvider {

	private final Map<Set<Term>, PartitionInformation> mArrayToPartitionInformation = new HashMap<>();
	private final DefaultIcfgSymbolTable mNewSymbolTable;

	private final Map<Term, Set<Term>> mArrayIdToArrayGroup = new HashMap<>();

	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final HeapSeparatorBenchmark mStatistics;

	public NewArrayIdProvider(final CfgSmtToolkit csToolkit,
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final HeapSepPreAnalysis hspav,
			final NestedMap2<Term, EdgeInfo, IProgramNonOldVar> writeIndexTermToTfInfoToFreezeVar,
			final HeapSeparatorBenchmark statistics) {
		mManagedScript = csToolkit.getManagedScript();
		mOldSymbolTable = csToolkit.getSymbolTable();
		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
		mStatistics = statistics;

		processAbstractInterpretationResult(equalityProvider, hspav);
	}

	/**
	 *
	 * @param equalityProvider
	 * @param hspav
	 * @return a map of the form (unseparated array --> index --> separated array)
	 */
	private void processAbstractInterpretationResult(
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final HeapSepPreAnalysis hspav) {

		final UnionFind<Term> arrayGroupingUf = computeArrayGroups(hspav);

		final Map<Set<Term>, IEqualityProvidingState> arrayGroupToVPState = computeEqStateForArrayGroups(
				equalityProvider, hspav, arrayGroupingUf);


//		/*
//		 * Compute the actual partitioning for each array.
//		 */
//		for (final Entry<Set<Term>, IEqualityProvidingState> en : arrayGroupToVPState.entrySet()) {
//			final Set<Term> arrayGroup = en.getKey();
//			final IEqualityProvidingState state = en.getValue();
//
//			final UnionFind<ArrayIndex> uf = new UnionFind<>();
//			for (final ArrayIndex accessingTerm : hspav.getAccessingIndicesForArrays(arrayGroup)) {
//				uf.findAndConstructEquivalenceClassIfNeeded(accessingTerm);
//			}
//			// TODO: optimization: compute partitioning on the equivalence class representatives instead
//			// of all nodes
//			for (final ArrayIndex accessingNode1 : hspav.getAccessingIndicesForArrays(arrayGroup)) {
//				for (final ArrayIndex accessingNode2 : hspav.getAccessingIndicesForArrays(arrayGroup)) {
//					assert accessingNode1.size() == accessingNode2.size();
//					boolean anyUnequal = false;
//					for (int i = 0; i < accessingNode1.size(); i++) {
//						anyUnequal |= state.areUnequal(accessingNode1.get(i), accessingNode2.get(i));
//					}
//
//					if (!anyUnequal) {
//						uf.union(accessingNode1, accessingNode2);
//					}
//				}
//			}
//			for (final Set<ArrayIndex> ec : uf.getAllEquivalenceClasses()) {
//				registerEquivalenceClass(arrayGroup, ec);
//				mStatistics.incrementEquivalenceClassCounter();
//			}
//		}

	}

	/**
	 * For each array group:
	 * Obtain an equality provider that sums up the equality and disequality information that * must hold at each
	 * program location where an array in the group is accessed.
	 *
	 * @param equalityProvider
	 * @param hspav
	 * @param arrayGroupingUf
	 * @return
	 */
	protected Map<Set<Term>, IEqualityProvidingState> computeEqStateForArrayGroups(
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final HeapSepPreAnalysis hspav, final UnionFind<Term> arrayGroupingUf) {
		final HashRelation<Set<Term>, IcfgLocation> arrayGroupToAccessLocations = new HashRelation<>();

//		for (final Set<Term> ec : arrayGroupingUf.getAllEquivalenceClasses()) {
//			for (final Term array : ec) {
//				for (final IcfgLocation loc : hspav.getArrayToAccessLocations().getImage(array)) {
//					arrayGroupToAccessLocations.addPair(ec, loc);
//				}
//			}
//		}

		final Map<Set<Term>, IEqualityProvidingState> arrayGroupToVPState = new HashMap<>();
		for (final Set<Term> arrayGroup : arrayGroupingUf.getAllEquivalenceClasses()) {
			final Set<IcfgLocation> arrayGroupAccessLocations = arrayGroupToAccessLocations.getImage(arrayGroup);
			final IEqualityProvidingState eqpState =
					equalityProvider.getEqualityProvidingStateForLocationSet(arrayGroupAccessLocations);
			assert eqpState != null;
			arrayGroupToVPState.put(arrayGroup, eqpState);
		}
		return arrayGroupToVPState;
	}

	/**
	 * compute which arrays are equated somewhere in the program and thus need the same partitioning
	 */
	protected UnionFind<Term> computeArrayGroups(final HeapSepPreAnalysis hspav) {
		final UnionFind<Term> arrayGroupingUf = new UnionFind<>();
//		for (final Term array : hspav.getArrayToAccessLocations().getDomain()) {
//			arrayGroupingUf.findAndConstructEquivalenceClassIfNeeded(array);
//		}
//		for (final Entry<Term, Term> pair : hspav.getArrayEqualities()) {
//			if (arrayGroupingUf.find(pair.getKey()) == null) {
//				continue;
//			}
//			if (arrayGroupingUf.find(pair.getValue()) == null) {
//				continue;
//			}
//			arrayGroupingUf.union(pair.getKey(), pair.getValue());
//		}
//		arrayGroupingUf.getAllEquivalenceClasses();
//
//		mStatistics.setNoArrays(hspav.getArrayToAccessLocations().getDomain().size());
		mStatistics.setNoArrayGroups(arrayGroupingUf.getAllEquivalenceClasses().size());
		return arrayGroupingUf;
	}




	/**
	 * Return the partition id of the partitioned array belonging to originalArrayId at position indexVector
	 * @param originalArrayId
	 * @param indexVector
	 * @return
	 */
	public Term getNewArrayId(final Term originalArrayId, final ArrayIndex indexVector) {
		return mArrayToPartitionInformation
				.get(mArrayIdToArrayGroup.get(originalArrayId))
				.getNewArray(originalArrayId, indexVector);
	}

	public void registerEquivalenceClass(
			final Set<Term> arrayIds,
			final Set<ArrayIndex> ec) {
		final IndexPartition indexPartition = new IndexPartition(arrayIds, ec);

		PartitionInformation partitionInfo = mArrayToPartitionInformation.get(arrayIds);
		if (partitionInfo == null) {
			partitionInfo = new PartitionInformation(arrayIds, mManagedScript, mNewSymbolTable, mOldSymbolTable);
			mArrayToPartitionInformation.put(arrayIds, partitionInfo);
		}
		partitionInfo.addPartition(indexPartition);


		for (final Term arrayId : arrayIds) {
			mArrayIdToArrayGroup.put(arrayId, arrayIds);
		}
	}

	public List<Term> getAllNewArrayIds(final Term oldLhs) {
		return mArrayToPartitionInformation.get(mArrayIdToArrayGroup.get(oldLhs)).getNewArrayIds().get(oldLhs);
	}

	@Override
	public String toString() {
		return "NewArrayIdProvider: \n" + mArrayToPartitionInformation.toString();
	}

	public IIcfgSymbolTable getNewSymbolTable() {
		return mNewSymbolTable;
	}
}

/*
 * Represents a set of Array Indices which, with respect to a given array, may never alias with
 * the indices in any other partition.
 */
class IndexPartition {
	final Set<Term> arrayIds;
	final Set<ArrayIndex> indices;

	public IndexPartition(final Set<Term> arrayIds, final Set<ArrayIndex> indices) {
		this.arrayIds = arrayIds;
		this.indices = Collections.unmodifiableSet(indices);
	}

	@Override
	public String toString() {
		return indices.toString();
	}
}

/**
 * Holds partition information for a given array group (as computed by the HeapSepPreAnalysis), i.e. which groups of
 * indices (called IndexPartitions) may alias, and what new Term/IProgramVar is assigned to it.
 * Also constructs these new identifiers and updates the new symbol table.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class PartitionInformation {
	/*
	 * an array group in the original program, an groups are formed as arrays that are equated anywhere in the program
	 */
	private final Set<Term> arrayIds;

	int versionCounter = 0;
	private final DefaultIcfgSymbolTable mNewSymbolTable;
	private final List<IndexPartition> indexPartitions;

	private final Map<Term, List<Term>> mOldArrayIdToNewArrayIds = new HashMap<>();

	final NestedMap2<IndexPartition, Term, Term> indexBlockToArrayToNewArrayId = new NestedMap2<>();

	private final Map<ArrayIndex, IndexPartition> indexToIndexBlock = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;

	public PartitionInformation(final Set<Term> arrayIds, final ManagedScript mScript,
			final DefaultIcfgSymbolTable newSymbolTable, final IIcfgSymbolTable oldSymbolTable) {
		this.arrayIds = arrayIds;
		indexPartitions = new ArrayList<>();
		mManagedScript = mScript;
		mNewSymbolTable = newSymbolTable;
		mOldSymbolTable = oldSymbolTable;
	}

	Term getNewArray(final Term oldArrayId, final ArrayIndex indexVector) {
		assert arrayIds.contains(oldArrayId);
		final IndexPartition ip = indexToIndexBlock.get(indexVector);
		assert ip != null;
		assert indexBlockToArrayToNewArrayId.get(ip, oldArrayId) != null;
		return indexBlockToArrayToNewArrayId.get(ip, oldArrayId);
	}

	void addPartition(final IndexPartition ip) {
		indexPartitions.add(ip);
		for (final ArrayIndex index : ip.indices) {
			indexToIndexBlock.put(index, ip);
		}
		constructFreshProgramVarsForIndexPartition(ip);
	}

	private int getFreshVersionIndex() {
		//TODO: a method seems overkill right now -- remove if nothing changes..
		return versionCounter++;
	}

	/**
	 * Given an IndexPartition constructs fresh Terms and ProgramVars for all the arrays in this ParititionInformation's
	 * array group.
	 * Updates the mappings that holds these fresh Terms.
	 *
	 * @param oldArrayId
	 * @param indexPartition
	 * @return
	 */
	private void constructFreshProgramVarsForIndexPartition(
			final IndexPartition indexPartition) {
		mManagedScript.lock(this);

		for (final Term arrayTv : arrayIds) {
			final IProgramVarOrConst arrayPv = mOldSymbolTable.getProgramVar((TermVariable) arrayTv);

			IProgramVarOrConst freshVar = null;
			if (arrayPv instanceof LocalBoogieVar) {
				final LocalBoogieVar lbv = (LocalBoogieVar) arrayPv;
				final String newId = lbv.getIdentifier() + "_part_" + getFreshVersionIndex();
				final TermVariable newTv = mManagedScript.constructFreshCopy(lbv.getTermVariable());

				final String constString = newId + "_const";
				mManagedScript.getScript().declareFun(constString, new Sort[0], newTv.getSort());
				final ApplicationTerm newConst = (ApplicationTerm) mManagedScript.term(this, constString);

				final String constPrimedString = newId + "_const_primed";
				mManagedScript.getScript().declareFun(constPrimedString, new Sort[0], newTv.getSort());
				final ApplicationTerm newPrimedConst = (ApplicationTerm) mManagedScript.term(this, constPrimedString);

				freshVar = new LocalBoogieVar(
						newId,
						lbv.getProcedure(),
						null,
						newTv,
						newConst,
						newPrimedConst);
				mNewSymbolTable.add(freshVar);

				indexBlockToArrayToNewArrayId.put(indexPartition, arrayTv, newTv);
			} else if (arrayPv instanceof BoogieNonOldVar) {
				// the oldVar may have come up first..
				final Term alreadyConstructed = indexBlockToArrayToNewArrayId.get(indexPartition, arrayTv);
				if (alreadyConstructed == null) {
					final BoogieNonOldVar bnovOld = (BoogieNonOldVar) arrayPv;

					final String newId = bnovOld.getIdentifier() + "_part_" + getFreshVersionIndex();

					final BoogieNonOldVar bnovNew =
							ProgramVarUtils.constructGlobalProgramVarPair(newId, bnovOld.getSort(), mManagedScript, this);

					freshVar = bnovNew;
					mNewSymbolTable.add(freshVar);

					indexBlockToArrayToNewArrayId.put(indexPartition, arrayTv, freshVar.getTerm());
					indexBlockToArrayToNewArrayId.put(indexPartition,
							((BoogieNonOldVar) arrayPv).getOldVar().getTerm(),
							bnovNew.getOldVar().getTerm());
				} else {
					freshVar = mNewSymbolTable.getProgramVar((TermVariable) alreadyConstructed);
				}

			} else if (arrayPv instanceof BoogieOldVar) {
				// the nonOldVar may have come up first..
				final Term alreadyConstructed = indexBlockToArrayToNewArrayId.get(indexPartition, arrayTv);
				if (alreadyConstructed == null) {
					final BoogieOldVar bovOld = (BoogieOldVar) arrayPv;

					final String newId = bovOld.getGloballyUniqueId() + "_part_" + getFreshVersionIndex();

					final BoogieNonOldVar bnovNew =
							ProgramVarUtils.constructGlobalProgramVarPair(newId, bovOld.getSort(), mManagedScript, this);

					freshVar = bnovNew.getOldVar();
					mNewSymbolTable.add(freshVar);

					indexBlockToArrayToNewArrayId.put(indexPartition, arrayTv, freshVar.getTerm());
					indexBlockToArrayToNewArrayId.put(indexPartition,
							((BoogieOldVar) arrayPv).getNonOldVar().getTerm(),
							bnovNew.getTerm());
				} else {
					freshVar = mNewSymbolTable.getProgramVar((TermVariable) alreadyConstructed);
				}
				assert freshVar != null;
			} else if (arrayPv instanceof IntraproceduralReplacementVar) {
				assert false : "TODO: implement";
			} else if (arrayPv instanceof BoogieConst) {
				assert false : "TODO: implement";
			} else {
				assert false : "case missing --> add it?";
			}


			List<Term> newIdList = mOldArrayIdToNewArrayIds.get(arrayPv);
			if (newIdList == null) {
				newIdList = new ArrayList<>();
				mOldArrayIdToNewArrayIds.put(arrayTv, newIdList);
			}
			newIdList.add(freshVar.getTerm());
		}

		mManagedScript.unlock(this);
	}


	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(" --- PartitionInformation for array group: " + arrayIds + " --- \n");

		sb.append(" " + indexPartitions.size() + " partitions: " + indexPartitions);
		sb.append("\n");
		sb.append(" partition sizes: " + indexPartitions.stream().map(ip -> ip.indices.size()).collect(Collectors.toList()));
		sb.append("\n");

		return sb.toString();
	}

	Map<Term, List<Term>> getNewArrayIds() {
		return mOldArrayIdToNewArrayIds;
	}
}

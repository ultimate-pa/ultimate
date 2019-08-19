/*
 * Copyright (C) 2016-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 University of Freiburg
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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayCellAccess;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SelectInfo;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Does an auxiliary analysis on the program before the actual heap separation is done.
 * <p>
 * Computes of each {@link IcfgEdge} the subterms of the edge's TransFormula that are subject to transformation by the
 * heap separator.
 * <p>
 * These subterms are divided into:
 * <ul>
 * <li> cell updates (array updates where the lhs and rhs array refer to the same program variable, "array writes")
 * <li> array relations (equalities where the lhs and rhs have array type -stores are allowed- and which are not cell
 *  updates )
 * <li> cell accesses (essentially select terms, "array reads")
 * </ul>
 * Furthermore from the result of this analysis we can compute the groups of arrays whose partitioning has to be
 * aligned because they are assigned to each other {@link ArrayGroup}.
 *
 * @author Alexander Nutz
 *
 */
public class FindSelects {


	// unclear if ArrayUpdate is the right choice here -- what about store chains?, also it uses MultiDimensionalStore..
	private final HashRelation<EdgeInfo, ArrayUpdate> mEdgeToCellUpdates;

	private final HashRelation<EdgeInfo, ArrayEqualityAllowStores> mEdgeToArrayRelations;

	private final ManagedScript mMgdScript;

	private final Set<SelectInfo> mSelectInfos;

	private Set<ArrayGroup> mArrayGroups;

	private final List<IProgramVarOrConst> mHeapArrays;

//	private final Map <IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	private final ILogger mLogger;

	private final HeapSeparatorBenchmark mStatistics;

	private final ComputeStoreInfosAndArrayGroups<?> mCsiag;

//	private final NestedMap2<EdgeInfo, Term, ArrayGroup> mEdgeToTermToArrayGroup;

	/**
	 * See {@link FindSelects}.
	 *
	 * @param logger
	 * @param heapArrays
	 * @param statistics
	 * @param edgeToTermToArrayGroup
	 * @param arrayToArrayGroup
	 * @param equalityProvider
	 */
	public FindSelects(final ILogger logger, final ManagedScript mgdScript,
			final List<IProgramVarOrConst> heapArrays, final HeapSeparatorBenchmark statistics,
			final ComputeStoreInfosAndArrayGroups<?> csiag) {
		mMgdScript = mgdScript;
		mLogger = logger;
		mStatistics = statistics;
		mHeapArrays = heapArrays;
		mEdgeToCellUpdates = new HashRelation<>();
		mEdgeToArrayRelations = new HashRelation<>();
		mSelectInfos = new HashSet<>();
//		mArrayToArrayGroup = arrayToArrayGroup;
//		mEdgeToTermToArrayGroup = edgeToTermToArrayGroup;
		mCsiag = csiag;
	}

	public void processEdge(final IcfgEdge edge) {
		final UnmodifiableTransFormula tf = edge.getTransformula();

		final EdgeInfo edgeInfo = new EdgeInfo(edge);

//		new ApplicationTermFinder("select", false);

		final List<MultiDimensionalSelect> mdSelects = MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), true);

		// not sure if the mdSelects are good enough, therefore making a check here
		if (!mdSelects.isEmpty()) {
			final Set<ApplicationTerm> allSelects =
				new ApplicationTermFinder("select", false).findMatchingSubterms(tf.getFormula());

			final Set<ApplicationTerm> selectsInMdSelects = mdSelects.stream()
					.map(mds -> new ApplicationTermFinder("select", false)
					.findMatchingSubterms(mds.getSelectTerm()))
					.reduce((s1, s2) -> DataStructureUtils.union(s1, s2)).get();

			if (!allSelects.equals(selectsInMdSelects)) {
				throw new AssertionError();
			}
		}

		for (final MultiDimensionalSelect mds : mdSelects) {
			final ArrayCellAccess aca = new ArrayCellAccess(mds);

			if (!mCsiag.isArrayTermSubjectToSeparation(edgeInfo, aca.getArray())) {
				// not a separated array --> do nothing
				continue;
			}

			final ArrayGroup ag = mCsiag.getArrayGroupForTermInEdge(edgeInfo, aca.getArray());
			final SelectInfo si = new SelectInfo(aca, edgeInfo, ag, mMgdScript);
			mSelectInfos.add(si);
		}
	}

	public Set<SelectInfo> getSelectInfos() {
		if (mSelectInfos == null) {
			throw new IllegalStateException("call finish first");
		}
		return mSelectInfos;
	}

	public void finish() {
//		/*
//		 * compute array read statistics
//		 */
//		final Map<ArrayGroup, Integer> heapArrayGroupToReadCount = new HashMap<>();
//		for (final SelectInfo selectInfo : mSelectInfos) {
//
//			final ArrayGroup ag = mArrayToArrayGroup.get(selectInfo.getArrayPvoc());
//
//			Integer oldCount = heapArrayGroupToReadCount.get(ag);
//			if (oldCount == null) {
//				oldCount = 0;
//				heapArrayGroupToReadCount.put(ag, oldCount);
//			}
//			heapArrayGroupToReadCount.put(ag, oldCount + 1);
//		}
//		for (final Entry<ArrayGroup, Integer> en : heapArrayGroupToReadCount.entrySet()) {
//			mLogger.info("Number of read from array group " + en.getKey() + " : " + en.getValue());
//			mStatistics.registerPerArrayInfo(en.getKey(), HeapSeparatorStatistics.COUNT_ARRAY_READS, en.getValue());
//		}

	}


}

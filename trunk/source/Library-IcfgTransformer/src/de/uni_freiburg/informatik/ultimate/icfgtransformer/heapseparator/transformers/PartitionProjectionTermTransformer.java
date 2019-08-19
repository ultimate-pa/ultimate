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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.ComputeStoreInfosAndArrayGroups;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.SubArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayCellAccess;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreLocationBlock;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Note: This TermTransformer is built with respect to a specific TransFormula whose term it should transform. (which is
 *  somewhat against the architecture of TermTransformers)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class PartitionProjectionTermTransformer extends PositionAwareTermTransformer {

	/**
	 * keeps track of the LocationBlocks that guide the projection in each scope.
	 */
	private final Stack<List<StoreLocationBlock>> mProjectLists;

	private final ManagedScript mMgdScript;

	/**
	 * Maps each Term in the formula that is used to access an array cell (i.e. that corresponds to a SelectInfo) in the
	 * TransFormula that this TermTransformer will be used to transform to an LocationBlock, i.e., a set of locations
	 * where a cell of that array may have been written to.
	 *
	 * input field (or computed from input)
	 * <p>
	 * Note: this may be null if the edge has no selects to a heap array
	 */
	private final NestedMap2<ArrayCellAccess, Integer, StoreLocationBlock> mArrayCellAccessToIntegerToLocationBlock;

	/**
	 * All the location blocks that belong to one array group, divided by dimension they belong to..
	 */
	private final HashRelation3<ArrayGroup, Integer, StoreLocationBlock> mArrayGroupToDimensionToLocationBlocks;

	private final SubArrayManager mSubArrayManager;

	private final HashMap<IProgramVar, TermVariable> mNewInVars;
	private final HashMap<IProgramVar, TermVariable> mNewOutVars;

//	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	private final EdgeInfo mEdgeInfo;

//	private final NestedMap2<EdgeInfo, Term, StoreInfo> mEdgeToIndexToStoreIndexInfo;
	private final NestedMap2<Term, IProgramVarOrConst, Term> mOriginalTermToSubArrayToReplacementTerm;

	private final List<IProgramVarOrConst> mHeapArrays;

	private boolean mIsFinished;

	private final Set<IProgramVar> mInVarsWithATermVar;
	private final Set<IProgramVar> mOutVarsWithATermVar;

	private final ILogger mLogger;


	/**
	 * For an array update "a' = (store a i v)", the projection operator that this transformer implements may create
	 *  many equations of the form "a_part_x' = a_part_x". We cannot just drop all equations of this sort, because
	 *  they might be in a disjunction with a real update.
	 * Thus, we globally track which subarrays (a_part_..) are actually updated anywhere in the formula.
	 * Afterwards we eliminate them from the formula (and invars/outvars) through a postprocessing.
	 */
	private final Set<IProgramVarOrConst> mUpdatedSubarrays;

	private final ComputeStoreInfosAndArrayGroups<?> mCsiag;

	/**
	 *
	 * @param mgdScript
	 * @param subArrayManager
	 * @param arrayCellAccessToDimensionToLocationBlock
	 * 			maps an ArrayCellAccess (essentially a MultiDimensionalSelect(over store) in the edge this ttf belongs
	 *          to (via edgeInfo parameter), and an access dimension, to a LocationBlocck... TODO
	 * @param edgeInfo
	 * @param arrayGroupToDimensionToLocationBlocks
	 * @param arrayToArrayGroup
	 * @param edgeToIndexToStoreIndexInfo
	 * 			enables us to find all StoreIndexInfos by their key members
	 * @param selectIndexTermToLocationBlock
	 *
//	 * 			The map StoreIndexInfo -> LocationBlock, projected down to mEdgeInfo
	 */
	public PartitionProjectionTermTransformer(final ILogger logger, final ManagedScript mgdScript,
			final SubArrayManager subArrayManager,
			final NestedMap2<ArrayCellAccess, Integer, StoreLocationBlock> arrayCellAccessToDimensionToLocationBlock,
			final EdgeInfo edgeInfo,
			final HashRelation3<ArrayGroup, Integer, StoreLocationBlock> arrayGroupToDimensionToLocationBlocks,
			final ComputeStoreInfosAndArrayGroups<?> csiag,
			final List<IProgramVarOrConst> heapArrays) {
		mLogger = Objects.requireNonNull(logger);
		mMgdScript = Objects.requireNonNull(mgdScript);

		mSubArrayManager = Objects.requireNonNull(subArrayManager);
		mHeapArrays = Objects.requireNonNull(heapArrays);

		mCsiag = csiag;

		assert Objects.nonNull(arrayCellAccessToDimensionToLocationBlock)
			|| !ArrayCellAccess.extractArrayCellAccesses(edgeInfo.getEdge().getTransformula().getFormula()).stream()
				.anyMatch(aca -> mHeapArrays.contains(edgeInfo.getProgramVarOrConstForTerm(aca.getSimpleArray())))
				: "this input map must be non-null if we have a select on a heap array inside the edge";
		mArrayCellAccessToIntegerToLocationBlock = arrayCellAccessToDimensionToLocationBlock;

		mArrayGroupToDimensionToLocationBlocks = arrayGroupToDimensionToLocationBlocks;

		mEdgeInfo = edgeInfo;

		mNewInVars = new HashMap<>();
		mNewOutVars = new HashMap<>();

		mInVarsWithATermVar = new HashSet<>();
		mOutVarsWithATermVar = new HashSet<>();

		mProjectLists = new Stack<>();
		mProjectLists.push(Collections.emptyList());

		mOriginalTermToSubArrayToReplacementTerm = new NestedMap2<>();

		mUpdatedSubarrays = new HashSet<>();
	}

	@Override
	protected void convert(final Term term, final SubtreePosition pos) {
		assert mProjectLists.stream().allMatch(l -> l.stream().allMatch(Objects::nonNull));
		final List<StoreLocationBlock> projectList = mProjectLists.peek();
		if (term instanceof ConstantTerm
				|| term instanceof TermVariable) {
			final IProgramVar invar = mEdgeInfo.getInVar(term);
			if (invar != null) {
				mInVarsWithATermVar.add(invar);
			}
			final IProgramVar outvar = mEdgeInfo.getOutVar(term);
			if (outvar != null) {
				mOutVarsWithATermVar.add(outvar);
			}

			if (isPartitionedArray(term)) {
				final Term subArrayTerm = getSubArrayReplacementTerm(term, projectList);
				setResult(subArrayTerm);
			} else {
				// leave term unchanged (projection does not apply to it)
				setResult(term);
			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			final String functionName = at.getFunction().getName();
			if (functionName.equals("=")
					&& at.getFunction().getParameterSorts().length == 2
					&& at.getParameters()[0].getSort().isArraySort()) {
				// equation of two array terms

				assert projectList.isEmpty() : "We should not have an active projection on the Boolean level.";

				final Term lhs = at.getParameters()[0];
				final Term rhs = at.getParameters()[1];

				final Term lhsBaseArray = extractSimpleArrayTerm(lhs);
				final Term rhsBaseArray = extractSimpleArrayTerm(rhs);

				if (!mCsiag.isArrayTermSubjectToSeparation(mEdgeInfo, lhsBaseArray)) {
					assert !mCsiag.isArrayTermSubjectToSeparation(mEdgeInfo, rhsBaseArray);
					super.convert(term, pos);
					return;
				}
				assert mCsiag.isArrayTermSubjectToSeparation(mEdgeInfo, rhsBaseArray);

				final ArrayGroup arrayGroup = mCsiag.getArrayGroupForTermInEdge(mEdgeInfo, lhsBaseArray);

				// holds the combinations of L1i .. Lni we will build a conjunct for each
				final List<List<StoreLocationBlock>> locationBlockTuples =
						getAllLocationBlockTuplesForHeapArray(arrayGroup);

				enqueueWalker(new BuildConjunction(locationBlockTuples.size(), mMgdScript.getScript()));

				for (final List<StoreLocationBlock> lbt : locationBlockTuples) {
					enqueueWalker(new EndScope());

					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term, pos));
					pushTerms(at.getParameters(), pos);

					enqueueWalker(new BeginScope(Collections.unmodifiableList(lbt)));
				}

			} else if (functionName.equals("select")) {

				final Term array = at.getParameters()[0];

				final IProgramVarOrConst arrayPvoc =
						mEdgeInfo.getProgramVarOrConstForTerm(extractSimpleArrayTerm(array));

				if (!mHeapArrays.contains(arrayPvoc)) {
					super.convert(term, pos);
					return;
				}


				/*
				 *  as soon as we see a select, we consume it fully as a ArrayCellAccess (MultiDimensionalSelect)
				 */
				final ArrayCellAccess aca = new ArrayCellAccess(new MultiDimensionalSelect(term));

				enqueueWalker(new BuildArrayCellAccessTerm(aca, mMgdScript.getScript()));

				// convert the index terms under an empty scope
				enqueueWalker(new EndScope());
				pushTerms(aca.getIndex().toArray(new Term[aca.getIndex().size()]), pos.append(1));
				enqueueWalker(new BeginScope(Collections.emptyList()));

				// construct a list of location blocks according to the indices
				final List<StoreLocationBlock> locationBlockList = new ArrayList<>();
				for (int dim = 1; dim <= aca.getIndex().size(); dim++) {
					/*
					 * TODO: indeed for this field it might be nicer to use Map<ArrayCellAccess, List<LocationBlock>>
					 *   instead of a NestedMap2...
					 */
					final StoreLocationBlock locationBlock = mArrayCellAccessToIntegerToLocationBlock.get(aca, dim);
					assert locationBlock != null;
					locationBlockList.add(locationBlock);
				}
				enqueueWalker(new EndScope());
				pushTerm(aca.getArray(), pos.append(2));
				enqueueWalker(new BeginScope(append(locationBlockList, projectList)));

			} else if (functionName.equals("store")) {

				final Term arraySubterm = at.getParameters()[0];
				final Term indexSubterm = at.getParameters()[1];
				final Term valueSubterm = at.getParameters()[2];

				final Term baseArray = extractSimpleArrayTerm(arraySubterm);
				final IProgramVarOrConst baseArrayPvoc = mEdgeInfo.getProgramVarOrConstForTerm(baseArray);
				if (!mHeapArrays.contains(baseArrayPvoc)) {
					super.convert(term, pos);
					return;
				}

				assert projectList.size() > 0 : "(IndexOutOfBoundsExceptions are hard to catch somehow..";
				if (fallsInto(pos, term, projectList.get(0))) {
					// i in L1 --> keep the store

					/*
					 * if (and only if) we have an 'outermost' store, i.e. one whose array term is not a select, we
					 * update the list of arrays which are subject to a real update
					 */
					if (baseArray == arraySubterm) {
						assert new MultiDimensionalSort(baseArray.getSort()).getDimension() == projectList.size();
						final IProgramVarOrConst subArrayPvoc =
								mSubArrayManager.getSubArray(baseArrayPvoc, projectList);
						mUpdatedSubarrays.add(subArrayPvoc);
					}

					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term, pos));

					/*
					 * deal with value
					 */
					enqueueWalker(new EndScope());
					pushTerm(valueSubterm, pos.append(2));
					enqueueWalker(new BeginScope(dropFirst(projectList)));

					/*
					 * deal with index
					 */
					enqueueWalker(new EndScope());
					pushTerm(indexSubterm, pos.append(1));
					enqueueWalker(new BeginScope(Collections.emptyList()));


					/*
					 * deal with array
					 */
					enqueueWalker(new EndScope());
					pushTerm(arraySubterm, pos.append(0));
					enqueueWalker(new BeginScope(projectList));

				} else {
					// i not in L1 --> drop the store, convert the array according to current scope

					// no extra scoping needed, right?
					pushTerm(arraySubterm, pos.append(0));
				}
			} else {
				// leave the term as is, convert its subterms

				// no extra scoping needed, right?
				enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term, pos));
				pushTerms(((ApplicationTerm) term).getParameters(), pos);
			}
		} else if (term instanceof LetTerm) {
			super.convert(term, pos);
		} else if (term instanceof QuantifiedFormula) {
			super.convert(term, pos);
		} else if (term instanceof AnnotatedTerm) {
			super.convert(term, pos);
		} else {
			throw new AssertionError("Unknown Term: " + term.toStringDirect());
		}
	}

	private List<StoreLocationBlock> append(final List<StoreLocationBlock> locationBlockList, final List<StoreLocationBlock> projectList) {
		final List<StoreLocationBlock> result = new ArrayList<>();
		result.addAll(locationBlockList);
		result.addAll(projectList);
		assert assertIsSortedByDimensions(result);
		return result;
	}

	static boolean isSorted(final List<Integer> collect) {
		final List<Integer> copy = new ArrayList<>(collect);
		Collections.sort(copy);
		return collect.equals(copy);
	}

	private Term extractSimpleArrayTerm(final Term term) {
		if (!term.getSort().isArraySort()) {
			throw new IllegalArgumentException();
		}
		Term currentTerm = term;
		while (SmtUtils.isFunctionApplication(currentTerm, "store")
				|| SmtUtils.isFunctionApplication(currentTerm, "select")) {
			currentTerm = ((ApplicationTerm) currentTerm).getParameters()[0];
		}
		assert !(currentTerm instanceof ApplicationTerm) || ((ApplicationTerm) currentTerm).getParameters().length == 0;
		return currentTerm;
	}

	private Term getSubArrayReplacementTerm(final Term originalTerm, final List<StoreLocationBlock> projectList) {

		final IProgramVarOrConst originalTermPvoc = mEdgeInfo.getProgramVarOrConstForTerm(originalTerm);

		final IProgramVarOrConst subArrayPv = mSubArrayManager.getSubArray(originalTermPvoc, projectList);

		return getOrConstructSubArrayTermAndUpdateInOutVarMappings(originalTerm, originalTermPvoc, subArrayPv);
	}

	private Term getOrConstructSubArrayTermAndUpdateInOutVarMappings(final Term originalTerm,
			final IProgramVarOrConst originalTermPvoc, final IProgramVarOrConst subArrayPvoc) {
		Term result = mOriginalTermToSubArrayToReplacementTerm.get(originalTerm, subArrayPvoc);

		if (result == null) {
			if (!(originalTerm instanceof TermVariable)) {
				throw new UnsupportedOperationException("TODO: if this occurs, extend below code to replace a "
						+ "constant term by a constant term");
			}

			result = mMgdScript.constructFreshTermVariable(subArrayPvoc.getGloballyUniqueId(), subArrayPvoc.getSort());

			mOriginalTermToSubArrayToReplacementTerm.put(originalTerm, subArrayPvoc, result);

			// update the in/out var mappings if necessary
			if (subArrayPvoc instanceof IProgramVar) {
				assert originalTermPvoc instanceof IProgramVar;

				final IProgramVar subArrayPv = (IProgramVar) subArrayPvoc;

				final Term origInVarTerm = mEdgeInfo.getEdge().getTransformula().getInVars().get(originalTermPvoc);
				if (origInVarTerm == originalTerm) {
					// original term was invar
					mNewInVars.put(subArrayPv, (TermVariable) result);
				}
				final Term origOutVarTerm = mEdgeInfo.getEdge().getTransformula().getOutVars().get(originalTermPvoc);
				if (origOutVarTerm == originalTerm) {
					// original term was outvar
					mNewOutVars.put(subArrayPv, (TermVariable) result);
				}
			}
		}
		return result;
	}

	private boolean isPartitionedArray(final Term term) {
		if (!term.getSort().isArraySort()) {
			return false;
		}
		// the given array term is not in an array group with one of the heap arrays
		if (!mCsiag.isArrayTermSubjectToSeparation(mEdgeInfo, term)) {
			// the given array term is not in an array group with one of the heap arrays
			return false;
		}

		return true;
	}

	/**
	 * TODO maybe make the field more convenient for our purposes rather than doing this translation each time?..
	 *
	 * @param arrayGroup
	 * @return
	 */
	private List<Set<StoreLocationBlock>> getLocationBlocksForArrayGroup(final ArrayGroup arrayGroup) {
		final List<Set<StoreLocationBlock>> result = new ArrayList<>();
		for (int dim = 1; dim <= arrayGroup.getDimensionality(); dim++) {
			result.add(mArrayGroupToDimensionToLocationBlocks.projectToTrd(arrayGroup, dim));
		}
		return result;
	}

	private static <E> List<E> addToFront(final E locationBlockForIndex, final List<E> projectList) {
		final List<E> newList = new ArrayList<>();
		newList.add(locationBlockForIndex);
		newList.addAll(projectList);
		return Collections.unmodifiableList(newList);
	}

	private static <E> List<E> dropFirst(final List<E> projectList) {
		final List<E> newList = new ArrayList<>();
		newList.addAll(projectList.subList(1, projectList.size()));
		return Collections.unmodifiableList(newList);
	}

	/**
	 *
	 * @param indexSubterm
	 * 			index in a store term
	 * @param locationBlock
	 * @return
	 */
	private boolean fallsInto(final SubtreePosition pos, final Term storeTerm, final StoreLocationBlock locationBlock) {
		// look up the StoreIndexInfo for the given term and mEdgeInfo
		assert SmtUtils.isFunctionApplication(storeTerm, "store");
		final StoreInfo sii = mCsiag.getStoreInfoForStoreTermAtPositionInEdge(mEdgeInfo, pos);
		return locationBlock.contains(sii);
	}

	private void pushLocationBlockList(final List<StoreLocationBlock> newList) {
		assert Objects.nonNull(newList);
		assert newList.stream().allMatch(Objects::nonNull);
		mProjectLists.push(Collections.unmodifiableList(newList));
	}

	private void popLocationBlockList() {
		mProjectLists.pop();
	}

	protected static class BuildArrayCellAccessTerm implements Walker {
		// a script to construct the fresh term
		private final Script mScript;

		private final ArrayCellAccess mArrayCellAccess;

		BuildArrayCellAccessTerm(final ArrayCellAccess aca, final Script script) {
			mArrayCellAccess = aca;
			mScript = script;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PartitionProjectionTermTransformer transformer = (PartitionProjectionTermTransformer) engine;

			final Term[] indexEntries = new Term[mArrayCellAccess.getIndex().size()];

			for (int i = mArrayCellAccess.getIndex().size() - 1; i >= 0 ; i--) {
				indexEntries[i] = transformer.getConverted();
			}
			final ArrayIndex index = new ArrayIndex(Arrays.asList(indexEntries));

			final Term array = transformer.getConverted();

			final Term mdsTerm = new MultiDimensionalSelect(array, index, mScript).getSelectTerm();
			transformer.setResult(mdsTerm);
		}

	}

	protected static class BuildConjunction implements Walker {

		// how many terms to pop from the converted stack and put into the result conjunction
		int mNumberOfConjuncts;

		// a script to construct the fresh term
		Script mScript;

		public BuildConjunction(final int noConjuncts, final Script script) {
			mNumberOfConjuncts = noConjuncts;
			mScript = script;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final PartitionProjectionTermTransformer transformer = (PartitionProjectionTermTransformer) engine;

			final Term[] conjuncts = new Term[mNumberOfConjuncts];

			for (int i = 0; i < mNumberOfConjuncts; i++) {
				conjuncts[i] = transformer.getConverted();
			}

			transformer.setResult(SmtUtils.and(mScript, conjuncts));
		}

		@Override
		public String toString() {
			return "and\\^" + mNumberOfConjuncts;
		}
	}

	static boolean assertIsSortedByDimensions(final List<StoreLocationBlock> list) {
		return isSorted(list.stream().map(lb -> lb.getDimension()).collect(Collectors.toList()));
	}


	protected static class BeginScope implements Walker {


		private final List<StoreLocationBlock> mLocBlockList;

		public BeginScope(final List<StoreLocationBlock> locBlockList) {
			assert Objects.nonNull(locBlockList);
			assert locBlockList.stream().allMatch(Objects::nonNull);
			assert assertIsSortedByDimensions(locBlockList);
			mLocBlockList = locBlockList;
		}


		@Override
		public void walk(final NonRecursive engine) {
			final PartitionProjectionTermTransformer ttf = (PartitionProjectionTermTransformer) engine;
			ttf.beginScope();
			ttf.pushLocationBlockList(mLocBlockList);
		}
	}

	protected static class EndScope implements Walker {
		@Override
		public void walk(final NonRecursive engine) {
			final PartitionProjectionTermTransformer ttf = (PartitionProjectionTermTransformer) engine;
			ttf.endScope();
			ttf.popLocationBlockList();
		}
	}

	public Map<IProgramVar, TermVariable> getNewInVars() {
		if (!mIsFinished) {
			throw new IllegalStateException();
		}
		return Collections.unmodifiableMap(mNewInVars);
	}

	public Map<IProgramVar, TermVariable> getNewOutVars() {
		if (!mIsFinished) {
			throw new IllegalStateException();
		}
		return Collections.unmodifiableMap(mNewOutVars);
	}

	public void finish() {
		/*
		 * Compute invars and outvars for the new transformula
		 *  criteria:
		 *  <li> invars and outvars that do not have a term in the formula mean a havoc on that variable
		 *    --> replace them by all subarrays
		 *  <li> invars/outvars that do have a termVariable in the formula are added on demand:
		 *    --> an single array read only introduces one subarray
		 *    --> an array equation (which includes updates) in principle introduces all subarrays, however
		 *      a subarray that is not updated (stored on) in any location (optimization)
		 */

		/*
		 * deal with non-heap variables
		 */
		for (final Entry<IProgramVar, TermVariable> en : mEdgeInfo.getInVars().entrySet()) {
			if (mHeapArrays.contains(en.getKey())) {
				// deal with heap arrays elsewhere
				continue;
			}
			mNewInVars.put(en.getKey(), en.getValue());
		}
		for (final Entry<IProgramVar, TermVariable> en : mEdgeInfo.getOutVars().entrySet()) {
			if (mHeapArrays.contains(en.getKey())) {
				// deal with heap arrays elsewhere
				continue;
			}
			mNewOutVars.put(en.getKey(), en.getValue());
		}

		/*
		 * deal with heap variables that are in invars but do not have a term in the formula
		 */
		for (final Entry<IProgramVar, TermVariable> en : mEdgeInfo.getInVars().entrySet()) {
			if (!mInVarsWithATermVar.contains(en.getKey())) {
				if (!mHeapArrays.contains(en.getKey())) {
					continue;
				}
				/* heap array invar whose termvariable does not occur in the formula
				 * --> add invar entries for all subarrays (with fresh Termvars)
				 */
				final List<List<StoreLocationBlock>> locationBlockTuples =
//						getAllLocationBlockTuplesForHeapArray(en.getKey());
						getAllLocationBlockTuplesForHeapArray(mCsiag.getArrayGroupForArrayPvoc(en.getKey()));
				for (final List<StoreLocationBlock> lbt : locationBlockTuples) {
					final IProgramVar subarray = (IProgramVar) mSubArrayManager.getSubArray(en.getKey(), lbt);
					final TermVariable freshTv = mMgdScript.constructFreshCopy(subarray.getTermVariable());
					assert !mNewInVars.containsKey(subarray);
					mNewInVars.put(subarray, freshTv);
				}
			}
		}
		for (final Entry<IProgramVar, TermVariable> en : mEdgeInfo.getOutVars().entrySet()) {
			if (!mOutVarsWithATermVar.contains(en.getKey())) {
				if (!mHeapArrays.contains(en.getKey())) {
					continue;
				}
				/* heap array outvar whose termvariable does not occur in the formula
				 * --> add invar entries for all subarrays (with fresh Termvars)
				 */
				final List<List<StoreLocationBlock>> locationBlockTuples =
						getAllLocationBlockTuplesForHeapArray(mCsiag.getArrayGroupForArrayPvoc(en.getKey()));
				for (final List<StoreLocationBlock> lbt : locationBlockTuples) {
					final IProgramVar subarray = (IProgramVar) mSubArrayManager.getSubArray(en.getKey(), lbt);
					final TermVariable freshTv = mMgdScript.constructFreshCopy(subarray.getTermVariable());
					assert !mNewOutVars.containsKey(subarray);
					mNewOutVars.put(subarray, freshTv);
				}
			}
		}

		for (final Entry<IProgramVar, TermVariable> en : mNewInVars.entrySet()) {
			if (mHeapArrays.contains(en.getKey())) {
				throw new IllegalStateException();
			}
		}
		for (final Entry<IProgramVar, TermVariable> en : mNewOutVars.entrySet()) {
			if (mHeapArrays.contains(en.getKey())) {
				throw new IllegalStateException();
			}
		}

		mIsFinished = true;
	}

	private List<List<StoreLocationBlock>> getAllLocationBlockTuplesForHeapArray(final ArrayGroup arrayGroup) {
		assert arrayGroup != null
				&& !DataStructureUtils.intersection(new HashSet<>(mHeapArrays), arrayGroup.getArrays()).isEmpty();
		final List<Set<StoreLocationBlock>> locationBlocks = getLocationBlocksForArrayGroup(arrayGroup);
		final List<List<StoreLocationBlock>> locationBlockTuples = CrossProducts.crossProductOfSets(locationBlocks);
		return locationBlockTuples;
	}

	public Set<IProgramVarOrConst> getUpdatedSubarrays() {
		return mUpdatedSubarrays;
	}
}

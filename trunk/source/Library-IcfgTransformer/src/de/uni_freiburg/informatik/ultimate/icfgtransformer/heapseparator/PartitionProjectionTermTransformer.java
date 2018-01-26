package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Note: This TermTransformer is built with respect to a specific TransFormula whose term it should transform. (which is
 *  somewhat against the architecture of TermTransformers)
 *
 * TODO: probably we need to add some  recognition for meaningless equations in order to drop them
 *   (a' = a where a, a' belong to the the same ProgramVariable)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class PartitionProjectionTermTransformer extends TermTransformer {

	/**
	 * keeps track of the LocationBlocks that guide the projection in each scope.
	 */
	private final Stack<List<LocationBlock>> mProjectLists;

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
//	private final Map<Term, LocationBlock> mTermToLocationBlock;
	private final NestedMap2<ArrayCellAccess, Integer, LocationBlock> mArrayCellAccessToIntegerToLocationBlock;

	/**
	 * All the location blocks that belong to one array group, divided by dimension they belong to..
	 */
	private final HashRelation3<ArrayGroup, Integer, LocationBlock> mArrayGroupToDimensionToLocationBlocks;
//	private final Map<ArrayGroup, List<Set<LocationBlock>>> mArrayGroupToDimensionToLocationBlocks;

	private final SubArrayManager mSubArrayManager;

	private final HashMap<IProgramVar, TermVariable> mNewInVars;
	private final HashMap<IProgramVar, TermVariable> mNewOutVars;

	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup;

	private final EdgeInfo mEdgeInfo;

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;
	private final NestedMap2<Term, IProgramVarOrConst, Term> mOriginalTermToSubArrayToReplacementTerm;

	private final List<IProgramVarOrConst> mHeapArrays;


//	/*
//	 *  maps a term that occurs in one of this's edge's select terms as index to its ArrayCellAccess
//	 */
//	private final Map<Term, ArrayCellAccess> mSelectIndexTermToArrayCellAccess;

//	/**
//	 * The map StoreIndexInfo -> LocationBlock, projected down to mEdgeInfo
//	 *
//	 */
//	private final Map<Term, LocationBlock> mSelectIndexTermToLocationBlock;

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
	public PartitionProjectionTermTransformer(final ManagedScript mgdScript, final SubArrayManager subArrayManager,
			final NestedMap2<ArrayCellAccess, Integer, LocationBlock> arrayCellAccessToDimensionToLocationBlock,
			final EdgeInfo edgeInfo,
			final HashRelation3<ArrayGroup, Integer, LocationBlock> arrayGroupToDimensionToLocationBlocks,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo,
			final List<IProgramVarOrConst> heapArrays) {
//			final Map<Term, ArrayCellAccess> selectIndexTermToArrayCellAccess) {
//			final Map<Term, LocationBlock> selectIndexTermToLocationBlock) {
		mMgdScript = mgdScript;

		mSubArrayManager = subArrayManager;

		mHeapArrays = heapArrays;


//		mSelectIndexTermToArrayCellAccess = selectIndexTermToArrayCellAccess;

		mArrayToArrayGroup = arrayToArrayGroup;

//		mSelectIndexTermToLocationBlock = selectIndexTermToLocationBlock;

//		assert Objects.nonNull(arrayCellAccessToDimensionToLocationBlock);
		mArrayCellAccessToIntegerToLocationBlock = arrayCellAccessToDimensionToLocationBlock;

		mArrayGroupToDimensionToLocationBlocks = arrayGroupToDimensionToLocationBlocks;

		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;

		mEdgeInfo = edgeInfo;

		mNewInVars = new HashMap<>(edgeInfo.getEdge().getTransformula().getInVars());
		mNewOutVars = new HashMap<>(edgeInfo.getEdge().getTransformula().getOutVars());

		mProjectLists = new Stack<>();
		mProjectLists.push(Collections.emptyList());

		mOriginalTermToSubArrayToReplacementTerm = new NestedMap2<>();
	}

	@Override
	protected void convert(final Term term) {
		final List<LocationBlock> projectList = mProjectLists.peek();
		assert projectList.stream().allMatch(Objects::nonNull);
		if (term instanceof ConstantTerm
				|| term instanceof TermVariable) {
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

//				final Term lhsSimpleArray = extractSimpleArrayTerm(lhs);
//				final Term rhsSimpleArray = extractSimpleArrayTerm(rhs);

				final IProgramVarOrConst lhsPvoc = mEdgeInfo.getProgramVarOrConstForTerm(extractSimpleArrayTerm(lhs));
				final IProgramVarOrConst rhsPvoc = mEdgeInfo.getProgramVarOrConstForTerm(extractSimpleArrayTerm(rhs));

				if (!mHeapArrays.contains(lhsPvoc) && !mHeapArrays.contains(rhsPvoc)) {
					super.convert(term);
					return;
				}

				final ArrayGroup arrayGroup = getArrayGroup(extractSimpleArrayTerm(lhs));
				assert arrayGroup.equals(getArrayGroup(extractSimpleArrayTerm(rhs)));

				final List<Set<LocationBlock>> locationBlocks = getLocationBlocksForArrayGroup(arrayGroup);

				final Sort arraySort = at.getParameters()[0].getSort();
//				final MultiDimensionalSort mdSort = new MultiDimensionalSort(arraySort);

				// holds the combinations of L1i .. Lni we will build a conjunct for each
				final List<List<LocationBlock>> locationBlockTuples =
						CrossProducts.crossProductOfSets(locationBlocks);

				enqueueWalker(new BuildConjunction(locationBlockTuples.size(), mMgdScript.getScript()));

				for (final List<LocationBlock> lbt : locationBlockTuples) {
					enqueueWalker(new EndScope());

					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));
					pushTerms(at.getParameters());

					enqueueWalker(new BeginScope(Collections.unmodifiableList(lbt)));
				}

			} else if (functionName.equals("select")) {

				final Term array = at.getParameters()[0];
//				final Term index = at.getParameters()[1];

				final IProgramVarOrConst arrayPvoc =
						mEdgeInfo.getProgramVarOrConstForTerm(extractSimpleArrayTerm(array));

				if (!mHeapArrays.contains(arrayPvoc)) {
					super.convert(term);
					return;
				}


				/*
				 *  as soon as we see a select, we consume it fully as a ArrayCellAccess (MultiDimensionalSelect)
				 */
				final ArrayCellAccess aca = new ArrayCellAccess(new MultiDimensionalSelect(term));

				enqueueWalker(new BuildArrayCellAccessTerm(aca, mMgdScript.getScript()));

				// convert the index terms under an empty scope
				enqueueWalker(new EndScope());
				pushTerms(aca.getIndex().toArray(new Term[aca.getIndex().size()]));
				enqueueWalker(new BeginScope(Collections.emptyList()));

				// construct a list of location blocks according to the indices
				final List<LocationBlock> locationBlockList = new ArrayList<>();
				for (int dim = 0; dim < aca.getIndex().size(); dim++) {
					/*
					 * TODO: indeed for this field it might be nicer to use Map<ArrayCellAccess, List<LocationBlock>>
					 *   instead of a NestedMap2...
					 */
					final LocationBlock locationBlock = mArrayCellAccessToIntegerToLocationBlock.get(aca, dim);
					assert locationBlock != null;
					locationBlockList.add(locationBlock);
				}
				enqueueWalker(new EndScope());
				pushTerm(aca.getArray());
				enqueueWalker(new BeginScope(locationBlockList));

			} else if (functionName.equals("store")) {

				final Term arraySubterm = at.getParameters()[0];
				final Term indexSubterm = at.getParameters()[1];
				final Term valueSubterm = at.getParameters()[2];

				final Term baseArray = extractSimpleArrayTerm(arraySubterm);
				final IProgramVarOrConst baseArrayPvoc = mEdgeInfo.getProgramVarOrConstForTerm(baseArray);
				if (!mHeapArrays.contains(baseArrayPvoc)) {
					super.convert(term);
					return;
				}

				assert projectList.size() > 0 : "(IndexOutOfBoundsExceptions are hard to catch somehow..";
				if (fallsInto(indexSubterm, projectList.get(0))) {
					// i in L1 --> keep the store

					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));

					/*
					 * deal with value
					 */
					enqueueWalker(new EndScope());
					pushTerm(valueSubterm);
					enqueueWalker(new BeginScope(dropFirst(projectList)));

					/*
					 * deal with index
					 */
					enqueueWalker(new EndScope());
					pushTerm(indexSubterm);
					enqueueWalker(new BeginScope(Collections.emptyList()));


					/*
					 * deal with array
					 */
					enqueueWalker(new EndScope());
					pushTerm(arraySubterm);
					enqueueWalker(new BeginScope(projectList));

				} else {
					// i not in L1 --> drop the store

					// no extra scoping needed, right?
					pushTerm(arraySubterm);
				}
			} else {
				// leave the term as is, convert its subterms

				// no extra scoping needed, right?
				enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));
				pushTerms(((ApplicationTerm) term).getParameters());
//				pushNLocationBlockLists(at.getParameters().length, Collections.emptyList());
			}
		} else if (term instanceof LetTerm) {
			enqueueWalker(new StartLetTerm((LetTerm) term));
			pushTerms(((LetTerm) term).getValues());
		} else if (term instanceof QuantifiedFormula) {
			enqueueWalker(new BuildQuantifier((QuantifiedFormula) term));
			pushTerm(((QuantifiedFormula) term).getSubformula());
			beginScope();
		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annterm = (AnnotatedTerm) term;
			enqueueWalker(new BuildAnnotation(annterm));
			final Annotation[] annots = annterm.getAnnotations();
			for (int i = annots.length - 1; i >= 0; i--) {
				final Object value = annots[i].getValue();
				if (value instanceof Term) {
					pushTerm((Term) value);
				} else if (value instanceof Term[]) {
					pushTerms((Term[]) value);
				}
			}
			pushTerm(annterm.getSubterm());
			return;
		} else {
			throw new AssertionError("Unknown Term: " + term.toStringDirect());
		}
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

	private Term getSubArrayReplacementTerm(final Term originalTerm, final List<LocationBlock> projectList) {

		final IProgramVarOrConst originalTermPvoc = mEdgeInfo.getProgramVarOrConstForTerm(originalTerm);

		final IProgramVarOrConst subArrayPv = mSubArrayManager.getSubArray(originalTermPvoc, projectList);

		return getOrConstructSubArrayTermAndUpdateInOutVarMappings(originalTerm, originalTermPvoc, subArrayPv);
	}

	private Term getOrConstructSubArrayTermAndUpdateInOutVarMappings(final Term originalTerm,
			final IProgramVarOrConst originalTermPvoc, final IProgramVarOrConst subArrayPvoc) {
		Term result = mOriginalTermToSubArrayToReplacementTerm.get(originalTerm, subArrayPvoc);

		if (result == null) {
			assert originalTerm instanceof TermVariable : "TODO: if this occurs, extend below code to replace a "
					+ "constant term by a constant term";

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
		if (!mHeapArrays.contains(mEdgeInfo.getProgramVarOrConstForTerm(term))) {
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
	private List<Set<LocationBlock>> getLocationBlocksForArrayGroup(final ArrayGroup arrayGroup) {
//	private Set<LocationBlock> getLocationBlocksForArrayGroup(final ArrayGroup arrayGroup, final int dim) {
		final List<Set<LocationBlock>> result = new ArrayList<>();
		for (int dim = 0; dim < arrayGroup.getDimensionality(); dim++) {
			result.add(mArrayGroupToDimensionToLocationBlocks.projectToTrd(arrayGroup, dim));
		}
		//		return mArrayGroupToDimensionToLocationBlocks.projectToTrd(arrayGroup, dim);
		return result;
	}

	private ArrayGroup getArrayGroup(final Term term) {
		assert isPartitionedArray(term);
		return mArrayToArrayGroup.get(mEdgeInfo.getProgramVarOrConstForTerm(term));
	}

	private static <E> List<E>
			addToFront(final E locationBlockForIndex, final List<E> projectList) {
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
	private boolean fallsInto(final Term indexSubterm, final LocationBlock locationBlock) {
		// look up the StoreIndexInfo for the given term and mEdgeInfo
		final StoreIndexInfo sii = mEdgeToIndexToStoreIndexInfo.get(mEdgeInfo, indexSubterm);
		return locationBlock.contains(sii);
	}

//	/**
//	 *
//	 * @param indexSubterm
//	 * @param dim
//	 * @return
//	 */
//	private LocationBlock getLocationBlockForIndex(final Term indexSubterm, final int dim) {
////		return mSelectIndexTermToLocationBlock.get(indexSubterm);
//		final ArrayCellAccess aca = mSelectIndexTermToArrayCellAccess.get(indexSubterm);
//		assert aca.getDimensionsOfIndexTerm(indexSubterm).contains(dim);
//		return mArrayCellAccessToIntegerToLocationBlock.get(aca, dim);
//	}

	private void pushLocationBlockList(final List<LocationBlock> newList) {
		assert Objects.nonNull(newList);
		assert newList.stream().allMatch(Objects::nonNull);
		mProjectLists.push(Collections.unmodifiableList(newList));
	}

	private void popLocationBlockList() {
		mProjectLists.pop();
	}

	//	private Term getProjectedSimpleTerm(final Term termToProject, final List<LocationBlock> projectList) {
//	private IProgramVarOrConst getProjectedArray(final Term termToProject, final List<LocationBlock> projectList) {
//		final IProgramVarOrConst subArrayPv = mSubArrayManager.getSubArray(getProgramVar(termToProject),
//				projectList);
//		return subArrayPv;
////		final Term subArrayTerm;
////
////		return subArrayTerm;
//	}
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

			// TODO check order


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



	protected static class BeginScope implements Walker {


		private final List<LocationBlock> mLocBlockList;

		public BeginScope(final List<LocationBlock> locBlockList) {
			assert Objects.nonNull(locBlockList);
			assert locBlockList.stream().allMatch(Objects::nonNull);
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
		return mNewInVars;
	}

	public Map<IProgramVar, TermVariable> getNewOutVars() {
		return mNewOutVars;
	}
}

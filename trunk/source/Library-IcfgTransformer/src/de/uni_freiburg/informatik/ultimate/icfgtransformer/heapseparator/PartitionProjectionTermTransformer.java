package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
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


	/**
	 *
	 * @param subArrayManager
	 * @param termToLocationBlock
	 * @param transformula
	 * 			the TransFormula whose formula will be transformed by this TermTransformer
	 * @param arrayGroupToDimensionToLocationBlocks
	 */
	public PartitionProjectionTermTransformer(final ManagedScript mgdScript, final SubArrayManager subArrayManager,
//			final Map<Term, LocationBlock> termToLocationBlock,
			final NestedMap2<ArrayCellAccess, Integer, LocationBlock> arrayCellAccessToIntegerToLocationBlock,
//			final UnmodifiableTransFormula transformula,
			final EdgeInfo edgeInfo,
//			final Map<ArrayGroup, List<Set<LocationBlock>>> arrayGroupToDimensionToLocationBlocks,
			final HashRelation3<ArrayGroup, Integer, LocationBlock> arrayGroupToDimensionToLocationBlocks,
			final Map<IProgramVarOrConst, ArrayGroup> arrayToArrayGroup,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo) {
//			final Map<IProgramVar, TermVariable> oldInVars,
//			final Map<IProgramVar, TermVariable> oldOutVars) {
		mMgdScript = mgdScript;

		mSubArrayManager = subArrayManager;

		mArrayToArrayGroup = arrayToArrayGroup;

//		mTermToLocationBlock = termToLocationBlock;
		mArrayCellAccessToIntegerToLocationBlock = arrayCellAccessToIntegerToLocationBlock;

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
		if (term instanceof ConstantTerm
				|| term instanceof TermVariable) {
			if (isPartitionedArray(term)) {
				final Term subArrayTerm = getSubArrayReplacementTerm(term, projectList);

				assert false;
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

				// TODO: determine the array group, act accordingly...
				final ArrayGroup arrayGroup = getArrayGroup(at.getParameters()[0]);
				assert arrayGroup.equals(getArrayGroup(at.getParameters()[1]));

//				final Set<LocationBlock> locationBlocks = getLocationBlocksForArrayGroup(arrayGroup);
				final List<Set<LocationBlock>> locationBlocks = getLocationBlocksForArrayGroup(arrayGroup);

				final Sort arraySort = at.getParameters()[0].getSort();
				final MultiDimensionalSort mdSort = new MultiDimensionalSort(arraySort);

				// holds the combinations of L1i .. Lni we will build a conjunct for each
				final List<List<LocationBlock>> locationBlockTuples =
						CrossProducts.crossProductOfSets(locationBlocks);
//						CrossProducts.crossProductNTimes(mdSort.getDimension(), locationBlocks);


				enqueueWalker(new BuildConjunction(locationBlockTuples.size(), mMgdScript.getScript()));

				for (final List<LocationBlock> lbt : locationBlockTuples) {
					enqueueWalker(new EndScope());

					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));
					pushTerms(at.getParameters());

					enqueueWalker(new BeginScope(Collections.unmodifiableList(lbt)));
				}

			} else if (functionName.equals("select")) {
				final Term arraySubterm = at.getParameters()[0];
				final Term indexSubterm = at.getParameters()[1];

				enqueueWalker(new BuildApplicationTerm((ApplicationTerm) term));

				/*
				 * deal with index
				 */
				enqueueWalker(new EndScope());
				pushTerm(indexSubterm);
				enqueueWalker(new BeginScope(Collections.emptyList()));

				/*
				 * deal with array
				 */
				// build list Li L1 ... Ln
				enqueueWalker(new EndScope());
				pushTerm(arraySubterm);
				enqueueWalker(new BeginScope(addToFront(getLocationBlockForIndex(indexSubterm), projectList)));



			} else if (functionName.equals("store")) {

				final Term arraySubterm = at.getParameters()[0];
				final Term indexSubterm = at.getParameters()[1];
				final Term valueSubterm = at.getParameters()[2];

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
		// TODO: restrict to mem, or some parametrized array set?..

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
		newList.addAll(projectList.subList(1, projectList.size() - 1));
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

	private LocationBlock getLocationBlockForIndex(final Term indexSubterm) {
		return mTermToLocationBlock.get(indexSubterm);
	}

	private void pushLocationBlockList(final List<LocationBlock> newList) {
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

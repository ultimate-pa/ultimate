package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityAllowStores;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityLocUpdateInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.HeapSepProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * A Note on the notion of array writes in our setting:
 * <li>array writes are to an array group
 * <li>a write to an array group is given by a store term in the program whose
 * base array is an array of the group
 * <li>as the base arrays on both sides of an equation are always in the same
 * array group, the write is also to the array on the side of the equation other
 * from where the store term is (so the standard notion of array updates is
 * covered, but also for example assume statements in Boogie can constitute an
 * array write)
 *
 * We compute array groups per TransFormula and globally, where the per
 * transformula partitions form the constraints for the global partition. Aux
 * vars may also belong to an array group, because they are equated to some term
 * that belongs to a pvoc in their TransFormula.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 */
public class ComputeStoreInfosAndArrayGroups<LOC extends IcfgLocation> {

	/**
	 * Note that this map only contains arrays that are subject to heap separation.
	 * (in contrast to {@link #mEdgeToTermToArrayGroup})
	 */
	private final Map<IProgramVarOrConst, ArrayGroup> mArrayToArrayGroup = new HashMap<>();

	/**
	 * Note that this map also contains arrays that not subject to heap separation.
	 * (because that would require a post-processing)
	 * For checking that, see {@link #isArrayTermSubjectToSeparation(EdgeInfo, Term)}.
	 */
	private final NestedMap2<EdgeInfo, Term, ArrayGroup> mEdgeToTermToArrayGroup = new NestedMap2<>();

	/**
	 * We need this internal partitions when inserting the loc-array updates later.
	 */

	/**
	 * Note that index -1 is reserved for the "NoStoreInfo" object. This counter
	 * should always be non-negative, so no mId-clash occurs.
	 */
	private int mStoreInfoCounter;

	private final MemlocArrayManager mLocArrayManager;

	private final ManagedScript mMgdScript;

	private final NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> mEdgeToPositionToLocUpdateInfo
		= new NestedMap2<>();


	private final HashRelation<EdgeInfo, TermVariable> mEdgeToUnconstrainedVariables = new HashRelation<>();

	private final Map<HeapSepProgramConst, StoreInfo> mLocLitToStoreInfo = new HashMap<>();

	private boolean mFrozen;

	private final Map<Term, HeapSepProgramConst> mLocLitTermToLocLitPvoc = new HashMap<>();

	private final NestedMap2<EdgeInfo, SubtreePosition, StoreInfo> mEdgeToPositionToStoreInfo = new NestedMap2<>();

	private final List<IProgramVarOrConst> mHeapArrays;

	public ComputeStoreInfosAndArrayGroups(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays,
			final ManagedScript mgdScript) {

		mMgdScript = mgdScript;

		mLocArrayManager = new MemlocArrayManager(mgdScript, this);

		mHeapArrays = heapArrays;

		run(icfg, heapArrays);
	}

	private void run(final IIcfg<LOC> icfg, final List<IProgramVarOrConst> heapArrays) throws AssertionError {
		if (mFrozen) {
			throw new AssertionError();
		}

		final UnionFind<IProgramVarOrConst> globalArrayPartition = new UnionFind<>();
		// base line for the array groups: the heap arrays
		heapArrays.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);


		final Map<EdgeInfo, UnionFind<Term>> edgeToPerEdgeArrayPartition = computeEdgeLevelArrayGroups(icfg,
				globalArrayPartition);


		computeProgramLevelArrayGroups(heapArrays, globalArrayPartition, edgeToPerEdgeArrayPartition);

		/*
		 * Construct StoreInfos for later use. Store them in a map with keys in EdgeInfos x SubtreePositions.
		 */
		{
			final IcfgEdgeIterator it = new IcfgEdgeIterator(icfg);
			while (it.hasNext()) {
				final IcfgEdge edge = it.next();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

				final Map<Term, ArrayGroup> termToArrayGroupForCurrentEdge = mEdgeToTermToArrayGroup.get(edgeInfo);


				final BuildStoreInfos bsi = new BuildStoreInfos(edgeInfo, termToArrayGroupForCurrentEdge, mMgdScript,
						mLocArrayManager, mStoreInfoCounter, collectDefinitelyUnconstrainedVariables(edgeInfo));
				bsi.buildStoreInfos();
				for (final Entry<SubtreePosition, ArrayEqualityLocUpdateInfo> en :
						bsi.getLocArrayUpdateInfos().entrySet()) {
					mEdgeToPositionToLocUpdateInfo.put(edgeInfo, en.getKey(), en.getValue());
				}
				mLocLitToStoreInfo.putAll(bsi.getLocLitToStoreInfo());
				bsi.getLocLitToStoreInfo().keySet().forEach(hspc -> mLocLitTermToLocLitPvoc.put(hspc.getTerm(), hspc));
				bsi.getLocLitToStoreInfo().values()
					.forEach(si -> mEdgeToPositionToStoreInfo.put(edgeInfo, si.getPosition(), si));
				// (managing the store counter this way is a bit inelegant..)
				mStoreInfoCounter = bsi.getStoreInfoCounter();
			}
		}

		mFrozen = true;
	}

	private Set<IProgramVar> collectDefinitelyUnconstrainedVariables(final EdgeInfo edgeInfo) {
		final Set<IProgramVar> result = new HashSet<>();
		// we are only interested in invars of the given edge
		for (final IProgramVar invar : edgeInfo.getInVars().keySet()) {
			if (isDefinitelyUnconstrained(invar, edgeInfo)) {
				result.add(invar);
			}
		}
		return result;
	}


	private boolean isDefinitelyUnconstrained(final IProgramVar var, final EdgeInfo edgeInfo) {
		IcfgEdge currentEdge = edgeInfo.getEdge();
		while (true) {
			{
				final List<IcfgEdge> inEdges = currentEdge.getSource().getIncomingEdges();
//				if (inEdges.size() == 0) {
//					// no incoming edge, var was not constrained so far
//					return true;
//				}
				if (inEdges.size() != 1) {
					// more than two incoming edges --> give up
					return false;
				}
				currentEdge = inEdges.get(0);
			}

			if (currentEdge.getTransformula().getAssignedVars().contains(var)) {
				if (!currentEdge.getTransformula().getInVars().containsKey(var)
						&& SmtUtils.isTrueLiteral(currentEdge.getTransformula().getFormula())) {
					// we have a (simple) havoc
					return true;
				} else {
					// we have something that is not a simple havoc (perhaps an assignment) of var
					return false;
				}
			} else if (currentEdge.getTransformula().getOutVars().containsKey(var)) {
				// edge might put constraints on var
				return false;
			}
		}
	}

	/**
	 * Construct the program-level array groups.
	 */
	private void computeProgramLevelArrayGroups(final List<IProgramVarOrConst> heapArrays,
			final UnionFind<IProgramVarOrConst> globalArrayPartition,
			final Map<EdgeInfo, UnionFind<Term>> edgeToPerEdgeArrayPartition) throws AssertionError {
		if (mFrozen) {
			throw new AssertionError();
		}

		{
			final Set<ArrayGroup> arrayGroups = new HashSet<>();
			for (final Set<IProgramVarOrConst> block : globalArrayPartition.getAllEquivalenceClasses()) {
				arrayGroups.add(new ArrayGroup(block));
			}

			for (final ArrayGroup ag : arrayGroups) {
				if (DataStructureUtils.intersection(new HashSet<>(heapArrays), ag.getArrays()).isEmpty()) {
					/* we are only interested in writes to heap arrays */
					continue;
				}
				for (final IProgramVarOrConst a : ag.getArrays()) {
					mArrayToArrayGroup.put(a, ag);
				}
			}
		}

		/**
		 * Construct the map {@link #mEdgeToTermToArrayGroup}, which links each Term in an edge to a program-level
		 * array group. (or to null, if we do not track the term)
		 */
		{
			for (final Entry<EdgeInfo, UnionFind<Term>> en : edgeToPerEdgeArrayPartition.entrySet()) {
				final EdgeInfo edgeInfo = en.getKey();

				for (final Set<Term> block : en.getValue().getAllEquivalenceClasses()) {
					/*
					 * find a Term that has an IProgramVarOrConst according to the EdgeInfo (there
					 * must be one as the above analysis starts from IProgramVarOrConsts, right (the
					 * heap arrays)? (a formula relating a group of auxVars only within itself would
					 * be weird anyway) (if that assertion does not hold, see commented out code
					 * below for a possible fix)
					 */
					final Optional<IProgramVarOrConst> opt = block.stream()
							.map(t -> edgeInfo.getProgramVarOrConstForTerm(t)).filter(pvoc -> pvoc != null).findAny();
					if (!opt.isPresent()) {
						throw new AssertionError("see comment");
					}
					final ArrayGroup arrayGroup = mArrayToArrayGroup.get(opt.get());

					for (final Term t : block) {
						mEdgeToTermToArrayGroup.put(edgeInfo, t, arrayGroup);
					}
				}
			}
		}
	}
	/**
	 * Build edge-level array groups.
	 * I.e. Terms that are weakly/strongly equivalent in an edge are in an edge-level array group.
	 *
	 * Note that the notion of edge-level array group is already imprecise in some sense:
	 *  Example: edge formula: a = b \/ b = c
	 *      we would put a, b, c into one array group here, even though a and c are never related in the edge.
	 * (our algorithm here does not account for Boolean structure of the formula, it simply considers all =
	 *  predicates)
	 * However this overapproximation does not hurt soundness of our heap separation.
	 *
	 * EDIT : Note there are a few places where we currently assume TransFormulas to be conjunctive, so we may
	 *  consider computing more precise array groups once that is changed
	 *
	 */
	private Map<EdgeInfo, UnionFind<Term>> computeEdgeLevelArrayGroups(final IIcfg<LOC> icfg,
			final UnionFind<IProgramVarOrConst> globalArrayPartition) {
		if (mFrozen) {
			throw new AssertionError();
		}

		final Map<EdgeInfo, UnionFind<Term>> edgeToPerEdgeArrayPartition = new HashMap<>();
		{
			final IcfgEdgeIterator edgeIt = new IcfgEdgeIterator(icfg);
			while (edgeIt.hasNext()) {
				final IcfgEdge edge = edgeIt.next();
				final UnmodifiableTransFormula tf = edge.getTransformula();
				final EdgeInfo edgeInfo = new EdgeInfo(edge);

//				if (SmtUtils.containsFunctionApplication(tf.getFormula(), "or")
//						|| !SmtUtils.isNNF(tf.getFormula())) {
//					throw new UnsupportedOperationException("this computation can only handle conjunctive formulas at"
//							+ "the moment");
//				}

				/*
				 * construct the per-edge (or per-transformula, the difference does not matter here) array partition
				 */
				final UnionFind<Term> perTfArrayPartition = new UnionFind<>();

				/* before we do the array groups based on array equalities, we initialize the groups for all array terms
				 * in the formula (this makes sure that also arrays that occur in select terms only in the formula get
				 * an array group) */
				final Set<Term> baseArrayTerms =
						new SubTermFinder(SmtUtils::isBasicArrayTerm).findMatchingSubterms(tf.getFormula());
				baseArrayTerms.forEach(perTfArrayPartition::findAndConstructEquivalenceClassIfNeeded);

				// compute edge-specific array groups
				final List<ArrayEqualityAllowStores> aeass = ArrayEqualityAllowStores
						.extractArrayEqualityAllowStores(tf.getFormula());
				for (final ArrayEqualityAllowStores aeas : aeass) {
					final Term lhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getLhsArray());
					final Term rhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getRhsArray());

					perTfArrayPartition.union(lhsArrayTerm, rhsArrayTerm);
				}
				edgeToPerEdgeArrayPartition.put(edgeInfo, perTfArrayPartition);

				/*
				 * update the global array partition
				 */
				for (final Set<Term> eqc : perTfArrayPartition.getAllEquivalenceClasses()) {
					// pick some element that has a pvoc from the group of array terms

					final Set<IProgramVarOrConst> eqcPvocs = eqc.stream()
							.map(term -> TransFormulaUtils.getProgramVarOrConstForTerm(tf, term))
							.filter(pvoc -> pvoc != null).collect(Collectors.toSet());
					eqcPvocs.forEach(globalArrayPartition::findAndConstructEquivalenceClassIfNeeded);
					globalArrayPartition.union(eqcPvocs);
				}

				// compute constrained variables
				final Set<TermVariable> unconstrainedVars = computeUnconstrainedVariables(tf, aeass);
				mEdgeToUnconstrainedVariables.addAllPairs(edgeInfo, unconstrainedVars);
			}
		}
		return edgeToPerEdgeArrayPartition;
	}

	private Set<TermVariable> computeUnconstrainedVariables(final UnmodifiableTransFormula tf,
			final List<ArrayEqualityAllowStores> aeass) {
		if (mFrozen) {
			throw new AssertionError();
		}

		final Set<TermVariable> constrainedVars = new HashSet<>();
		final Set<TermVariable> unconstrainedVars =
				new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		boolean goOn = true;
		while (goOn) {
			goOn = false;
			for (final ArrayEqualityAllowStores aeas : aeass) {
				final Term lhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getLhsArray());
				final Term rhsArrayTerm = SmtUtils.getBasicArrayTerm(aeas.getRhsArray());

				final TermVariable lhsArrayTv =
						(lhsArrayTerm instanceof TermVariable) ? (TermVariable) lhsArrayTerm : null;
				final TermVariable rhsArrayTv =
								(rhsArrayTerm instanceof TermVariable) ? (TermVariable) rhsArrayTerm : null;

				// code for determining which variables are unconstrained ("havocced") in this edge
				final boolean lhsIsAStore = lhsArrayTerm != aeas.getLhsArray();
				final boolean rhsIsAStore = rhsArrayTerm != aeas.getRhsArray();
				final boolean neitherIsAStore = !lhsIsAStore && !rhsIsAStore;

				if (lhsArrayTv == null && rhsArrayTv != null) {
					// constants are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}
				if (rhsArrayTv == null && lhsArrayTv != null) {
					// constants are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}

				if (tf.getInVars().containsValue(lhsArrayTv)) {
					// in vars are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}
				if (tf.getInVars().containsValue(rhsArrayTv)) {
					// in vars are constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}

				if (neitherIsAStore && constrainedVars.contains(lhsArrayTv) && rhsArrayTv != null) {
					// strong equality, lhs is constrained --> rhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}

				if (neitherIsAStore && constrainedVars.contains(rhsArrayTv) && lhsArrayTv != null) {
					// strong equality, rhs is constrained --> lhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}

				if (lhsIsAStore && rhsArrayTv != null && unconstrainedVars.contains(rhsArrayTv)) {
					// lhs is a store --> rhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, rhsArrayTv);
				}
				if (rhsIsAStore && lhsArrayTv != null && unconstrainedVars.contains(lhsArrayTv)) {
					// rhs is a store --> lhs is constrained
					goOn |= markAsConstrainedIfNecessary(constrainedVars, unconstrainedVars, lhsArrayTv);
				}
			}
		}
		return unconstrainedVars;
	}

	/**
	 *
	 * @param constrainedVars
	 * @param unconstrainedVars
	 * @param tv
	 * @return true iff changes were made
	 */
	private boolean markAsConstrainedIfNecessary(final Set<TermVariable> constrainedVars,
			final Set<TermVariable> unconstrainedVars, final TermVariable tv) {
		if (mFrozen) {
			throw new AssertionError();
		}


		if (constrainedVars.contains(tv)) {
			assert !unconstrainedVars.contains(tv);
			return false;
		}
		unconstrainedVars.remove(tv);
		constrainedVars.add(tv);
		return true;
	}

	public MemlocArrayManager getLocArrayManager() {
		if (!mFrozen) {
			throw new AssertionError();
		}
		return mLocArrayManager;
	}

	public NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> getEdgeToPositionToLocUpdateInfo() {
		if (!mFrozen) {
			throw new AssertionError();
		}

		return mEdgeToPositionToLocUpdateInfo;
	}

	public Map<HeapSepProgramConst, StoreInfo> getLocLitToStoreInfo() {
		if (!mFrozen) {
			throw new AssertionError();
		}

		return Collections.unmodifiableMap(mLocLitToStoreInfo);
	}

	public Set<HeapSepProgramConst> getLocLiterals() {
		if (!mFrozen) {
			throw new AssertionError();
		}

		return Collections.unmodifiableSet(mLocLitToStoreInfo.keySet());
	}

	/**
	 * @return per edge, the variables that are unconstrained/havocced by that edge. (Assuming purely conjunctive edges
	 *  at the moment.)
	 */
	public HashRelation<EdgeInfo, TermVariable> getEdgeToUnconstrainedVariables() {
		if (!mFrozen) {
			throw new AssertionError();
		}

		return mEdgeToUnconstrainedVariables;
	}

	public StoreInfo getStoreInfoForLocLitTerm(final Term locLitTerm) {
		final HeapSepProgramConst hspc = getLocLitPvocForLocLitTerm(locLitTerm);
		if (mLocArrayManager.isInitLocPvoc(hspc)) {
			return mLocArrayManager.getNoStoreInfo(hspc);
		}
		assert hspc != null;
		return mLocLitToStoreInfo.get(hspc);
	}

	private HeapSepProgramConst getLocLitPvocForLocLitTerm(final Term locLitTerm) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		final HeapSepProgramConst initLocLitPvoc = mLocArrayManager.getInitLocLitPvocForLocLitTerm(locLitTerm);
		if (initLocLitPvoc != null) {
			return initLocLitPvoc;
		}
		return mLocLitTermToLocLitPvoc.get(locLitTerm);
	}

	public ArrayGroup getArrayGroupForTermInEdge(final EdgeInfo edgeInfo, final Term term) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		final ArrayGroup result = mEdgeToTermToArrayGroup.get(edgeInfo, term);
		if (result == null) {
			throw new AssertionError();
		}
		return result;
	}

	public StoreInfo getStoreInfoForStoreTermAtPositionInEdge(final EdgeInfo edgeInfo, final SubtreePosition pos) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		return mEdgeToPositionToStoreInfo.get(edgeInfo, pos);
	}

	public boolean isArrayTermSubjectToSeparation(final EdgeInfo edgeInfo, final Term term) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		final ArrayGroup ag = mEdgeToTermToArrayGroup.get(edgeInfo, term);
		return mArrayToArrayGroup.values().contains(ag);
	}

	public ArrayGroup getArrayGroupForArrayPvoc(final IProgramVarOrConst pvoc) {
		if (!mFrozen) {
			throw new AssertionError();
		}
		final ArrayGroup result = mArrayToArrayGroup.get(pvoc);
		assert result != null;
		return result;
	}

	/**
	 *  Note that this only returns arrays that are subject to heap separation.
	 * @return
	 */
	public Collection<ArrayGroup> getArrayGroups() {
		return Collections.unmodifiableCollection(mArrayToArrayGroup.values());
	}

	public List<StoreInfo> getStoreInfosForDimensionAndArrayGroup(final int dim, final ArrayGroup arrayGroup) {
		return mLocLitToStoreInfo.values().stream()
				.filter(si -> si.getDimension() == dim && si.getArrayGroup().equals(arrayGroup))
				.collect(Collectors.toList());
	}
}

class BuildStoreInfos extends NonRecursive {

	/**
	 * The edge the store infos belong to.
	 */
	private final EdgeInfo mEdge;
	private final Map<Term, ArrayGroup> mTermToArrayGroup;
	private final ManagedScript mMgdScript;

	private final Map<SubtreePosition, StoreInfo> mCollectedStoreInfos = new HashMap<>();
	private final MemlocArrayManager mLocArrayManager;
	private int mSiidCtr;
	private final Map<SubtreePosition, ArrayEqualityLocUpdateInfo> mPositionToLocArrayUpdateInfos = new HashMap<>();
	private final Map<HeapSepProgramConst, StoreInfo> mLocLitToStoreInfo = new HashMap<>();

	/**
	 * Program variables that are definitely unconstrained when {@link mEdge} is taken.
	 */
	private final Set<IProgramVar> mDefinitelyUnconstrainedVariables;

	BuildStoreInfos(final EdgeInfo edge, final Map<Term, ArrayGroup> termToArrayGroup, final ManagedScript mgdScript,
			final MemlocArrayManager locArrayManager, final int storeInfoCounter,
			final Set<IProgramVar> definitelyUnconstrainedVariables) {
		mEdge = edge;
		mTermToArrayGroup = termToArrayGroup;
		mMgdScript = mgdScript;
		mLocArrayManager = locArrayManager;
		mSiidCtr = storeInfoCounter;
		mDefinitelyUnconstrainedVariables = definitelyUnconstrainedVariables;
	}

	public Map<HeapSepProgramConst, StoreInfo> getLocLitToStoreInfo() {
		return mLocLitToStoreInfo;
	}

	public Map<SubtreePosition, ArrayEqualityLocUpdateInfo> getLocArrayUpdateInfos() {
		return mPositionToLocArrayUpdateInfos;
	}

	public void buildStoreInfos() {
		run(new BuildStoreInfoWalker(mEdge.getEdge().getTransformula().getFormula(), new SubtreePosition(),
				new ArrayIndex(), null, null));
	}

	public Map<SubtreePosition, ArrayEqualityLocUpdateInfo> getPositionToLocArrayUpdateInfos() {
		return mPositionToLocArrayUpdateInfos;
	}

	public int getStoreInfoCounter() {
		return mSiidCtr;
	}

	/**
	 * Note that this walks the Term "tree-style". For Terms with extensive sharing of sub-terms this may explode.
	 * (But we want to take the surrounding of each store Term into account, so we must do it this way.)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	private class BuildStoreInfoWalker extends TermWalker {

		private final ArrayIndex mEnclosingStoreIndices;
		private final SubtreePosition mSubTreePosition;
		/**
		 * position relative to the equality the current Term occurs in.
		 */
		private final SubtreePosition mRelativePosition;
		private final ArrayEqualityLocUpdateInfo mEnclosingEquality;

		public BuildStoreInfoWalker(final Term term, final SubtreePosition position,
				final ArrayIndex enclosingStoreIndices, final ArrayEqualityLocUpdateInfo enclosingEquality,
				final SubtreePosition relativePosition) {
			super(term);
			mEnclosingStoreIndices = enclosingStoreIndices;
			mSubTreePosition = position;
			mEnclosingEquality = enclosingEquality;
			mRelativePosition = relativePosition;
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// do nothing
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubterm(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final String funcName = term.getFunction().getName();
			switch (funcName) {
			case "store":
			{
				final ArrayGroup arrayGroup = mTermToArrayGroup.get(SmtUtils.getBasicArrayTerm(term));

				if (arrayGroup == null) {
					// array that is stored on is not subject to separation --> nothing to do here
					break;
				}

				final int siId = getNextStoreInfoId();
				final int siDim = mEnclosingStoreIndices.size() + 1;
				final HeapSepProgramConst locLit = constructLocationLiteral(mEdge, siId, siDim);
				final StoreInfo si = StoreInfo.buildStoreInfo(siId, mEdge, mSubTreePosition, term,
						arrayGroup, mEnclosingStoreIndices,
						locLit, mEnclosingEquality, mRelativePosition);
				mLocLitToStoreInfo.put(locLit, si);
				mCollectedStoreInfos.put(mSubTreePosition, si);
			}
			{
				// dive deeper into the array (no change to enclosing store indices)
				walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[0], mSubTreePosition.append(0),
						mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
				// dive deeper into the value
				final ArrayIndex newEnclosingStoreIndicesForValue =
						mEnclosingStoreIndices.append(term.getParameters()[1]);
				walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[2], mSubTreePosition.append(2),
						newEnclosingStoreIndicesForValue, mEnclosingEquality, mRelativePosition.append(2)));
			}
				break;
			case "=":
				if (term.getParameters()[0].getSort().isArraySort()) {
					assert mEnclosingEquality == null;
					final ArrayEqualityLocUpdateInfo newEnclosingEquality =
							new ArrayEqualityLocUpdateInfo(mMgdScript, term, mEdge, mLocArrayManager,
									mDefinitelyUnconstrainedVariables);
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[0], mSubTreePosition.append(0),
						 mEnclosingStoreIndices, newEnclosingEquality, new SubtreePosition().append(0)));
					walker.enqueueWalker(new BuildStoreInfoWalker(term.getParameters()[1], mSubTreePosition.append(1),
							mEnclosingStoreIndices, newEnclosingEquality, new SubtreePosition().append(1)));
					mPositionToLocArrayUpdateInfos.put(mSubTreePosition, newEnclosingEquality);
				}
				// do nothing if the equated terms are not of array type
				break;
			default:
				if ("Bool".equals(term.getSort().getName()) && SmtUtils.allParamsAreBool(term)) {
					assert mEnclosingEquality == null;
					// we have a Boolean connective --> dive deeper
					for (int i = 0; i < term.getParameters().length; i++) {
						final Term param = term.getParameters()[i];
						walker.enqueueWalker(new BuildStoreInfoWalker(param, mSubTreePosition.append(i),
								mEnclosingStoreIndices, null, null));
					}
				} else {
					// do nothing
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubTerm(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, mEnclosingEquality, mRelativePosition.append(0)));
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			assert mEnclosingEquality == null;
			walker.enqueueWalker(new BuildStoreInfoWalker(term.getSubformula(), mSubTreePosition.append(0),
					mEnclosingStoreIndices, null, null));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// do nothing
		}

	}

	private int getNextStoreInfoId() {
		mSiidCtr++;
		return mSiidCtr;
	}

	private HeapSepProgramConst constructLocationLiteral(final EdgeInfo edgeInfo, final int storeInfoId,
			final int storeDim) {

		assert storeInfoId > 0 : "use a long if this may overflow";

		mMgdScript.lock(this);

		final String locLitName = getLocationLitName(edgeInfo, storeInfoId);

		final Sort sort = mLocArrayManager.getMemlocSort(storeDim);

		mMgdScript.declareFun(this, locLitName, new Sort[0], sort);
		final ApplicationTerm locLitTerm = (ApplicationTerm) mMgdScript.term(this, locLitName);

		mMgdScript.unlock(this);

		final HeapSepProgramConst result = new HeapSepProgramConst(locLitTerm);
		return result;
	}

	private String getLocationLitName(final EdgeInfo location, final int storeInfoId) {
		return "lit_" + location.getSourceLocation() + "_" + storeInfoId;
	}
}
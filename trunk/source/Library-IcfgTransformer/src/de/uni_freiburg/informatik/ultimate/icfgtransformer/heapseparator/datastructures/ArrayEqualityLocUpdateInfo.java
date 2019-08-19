package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.LocArrayInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.MemlocArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.PositionAwareSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * For an array equality in a given {@link TransFormula}, this collects,
 * computes and provides information required for the program transformation
 * that inserts loc-arrays.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ArrayEqualityLocUpdateInfo {

	/**
	 * Find all enclosed StoreInfos by their position in the equality formula.
	 */
	private final Map<SubtreePosition, StoreInfo> mRelPositionToInnerStoreInfo = new HashMap<>();

	private boolean mFinalized;

	/**
	 * The {@link EdgeInfo} that this array equality occurs in.
	 */
	private final EdgeInfo mEdge;

	private final MemlocArrayManager mLocArrayManager;

	private Term mFormulaWithLocUpdates;

	private final Map<IProgramVar, TermVariable> mExtraInVars = new HashMap<>();

	private final Map<IProgramVar, TermVariable> mExtraOutVars = new HashMap<>();

	private final Collection<TermVariable> mExtraAuxVars = new HashSet<>();

	private final Collection<IProgramConst> mExtraConstants = new HashSet<>();

	private final ApplicationTerm mEquality;

	private final ManagedScript mMgdScript;

	private final Set<IProgramVar> mDefinitelyUnconstrainedVariables;

	/**
	 *
	 * @param edge
	 * @param locArrayManager
	 */
	public ArrayEqualityLocUpdateInfo(final ManagedScript mgdScript, final ApplicationTerm equality,
			final EdgeInfo edge, final MemlocArrayManager locArrayManager,
			final Set<IProgramVar> definitelyUnconstrainedVariables) {
		mMgdScript = mgdScript;
		mEdge = edge;
		mLocArrayManager = locArrayManager;
		mEquality = equality;
		mDefinitelyUnconstrainedVariables = definitelyUnconstrainedVariables;
	}

	public void addEnclosedStoreInfo(final StoreInfo storeInfo, final SubtreePosition posRelativeToEquality) {
		if (mFinalized) {
			throw new AssertionError();
		}
		mRelPositionToInnerStoreInfo.put(posRelativeToEquality, storeInfo);
	}

	private void computeResult() {
		assert !mFinalized;

		final Set<Term> baseArrayTermsRaw = extractBaseArrayTerms(mEquality);
		final Set<Term> baseArrayTerms = baseArrayTermsRaw.stream()
				.filter(bat -> mLocArrayManager.isArrayTermSubjectToSeparation(mEdge, bat))
				.collect(Collectors.toSet());

		final int dimensionality = computeDimensionality();

		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(mEquality);

		// compute the conjuncts for each dimension, dimensions are 1-based (e.g. a[i]
		// accesses first dimension)
		for (int dim = 1; dim <= dimensionality; dim++) {
			// used to make lambda expression work, which needs a final variable, nothing
			// else..
			final int currentDim = dim;

			// substitute arrays with their loc-arrays for the current dimension
			// final Term equalityWithLocArrays;
			final Map<Term, Term> termSubstitutionMapping = new HashMap<>();
			{
				for (final Term bat : baseArrayTerms) {

					// obtain the loc array for the given base array term (typically a term-variable
					// like a, or mem..)
					final LocArrayInfo locArray = mLocArrayManager.getOrConstructLocArray(mEdge, bat, currentDim);

					// update the substitution mapping (e.g. with a pair (a, a-loc-dim))
					termSubstitutionMapping.put(bat, locArray.getTerm());

					/*
					 * update invars, outvars, etc. E.g. if a was an invar and we introduced
					 * a-loc-1, then a-loc-1 must also be an invar.
					 */
					if (mEdge.getInVars().containsValue(bat)) {
						if (isDefinitelyUnconstrained(bat) && mEdge.getOutVar(bat) == mEdge.getInVar(bat)) {
							/* omit this invar --> effectively makes an assignment out of an assume on the loc array
							 *  (this is sound because the base array is in a freshly-havocced state, thus it would not
							 *   make a difference to havoc the base array, too)
							 *  TODO: If this cannot be done for assume statements that relate maps, we should crash,
							 *   as we do not support that syntax. */
						} else {
							mExtraInVars.put((IProgramVar) locArray.getPvoc(), (TermVariable) locArray.getTerm());
						}
					}
					if (mEdge.getOutVars().containsValue(bat)) {
						mExtraOutVars.put((IProgramVar) locArray.getPvoc(), (TermVariable) locArray.getTerm());
					}
					if (mEdge.getAuxVars().contains(bat)) {
						mExtraAuxVars.add((TermVariable) locArray.getTerm());
					}
					if (mEdge.getNonTheoryConsts().stream().map(ntc -> ntc.getTerm()).anyMatch(t -> t.equals(bat))) {
						mExtraConstants.add((IProgramConst) locArray.getPvoc());
					}
				}
			}

			/*
			 * substitute store-values with their corresponding loc literals for the current
			 * dimension e.g. phi(a) becomes phi(a-loc-currentDim)
			 */
			final Term equalityWithLocArraysAndLocLiterals;
			{
				final List<StoreInfo> storeInfosForCurrentDimension = mRelPositionToInnerStoreInfo.values().stream()
						.filter(si -> (si.getDimension() == currentDim)).collect(Collectors.toList());
				final Map<SubtreePosition, Term> positionSubstitutionMapping = new HashMap<>();
				for (final StoreInfo si : storeInfosForCurrentDimension) {
					positionSubstitutionMapping.put(si.getPositionOfStoredValueRelativeToEquality(),
							si.getLocLiteral().getTerm());

					mExtraConstants.add(si.getLocLiteral());
				}
				equalityWithLocArraysAndLocLiterals =
						new PositionAwareSubstitution(mMgdScript, positionSubstitutionMapping, termSubstitutionMapping)
								.transform(mEquality);
			}
			conjuncts.add(equalityWithLocArraysAndLocLiterals);
		}

		mFormulaWithLocUpdates = SmtUtils.and(mMgdScript.getScript(), conjuncts);

		mFinalized = true;
	}

	private boolean isDefinitelyUnconstrained(final Term baseArrayTerm) {
		if (baseArrayTerm instanceof TermVariable) {
			final IProgramVar invar = mEdge.getInVar(baseArrayTerm);
			if (mDefinitelyUnconstrainedVariables.contains(invar)) {
				return true;
			}
		}
		return false;
	}

	public int computeDimensionality() {
		final int dimensionality = new MultiDimensionalSort(mEquality.getParameters()[0].getSort()).getDimension();
		assert mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0)) == null
				|| dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0)).getArrayGroup()
						.getDimensionality();
		assert mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1)) == null
				|| dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1)).getArrayGroup()
						.getDimensionality();
		return dimensionality;
	}

	private static Set<Term> extractBaseArrayTerms(final ApplicationTerm equality) {
		final Predicate<Term> pred = subterm -> SmtUtils.isBasicArrayTerm(subterm);
		return new SubTermFinder(pred).findMatchingSubterms(equality);
	}

	public Term getFormulaWithLocUpdates() {
		if (!mFinalized) {
			computeResult();
		}
		return mFormulaWithLocUpdates;
	}

	public Map<? extends IProgramVar, ? extends TermVariable> getExtraInVars() {
		if (!mFinalized) {
			computeResult();
		}
		return mExtraInVars;
	}

	public Map<? extends IProgramVar, ? extends TermVariable> getExtraOutVars() {
		if (!mFinalized) {
			computeResult();
		}
		return mExtraOutVars;
	}

	public Collection<? extends TermVariable> getExtraAuxVars() {
		if (!mFinalized) {
			computeResult();
		}
		return mExtraAuxVars;
	}

	public Collection<? extends IProgramConst> getExtraConstants() {
		if (!mFinalized) {
			computeResult();
		}
		return mExtraConstants;
	}

	@Override
	public String toString() {
		return "ArrayEqualityLocUpdateInfo [mEquality=" + mEquality + "]";
	}
}

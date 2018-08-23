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
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * For an array equality in a given {@link TransFormula}, this collects, computes and provides information required for
 * the program transformation that inserts loc-arrays.
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

	/**
	 *
	 * @param edge
	 * @param locArrayManager
	 */
	public ArrayEqualityLocUpdateInfo(final ManagedScript mgdScript, final ApplicationTerm equality, final EdgeInfo edge,
			final MemlocArrayManager locArrayManager) {
		mMgdScript = mgdScript;
		mEdge = edge;
		mLocArrayManager = locArrayManager;
		mEquality = equality;
	}

	public void addEnclosedStoreInfo(final StoreInfo storeInfo, final SubtreePosition posRelativeToEquality) {
		if (mFinalized) {
			throw new AssertionError();
		}
		mRelPositionToInnerStoreInfo.put(posRelativeToEquality, storeInfo);
	}

	private void computeResult() {
		assert !mFinalized;

		final Set<Term> baseArrayTerms = extractBaseArrayTerms(mEquality);

//		final StoreInfo lhsStoreInfo = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0));
//		final StoreInfo rhsStoreInfo = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1));

		final int dimensionality = computeDimensionality();

		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(mEquality);


		// compute the conjuncts for each dimension
		for (int dim = 0; dim < dimensionality; dim++) {
			// used to make lambda expression work, which needs a final variable, nothing else..
			final int currentDim = dim;

			// substitute arrays with their loc-arrays for the current dimension
			final Term equalityWithLocArrays;
			{
				final Map<Term, Term> subs = new HashMap<>();
				for (final Term bat : baseArrayTerms) {
					// obtain the loc array for the given base array term (typically a term-variable like a, or mem..)
					final LocArrayInfo locArray =
							mLocArrayManager.getOrConstructLocArray(mEdge, bat, currentDim);

					// update the substitution mapping (e.g. with a pair (a, a-loc-dim))
					subs.put(bat, locArray.getTerm());

					/* update invars, outvars, etc. E.g. if a was an invar and we introduced a-loc-1, then a-loc-1
					 *  must also be an invar. */
					if (mEdge.getInVars().containsValue(bat)) {
						mExtraInVars.put((IProgramVar) locArray.getPvoc(), (TermVariable) locArray.getTerm());
					}
					if (mEdge.getOutVars().containsValue(bat)) {
						mExtraOutVars.put((IProgramVar) locArray.getPvoc(), (TermVariable) locArray.getTerm());
					}
					if (mEdge.getAuxVars().contains(bat)) {
						mExtraAuxVars.add((TermVariable) locArray.getTerm());
					}
					if (mEdge.getNonTheoryConsts().stream()
							.map(ntc -> ntc.getTerm())
							.anyMatch(t -> t.equals(bat))) {
						mExtraConstants.add((IProgramConst) locArray.getPvoc());
					}
				}
				equalityWithLocArrays = new Substitution(mMgdScript, subs).transform(mEquality);
			}

			/* substitute store-values with their corresponding loc literals for the current dimension
			 * e.g. phi(a) becomes phi(a-loc-currentDim) */
			final Term equalityWithLocArraysAndLocLiterals;
			{
				final List<StoreInfo> storeInfosForCurrentDimension = mRelPositionToInnerStoreInfo.values().stream()
						.filter(si -> (si.getDimension() == currentDim)).collect(Collectors.toList());
				final Map<SubtreePosition, Term> substitutionMapping = new HashMap<>();
				for (final StoreInfo si : storeInfosForCurrentDimension) {
					substitutionMapping.put(si.getPositionOfStoredValueRelativeToEquality(),
							si.getLocLiteral().getTerm());

				}
				equalityWithLocArraysAndLocLiterals =
					new PositionAwareSubstitution(mMgdScript, substitutionMapping).transform(equalityWithLocArrays);
			}
			conjuncts.add(equalityWithLocArraysAndLocLiterals);
		}

		mFormulaWithLocUpdates = SmtUtils.and(mMgdScript.getScript(), conjuncts);

		mFinalized = true;
	}

	public int computeDimensionality() {
//		final int dimensionality = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0))
//				.getArrayGroup().getDimensionality();
//		assert dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1))
//				.getArrayGroup().getDimensionality();
//		assert dimensionality == new MultiDimensionalSort(mEquality.getParameters()[0].getSort()).getDimension();
		final int dimensionality = new MultiDimensionalSort(mEquality.getParameters()[0].getSort()).getDimension();
		assert mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0)) == null
				|| dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0))
						.getArrayGroup().getDimensionality();
		assert mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1)) == null
				|| dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1))
						.getArrayGroup().getDimensionality();
		return dimensionality;
	}

	private static Set<Term> extractBaseArrayTerms(final ApplicationTerm equality) {
		final Predicate<Term> pred =
				subterm -> (subterm.getSort().isArraySort() && !SmtUtils.isFunctionApplication(subterm, "store"));
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

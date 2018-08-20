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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.MemlocArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers.PositionAwareSubstitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

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

	private final Map<? extends IProgramVar, ? extends TermVariable> mExtraInVars = new HashMap<>();

	private final Map<? extends IProgramVar, ? extends TermVariable> mExtraOutVars = new HashMap<>();

	private final Collection<? extends TermVariable> mExtraAuxVars = new HashSet<>();

	private final Collection<? extends IProgramConst> mExtraConstants = new HashSet<>();

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

		final StoreInfo lhsStoreInfo = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0));
		final StoreInfo rhsStoreInfo = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1));

		final int dimensionality = mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(0))
				.getArrayGroup().getDimensionality();
		assert dimensionality == mRelPositionToInnerStoreInfo.get(new SubtreePosition().append(1))
				.getArrayGroup().getDimensionality();
		assert dimensionality == new MultiDimensionalSort(mEquality.getParameters()[0].getSort()).getDimension();

		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(mEquality);


		// compute the conjuncts for each dimension
		for (final int dim = 0; dim < dimensionality; dim++) {
			// used to make lambda expression work, which needs a final variable, nothing else..
			final int currentDim = dim;

			// substitute arrays with their loc-arrays for the current dimension
			final Term equalityWithLocArrays;
			{
				final Map<Term, Term> subs = new HashMap<>();
				for (final Term bat : baseArrayTerms) {
					final Term locArray = mLocArrayManager.getOrConstructLocArray(mEdge, bat, currentDim);
					subs.put(bat, locArray);

					if (mEdge.getInVars().containsValue(bat)) {
						mExtra
					}
				}
				equalityWithLocArrays = new Substitution(mMgdScript, subs).transform(mEquality);
			}

			// substitute store-values with their corresponding loc literals for the current dimension
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

	private Set<Term> extractBaseArrayTerms(final ApplicationTerm equality) {
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

}

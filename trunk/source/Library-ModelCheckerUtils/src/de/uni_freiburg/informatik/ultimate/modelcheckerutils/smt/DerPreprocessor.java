/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.NestedArrayStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Preprocessor for array partial quantifier elimination that handles the
 * following DER-like cases.
 *
 * Let's assume that arr is the variable that we want to eliminate.
 *
 * The term (= arr (store b k v)) is replaced by (= (select arr k') v') if
 * arr==b and replaced by (= arr (store b k' v') if arr!=b. The term (= arr
 * (select b k) is replaced by (= arr (select b k'). In all cases k'==k (resp.
 * v'==v) if arr is not a subterm of arr. In case arr is a subterm of k, we k'
 * is a fresh variable and we set mIntroducedDerPossibility to true.
 *
 * The result should be used as follows. If mIntroducedDerPossibility == false
 * the result can be used directly. The variable might still be there but the
 * annoying DER term is gone (sef-update case only)> If
 * mIntroducedDerPossibility == false we introduced a equality (resp.
 * disequality for universal quantification) that allow us the eliminate arr via
 * the DER quantifier elimination technique. (Apply DER for the variable arr
 * only!). However, we also introduced auxiliary variables that have to be
 * quantified and we introduced additional conjuncts (resp. disjuncts for
 * universal quantification) of the form k'=k that have to be merged to the
 * operand term of the quantifier elimination.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class DerPreprocessor extends TermTransformer {

	private static final String AUX_VAR_PREFIX = "DerPreprocessor";

	private enum DerCase {
		SELF_UPDATE, EQ_STORE, EQ_SELECT
	};

	private final List<TermVariable> mNewAuxVars = new ArrayList<>();
	private final Term mResult;
	private final boolean mIntroducedDerPossibility;

	public DerPreprocessor(final IUltimateServiceProvider services, final ManagedScript mgdScript, final int quantifier,
			final TermVariable eliminatee, final Term input, final List<BinaryEqualityRelation> bers) {
		final HashRelation<DerCase, BinaryEqualityRelation> classification = classify(bers, eliminatee);
		boolean existsEqualityThatIsNotOnTopLevel = false;
		BinaryEqualityRelation someTopLevelEquality = null;
		DerCase derCase = null;
		final Set<Term> topLevelDualJuncts = Arrays.stream(QuantifierUtils.getXjunctsInner(quantifier, input))
				.collect(Collectors.toSet());
		for (final BinaryEqualityRelation ber : classification.getImage(DerCase.EQ_SELECT)) {
			if (topLevelDualJuncts.contains(ber.toTerm(mgdScript.getScript()))) {
				if (someTopLevelEquality == null) {
					someTopLevelEquality = ber;
					derCase = DerCase.EQ_SELECT;
				}
			} else {
				existsEqualityThatIsNotOnTopLevel = true;
			}
		}
		for (final BinaryEqualityRelation ber : classification.getImage(DerCase.EQ_STORE)) {
			final Term toterm = ber.toTerm(mgdScript.getScript());
			if (topLevelDualJuncts.contains(toterm)) {
				if (someTopLevelEquality == null) {
					someTopLevelEquality = ber;
					derCase = DerCase.EQ_STORE;
				}
			} else {
				existsEqualityThatIsNotOnTopLevel = true;
			}
		}

		final List<Term> mAuxVarDefinitions = new ArrayList<>();
		final ConstructionCache<Term, TermVariable> auxVarCc;
		{
			final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {
				@Override
				public TermVariable constructValue(final Term term) {
					final TermVariable auxVar = mgdScript.constructFreshTermVariable(AUX_VAR_PREFIX, term.getSort());
					Term definition = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier, auxVar, term);

					// TODO: let Prenex transformer deal with non-NNF terms and
					// remove the following line
					definition = new NnfTransformer(mgdScript, services, QuantifierHandling.CRASH)
							.transform(definition);

					mAuxVarDefinitions.add(definition);
					mNewAuxVars.add(auxVar);
					return auxVar;
				}
			};
			auxVarCc = new ConstructionCache<>(valueConstruction);
		}

		final Map<Term, Term> substitutionMapping;
		if (someTopLevelEquality != null) {
			final Term derEnabler = constructDerEnabler(someTopLevelEquality, mgdScript, eliminatee, quantifier,
					derCase, auxVarCc);
			substitutionMapping = Collections.singletonMap(someTopLevelEquality.toTerm(mgdScript.getScript()),
					derEnabler);
			mIntroducedDerPossibility = true;
		} else {
			if (existsEqualityThatIsNotOnTopLevel) {
				throw new AssertionError("Some non-self update cases but no top-level DER relation");
			}
			substitutionMapping = handleAllSelfUpdates(classification.getImage(DerCase.SELF_UPDATE), mgdScript,
					eliminatee, quantifier, auxVarCc);
			mIntroducedDerPossibility = false;
		}
		final Term inputReplacement = new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping)
				.transform(input);
		final Term allAuxVarDefs = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier,
				mAuxVarDefinitions);
		mResult = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, inputReplacement,
				allAuxVarDefs);
	}

	private static Map<Term, Term> handleAllSelfUpdates(final Set<BinaryEqualityRelation> selfupdates,
			final ManagedScript mgdScript, final TermVariable eliminatee, final int quantifier,
			final ConstructionCache<Term, TermVariable> auxVarCc) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final BinaryEqualityRelation selfUpdate : selfupdates) {
			final Term otherSide = getOtherSide(selfUpdate, eliminatee);
			final NestedArrayStore nas = NestedArrayStore.convert(otherSide);
			final Term selfUpdateReplacement = constructReplacementForStoreCase(nas, mgdScript, eliminatee, quantifier,
					auxVarCc);
			substitutionMapping.put(selfUpdate.toTerm(mgdScript.getScript()), selfUpdateReplacement);
		}
		return substitutionMapping;
	}

	private static Term constructDerEnabler(final BinaryEqualityRelation someTopLevelEquality,
			final ManagedScript mgdScript, final TermVariable eliminatee, final int quantifier, final DerCase derCase,
			final ConstructionCache<Term, TermVariable> auxVarCc) {
		final Term otherSide = getOtherSide(someTopLevelEquality, eliminatee);
		Term result;
		switch (derCase) {
		case EQ_SELECT:
			final ArraySelect as = ArraySelect.convert(otherSide);
			result = constructReplacementForSelectCase(as.getArray(), as.getIndex(), mgdScript, eliminatee, quantifier,
					auxVarCc);
			break;
		case EQ_STORE:
			final NestedArrayStore nas = NestedArrayStore.convert(otherSide);
			result = constructReplacementForStoreCase(nas, mgdScript, eliminatee, quantifier, auxVarCc);
			break;
		case SELF_UPDATE:
		default:
			throw new AssertionError("only select case and store case possible");
		}
		return result;
	}

	private static HashRelation<DerCase, BinaryEqualityRelation> classify(final List<BinaryEqualityRelation> bers,
			final TermVariable eliminatee) {
		final HashRelation<DerCase, BinaryEqualityRelation> result = new HashRelation<>();
		for (final BinaryEqualityRelation ber : bers) {
			final Term otherSide = getOtherSide(ber, eliminatee);
			final DerCase derCase = classify(otherSide, eliminatee);
			result.addPair(derCase, ber);
		}
		return result;
	}

	private static Term getOtherSide(final BinaryEqualityRelation ber, final TermVariable oneSide) {
		Term otherSide;
		if (ber.getLhs().equals(oneSide)) {
			otherSide = ber.getRhs();
		} else if (ber.getRhs().equals(oneSide)) {
			otherSide = ber.getLhs();
		} else {
			throw new AssertionError("has to be on one side");
		}
		return otherSide;
	}

	private static DerCase classify(final Term otherSide, final TermVariable eliminatee) {
		if (!Arrays.asList(otherSide.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("This case should habe been handled by DER");
		}
		final MultiDimensionalNestedStore mdns = MultiDimensionalNestedStore.convert(otherSide);
		if (mdns != null) {
			if (mdns.getArray() == eliminatee) {
				return DerCase.SELF_UPDATE;
			} else {
				if (Arrays.asList(mdns.getArray().getFreeVars()).contains(eliminatee)) {
					throw new AssertionError("Complicated and unsupported kind of self-update: " + mdns.getArray());
				} else {
					return DerCase.EQ_STORE;
				}
			}
		}
		final MultiDimensionalSelect arraySelect = MultiDimensionalSelect.convert(otherSide);
		if (arraySelect != null) {
			return DerCase.EQ_SELECT;
		}
		throw new UnsupportedOperationException("DerPreprocessor supports only store and select, but not " + otherSide);
	}

	public List<TermVariable> getNewAuxVars() {
		return mNewAuxVars;
	}



	public Term getResult() {
		return mResult;
	}

	public boolean introducedDerPossibility() {
		return mIntroducedDerPossibility;
	}

	private static Term constructReplacementForStoreCase(final NestedArrayStore nas, final ManagedScript mgdScript,
			final TermVariable eliminatee, final int quantifier, final ConstructionCache<Term, TermVariable> auxVarCc) {
		final List<Term> newIndices = constructReplacementsIfNeeded(nas.getIndices(), auxVarCc, eliminatee);
		final List<Term> newValues = constructReplacementsIfNeeded(nas.getValues(), auxVarCc, eliminatee);
		final Term result;
		if (nas.getArray().equals(eliminatee)) {
			// is (possibly nested) self-update
			final LinkedList<Term> indices = new LinkedList<>(newIndices);
			final LinkedList<Term> values = new LinkedList<>(newValues);
			final Term[] resultDualFiniteJuncts = new Term[indices.size()];
			for (int i = 0; i < newIndices.size(); i++) {
				final Term innermostIndex = indices.removeFirst();
				final Term innermostValue = values.removeFirst();
				resultDualFiniteJuncts[i] = constructDisjointIndexImplication(innermostIndex, indices, innermostValue,
						eliminatee, mgdScript.getScript(), quantifier);
			}
			assert indices.isEmpty();
			values.isEmpty();
			result = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier,
					resultDualFiniteJuncts);
		} else {
			if (Arrays.asList(nas.getArray().getFreeVars()).contains(eliminatee)) {
				throw new UnsupportedOperationException(
						"We have to descend beyond store chains. Introduce auxiliary variables only for arrays of lower dimension to avoid non-termination.");
			}
			result = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier,
					new NestedArrayStore(nas.getArray(), newIndices, newValues).toTerm(mgdScript.getScript()),
					eliminatee);
		}
		return result;
	}

	private static List<Term> constructReplacementsIfNeeded(final List<Term> indices,
			final ConstructionCache<Term, TermVariable> auxVarCc, final TermVariable eliminatee) {
		final List<Term> newIndices = new ArrayList<>();
		boolean replacementMade = false;
		for (final Term index : indices) {
			Term newIndex;
			if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
				newIndex = auxVarCc.getOrConstruct(index);
				replacementMade = true;
			} else {
				newIndex = index;
			}
			newIndices.add(newIndex);
		}
		if (replacementMade) {
			return newIndices;
		} else {
			return indices;
		}
	}

	private static Term constructReplacementForSelectCase(final Term array, final Term index,
			final ManagedScript mgdScript, final TermVariable eliminatee, final int quantifier,
			final ConstructionCache<Term, TermVariable> auxVarCc) {
		final Term newIndex;
		if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
			newIndex = auxVarCc.getOrConstruct(index);
		} else {
			newIndex = index;
		}
		final Term store = SmtUtils.select(mgdScript.getScript(), array, newIndex);
		final Term result = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier, eliminatee, store);

		// TODO: let Prenex transformer deal with non-NNF terms and remove the
		// following line
		// result = new NnfTransformer(mMgdScript, mServices,
		// QuantifierHandling.CRASH).transform(result);
		return result;
	}

	/**
	 * Let oi_1,...,oi_n be the terms in otherIndices, construct the formula ((idx
	 * != oi_1) /\ ... /\ (idx != oi_n)) ==> ((select arr idx) = value) for
	 * existential quantification and the formula (not ((idx == oi_1) \/ ... \/ (idx
	 * == oi_n))) /\ ((select arr idx) != value) for universal quantification.
	 *
	 * @param quantifier
	 * @param script
	 */
	private static Term constructDisjointIndexImplication(final Term idx, final List<Term> otherIndices,
			final Term value, final Term arr, final Script script, final int quantifier) {
		final Term select = SmtUtils.select(script, arr, idx);
		final Term selectEqualsValue = QuantifierUtils.applyDerOperator(script, quantifier, select, value);
		final List<Term> dualFiniteJuncts = otherIndices.stream()
				.map(x -> QuantifierUtils.applyAntiDerOperator(script, quantifier, idx, x))
				.collect(Collectors.toList());
		final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(script, quantifier, dualFiniteJuncts);
		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier,
				SmtUtils.not(script, dualFiniteJunction), selectEqualsValue);
		return result;
	}

}

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
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.NestedArrayStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

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

	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final TermVariable mEliminatee;
	private final int mQuantifier;
	private final List<TermVariable> mNewAuxVars = new ArrayList<>();
	private final ConstructionCache<Term, TermVariable> mAuxVarCc;
	private final List<Term> mAuxVarDefinitions = new ArrayList<>();
	private boolean mIntroducedDerPossibility = false;

	public DerPreprocessor(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final TermVariable eliminatee, final int quantifier) {
		mServices = services;
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mEliminatee = eliminatee;
		mQuantifier = quantifier;
		final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

			@Override
			public TermVariable constructValue(final Term term) {
				final TermVariable auxVar = mMgdScript.constructFreshTermVariable(AUX_VAR_PREFIX, term.getSort());
				Term definition = QuantifierUtils.applyDerOperator(mScript, mQuantifier, auxVar, term);

				// TODO: let Prenex transformer deal with non-NNF terms and
				// remove the following line
				definition = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(definition);

				mAuxVarDefinitions.add(definition);
				mNewAuxVars.add(auxVar);
				return auxVar;
			}
		};
		mAuxVarCc = new ConstructionCache<>(valueConstruction);
	}

	public List<TermVariable> getNewAuxVars() {
		return mNewAuxVars;
	}

	public List<Term> getAuxVarDefinitions() {
		return mAuxVarDefinitions;
	}

	public boolean introducedDerPossibility() {
		return mIntroducedDerPossibility;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String fun = appTerm.getFunction().getName();
			if (fun.equals("=")) {
				if (appTerm.getParameters().length != 2) {
					throw new UnsupportedOperationException("only binary equality supported");
				}
				final Term lhs = appTerm.getParameters()[0];
				final Term rhs = appTerm.getParameters()[1];
				if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						final Term result = constructReplacement(lhs, rhs);
						setResult(result);
						return;
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						return;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				}
			} else if (fun.equals("distinct")) {
				// TODO: do not allow distinct after our convention does not
				// allow it nay more
				// throw new AssertionError("distinct should have been
				// removed");
				if (appTerm.getParameters().length != 2) {
					throw new UnsupportedOperationException("only binary equality supported");
				}
				final Term lhs = appTerm.getParameters()[0];
				final Term rhs = appTerm.getParameters()[1];
				if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						return;
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						final Term result = constructReplacement(lhs, rhs);
						setResult(result);
						return;
					} else {
						throw new AssertionError("unknown quantifier");
					}
				}
			} else if (fun.equals("not")) {
				assert appTerm.getParameters().length == 1;
				final Term argNot = appTerm.getParameters()[0];
				if (argNot instanceof ApplicationTerm) {
					final ApplicationTerm appTermNot = (ApplicationTerm) argNot;
					if (NonCoreBooleanSubTermTransformer.isCoreBoolean(appTermNot)) {
						throw new AssertionError("should have been transformed to NNF");
					}
					final String funNot = appTermNot.getFunction().getName();
					if (funNot.equals("=")) {
						if (appTermNot.getParameters().length != 2) {
							throw new UnsupportedOperationException("only binary equality supported");
						}
						final Term lhs = appTermNot.getParameters()[0];
						final Term rhs = appTermNot.getParameters()[1];
						if (lhs.equals(mEliminatee) || rhs.equals(mEliminatee)) {
							if (mQuantifier == QuantifiedFormula.EXISTS) {
								return;
							} else if (mQuantifier == QuantifiedFormula.FORALL) {
								final Term result = constructReplacement(lhs, rhs);
								setResult(result);
								return;
							} else {
								throw new AssertionError("unknown quantifier");
							}
						}
					}
				}
			}
		}

		super.convert(term);
	}

	private Term constructReplacement(final Term lhs, final Term rhs) {
		if (lhs.equals(mEliminatee)) {
			return constructReplacement(rhs);
		} else if (rhs.equals(mEliminatee)) {
			return constructReplacement(lhs);
		} else {
			throw new AssertionError("has to be on one side");
		}
	}

	private Term constructReplacement(final Term otherSide) {
		if (!Arrays.asList(otherSide.getFreeVars()).contains(mEliminatee)) {
			throw new AssertionError("This case should habe been handled by DER");
		}
		final NestedArrayStore nas = NestedArrayStore.convert(otherSide);
		if (nas != null) {
			return constructReplacementForStoreCase(nas);
		}
		final ArraySelect arraySelect = ArraySelect.convert(otherSide);
		if (arraySelect != null) {
			return constructReplacementForSelectCase(arraySelect.getArray(), arraySelect.getIndex());
		}
		throw new UnsupportedOperationException("DerPreprocessor supports only store and select, but not " + otherSide);
	}

	private Term constructReplacementForStoreCase(final NestedArrayStore nas) {
		final List<Term> newIndices = constructReplacementsIfNeeded(nas.getIndices());
		final List<Term> newValues = constructReplacementsIfNeeded(nas.getValues());
		if (newIndices != nas.getIndices() || newValues != nas.getValues()) {
			mIntroducedDerPossibility = true;
		}
		final Term result;
		if (nas.getArray().equals(mEliminatee)) {
			// is (possibly nested) self-update
			final LinkedList<Term> indices = new LinkedList<>(newIndices);
			final LinkedList<Term> values = new LinkedList<>(newValues);
			final Term[] resultDualFiniteJuncts = new Term[indices.size()];
			for (int i = 0; i < newIndices.size(); i++) {
				final Term innermostIndex = indices.removeFirst();
				final Term innermostValue = values.removeFirst();
				resultDualFiniteJuncts[i] = constructDisjointIndexImplication(innermostIndex, indices, innermostValue,
						mEliminatee);
			}
			assert indices.isEmpty();
			values.isEmpty();
			result = QuantifierUtils.applyDualFiniteConnective(mScript, mQuantifier, resultDualFiniteJuncts);
		} else {
			if (Arrays.asList(nas.getArray().getFreeVars()).contains(mEliminatee)) {
				throw new UnsupportedOperationException(
						"We have to descend beyond store chains. Introduce auxiliary variables only for arrays of lower dimension to avoid non-termination.");
			}
			result = new NestedArrayStore(nas.getArray(), newIndices, newValues).toTerm(mScript);
		}
		return result;
	}

	private List<Term> constructReplacementsIfNeeded(final List<Term> indices) {
		final List<Term> newIndices = new ArrayList<>();
		boolean replacementMade = false;
		for (final Term index : indices) {
			Term newIndex;
			if (Arrays.asList(index.getFreeVars()).contains(mEliminatee)) {
				newIndex = mAuxVarCc.getOrConstruct(index);
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

	private Term constructReplacementForSelectCase(final Term array, final Term index) {
		final Term newIndex;
		if (Arrays.asList(index.getFreeVars()).contains(mEliminatee)) {
			newIndex = mAuxVarCc.getOrConstruct(index);
		} else {
			newIndex = index;
		}
		Term result;
		if (newIndex != index) {
			mIntroducedDerPossibility = true;
		}
		final Term store = mScript.term("select", array, newIndex);
		result = QuantifierUtils.applyDerOperator(mScript, mQuantifier, mEliminatee, store);

		// TODO: let Prenex transformer deal with non-NNF terms and remove the
		// following line
		result = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(result);
		return result;
	}

	/**
	 * Let oi_1,...,oi_n be the terms in otherIndices, construct the formula
	 * ((idx != oi_1) /\ ... /\ (idx != oi_n)) ==> ((select arr idx) = value)
	 * for existential quantification and the formula
	 * (not ((idx == oi_1) \/ ... \/ (idx == oi_n))) /\ ((select arr idx) != value)
	 * for universal quantification.
	 */
	private Term constructDisjointIndexImplication(final Term idx, final List<Term> otherIndices, final Term value,
			final Term arr) {
		final Term select = SmtUtils.select(mScript, arr, idx);
		final Term selectEqualsValue = QuantifierUtils.applyDerOperator(mScript, mQuantifier, select, value);
		final List<Term> dualFiniteJuncts = otherIndices.stream()
				.map(x -> QuantifierUtils.applyAntiDerOperator(mScript, mQuantifier, idx, x))
				.collect(Collectors.toList());
		final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mScript, mQuantifier,
				dualFiniteJuncts);
		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, mQuantifier,
				SmtUtils.not(mScript, dualFiniteJunction), selectEqualsValue);
		return result;
	}

}

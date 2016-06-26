/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.mapelimination;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.SingleUpdateNormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.SingleUpdateNormalFormTransformer.FreshAuxVarGenerator;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */

public class MapEliminator {
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final IFreshTermVariableConstructor mVariableManager;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final ILogger mLogger;

	private final Collection<TransFormula> mTransFormulas;

	// Maps the indices to the tuples, which contain it
	private final Map<Term, Set<ArrayIndex>> mIndicesToTuples;

	// Maps the arrays to tuples, which access it
	private final Map<Term, Set<ArrayIndex>> mArrayIndices;

	// Maps the tuples to the arrays, which access it
	private final Map<ArrayIndex, Set<Term>> mTupleToArray;

	// Maps the array indices to expressions which contain it
	private final Map<Term, Set<Term>> mVariableInExpressions;

	// Maps each expression to variables which occur in it (this is just needed temporarily)
	private final Map<Term, Set<Term>> mExpressionContainsVariable;

	// Maps the global TermVariables to the RankVar with this definition
	private final Map<Term, RankVar> mRankVars;

	// A term that contains information about the the created aux-vars (this occurs if a (select (store ...))-Expression occurs)
	private Term mAuxVarTerm;
	private final Set<TermVariable> mAuxVars;

	// Stores information about the arrays that get assigned to another array (then these arrays have the same indices)
	private final List<Term> mSharedIndicesLeft;
	private final List<Term> mSharedIndicesRight;

	public MapEliminator(final IUltimateServiceProvider services, final Boogie2SMT boogie2smt, final Collection<TransFormula> transformulas) {
		super();
		mServices = services;
		mScript = boogie2smt.getScript();
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mIndicesToTuples = new HashMap<>();
		mArrayIndices = new HashMap<>();
		mTupleToArray = new HashMap<>();
		mExpressionContainsVariable = new HashMap<>();
		mVariableInExpressions = new HashMap<>();
		mVariableManager = boogie2smt.getVariableManager();
		mReplacementVarFactory = new ReplacementVarFactory(mVariableManager);
		mRankVars = new HashMap<>();
		mAuxVarTerm = mScript.term("true");
		mSharedIndicesLeft = new ArrayList<>();
		mSharedIndicesRight = new ArrayList<>();
		mTransFormulas = transformulas;
		mAuxVars = new HashSet<>();
		initialize();
	}

	private void initialize() {
		for (final TransFormula tf : mTransFormulas) {
			final TransFormulaLR newTF = TransFormulaLR.buildTransFormula(tf, mReplacementVarFactory);
			findIndices(newTF.getFormula(), newTF.getInVarsReverseMapping(), newTF.getOutVarsReverseMapping());
		}
		// Merge indices of mSharedIndices (maybe get transitivity?)
		for (int i = 0; i < mSharedIndicesLeft.size(); i++) {
			final Term array1 = mSharedIndicesLeft.get(i);
			final Term array2 = mSharedIndicesRight.get(i);
			if (!mArrayIndices.containsKey(array1)) {
				mArrayIndices.put(array1, new HashSet<ArrayIndex>());
			}
			if (!mArrayIndices.containsKey(array2)) {
				mArrayIndices.put(array2, new HashSet<ArrayIndex>());
			}
			mArrayIndices.get(array1).addAll(mArrayIndices.get(array2));
			mArrayIndices.put(array2, mArrayIndices.get(array1));
		}
	}

	private void findIndices(final Term term, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final String function = a.getFunction().getApplicationString();
			final Term[] params = a.getParameters();
			if (function.equals("=") && params[0].getSort().isArraySort() || function.equals("store")) {
				// Get relations of different arrays (the indices need to be shared then)
				final SingleUpdateNormalFormTransformer normalForm = new SingleUpdateNormalFormTransformer(term, mScript,
						new FreshAuxVarGenerator(mReplacementVarFactory));
				final List<ArrayUpdate> list = normalForm.getArrayUpdates();
				Term array1;
				Term array2;
				if (list.isEmpty()) {
					array1 = params[0];
					array2 = params[1];

				} else {
					array1 = list.get(0).getOldArray();
					array2 = list.get(list.size() - 1).getNewArray();
					findIndicesInArrayUpdate(list, inVars, outVars);
				}
				final Term globalArray1 = getGlobalTerm(array1, inVars, outVars);
				final Term globalArray2 = getGlobalTerm(array2, inVars, outVars);
				if (globalArray1 != globalArray2) {
					mSharedIndicesLeft.add(globalArray1);
					mSharedIndicesRight.add(globalArray2);
				}
			} else if (function.equals("select")) {
				final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
				Term array = select.getArray();
				if (SmtUtils.isFunctionApplication(array, "store")) {
					final SingleUpdateNormalFormTransformer normalForm = new SingleUpdateNormalFormTransformer(term, mScript,
							new FreshAuxVarGenerator(mReplacementVarFactory));
					final List<ArrayUpdate> list = normalForm.getArrayUpdates();
					findIndicesInArrayUpdate(list, inVars, outVars);
					array = list.get(0).getOldArray();
				}
				final ArrayIndex index = select.getIndex();
				for (final Term t : index) {
					findIndices(t, inVars, outVars);
				}
				final Term globalArray = getGlobalTerm(array, inVars, outVars);
				final ArrayIndex globalIndex = getGlobalArrayIndex(index, inVars, outVars);
				addToMap(globalArray, globalIndex);
			} else {
				for (final Term t : params) {
					findIndices(t, inVars, outVars);
				}
			}
		}
	}

	private void findIndicesInArrayUpdate(final List<ArrayUpdate> arrayUpdates, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		final Term oldArray = arrayUpdates.get(0).getOldArray();
		final Term globalArray = getGlobalTerm(oldArray, inVars, outVars);
		final HashMap<Term, Term> arrayReplacements = new HashMap<>();
		for (final ArrayUpdate update : arrayUpdates) {
			final MultiDimensionalStore store = update.getMultiDimensionalStore();
			final ArrayIndex newIndex = replaceIndex(store.getIndex(), arrayReplacements);
			final Term newValue = replaceTerm(store.getValue(), arrayReplacements);
			for (final Term t : newIndex) {
				findIndices(t, inVars, outVars);
			}
			findIndices(newValue, inVars, outVars);
			final ArrayIndex globalIndex = getGlobalArrayIndex(newIndex, inVars, outVars);
			addToMap(globalArray, globalIndex);
			arrayReplacements.put(update.getNewArray(), store.getStoreTerm());
		}
	}

	// This is to replace aux-vars created by SingleUpdateNormalFormTransformer with the their defintion, that doesn't contain aux-vars
	// TODO: Change SingleUpdateNormalFormTransformer?
	private Term replaceTerm(final Term term, final Map<Term, Term> arrayReplacements) {
		if (arrayReplacements.isEmpty()) {
			return term;
		}
		if (term instanceof TermVariable) {
			if (arrayReplacements.containsKey(term)) {
				return replaceTerm(arrayReplacements.get(term), arrayReplacements);
			} else {
				return term;
			}
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final Term[] params = a.getParameters();
			final int length = params.length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = replaceTerm(params[i], arrayReplacements);
			}
			return mScript.term(a.getFunction().getApplicationString(), newParams);
		}
		return term;
	}

	private ArrayIndex replaceIndex(final ArrayIndex index, final Map<Term, Term> arrayReplacements) {
		final List<Term> newList = new ArrayList<>();
		for (final Term t : index) {
			newList.add(replaceTerm(t, arrayReplacements));
		}
		return new ArrayIndex(newList);
	}

	private void addToMap(final Term globalArray, final ArrayIndex globalIndex) {
		for (final Term i : globalIndex) {
			if (!mIndicesToTuples.containsKey(i)) {
				mIndicesToTuples.put(i, new HashSet<ArrayIndex>());
			}
			mIndicesToTuples.get(i).add(globalIndex);
		}
		if (!mArrayIndices.containsKey(globalArray)) {
			mArrayIndices.put(globalArray, new HashSet<ArrayIndex>());
		}
		mArrayIndices.get(globalArray).add(globalIndex);

		if (!mTupleToArray.containsKey(globalIndex)) {
			mTupleToArray.put(globalIndex, new HashSet<Term>());
		}
		mTupleToArray.get(globalIndex).add(globalArray);
	}

	public TransFormulaLR getRewrittenTransFormula(final TransFormula tf) {
		assert mTransFormulas.contains(tf);
		final TransFormulaLR newTF = TransFormulaLR.buildTransFormula(tf, mReplacementVarFactory);
		final Set<Term> assignedVars = new HashSet<>();
		for (final BoogieVar boogieVar : tf.getAssignedVars()) {
			assignedVars.add(boogieVar.getTermVariable());
		}
		Term newTerm = newTF.getFormula();
		// Handle havoc's first
		for (final Term global : getHavocedIndices(newTF)) {
			final Term havocTerm = processIndexAssignment(newTF, global, assignedVars);
			newTerm = Util.and(mScript, newTerm, havocTerm);
		}
		for (final Term global : getHavocedArrays(newTF)) {
			final Term havocTerm = processArrayHavoc(newTF, global, assignedVars);
			newTerm = Util.and(mScript, newTerm, havocTerm);
		}
		// Process other terms
		newTerm = process(newTerm, newTF, assignedVars);
		if (!mAuxVars.isEmpty()) {
			// If aux-vars have been created, eliminate them
			final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, mAuxVars, Util.and(mScript, newTerm, mAuxVarTerm));
			newTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript,
					mVariableManager, quantified);
			mAuxVars.clear();
			mAuxVarTerm = mScript.term("true");
		}
		newTF.setFormula(SmtUtils.simplify(mScript, newTerm, mServices));
		return newTF;
	}

	private Set<Term> getHavocedArrays(final TransFormulaLR tf) {
		final Set<Term> result = new HashSet<>();
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		for (final Term array : mArrayIndices.keySet()) {
			final RankVar rankVar = mRankVars.get(array);
			final Term inVar = tf.getInVars().get(rankVar);
			final Term outVar = tf.getOutVars().get(rankVar);
			if (inVar != outVar && !freeVars.contains(outVar)) {
				result.add(array);
			}
		}
		return result;
	}

	private Set<Term> getHavocedIndices(final TransFormulaLR tf) {
		final Set<Term> result = new HashSet<>();
		final Set<Term> vars = new HashSet<>(mIndicesToTuples.keySet());
		vars.addAll(mVariableInExpressions.keySet());
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		for (final Term var : vars) {
			final RankVar rankVar = mRankVars.get(var);
			final Term inVar = tf.getInVars().get(rankVar);
			final Term outVar = tf.getOutVars().get(rankVar);
			if (inVar != outVar && !freeVars.contains(outVar)) {
				result.add(var);
			}
		}
		return result;
	}

	// Wrapper method, returns a new Term (without arrays!) for the TransFormula and adds needed vars to in- and out-vars
	private Term process(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final String function = a.getFunction().getApplicationString();
			final Term[] params = a.getParameters();
			if (function.equals("select")) {
				return processArrayRead(term, tf, assignedVars);
			}
			if (function.equals("=") && params[0].getSort().isArraySort()) {
				// Handle array assignment
				return processArrayAssignment(term, tf, assignedVars);
			}
			// Process recursively
			final int length = params.length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = process(params[i], tf, assignedVars);
			}
			final Term newTerm = mScript.term(function, newParams);
			if (function.equals("=")) {
				// Check if an index is assigned
				for (final Term t : newParams) {
					if (tf.getOutVarsReverseMapping().containsKey(t)) {
						final Term var = tf.getOutVarsReverseMapping().get(t).getDefinition();
						if (assignedVars.contains(var)) {
							// Handle index assignment
							return Util.and(mScript, newTerm, processIndexAssignment(tf, var, assignedVars));
						}
					}

				}
			}
			return newTerm;
		}
		return term;
	}

	private Term processArrayRead(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars) {
		final Term globalTerm = getGlobalTerm(term, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final RankVar rv = mReplacementVarFactory.getOrConstuctReplacementVar(globalTerm);
		final MultiDimensionalSelect multiDimensionalSelect = new MultiDimensionalSelect(term);
		final Term array = multiDimensionalSelect.getArray();
		final ArrayIndex index = multiDimensionalSelect.getIndex();
		if (SmtUtils.isFunctionApplication(array, "store")) {
			final SingleUpdateNormalFormTransformer normalForm = new SingleUpdateNormalFormTransformer(term, mScript,
					new FreshAuxVarGenerator(mReplacementVarFactory));
			final List<ArrayUpdate> arrayUpdates = normalForm.getArrayUpdates();
			final int last = arrayUpdates.size() - 1;
			final Set<ArrayIndex> processedIndices = new HashSet<>();
			Term result = mScript.term("true");
			final TermVariable auxVar = mVariableManager.constructFreshTermVariable("aux", term.getSort());
			mAuxVars.add(auxVar);
			final Map<Term, Term> arrayReplacements = new HashMap<>();
			for (final ArrayUpdate update : arrayUpdates) {
				arrayReplacements.put(update.getNewArray(), update.getMultiDimensionalStore().getStoreTerm());
			}
			for (int i = last; i >= 0; i--) {
				final ArrayUpdate update = arrayUpdates.get(i);
				final ArrayIndex assignedIndex = update.getIndex();
				if (processedIndices.contains(assignedIndex)) {
					continue;
				}
				final Term value = process(replaceTerm(update.getValue(), arrayReplacements), tf, assignedVars);
				final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, assignedIndex, processedIndices, auxVar, value);
				result = Util.and(mScript, result, newTerm);
				processedIndices.add(assignedIndex);
			}
			final Term realArray = arrayUpdates.get(0).getOldArray();
			final Term selectTerm = processArrayRead(SmtUtils.multiDimensionalSelect(mScript, realArray, index), tf, assignedVars);
			final Term arrayRead = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, index, processedIndices, auxVar, selectTerm);
			mAuxVarTerm = Util.and(mScript, mAuxVarTerm, result, arrayRead);
			return auxVar;
		} else {
			final TermVariable var = getFreshTermVar(globalTerm);
			if (containsInVarsOnly(term, tf)) {
				if (!tf.getInVars().containsKey(rv)) {
					tf.addInVar(rv, var);
				}
				return tf.getInVars().get(rv);
			} else {
				if (!tf.getOutVars().containsKey(rv)) {
					tf.addOutVar(rv, var);
				}
				return tf.getOutVars().get(rv);
			}
		}
	}

	private Term processArrayAssignment(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars) {
		final SingleUpdateNormalFormTransformer normalForm = new SingleUpdateNormalFormTransformer(term, mScript,
				new FreshAuxVarGenerator(mReplacementVarFactory));
		final List<ArrayUpdate> arrayUpdates = normalForm.getArrayUpdates();
		Term oldArray;
		Term newArray;
		if (arrayUpdates.isEmpty()) {
			// New / Old array might be "wrong" (isn't important because first loop isn't entered)
			final Term[] params = ((ApplicationTerm) term).getParameters();
			oldArray = params[0];
			newArray = params[1];
		} else {
			oldArray = arrayUpdates.get(0).getOldArray();
			newArray = arrayUpdates.get(arrayUpdates.size() - 1).getNewArray();
		}
		final Map<Term, Term> arrayReplacements = new HashMap<>();
		for (final ArrayUpdate update : arrayUpdates) {
			arrayReplacements.put(update.getNewArray(), update.getMultiDimensionalStore().getStoreTerm());
		}
		final Term globalOldArray = getGlobalTerm(oldArray, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final Term globalNewArray = getGlobalTerm(newArray, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final Set<ArrayIndex> assignedIndices = new HashSet<>();
		Term result = mScript.term("true");
		for (int i = arrayUpdates.size() - 1; i >= 0; i--) {
			final ArrayUpdate update = arrayUpdates.get(i);
			// The value of the update might contain an aux-var, so replace it and process it then
			final List<Term> list = new ArrayList<>();
			for (final Term t : update.getIndex()) {
				list.add(process(replaceTerm(t, arrayReplacements), tf, assignedVars));
			}
			final ArrayIndex assignedIndex = new ArrayIndex(list);
			final Term value = process(replaceTerm(update.getValue(), arrayReplacements), tf, assignedVars);
			for (final ArrayIndex globalIndex : mArrayIndices.get(globalNewArray)) {
				final ArrayIndex index = getLocalIndex(globalIndex, tf, assignedVars, false);
				if (assignedIndices.contains(index)) {
					continue;
				}
				final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, globalNewArray, globalIndex);
				final RankVar rv = mReplacementVarFactory.getOrConstuctReplacementVar(selectTerm);
				final Term var;
				if (tf.getOutVars().containsKey(rv)) {
					var = tf.getOutVars().get(rv);
				} else {
					var = getFreshTermVar(selectTerm);
					tf.addOutVar(rv, var);
				}
				final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, assignedIndex, assignedIndices, var, value);
				result = Util.and(mScript, result, newTerm);
			}
			assignedIndices.add(assignedIndex);
		}
		// For un-assigned indices i add: newArray[i] = oldArray[i]
		for (final ArrayIndex globalIndex : mArrayIndices.get(globalOldArray)) {
			final Term selectNew = SmtUtils.multiDimensionalSelect(mScript, globalNewArray, globalIndex);
			final Term selectOld = SmtUtils.multiDimensionalSelect(mScript, globalOldArray, globalIndex);
			final RankVar rvOld = mReplacementVarFactory.getOrConstuctReplacementVar(selectOld);
			final RankVar rvNew = mReplacementVarFactory.getOrConstuctReplacementVar(selectNew);
			final TermVariable freshOld = getFreshTermVar(selectOld);
			final TermVariable freshNew = getFreshTermVar(selectNew);
			final Term varOld;
			if (tf.getInVarsReverseMapping().containsKey(oldArray)) {
				if (!tf.getInVars().containsKey(rvOld)) {
					tf.addInVar(rvOld, freshOld);
				}
				varOld = tf.getInVars().get(rvOld);
			} else {
				if (!tf.getOutVars().containsKey(rvOld)) {
					tf.addOutVar(rvOld, freshOld);
				}
				varOld = tf.getOutVars().get(rvOld);
				// If in the out-vars, look if also an index (needs to be processed then)
				result = Util.and(mScript, result, processIndexAssignment(tf, selectOld, assignedVars));

			}
			final Term varNew;
			if (tf.getInVarsReverseMapping().containsKey(newArray)) {
				if (!tf.getInVars().containsKey(rvNew)) {
					tf.addInVar(rvNew, freshNew);
				}
				varNew = tf.getInVars().get(rvNew);
			} else {
				if (!tf.getOutVars().containsKey(rvNew)) {
					tf.addOutVar(rvNew, freshNew);
				}
				varNew = tf.getOutVars().get(rvNew);
				// If in the out-vars, look if also an index (needs to be processed then)
				result = Util.and(mScript, result, processIndexAssignment(tf, selectNew, assignedVars));
			}
			final ArrayIndex indexNew = getLocalIndex(globalIndex, tf, assignedVars, false);
			final ArrayIndex indexOld = getLocalIndex(globalIndex, tf, assignedVars, true);
			final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, indexNew, indexOld, assignedIndices, varNew, varOld);
			result = Util.and(mScript, result, newTerm);
		}
		return result;
	}

	private Term processArrayHavoc(final TransFormulaLR tf, final Term globalArray, final Set<Term> assignedVars) {
		Term result = mScript.term("true");
		if (!mArrayIndices.containsKey(globalArray)) {
			return result;
		}
		// Just add all array-replacement-vars for the given array to the out-vars (so havoc the ReplacementVars)
		for (final ArrayIndex index : mArrayIndices.get(globalArray)) {
			final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, globalArray, index);
			final RankVar rankVar = mReplacementVarFactory.getOrConstuctReplacementVar(selectTerm);
			final Term var = getFreshTermVar(selectTerm);
			tf.addOutVar(rankVar, var);
			// The havoced array cells might also be indices!
			result = Util.and(mScript, result, processIndexAssignment(tf, selectTerm, assignedVars));
		}
		return result;
	}

	private Term processIndexAssignment(final TransFormulaLR tf, final Term assignedTerm, final Set<Term> assignedVars) {
		Term result = mScript.term("true");
		if (mIndicesToTuples.containsKey(assignedTerm)) {
			final Set<Term> havocedArrays = getHavocedArrays(tf);
			final Set<Term> newAssignedVars = new HashSet<>(assignedVars);
			for (final ArrayIndex globalIndexWritten : mIndicesToTuples.get(assignedTerm)) {
				final ArrayIndex indexWrittenIn = getLocalIndex(globalIndexWritten, tf, assignedVars, true);
				final ArrayIndex indexWrittenOut = getLocalIndex(globalIndexWritten, tf, assignedVars, false);
				for (final Term array : mTupleToArray.get(globalIndexWritten)) {
					if (havocedArrays.contains(array)) {
						continue;
					}
					final Term selectWritten = SmtUtils.multiDimensionalSelect(mScript, array, globalIndexWritten);
					// Workaround to force different in and out-vars
					newAssignedVars.add(array);
					final Term written = getLocalVar(selectWritten, tf, newAssignedVars, false);
					final Term writtenOld = getLocalVar(selectWritten, tf, newAssignedVars, true);
					for (final ArrayIndex globalIndexRead : mArrayIndices.get(array)) {
						if (globalIndexWritten == globalIndexRead) {
							continue;
						}
						// If written to array or an index use out-var, otherwise in-var (needs to be determined this way)
						boolean assigned = false;
						if (assignedVars.contains(array)) {
							assigned = true;
						} else {
							for (final Term t : globalIndexRead) {
								if (assignedVars.contains(t)) {
									assigned = true;
									break;
								}
							}
						}
						final Term selectRead = SmtUtils.multiDimensionalSelect(mScript, array, globalIndexRead);
						final Term read = getLocalVar(selectRead, tf, assignedVars, false);
						final ArrayIndex indexRead = getLocalIndex(globalIndexRead, tf, assignedVars, !assigned);
						final Term assignment = SmtUtils.indexEqualityImpliesValueEquality(mScript, indexWrittenOut, indexRead, written, read);
						result = Util.and(mScript, result, assignment);
					}
					// The assigned cells might also be indices!
					final Term indexAssignment = processIndexAssignment(tf, selectWritten, assignedVars);
					result = Util.and(mScript, result, indexAssignment);
					// If it is not written to the array, add the unchanged property if the index didn't change
					// (If written to the array, there is a stronger unchanged-condition)
					if (!assignedVars.contains(array)) {
						final Term unchanged = SmtUtils.indexEqualityImpliesValueEquality(mScript, indexWrittenOut, indexWrittenIn, written, writtenOld);
						result = Util.and(mScript, result, unchanged);
					}
				}
			}
		}
		// Assign all indices which depend on assignedTerm
		if (!mVariableInExpressions.containsKey(assignedTerm)) {
			return result;
		}
		for (final Term globalVar : mVariableInExpressions.get(assignedTerm)) {
			// Force different in and out-vars
			final RankVar rankVar = mReplacementVarFactory.getOrConstuctReplacementVar(globalVar);
			if (!tf.getInVars().containsKey(rankVar)) {
				tf.addInVar(rankVar, getFreshTermVar(globalVar));
			}
			if (!tf.getOutVars().containsKey(rankVar)) {
				tf.addOutVar(rankVar, getFreshTermVar(globalVar));
			}
			final Term lhs = getLocalVar(globalVar, tf, assignedVars, false);
			final Term rhs = getOutVarDefintion(globalVar, tf);
			final Term assignment = SmtUtils.binaryEquality(mScript, lhs, rhs);
			result = Util.and(mScript, result, assignment, processIndexAssignment(tf, globalVar, assignedVars));
		}
		return result;
	}

	private Term getLocalVar(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars, final boolean inVar) {
		if (term instanceof ConstantTerm) {
			return term;
		}
		RankVar rankVar;
		if (term instanceof TermVariable) {
			rankVar  = mRankVars.get(term);
		} else  {
			rankVar = mReplacementVarFactory.getOrConstuctReplacementVar(term);
		}
		boolean assignedArray = false;
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			if (assignedVars.contains(select.getArray())) {
				assignedArray = true;
			}
		}
		final Term var = getFreshTermVar(term);
		if (!tf.getInVars().containsKey(rankVar)) {
			tf.addInVar(rankVar, var);
		}
		if (!tf.getOutVars().containsKey(rankVar)) {
			if (assignedArray) {
				tf.addOutVar(rankVar, getFreshTermVar(term));
			} else {
				tf.addOutVar(rankVar, var);
			}

		}
		if (inVar) {
			return tf.getInVars().get(rankVar);
		} else {
			return tf.getOutVars().get(rankVar);
		}
	}

	private ArrayIndex getLocalIndex(final ArrayIndex globalIndex, final TransFormulaLR tf, final Set<Term> assignedVars, final boolean inVar) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : globalIndex) {
			list.add(getLocalVar(t, tf, assignedVars, inVar));
		}
		return new ArrayIndex(list);
	}

	private Term getOutVarDefintion(final Term term, final TransFormulaLR tf) {
		if (term instanceof ConstantTerm) {
			return term;
		}
		if (term instanceof TermVariable) {
			final RankVar rankVar  = mRankVars.get(term);
			final Term var = getFreshTermVar(term);
			if (!tf.getInVars().containsKey(rankVar)) {
				tf.addInVar(rankVar, var);
			}
			if (!tf.getOutVars().containsKey(rankVar)) {
				tf.addOutVar(rankVar, var);
			}
			return tf.getOutVars().get(rankVar);
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final int length = a.getParameters().length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = getOutVarDefintion(a.getParameters()[i], tf);
			}
			return mScript.term(a.getFunction().getApplicationString(), newParams);
		}
		throw new UnsupportedOperationException("Term-type " + term.getClass().getSimpleName() + " is not supported at this position");
	}

	// Returns a fresh TermVariable with term as definition (with a nicer name for select-terms)
	private TermVariable getFreshTermVar(final Term term) {
		return mVariableManager.constructFreshTermVariable(niceTermString(term), term.getSort());
	}

	private String niceTermString(final Term term) {
		final StringBuilder sb = new StringBuilder();
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			sb.append(select.getArray().toString()).append('[');
			final ArrayIndex index = select.getIndex();
			for (int i = 0; i < index.size(); i++) {
				sb.append(niceTermString(index.get(i))).append(i == index.size() - 1 ? ']' : ',');
			}
			return sb.toString();
		}
		return term.toString();
	}

	// Get the global definition of a term and add the information about the contained vars to a hash-map
	private Term getGlobalTerm(final Term term, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		if (term instanceof TermVariable) {
			RankVar rv;
			if (inVars.containsKey(term)) {
				rv = inVars.get(term);
			} else if (outVars.containsKey(term)){
				rv = outVars.get(term);
			} else {
				throw new UnsupportedOperationException(term.toString() + " is neither an in- nor an out-var!");
			}
			final Term newTerm = rv.getDefinition();
			mRankVars.put(newTerm, rv);
			return newTerm;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final int length = a.getParameters().length;
			final Term[] newParams = new Term[length];
			final Set<Term> varsContained = new HashSet<>();
			for (int i = 0; i < length; i++) {
				final Term t = getGlobalTerm(a.getParameters()[i], inVars, outVars);
				newParams[i] = t;
				if (t instanceof TermVariable) {
					varsContained.add(t);
				} else {
					if (!mExpressionContainsVariable.containsKey(t)) {
						continue;
					}
					varsContained.addAll(mExpressionContainsVariable.get(t));
				}

			}
			final String function = a.getFunction().getApplicationString();
			final Term newTerm = mScript.term(function, newParams);
			if (!function.equals("select") && !function.equals("store")) {
				if (!mExpressionContainsVariable.containsKey(newTerm)) {
					mExpressionContainsVariable.put(newTerm, new HashSet<Term>());
				}
				mExpressionContainsVariable.get(newTerm).addAll(varsContained);
				for (final Term var : varsContained) {
					if (!mVariableInExpressions.containsKey(var)) {
						mVariableInExpressions.put(var, new HashSet<Term>());
					}
					mVariableInExpressions.get(var).add(newTerm);
				}
				mRankVars.put(newTerm, mReplacementVarFactory.getOrConstuctReplacementVar(newTerm));
			}
			return newTerm;
		}
		return term;
	}

	private ArrayIndex getGlobalArrayIndex(final ArrayIndex arrayIndex, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : arrayIndex) {
			list.add(getGlobalTerm(t, inVars, outVars));
		}
		return new ArrayIndex(list);
	}

	private boolean containsInVarsOnly(final Term term, final TransFormulaLR tf) {
		if (term instanceof ConstantTerm) {
			return true;
		}
		if (term instanceof TermVariable) {
			return tf.getInVarsReverseMapping().containsKey(term);
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			for (final Term t : applicationTerm.getParameters()) {
				if (!containsInVarsOnly(t, tf)) {
					return false;
				}
			}
			return true;
		}
		throw new UnsupportedOperationException("Term-type " + term.getClass().getSimpleName() + " is not supported at this position");
	}
}

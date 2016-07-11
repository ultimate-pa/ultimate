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

	// Stores information, for which select-terms aux-vars have already been created (to avoid duplicates)
	private final Map<Term, TermVariable> mSelectToAuxVars;

	// Stores information about the arrays that get assigned to another array (then these arrays have the same indices)
	private final List<Term> mSharedIndicesLeft;
	private final List<Term> mSharedIndicesRight;

	/**
	 * Creates a new map eliminator and preprocesses (stores the indices and arrays used in the {@code transformulas})
	 */
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
		mSelectToAuxVars = new HashMap<>();
		initialize();
	}

	/**
	 * Finds the array accesses in the transformulas and merges the indices if necessary
	 */
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

	/**
	 * A recursive method that finds arrays / indices in the given {@code term} and stores it in the maps
	 *
	 * @param term A SMT-Term
	 * @param inVars Mapping from SMT-inVars to RankVars
	 * @param outVars Mapping from SMT-outVars to RankVars
	 */
	private void findIndices(final Term term, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final String function = a.getFunction().getApplicationString();
			final Term[] params = a.getParameters();
			if (function.equals("=") && params[0].getSort().isArraySort() || function.equals("store")) {
				// Get relations of different arrays (the indices need to be shared then)
				final ArrayWrite arrayWrite = new ArrayWrite(term);
				findIndicesArrayWrite(arrayWrite, inVars, outVars);
				final Term newArray = getGlobalTerm(arrayWrite.getNewArray(), inVars, outVars);
				final Term oldArray = getGlobalTerm(arrayWrite.getOldArray(), inVars, outVars);
				if (newArray != oldArray) {
					mSharedIndicesLeft.add(newArray);
					mSharedIndicesRight.add(oldArray);
				}
			} else if (function.equals("select")) {
				final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
				final ArrayIndex index = select.getIndex();
				for (final Term t : index) {
					findIndices(t, inVars, outVars);
				}
				final ArrayWrite arrayWrite = new ArrayWrite(select.getArray());
				findIndicesArrayWrite(arrayWrite, inVars, outVars);
				final Term array = arrayWrite.getOldArray();
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

	private void findIndicesArrayWrite(final ArrayWrite araryWrite, final Map<Term, RankVar> inVars, final Map<Term, RankVar> outVars) {
		final Term oldArray = araryWrite.getOldArray();
		final Term globalArray = getGlobalTerm(oldArray, inVars, outVars);
		for (final MultiDimensionalStore store : araryWrite.getStoreList()) {
			for (final Term t : store.getIndex()) {
				findIndices(t, inVars, outVars);
			}
			findIndices(store.getValue(), inVars, outVars);
			final ArrayIndex globalIndex = getGlobalArrayIndex(store.getIndex(), inVars, outVars);
			addToMap(globalArray, globalIndex);
		}
	}

	/**
	 * Adds the info, that {@code array} is accessed by {@code index} to the maps
	 */
	private void addToMap(final Term array, final ArrayIndex index) {
		for (final Term i : index) {
			if (!mIndicesToTuples.containsKey(i)) {
				mIndicesToTuples.put(i, new HashSet<ArrayIndex>());
			}
			mIndicesToTuples.get(i).add(index);
		}
		if (!mArrayIndices.containsKey(array)) {
			mArrayIndices.put(array, new HashSet<ArrayIndex>());
		}
		mArrayIndices.get(array).add(index);

		if (!mTupleToArray.containsKey(index)) {
			mTupleToArray.put(index, new HashSet<Term>());
		}
		mTupleToArray.get(index).add(array);
	}

	/**
	 * Given a TransFormula with possibly array accesses, returns an array-free TransFormula, which is (in general) an overapproximation.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor
	 *
	 * @param tf The old TransFormula, which might contain arrays accesses
	 * @return A TransFormulaLR, where array accesses are replaced by ReplacementVars
	 */
	public TransFormulaLR getArrayFreeTransFormula(final TransFormula tf) {
		assert mTransFormulas.contains(tf);
		final TransFormulaLR newTF = TransFormulaLR.buildTransFormula(tf, mReplacementVarFactory);
		final Set<Term> assignedVars = new HashSet<>();
		for (final BoogieVar boogieVar : tf.getAssignedVars()) {
			assignedVars.add(boogieVar.getTermVariable());
		}
		// Handle havoc's first
		Term havocTerms = mScript.term("true");
		for (final Term global : getHavocedIndices(newTF)) {
			final Term newHavocTerm = processIndexAssignment(newTF, global, assignedVars);
			havocTerms = Util.and(mScript, havocTerms, newHavocTerm);
		}
		for (final Term global : getHavocedArrays(newTF)) {
			final Term newHavocTerm = processArrayHavoc(newTF, global, assignedVars);
			havocTerms = Util.and(mScript, havocTerms, newHavocTerm);
		}
		// Process other terms
		final Term processedTerm = process(newTF.getFormula(), newTF, assignedVars);
		Term newTerm = Util.and(mScript, processedTerm, havocTerms);
		if (!mAuxVars.isEmpty()) {
			// If aux-vars have been created, eliminate them
			final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, mAuxVars, Util.and(mScript, newTerm, mAuxVarTerm));
			newTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript,
					mVariableManager, quantified);
			mAuxVars.clear();
			mSelectToAuxVars.clear();
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

	/**
	 * A recursive method, that returns an array-free term, which replaces {@code term} and adds the neeeded in-/out-vars to {@code tf}
	 *
	 * @param term The term to be replaced
	 * @param tf The new TransFormulaLR (in-/out-vars are added)
	 * @param assignedVars A set of vars, that have been assigned
	 * @return A new array-free term
	 */
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

	private ArrayIndex processArrayIndex(final ArrayIndex arrayIndex, final TransFormulaLR tf, final Set<Term> assignedVars) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : arrayIndex) {
			list.add(process(t, tf, assignedVars));
		}
		return new ArrayIndex(list);
	}

	private Term processArrayRead(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars) {
		final Term globalTerm = getGlobalTerm(term, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final RankVar rv = mReplacementVarFactory.getOrConstuctReplacementVar(globalTerm);
		final MultiDimensionalSelect multiDimensionalSelect = new MultiDimensionalSelect(term);
		final Term array = multiDimensionalSelect.getArray();
		final ArrayIndex index = multiDimensionalSelect.getIndex();
		if (SmtUtils.isFunctionApplication(array, "store")) {
			final ArrayWrite arrayWrite = new ArrayWrite(array);
			final Set<ArrayIndex> processedIndices = new HashSet<>();
			Term result = mScript.term("true");
			final TermVariable auxVar = mVariableManager.constructFreshTermVariable("aux", term.getSort());
			mAuxVars.add(auxVar);
			for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
				final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), tf, assignedVars);
				if (processedIndices.contains(assignedIndex)) {
					continue;
				}
				final Term value = process(store.getValue(), tf, assignedVars);
				final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, assignedIndex, processedIndices, auxVar, value);
				result = Util.and(mScript, result, newTerm);
				processedIndices.add(assignedIndex);
			}
			final Term realArray = arrayWrite.getOldArray();
			final Term selectTerm = processArrayRead(SmtUtils.multiDimensionalSelect(mScript, realArray, index), tf, assignedVars);
			final Term arrayRead = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, index, processedIndices, auxVar, selectTerm);
			mAuxVarTerm = Util.and(mScript, mAuxVarTerm, result, arrayRead);
			return auxVar;
		} else {
			final TermVariable var = getFreshTermVar(globalTerm);
			if (containsOnlyOneVarType(term, tf, true)) {
				if (!tf.getInVars().containsKey(rv)) {
					tf.addInVar(rv, var);
				}
				return tf.getInVars().get(rv);
			}
			if (containsOnlyOneVarType(term, tf, false)) {
				if (!tf.getOutVars().containsKey(rv)) {
					tf.addOutVar(rv, var);
				}
				return tf.getOutVars().get(rv);
			}
			// If the term contains "mixed" vars, aux-vars are introduced
			if (!mSelectToAuxVars.containsKey(term)) {
				final TermVariable auxVar = mVariableManager.constructFreshTermVariable("aux", term.getSort());
				mAuxVars.add(auxVar);
				mSelectToAuxVars.put(term, auxVar);
				final ArrayIndex globalIndex = getGlobalArrayIndex(index, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
				if (tf.getInVarsReverseMapping().containsKey(array)) {
					final ArrayIndex inVarIndex = getLocalIndex(globalIndex, tf, assignedVars, true);
					final Term inVarSelect = getLocalVar(term, tf, assignedVars, true);
					final Term newTerm = SmtUtils.indexEqualityImpliesValueEquality(mScript, index, inVarIndex, auxVar, inVarSelect);
					mAuxVarTerm = Util.and(mScript, mAuxVarTerm, newTerm);
				}
				if (tf.getOutVarsReverseMapping().containsKey(array)) {
					final ArrayIndex outVarIndex = getLocalIndex(globalIndex, tf, assignedVars, true);
					final Term outVarSelect = getLocalVar(term, tf, assignedVars, true);
					final Term newTerm = SmtUtils.indexEqualityImpliesValueEquality(mScript, index, outVarIndex, auxVar, outVarSelect);
					mAuxVarTerm = Util.and(mScript, mAuxVarTerm, newTerm);
				}
			}
			return mSelectToAuxVars.get(term);
		}
	}

	private Term processArrayAssignment(final Term term, final TransFormulaLR tf, final Set<Term> assignedVars) {
		final ArrayWrite arrayWrite = new ArrayWrite(term);
		final Term oldArray = arrayWrite.getOldArray();
		final Term newArray = arrayWrite.getNewArray();
		final Term globalOldArray = getGlobalTerm(oldArray, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final Term globalNewArray = getGlobalTerm(newArray, tf.getInVarsReverseMapping(), tf.getOutVarsReverseMapping());
		final Set<ArrayIndex> assignedIndices = new HashSet<>();
		Term result = mScript.term("true");
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), tf, assignedVars);
			if (assignedIndices.contains(assignedIndex)) {
				continue;
			}
			final Term value = process(store.getValue(), tf, assignedVars);
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

	/**
	 * Check if the given {@code term} only contains in- or out-vars
	 *
	 * @param term A SMT-Term to be checked
	 * @param tf A TransFormulaLR
	 * @param inVar Switch between in- and out-vars
	 * @return {@code true}, iff the given {@code term} only contains one type of vars (in- or out-vars, depending on {@code inVar})
	 */
	private boolean containsOnlyOneVarType(final Term term, final TransFormulaLR tf, final boolean inVar) {
		if (term instanceof ConstantTerm) {
			return true;
		}
		if (term instanceof TermVariable) {
			if (inVar) {
				return tf.getInVarsReverseMapping().containsKey(term);
			} else {
				return tf.getOutVarsReverseMapping().containsKey(term);
			}
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			for (final Term t : applicationTerm.getParameters()) {
				if (!containsOnlyOneVarType(t, tf, inVar)) {
					return false;
				}
			}
			return true;
		}
		throw new UnsupportedOperationException("Term-type " + term.getClass().getSimpleName() + " is not supported at this position");
	}
}

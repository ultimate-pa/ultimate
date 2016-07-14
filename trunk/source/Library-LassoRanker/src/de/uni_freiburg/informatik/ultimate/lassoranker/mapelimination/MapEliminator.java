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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

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
	private final Collection<TransFormulaLR> mTransFormulas;

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
	private final Set<Doubleton<Term>> mSharedIndices;

	/**
	 * Creates a new map eliminator and preprocesses (stores the indices and arrays used in the {@code transformulas})
	 */
	public MapEliminator(final IUltimateServiceProvider services, final Boogie2SMT boogie2smt, final Collection<TransFormulaLR> transformulas) {
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
		mTransFormulas = transformulas;
		mAuxVars = new HashSet<>();
		mSelectToAuxVars = new HashMap<>();
		mSharedIndices = new HashSet<>();
		initialize();
	}

	/**
	 * Finds the array accesses in the transformulas and merges the indices if necessary
	 */
	private void initialize() {
		// First check, if any of the transformulas contains arrays
		boolean noArrays = true;
		for (final TransFormulaLR tf : mTransFormulas) {
			if (containsArray(tf)) {
				noArrays = false;
				break;
			}
		}
		if (noArrays) {
			return;
		}
		for (final TransFormulaLR tf : mTransFormulas) {
			findIndices(tf.getFormula(), tf);
		}
		// Merge indices of mSharedIndices (maybe get transitivity?)
		for (final Doubleton<Term> doubleton : mSharedIndices) {
			final Term array1 = doubleton.getOneElement();
			final Term array2 = doubleton.getOtherElement();
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
	 * @param transformula A TransFormulaLR (needed to get the global definitions of the term)
	 */
	private void findIndices(final Term term, final TransFormulaLR transformula) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final String function = a.getFunction().getApplicationString();
			final Term[] params = a.getParameters();
			if ("=".equals(function) && params[0].getSort().isArraySort() || "store".equals(function)) {
				// Get relations of different arrays (the indices need to be shared then)
				final ArrayWrite arrayWrite = new ArrayWrite(term);
				findIndicesArrayWrite(arrayWrite, transformula);
				final Term newArray = getGlobalTerm(arrayWrite.getNewArray(), transformula);
				final Term oldArray = getGlobalTerm(arrayWrite.getOldArray(), transformula);
				if (newArray != oldArray) {
					mSharedIndices.add(new Doubleton<Term>(oldArray, newArray));
				}
			} else if ("select".equals(function)) {
				final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
				final ArrayIndex index = select.getIndex();
				for (final Term t : index) {
					findIndices(t, transformula);
				}
				final ArrayWrite arrayWrite = new ArrayWrite(select.getArray());
				findIndicesArrayWrite(arrayWrite, transformula);
				final Term array = arrayWrite.getOldArray();
				final Term globalArray = getGlobalTerm(array, transformula);
				final ArrayIndex globalIndex = getGlobalIndex(index, transformula);
				addToMap(globalArray, globalIndex);
			} else {
				for (final Term t : params) {
					findIndices(t, transformula);
				}
			}
		}
	}

	private void findIndicesArrayWrite(final ArrayWrite araryWrite, final TransFormulaLR transformula) {
		final Term globalArray = getGlobalTerm(araryWrite.getOldArray(), transformula);
		for (final MultiDimensionalStore store : araryWrite.getStoreList()) {
			for (final Term t : store.getIndex()) {
				findIndices(t, transformula);
			}
			findIndices(store.getValue(), transformula);
			final ArrayIndex globalIndex = getGlobalIndex(store.getIndex(), transformula);
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
	 * @param transformula The old TransFormula, which might contain arrays accesses
	 * @return A TransFormulaLR, where array accesses are replaced by ReplacementVars
	 */
	public TransFormulaLR getArrayFreeTransFormula(final TransFormulaLR transformula) {
		assert mTransFormulas.contains(transformula);
		final TransFormulaLR newTF = new TransFormulaLR(transformula);
		// Check if the transformula has to be handled. If not, simply return a copy of the old transformula
		if (mArrayIndices.isEmpty() || !containsArray(newTF) && !containsIndexAssignment(newTF)) {
			return newTF;
		}
		final Set<Term> assignedVars = new HashSet<>();
		for (final RankVar rv : transformula.getAssignedVars()) {
			assignedVars.add(rv.getDefinition());
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

	private Set<Term> getHavocedArrays(final TransFormulaLR transformula) {
		final Set<Term> result = new HashSet<>();
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		for (final Term array : mArrayIndices.keySet()) {
			final RankVar rankVar = mRankVars.get(array);
			final Term inVar = transformula.getInVars().get(rankVar);
			final Term outVar = transformula.getOutVars().get(rankVar);
			if (inVar != outVar && !freeVars.contains(outVar)) {
				result.add(array);
			}
		}
		return result;
	}

	private Set<Term> getHavocedIndices(final TransFormulaLR transformula) {
		final Set<Term> result = new HashSet<>();
		final Set<Term> vars = new HashSet<>(mIndicesToTuples.keySet());
		vars.addAll(mVariableInExpressions.keySet());
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		for (final Term var : vars) {
			final RankVar rankVar = mRankVars.get(var);
			final Term inVar = transformula.getInVars().get(rankVar);
			final Term outVar = transformula.getOutVars().get(rankVar);
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
	 * @param transformula The new TransFormulaLR (in-/out-vars are added)
	 * @param assignedVars A set of vars, that have been assigned
	 * @return A new array-free term
	 */
	private Term process(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final String function = a.getFunction().getApplicationString();
			if ("select".equals(function)) {
				return processArrayRead(term, transformula, assignedVars);
			}
			final Term[] params = a.getParameters();
			if ("=".equals(function) && params[0].getSort().isArraySort()) {
				// Handle array assignment
				return processArrayAssignment(term, transformula, assignedVars);
			}
			// Process recursively
			final int length = params.length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = process(params[i], transformula, assignedVars);
			}
			final Term newTerm = mScript.term(function, newParams);
			if ("=".equals(function)) {
				// Check if an index is assigned
				for (final Term t : newParams) {
					if (transformula.getOutVarsReverseMapping().containsKey(t)) {
						final Term var = transformula.getOutVarsReverseMapping().get(t).getDefinition();
						if (assignedVars.contains(var)) {
							// Handle index assignment
							return Util.and(mScript, newTerm, processIndexAssignment(transformula, var, assignedVars));
						}
					}

				}
			}
			return newTerm;
		}
		return term;
	}

	private ArrayIndex processArrayIndex(final ArrayIndex arrayIndex, final TransFormulaLR transformula, final Set<Term> assignedVars) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : arrayIndex) {
			list.add(process(t, transformula, assignedVars));
		}
		return new ArrayIndex(list);
	}

	private Term processArrayRead(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars) {
		final Term globalTerm = getGlobalTerm(term, transformula);
		final RankVar rankVar = mReplacementVarFactory.getOrConstuctReplacementVar(globalTerm);
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
				final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), transformula, assignedVars);
				if (processedIndices.contains(assignedIndex)) {
					continue;
				}
				final Term value = process(store.getValue(), transformula, assignedVars);
				final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, assignedIndex, processedIndices, auxVar, value);
				result = Util.and(mScript, result, newTerm);
				processedIndices.add(assignedIndex);
			}
			final Term realArray = arrayWrite.getOldArray();
			final Term selectTerm = processArrayRead(SmtUtils.multiDimensionalSelect(mScript, realArray, index), transformula, assignedVars);
			final Term arrayRead = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, index, processedIndices, auxVar, selectTerm);
			mAuxVarTerm = Util.and(mScript, mAuxVarTerm, result, arrayRead);
			return auxVar;
		} else {
			final TermVariable var = getFreshTermVar(globalTerm);
			if (containsOnlyOneVarType(term, transformula, true)) {
				if (!transformula.getInVars().containsKey(rankVar)) {
					transformula.addInVar(rankVar, var);
				}
				return transformula.getInVars().get(rankVar);
			}
			if (containsOnlyOneVarType(term, transformula, false)) {
				if (!transformula.getOutVars().containsKey(rankVar)) {
					transformula.addOutVar(rankVar, var);
				}
				return transformula.getOutVars().get(rankVar);
			}
			// If the term contains "mixed" vars, aux-vars are introduced
			if (!mSelectToAuxVars.containsKey(term)) {
				final TermVariable auxVar = mVariableManager.constructFreshTermVariable("aux", term.getSort());
				mAuxVars.add(auxVar);
				mSelectToAuxVars.put(term, auxVar);
				final ArrayIndex globalIndex = getGlobalIndex(index, transformula);
				if (transformula.getInVarsReverseMapping().containsKey(array)) {
					final ArrayIndex inVarIndex = getLocalIndex(globalIndex, transformula, assignedVars, true);
					final Term inVarSelect = getLocalVar(term, transformula, assignedVars, true);
					final Term newTerm = SmtUtils.indexEqualityImpliesValueEquality(mScript, index, inVarIndex, auxVar, inVarSelect);
					mAuxVarTerm = Util.and(mScript, mAuxVarTerm, newTerm);
				}
				if (transformula.getOutVarsReverseMapping().containsKey(array)) {
					final ArrayIndex outVarIndex = getLocalIndex(globalIndex, transformula, assignedVars, true);
					final Term outVarSelect = getLocalVar(term, transformula, assignedVars, true);
					final Term newTerm = SmtUtils.indexEqualityImpliesValueEquality(mScript, index, outVarIndex, auxVar, outVarSelect);
					mAuxVarTerm = Util.and(mScript, mAuxVarTerm, newTerm);
				}
			}
			return mSelectToAuxVars.get(term);
		}
	}

	private Term processArrayAssignment(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars) {
		final ArrayWrite arrayWrite = new ArrayWrite(term);
		final Term oldArray = arrayWrite.getOldArray();
		final Term newArray = arrayWrite.getNewArray();
		final Term globalOldArray = getGlobalTerm(oldArray, transformula);
		final Term globalNewArray = getGlobalTerm(newArray, transformula);
		final Set<ArrayIndex> assignedIndices = new HashSet<>();
		Term result = mScript.term("true");
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), transformula, assignedVars);
			if (assignedIndices.contains(assignedIndex)) {
				continue;
			}
			final Term value = process(store.getValue(), transformula, assignedVars);
			for (final ArrayIndex globalIndex : mArrayIndices.get(globalNewArray)) {
				final ArrayIndex index = getLocalIndex(globalIndex, transformula, assignedVars, false);
				if (assignedIndices.contains(index)) {
					continue;
				}
				final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, globalNewArray, globalIndex);
				final Term var = getLocalVar(selectTerm, transformula, assignedVars, false);
				final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, index, assignedIndex, assignedIndices, var, value);
				result = Util.and(mScript, result, newTerm);
			}
			assignedIndices.add(assignedIndex);
		}
		// For un-assigned indices i add: newArray[i] = oldArray[i]
		for (final ArrayIndex globalIndex : mArrayIndices.get(globalOldArray)) {
			final Term selectNew = SmtUtils.multiDimensionalSelect(mScript, globalNewArray, globalIndex);
			final Term selectOld = SmtUtils.multiDimensionalSelect(mScript, globalOldArray, globalIndex);
			final boolean oldIsInVar = transformula.getInVarsReverseMapping().containsKey(oldArray);
			final Term varOld =  getLocalVar(selectOld, transformula, assignedVars, oldIsInVar);
			final boolean newIsInVar = transformula.getInVarsReverseMapping().containsKey(newArray);
			final Term varNew =  getLocalVar(selectNew, transformula, assignedVars, newIsInVar);
			if (!oldIsInVar) {
				// If in the out-vars, look if also an index (needs to be processed then)
				result = Util.and(mScript, result, processIndexAssignment(transformula, selectOld, assignedVars));
			}
			if (!newIsInVar) {
				// If in the out-vars, look if also an index (needs to be processed then)
				result = Util.and(mScript, result, processIndexAssignment(transformula, selectNew, assignedVars));
			}
			final ArrayIndex indexIn = getLocalIndex(globalIndex, transformula, assignedVars, true);
			final ArrayIndex indexOut = getLocalIndex(globalIndex, transformula, assignedVars, false);
			final Term newTerm = SmtUtils.indexEqualityInequalityImpliesValueEquality(mScript, indexOut, indexIn, assignedIndices, varNew, varOld);
			result = Util.and(mScript, result, newTerm);
		}
		return result;
	}

	private Term processArrayHavoc(final TransFormulaLR transformula, final Term globalArray, final Set<Term> assignedVars) {
		Term result = mScript.term("true");
		if (!mArrayIndices.containsKey(globalArray)) {
			return result;
		}
		// Just add all array-replacement-vars for the given array to the out-vars (so havoc the ReplacementVars)
		for (final ArrayIndex index : mArrayIndices.get(globalArray)) {
			final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, globalArray, index);
			final RankVar rankVar = mReplacementVarFactory.getOrConstuctReplacementVar(selectTerm);
			final Term var = getFreshTermVar(selectTerm);
			transformula.addOutVar(rankVar, var);
			// The havoced array cells might also be indices!
			result = Util.and(mScript, result, processIndexAssignment(transformula, selectTerm, assignedVars));
		}
		return result;
	}

	private Term processIndexAssignment(final TransFormulaLR transformula, final Term assignedTerm, final Set<Term> assignedVars) {
		Term result = mScript.term("true");
		if (mIndicesToTuples.containsKey(assignedTerm)) {
			final Set<Term> havocedArrays = getHavocedArrays(transformula);
			for (final ArrayIndex globalIndexWritten : mIndicesToTuples.get(assignedTerm)) {
				final ArrayIndex indexWrittenIn = getLocalIndex(globalIndexWritten, transformula, assignedVars, true);
				final ArrayIndex indexWrittenOut = getLocalIndex(globalIndexWritten, transformula, assignedVars, false);
				for (final Term array : mTupleToArray.get(globalIndexWritten)) {
					if (havocedArrays.contains(array)) {
						continue;
					}
					final Term selectWritten = SmtUtils.multiDimensionalSelect(mScript, array, globalIndexWritten);
					// The replacement-vars of the array have changed, therefore add the array to the assignedVars
					assignedVars.add(array);
					final Term written = getLocalVar(selectWritten, transformula, assignedVars, false);
					final Term writtenOld = getLocalVar(selectWritten, transformula, assignedVars, true);
					for (final ArrayIndex globalIndexRead : mArrayIndices.get(array)) {
						if (globalIndexWritten == globalIndexRead) {
							continue;
						}
						// Compare with the other indices (in- and out-var-version)
						final Term selectRead = SmtUtils.multiDimensionalSelect(mScript, array, globalIndexRead);
						final Term readIn = getLocalVar(selectRead, transformula, assignedVars, true);
						final Term readOut = getLocalVar(selectRead, transformula, assignedVars, false);
						final ArrayIndex indexReadIn = getLocalIndex(globalIndexRead, transformula, assignedVars, true);
						final ArrayIndex indexReadOut = getLocalIndex(globalIndexRead, transformula, assignedVars, false);
						final Term assignmentIn = SmtUtils.indexEqualityImpliesValueEquality(mScript, indexWrittenOut, indexReadIn, written, readIn);
						final Term assignmentOut = SmtUtils.indexEqualityImpliesValueEquality(mScript, indexWrittenOut, indexReadOut, written, readOut);
						result = Util.and(mScript, result, assignmentIn, assignmentOut);
					}
					// The assigned cells might also be indices!
					final Term indexAssignment = processIndexAssignment(transformula, selectWritten, assignedVars);
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
			if (!transformula.getInVars().containsKey(rankVar)) {
				transformula.addInVar(rankVar, getFreshTermVar(globalVar));
			}
			if (!transformula.getOutVars().containsKey(rankVar)) {
				transformula.addOutVar(rankVar, getFreshTermVar(globalVar));
			}
			final Term lhs = getLocalVar(globalVar, transformula, assignedVars, false);
			final Term rhs = getOutVarDefintion(globalVar, transformula);
			final Term assignment = SmtUtils.binaryEquality(mScript, lhs, rhs);
			result = Util.and(mScript, result, assignment, processIndexAssignment(transformula, globalVar, assignedVars));
		}
		return result;
	}

	private Term getLocalVar(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars, final boolean returnInVar) {
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
		if (!transformula.getInVars().containsKey(rankVar)) {
			transformula.addInVar(rankVar, var);
		}
		if (!transformula.getOutVars().containsKey(rankVar)) {
			if (assignedArray) {
				transformula.addOutVar(rankVar, getFreshTermVar(term));
			} else {
				transformula.addOutVar(rankVar, var);
			}

		}
		if (returnInVar) {
			return transformula.getInVars().get(rankVar);
		} else {
			return transformula.getOutVars().get(rankVar);
		}
	}

	private ArrayIndex getLocalIndex(final ArrayIndex globalIndex, final TransFormulaLR transformula, final Set<Term> assignedVars,
			final boolean returnInVar) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : globalIndex) {
			list.add(getLocalVar(t, transformula, assignedVars, returnInVar));
		}
		return new ArrayIndex(list);
	}

	private Term getOutVarDefintion(final Term term, final TransFormulaLR transformula) {
		if (term instanceof ConstantTerm) {
			return term;
		}
		if (term instanceof TermVariable) {
			final RankVar rankVar  = mRankVars.get(term);
			final Term var = getFreshTermVar(term);
			if (!transformula.getInVars().containsKey(rankVar)) {
				transformula.addInVar(rankVar, var);
			}
			if (!transformula.getOutVars().containsKey(rankVar)) {
				transformula.addOutVar(rankVar, var);
			}
			return transformula.getOutVars().get(rankVar);
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final int length = a.getParameters().length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = getOutVarDefintion(a.getParameters()[i], transformula);
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
		final StringBuilder stringBuilder = new StringBuilder();
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			stringBuilder.append(select.getArray().toString()).append('[');
			final ArrayIndex index = select.getIndex();
			for (int i = 0; i < index.size(); i++) {
				stringBuilder.append(niceTermString(index.get(i))).append(i == index.size() - 1 ? ']' : ',');
			}
			return stringBuilder.toString();
		}
		return term.toString();
	}

	// Get the global definition of a term and add the information about the contained vars to a hash-map
	private Term getGlobalTerm(final Term term, final TransFormulaLR transformula) {
		if (term instanceof TermVariable) {
			RankVar rankVar;
			if (transformula.getInVarsReverseMapping().containsKey(term)) {
				rankVar = transformula.getInVarsReverseMapping().get(term);
			} else if (transformula.getOutVarsReverseMapping().containsKey(term)){
				rankVar = transformula.getOutVarsReverseMapping().get(term);
			} else {
				throw new UnsupportedOperationException(term.toString() + " is neither an in- nor an out-var!");
			}
			final Term newTerm = rankVar.getDefinition();
			mRankVars.put(newTerm, rankVar);
			return newTerm;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final int length = a.getParameters().length;
			final Term[] newParams = new Term[length];
			final Set<Term> varsContained = new HashSet<>();
			for (int i = 0; i < length; i++) {
				final Term globalTerm = getGlobalTerm(a.getParameters()[i], transformula);
				newParams[i] = globalTerm;
				if (globalTerm instanceof TermVariable) {
					varsContained.add(globalTerm);
				} else {
					if (!mExpressionContainsVariable.containsKey(globalTerm)) {
						continue;
					}
					varsContained.addAll(mExpressionContainsVariable.get(globalTerm));
				}

			}
			final String function = a.getFunction().getApplicationString();
			final Term newTerm = mScript.term(function, newParams);
			if (!("select".equals(function) || "store".equals(function))) {
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

	private ArrayIndex getGlobalIndex(final ArrayIndex arrayIndex, final TransFormulaLR transformula) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : arrayIndex) {
			list.add(getGlobalTerm(t, transformula));
		}
		return new ArrayIndex(list);
	}

	/**
	 * Check if the given {@code term} only contains in- or out-vars
	 *
	 * @param term A SMT-Term to be checked
	 * @param transformula A TransFormulaLR
	 * @param onlyInVars Switch between in- and out-vars
	 * @return {@code true}, iff the given {@code term} only contains one type of vars (in- or out-vars, depending on {@code inVar})
	 */
	private boolean containsOnlyOneVarType(final Term term, final TransFormulaLR transformula, final boolean onlyInVars) {
		if (term instanceof ConstantTerm) {
			return true;
		}
		if (term instanceof TermVariable) {
			if (onlyInVars) {
				return transformula.getInVarsReverseMapping().containsKey(term);
			} else {
				return transformula.getOutVarsReverseMapping().containsKey(term);
			}
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			for (final Term t : applicationTerm.getParameters()) {
				if (!containsOnlyOneVarType(t, transformula, onlyInVars)) {
					return false;
				}
			}
			return true;
		}
		throw new UnsupportedOperationException("Term-type " + term.getClass().getSimpleName() + " is not supported at this position");
	}

	private boolean containsArray(final TransFormulaLR transformula) {
		for (final Term var : transformula.getInVars().values()) {
			if (var.getSort().isArraySort()) {
				return true;
			}
		}
		for (final Term var : transformula.getOutVars().values()) {
			if (var.getSort().isArraySort()) {
				return true;
			}
		}
		return false;
	}

	private boolean containsIndexAssignment(final TransFormulaLR transformula) {
		for (final RankVar rankVar : transformula.getAssignedVars()) {
			if (mIndicesToTuples.containsKey(rankVar.getDefinition())) {
				return true;
			}
		}
		return false;
	}
}

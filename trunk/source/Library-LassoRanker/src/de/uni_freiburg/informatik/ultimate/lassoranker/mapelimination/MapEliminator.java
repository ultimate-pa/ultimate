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

import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils.allVariablesAreInVars;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils.allVariablesAreOutVars;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils.allVariablesAreVisible;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils.translateTermVariablesToDefinitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexAnalyzer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminator {
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ManagedScript mMangagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final ILogger mLogger;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final Collection<TransFormulaLR> mTransFormulas;

	// Stores for each term, which indices contain it
	private final HashRelation<Term, ArrayIndex> mTermsToIndices;

	// Stores for each array, which indices access it (bidirectional)
	private final HashRelation<ApplicationTermTemplate, ArrayIndex> mFunctionsToIndices;
	private final HashRelation<ArrayIndex, ApplicationTermTemplate> mIndicesToFunctions;

	// Stores for each variable, which index terms contain it
	private final HashRelation<Term, Term> mVariablesToIndexTerms;

	// A term that contains information about the the created aux-vars
	private final List<Term> mAuxVarTerms;

	// The created aux-vars (needed for quantifier-elimination)
	private final Set<TermVariable> mAuxVars;

	// Stores information, for which select-terms aux-vars have already been created (to avoid duplicates)
	private final Map<Term, TermVariable> mSelectToAuxVars;

	// Stores information about the arrays that get assigned to another array (then these arrays have the same indices)
	private final Set<Doubleton<Term>> mRelatedArays;

	// Stores all doubletons of terms, which might be compared
	private final Set<Doubleton<Term>> mDoubletons;

	/**
	 * Creates a new map eliminator and preprocesses (stores the indices and arrays used in the {@code transformulas})
	 */
	public MapEliminator(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final Boogie2SmtSymbolTable symbolTable, final ReplacementVarFactory replacementVarFactory,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Collection<TransFormulaLR> transformulas) {
		super();

		mServices = services;
		mScript = managedScript.getScript();
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mMangagedScript = managedScript;
		mReplacementVarFactory = replacementVarFactory;
		mSymbolTable = symbolTable;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;

		mTransFormulas = transformulas;

		mTermsToIndices = new HashRelation<>();
		mFunctionsToIndices = new HashRelation<>();
		mIndicesToFunctions = new HashRelation<>();

		mVariablesToIndexTerms = new HashRelation<>();

		mAuxVars = new HashSet<>();
		mAuxVarTerms = new ArrayList<>();
		mSelectToAuxVars = new HashMap<>();

		mRelatedArays = new HashSet<>();

		findAllIndices();
		mDoubletons = computeDoubletons(mFunctionsToIndices);
	}

	/**
	 * Finds the array accesses in the transformulas and merges the indices if necessary
	 */
	private void findAllIndices() {
		// Get all array indices from each transformula (only necessary, if it contains arrays)
		for (final TransFormulaLR tf : mTransFormulas) {
			findIndices(tf.getFormula(), tf);
		}
		// Merge the indices of the related arrays using union-find
		final UnionFind<Term> unionFind = new UnionFind<>();
		final Map<Term, SelectTemplate> templates = new HashMap<>();
		for (final Doubleton<Term> doubleton : mRelatedArays) {
			final Term array1 = doubleton.getOneElement();
			final Term array2 = doubleton.getOtherElement();
			templates.put(array1, new SelectTemplate(array1, mScript));
			templates.put(array2, new SelectTemplate(array2, mScript));
			unionFind.findAndConstructEquivalenceClassIfNeeded(array1);
			unionFind.findAndConstructEquivalenceClassIfNeeded(array2);
			unionFind.union(array1, array2);
		}
		for (final Set<Term> equivalenceClass : unionFind.getAllEquivalenceClasses()) {
			final Set<ArrayIndex> indices = new HashSet<>();
			for (final Term array : equivalenceClass) {
				indices.addAll(mFunctionsToIndices.getImage(templates.get(array)));
			}
			for (final Term array : equivalenceClass) {
				for (final ArrayIndex index : indices) {
					mFunctionsToIndices.addPair(templates.get(array), index);
					mIndicesToFunctions.addPair(index, templates.get(array));
				}
			}
		}
		// Map each variable to the index terms, which contain it
		for (final Term t : mTermsToIndices.getDomain()) {
			for (final TermVariable var : t.getFreeVars()) {
				mVariablesToIndexTerms.addPair(var, t);
			}
		}
	}

	/**
	 * A recursive method that finds arrays / indices in the given {@code term} and stores it in the maps
	 *
	 * @param term
	 *            A SMT-Term
	 * @param transformula
	 *            A TransFormulaLR (needed to get the global definitions of the term)
	 */
	// TODO: Use non-recursive version
	private void findIndices(final Term term, final TransFormulaLR transformula) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final FunctionSymbol function = a.getFunction();
			final Term[] params = a.getParameters();
			if ("=".equals(function.getName()) && params[0].getSort().isArraySort()) {
				// Get relations of different arrays (the indices need to be shared then)
				final ArrayWrite arrayWrite = new ArrayWrite(term);
				findIndicesArrayWrite(arrayWrite, transformula);
				final Term oldArray = arrayWrite.getOldArray();
				final Term newArray = arrayWrite.getNewArray();
				if (allVariablesAreVisible(oldArray, transformula) && allVariablesAreVisible(newArray, transformula)) {
					final Term array1 = translateTermVariablesToDefinitions(mScript, transformula, oldArray);
					final Term array2 = translateTermVariablesToDefinitions(mScript, transformula, newArray);
					if (array1 != array2) {
						mRelatedArays.add(new Doubleton<Term>(array1, array2));
					}
				}
			} else if ("select".equals(function.getName())) {
				final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
				final ArrayIndex index = select.getIndex();
				for (final Term t : index) {
					findIndices(t, transformula);
				}
				final ArrayWrite arrayWrite = new ArrayWrite(select.getArray());
				findIndicesArrayWrite(arrayWrite, transformula);
				addArrayToRelation(arrayWrite.getOldArray(), index, transformula);
			} else {
				if (!function.isIntern()) {
					addCallToRelation(function.getName(), params, transformula);
				}
				for (final Term t : params) {
					findIndices(t, transformula);
				}
			}
		}
	}

	private void findIndicesArrayWrite(final ArrayWrite arrayWrite, final TransFormulaLR transformula) {
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			for (final Term t : store.getIndex()) {
				findIndices(t, transformula);
			}
			findIndices(store.getValue(), transformula);
			addArrayToRelation(arrayWrite.getOldArray(), store.getIndex(), transformula);
		}
	}

	/**
	 * Adds the info, that {@code array} is accessed by {@code index} to the hash relations
	 */
	private void addArrayToRelation(final Term array, final ArrayIndex index, final TransFormulaLR transformula) {
		if (allVariablesAreVisible(array, transformula) && allVariablesAreVisible(index, transformula)) {
			final ArrayIndex globalIndex = new ArrayIndex(
					translateTermVariablesToDefinitions(mScript, transformula, index));
			final Term globalArray = translateTermVariablesToDefinitions(mScript, transformula, array);
			for (final Term t : globalIndex) {
				mTermsToIndices.addPair(t, globalIndex);
			}
			final SelectTemplate template = new SelectTemplate(globalArray, mScript);
			mFunctionsToIndices.addPair(template, globalIndex);
			mIndicesToFunctions.addPair(globalIndex, template);
		}
	}

	private void addCallToRelation(final String functionName, final Term[] arguments,
			final TransFormulaLR transformula) {
		final List<Term> argumentsList = Arrays.asList(arguments);
		if (allVariablesAreVisible(argumentsList, transformula)) {
			final ArrayIndex globalIndex = new ArrayIndex(
					translateTermVariablesToDefinitions(mScript, transformula, argumentsList));
			for (final Term t : globalIndex) {
				mTermsToIndices.addPair(t, globalIndex);
			}
			final FunctionTemplate template = new FunctionTemplate(functionName, mScript);
			mFunctionsToIndices.addPair(template, globalIndex);
			mIndicesToFunctions.addPair(globalIndex, template);
		}
	}

	/**
	 * Given a TransFormula with possibly array accesses or uninterpreted function calls, returns a new TransFormula,
	 * where these are replaced. In general an overapproximation is returned.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor
	 * <p>
	 * This method ignores the index analysis
	 *
	 * @param transformula
	 *            The old TransFormulaLR, which might contain arrays accesses
	 * @return A TransFormulaLR, where array accesses are replaced by ReplacementVars
	 */
	public TransFormulaLR getRewrittenTransFormula(final TransFormulaLR transformula) {
		final EqualityAnalysisResult emptyResult = new EqualityAnalysisResult(mDoubletons);
		return getRewrittenTransFormula(transformula, emptyResult, emptyResult, false);
	}

	/**
	 * Given a TransFormula with possibly array accesses or uninterpreted function calls, returns a new TransFormula,
	 * where these are replaced. In general an overapproximation is returned.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor
	 *
	 * @param transformula
	 *            The old TransFormulaLR, which might contain arrays accesses
	 * @param equalityAnalysisBefore
	 *            The invariants that are valid before the transformula
	 * @param equalityAnalysisAfter
	 *            The invariants that are valid after the transformula
	 * @param overapproximate
	 *            If true, a slightly weaker, but also smaller formula is returned
	 * @return A TransFormulaLR, where array accesses are replaced by ReplacementVars
	 */
	public TransFormulaLR getRewrittenTransFormula(final TransFormulaLR transformula,
			final EqualityAnalysisResult equalityAnalysisBefore, final EqualityAnalysisResult equalityAnalysisAfter,
			final boolean overapproximate) {
		assert mTransFormulas.contains(transformula);
		final TransFormulaLR newTF = new TransFormulaLR(transformula);
		final Term originalTerm = newTF.getFormula();
		final Set<Term> assignedVars = new HashSet<>();
		for (final IProgramVar var : transformula.getAssignedVars()) {
			assignedVars.add(ReplacementVarUtils.getDefinition(var));
		}
		final HashRelation<ApplicationTermTemplate, ArrayIndex> localIndices = new HashRelation<>();
		for (final ApplicationTermTemplate array : mFunctionsToIndices.getDomain()) {
			for (final ArrayIndex globalIndex : mFunctionsToIndices.getImage(array)) {
				for (final ArrayIndex index : getInOutVarIndices(globalIndex, newTF, assignedVars)) {
					localIndices.addPair(array, index);
				}
			}
		}
		final Set<Doubleton<Term>> doubletons = computeDoubletons(localIndices);
		final IndexAnalyzer indexAnalyzer = new IndexAnalyzer(originalTerm, doubletons, mSymbolTable, newTF,
				equalityAnalysisBefore, equalityAnalysisAfter, mLogger, mReplacementVarFactory);
		final EqualityAnalysisResult invariants = indexAnalyzer.getResult();
		final List<Term> conjuncts = new ArrayList<Term>();
		// Handle reads and writes
		final Term processedTerm = process(originalTerm, newTF, assignedVars, invariants, overapproximate);
		conjuncts.addAll(Arrays.asList(SmtUtils.getConjuncts(processedTerm)));
		// Handle array havoc's
		for (final Term array : getHavocedArrays(newTF)) {
			processArrayHavoc(newTF, array, assignedVars);
		}
		conjuncts.addAll(getReplacementVarEqualities(newTF, assignedVars, invariants, true, overapproximate));
		conjuncts.addAll(getReplacementVarEqualities(newTF, assignedVars, invariants, false, overapproximate));
		conjuncts.addAll(invariants.constructListOfEqualities(mScript));
		if (!overapproximate) {
			conjuncts.addAll(invariants.constructListOfNotEquals(mScript));
		}
		setFormulaAndSimplify(newTF, conjuncts);
		return newTF;
	}

	private List<Term> getReplacementVarEqualities(final TransFormulaLR transformula, final Set<Term> assignedVars,
			final EqualityAnalysisResult invariants, final boolean returnInVar, final boolean overapproximate) {
		final List<Term> result = new ArrayList<>();
		final Set<ArrayIndex> hasEqualIndex = new HashSet<>();
		for (final ApplicationTermTemplate template : mFunctionsToIndices.getDomain()) {
			final Set<ArrayIndex> indicesSet = mFunctionsToIndices.getImage(template);
			final ArrayIndex[] indices = indicesSet.toArray(new ArrayIndex[indicesSet.size()]);
			for (int i = 0; i < indices.length; i++) {
				for (int j = i + 1; j < indices.length; j++) {
					final ArrayIndex index1 = getLocalIndex(indices[i], transformula, assignedVars, returnInVar);
					final ArrayIndex index2 = getLocalIndex(indices[j], transformula, assignedVars, returnInVar);
					if (areIndicesEqual(index1, index2, invariants)) {
						hasEqualIndex.add(indices[i]);
						hasEqualIndex.add(indices[j]);
						final Term term1 = getLocalTerm(template.getTerm(indices[i]), transformula, assignedVars,
								returnInVar);
						final Term term2 = getLocalTerm(template.getTerm(indices[j]), transformula, assignedVars,
								returnInVar);
						result.add(SmtUtils.binaryEquality(mScript, term1, term2));
					}
				}
			}
		}
		// For out vars also add some constraints for assigned indices
		// TODO: If overapproximate = false, maybe do things like on earlier processIndexAssignment
		if (!returnInVar) {
			final Set<Term> assignedIndexTerms = new HashSet<>();
			for (final Term t : assignedVars) {
				assignedIndexTerms.addAll(mVariablesToIndexTerms.getImage(t));
			}
			for (final Term t : assignedIndexTerms) {
				for (final ArrayIndex index : mTermsToIndices.getImage(t)) {
					if (hasEqualIndex.contains(index)) {
						continue;
					}
					for (final ApplicationTermTemplate template : mIndicesToFunctions.getImage(index)) {
						final ArrayIndex inVarIndex = getLocalIndex(index, transformula, assignedVars, true);
						final ArrayIndex outVarIndex = getLocalIndex(index, transformula, assignedVars, false);
						if (!assignedVars.contains(template.getIdentifier())
								&& areIndicesEqual(inVarIndex, outVarIndex, invariants)) {
							final Term term1 = getLocalTerm(template.getTerm(index), transformula, assignedVars, true);
							final Term term2 = getLocalTerm(template.getTerm(index), transformula, assignedVars, false);
							result.add(SmtUtils.binaryEquality(mScript, term1, term2));
						}
					}
				}
			}
		}
		return result;
	}

	private void setFormulaAndSimplify(final TransFormulaLR transformula, final List<Term> conjuncts) {
		Term newTerm;
		if (mAuxVars.isEmpty()) {
			newTerm = SmtUtils.and(mScript, conjuncts);
		} else {
			// If aux-vars have been created, eliminate them
			conjuncts.addAll(mAuxVarTerms);
			final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, mAuxVars,
					SmtUtils.and(mScript, conjuncts));
			newTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMangagedScript, quantified,
					mSimplificationTechnique, mXnfConversionTechnique);
			mAuxVars.clear();
			mSelectToAuxVars.clear();
			mAuxVarTerms.clear();
		}
		if (!SmtUtils.isArrayFree(newTerm)) {
			throw new UnsupportedOperationException("The rewritten transformula still contains arrays!");
		}
		transformula.setFormula(SmtUtils.simplify(mMangagedScript, newTerm, mServices, mSimplificationTechnique));
		clearTransFormula(transformula);
	}

	/**
	 * Remove unnecessary variables from the transformula
	 *
	 * @param transformula
	 */
	private void clearTransFormula(final TransFormulaLR transformula) {
		final List<IProgramVar> inVarsToRemove = new ArrayList<>();
		final List<IProgramVar> outVarsToRemove = new ArrayList<>();
		final List<TermVariable> auxVarsToRemove = new ArrayList<>();
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		for (final Entry<IProgramVar, Term> entry : transformula.getInVars().entrySet()) {
			final Term inVar = entry.getValue();
			final IProgramVar var = entry.getKey();
			if (inVar.getSort().isArraySort()) {
				inVarsToRemove.add(var);
			} else if (!freeVars.contains(inVar) && transformula.getOutVars().get(var) == inVar) {
				inVarsToRemove.add(var);
				outVarsToRemove.add(var);
			}
		}
		for (final Entry<IProgramVar, Term> entry : transformula.getOutVars().entrySet()) {
			final Term outVar = entry.getValue();
			if (outVar.getSort().isArraySort()) {
				outVarsToRemove.add(entry.getKey());
			}
		}
		for (final TermVariable tv : transformula.getAuxVars()) {
			if (!freeVars.contains(tv)) {
				auxVarsToRemove.add(tv);
			}
		}
		for (final IProgramVar var : inVarsToRemove) {
			transformula.removeInVar(var);
		}
		for (final IProgramVar var : outVarsToRemove) {
			transformula.removeOutVar(var);
		}
		for (final TermVariable tv : auxVarsToRemove) {
			transformula.removeAuxVar(tv);
		}
	}

	private Set<Term> getHavocedArrays(final TransFormulaLR transformula) {
		final Set<Term> result = new HashSet<>();
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		for (final ApplicationTermTemplate template : mFunctionsToIndices.getDomain()) {
			if (template instanceof SelectTemplate) {
				assert template.getIdentifier() instanceof TermVariable;
				final TermVariable array = (TermVariable) template.getIdentifier();
				final IProgramVar var = mSymbolTable.getBoogieVar(array);
				final Term inVar = transformula.getInVars().get(var);
				final Term outVar = transformula.getOutVars().get(var);
				if (inVar != outVar && !freeVars.contains(outVar)) {
					result.add(array);
				}
			}
		}
		return result;
	}

	/**
	 * A recursive method, that returns an array-free term, which replaces {@code term} and adds the neeeded
	 * in-/out-vars to {@code transformula}
	 *
	 * @param term
	 *            The term to be replaced
	 * @param transformula
	 *            The new TransFormulaLR (in-/out-vars are added)
	 * @param assignedVars
	 *            A set of vars, that have been assigned
	 * @param invariants
	 * @param overapproximate
	 * @return A new array-free term
	 */
	// TODO: Use non-recursive version
	private Term process(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars,
			final EqualityAnalysisResult invariants, final boolean overapproximate) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			final FunctionSymbol function = a.getFunction();
			if ("select".equals(function.getName()) || !function.isIntern()) {
				// Handle array read / uf-call
				return processRead(term, transformula, assignedVars, invariants, overapproximate);
			}
			final Term[] params = a.getParameters();
			if ("=".equals(function.getName()) && params[0].getSort().isArraySort()) {
				// Handle array assignment
				return processArrayAssignment(term, transformula, assignedVars, invariants, overapproximate);
			}
			// Process recursively
			final int length = params.length;
			final Term[] newParams = new Term[length];
			for (int i = 0; i < length; i++) {
				newParams[i] = process(params[i], transformula, assignedVars, invariants, overapproximate);
			}
			final Term newTerm = mScript.term(function.getName(), newParams);
			return newTerm;
		}
		return term;
	}

	private ArrayIndex processArrayIndex(final ArrayIndex arrayIndex, final TransFormulaLR transformula,
			final Set<Term> assignedVars, final EqualityAnalysisResult invariants, final boolean overapproximate) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : arrayIndex) {
			list.add(process(t, transformula, assignedVars, invariants, overapproximate));
		}
		return new ArrayIndex(list);
	}

	private Term processRead(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars,
			final EqualityAnalysisResult invariants, final boolean overapproximate) {
		if ("select".equals(((ApplicationTerm) term).getFunction().getName())) {
			final MultiDimensionalSelect multiDimensionalSelect = new MultiDimensionalSelect(term);
			final Term array = multiDimensionalSelect.getArray();
			// If there is a select-store-expression, create an aux-var
			if (SmtUtils.isFunctionApplication(array, "store")) {
				final ArrayIndex index = multiDimensionalSelect.getIndex();
				final ArrayWrite arrayWrite = new ArrayWrite(array);
				final Set<ArrayIndex> processedIndices = new HashSet<>();
				final TermVariable auxVar = mMangagedScript.constructFreshTermVariable("aux", term.getSort());
				mAuxVars.add(auxVar);
				for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
					final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), transformula, assignedVars,
							invariants, overapproximate);
					if (processedIndices.contains(assignedIndex)) {
						continue;
					}
					final Term value = process(store.getValue(), transformula, assignedVars, invariants,
							overapproximate);
					final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex,
							processedIndices, auxVar, value, invariants);
					mAuxVarTerms.add(newTerm);
					processedIndices.add(assignedIndex);
				}
				final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, arrayWrite.getOldArray(), index);
				final Term newTerm = processRead(selectTerm, transformula, assignedVars, invariants, overapproximate);
				final Term arrayRead = indexEqualityInequalityImpliesValueEquality(index, index, processedIndices,
						auxVar, newTerm, invariants);
				mAuxVarTerms.add(arrayRead);
				return auxVar;
			}
		}
		// Otherwise just return the corresponding variable
		final Term globalTerm = translateTermVariablesToDefinitions(mScript, transformula, term);
		if (allVariablesAreInVars(term, transformula)) {
			return getLocalTerm(globalTerm, transformula, assignedVars, true);
		}
		if (allVariablesAreOutVars(term, transformula)) {
			return getLocalTerm(globalTerm, transformula, assignedVars, false);
		}
		// If the term contains "mixed" vars or aux-vars, an aux-var is returned
		if (!mSelectToAuxVars.containsKey(term)) {
			final TermVariable auxVar = mMangagedScript.constructFreshTermVariable("aux", term.getSort());
			mAuxVars.add(auxVar);
			mSelectToAuxVars.put(term, auxVar);
		}
		return mSelectToAuxVars.get(term);
	}

	private Term processArrayAssignment(final Term term, final TransFormulaLR transformula,
			final Set<Term> assignedVars, final EqualityAnalysisResult invariants, final boolean overapproximate) {
		final ArrayWrite arrayWrite = new ArrayWrite(term);
		final Term oldArray = arrayWrite.getOldArray();
		final Term newArray = arrayWrite.getNewArray();
		// If the old or new array is an aux-var, just return true
		if (!allVariablesAreVisible(oldArray, transformula) || !allVariablesAreVisible(newArray, transformula)) {
			return mScript.term("true");
		}
		final List<Term> result = new ArrayList<>();
		final Term globalOldArray = translateTermVariablesToDefinitions(mScript, transformula, oldArray);
		final Term globalNewArray = translateTermVariablesToDefinitions(mScript, transformula, newArray);
		final SelectTemplate oldTemplate = new SelectTemplate(globalOldArray, mScript);
		final SelectTemplate newTemplate = new SelectTemplate(globalNewArray, mScript);
		final Set<ArrayIndex> assignedIndices = new HashSet<>();
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			final ArrayIndex assignedIndex = processArrayIndex(store.getIndex(), transformula, assignedVars, invariants,
					overapproximate);
			if (assignedIndices.contains(assignedIndex)) {
				continue;
			}
			final Term value = process(store.getValue(), transformula, assignedVars, invariants, overapproximate);
			for (final ArrayIndex globalIndex : mFunctionsToIndices.getImage(newTemplate)) {
				final ArrayIndex index = getLocalIndex(globalIndex, transformula, assignedVars, false);
				if (assignedIndices.contains(index)) {
					continue;
				}
				if (overapproximate && !areIndicesEqual(index, assignedIndex, invariants)) {
					continue;
				}
				final Term selectTerm = newTemplate.getTerm(globalIndex);
				final Term var = getLocalTerm(selectTerm, transformula, assignedVars, false);
				final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex, assignedIndices,
						var, value, invariants);
				result.add(newTerm);
			}
			assignedIndices.add(assignedIndex);
		}
		// For un-assigned indices i add: newArray[i] = oldArray[i]
		if (!overapproximate) {
			for (final ArrayIndex globalIndex : mFunctionsToIndices.getImage(oldTemplate)) {
				final Term selectNew = newTemplate.getTerm(globalIndex);
				final Term selectOld = oldTemplate.getTerm(globalIndex);
				final boolean oldIsInVar = transformula.getInVarsReverseMapping().containsKey(oldArray);
				final Term varOld = getLocalTerm(selectOld, transformula, assignedVars, oldIsInVar);
				final boolean newIsInVar = transformula.getInVarsReverseMapping().containsKey(newArray);
				final Term varNew = getLocalTerm(selectNew, transformula, assignedVars, newIsInVar);
				final ArrayIndex indexIn = getLocalIndex(globalIndex, transformula, assignedVars, true);
				final ArrayIndex indexOut = getLocalIndex(globalIndex, transformula, assignedVars, false);
				final Term newTerm = indexEqualityInequalityImpliesValueEquality(indexOut, indexIn, assignedIndices,
						varNew, varOld, invariants);
				result.add(newTerm);
			}
		}
		return SmtUtils.and(mScript, result);
	}

	private void processArrayHavoc(final TransFormulaLR transformula, final Term array, final Set<Term> assignedVars) {
		// Just different in- and out-vars for all arrays cells of the given array
		final SelectTemplate template = new SelectTemplate(array, mScript);
		for (final ArrayIndex index : mFunctionsToIndices.getImage(template)) {
			// This creates different in- and out-vars if not existing
			getLocalTerm(template.getTerm(index), transformula, assignedVars, true);
		}
	}

	/**
	 * Given a global term (=definition), adds the in- and out-vars to the transformula and returns the term with in- or
	 * out-vars
	 *
	 * @param term
	 *            A SMT-Term wit
	 * @param transformula
	 *            A TransFormulaLR
	 * @param assignedVars
	 *            The set of global vars which have been assigend
	 * @param returnInVar
	 *            Switch between in- and out-vars
	 * @return The local term (with in- or out-vars) for the given global term
	 */
	private Term getLocalTerm(final Term term, final TransFormulaLR transformula, final Set<Term> assignedVars,
			final boolean returnInVar) {
		if (term instanceof ConstantTerm) {
			return term;
		}
		IProgramVar var = null;
		if (term instanceof TermVariable) {
			var = mSymbolTable.getBoogieVar((TermVariable) term);
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm a = (ApplicationTerm) term;
			if (a.getFunction().isIntern() && !"select".equals(a.getFunction().getName())) {
				final int length = a.getParameters().length;
				final Term[] newParams = new Term[length];
				for (int i = 0; i < length; i++) {
					newParams[i] = getLocalTerm(a.getParameters()[i], transformula, assignedVars, returnInVar);
				}
				return mScript.term(a.getFunction().getName(), newParams);
			} else {
				var = mReplacementVarFactory.getOrConstuctReplacementVar(term);
			}
		}
		// If any of the free vars has been assigned, create different in- and out-vars
		boolean isAssigned = false;
		for (final TermVariable t : term.getFreeVars()) {
			if (assignedVars.contains(t)) {
				isAssigned = true;
				break;
			}
		}
		final Term termVar = getFreshTermVar(term);
		if (!transformula.getInVars().containsKey(var)) {
			transformula.addInVar(var, termVar);
		}
		if (!transformula.getOutVars().containsKey(var)) {
			if (isAssigned) {
				transformula.addOutVar(var, getFreshTermVar(term));
			} else {
				transformula.addOutVar(var, termVar);
			}
		}

		if (returnInVar) {
			return transformula.getInVars().get(var);
		} else {
			return transformula.getOutVars().get(var);
		}
	}

	private ArrayIndex getLocalIndex(final ArrayIndex globalIndex, final TransFormulaLR transformula,
			final Set<Term> assignedVars, final boolean returnInVar) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : globalIndex) {
			list.add(getLocalTerm(t, transformula, assignedVars, returnInVar));
		}
		return new ArrayIndex(list);
	}

	// Returns a fresh TermVariable with term as definition (with a nicer name for select-terms)
	private TermVariable getFreshTermVar(final Term term) {
		return mMangagedScript.constructFreshTermVariable(niceTermString(term), term.getSort());
	}

	private String niceTermString(final Term term) {
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final StringBuilder stringBuilder = new StringBuilder();
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			stringBuilder.append("array_").append((niceTermString(select.getArray()))).append('[');
			final ArrayIndex index = select.getIndex();
			for (int i = 0; i < index.size(); i++) {
				stringBuilder.append(niceTermString(index.get(i))).append(i == index.size() - 1 ? ']' : ',');
			}
			return stringBuilder.toString();
		}
		if (term instanceof TermVariable) {
			final TermVariable termVariable = (TermVariable) term;
			return termVariable.getName();
		}
		if (term instanceof ApplicationTerm) {
			final StringBuilder stringBuilder = new StringBuilder();
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final FunctionSymbol function = applicationTerm.getFunction();
			if (!function.isIntern()) {
				stringBuilder.append("uf_");
			}
			stringBuilder.append('(').append(function.getApplicationString()).append(' ');
			final Term[] params = applicationTerm.getParameters();
			for (int i = 0; i < params.length; i++) {
				stringBuilder.append(niceTermString(params[i])).append(i == params.length - 1 ? ')' : ' ');
			}
			return stringBuilder.toString();

		}
		return term.toString();
	}

	private Set<Doubleton<Term>> computeDoubletons(
			final HashRelation<ApplicationTermTemplate, ArrayIndex> hashRelation) {
		final Set<Doubleton<Term>> result = new HashSet<>();
		for (final ApplicationTermTemplate template : hashRelation.getDomain()) {
			final Set<ArrayIndex> indicesSet = hashRelation.getImage(template);
			final ArrayIndex[] indices = indicesSet.toArray(new ArrayIndex[indicesSet.size()]);
			for (int i = 0; i < indices.length; i++) {
				for (int j = i + 1; j < indices.length; j++) {
					final ArrayIndex index1 = indices[i];
					final ArrayIndex index2 = indices[j];
					for (int k = 0; k < index1.size(); k++) {
						final Term term1 = index1.get(k);
						final Term term2 = index2.get(k);
						if (term1 != term2) {
							result.add(new Doubleton<Term>(term1, term2));
						}
					}
				}
			}
		}
		return result;
	}

	public Set<Doubleton<Term>> getDoubletons() {
		return mDoubletons;
	}

	private boolean areIndicesEqual(final ArrayIndex index1, final ArrayIndex index2,
			final EqualityAnalysisResult invariants) {
		for (int i = 0; i < index1.size(); i++) {
			final Term term1 = index1.get(i);
			final Term term2 = index2.get(i);
			if (term1 != term2 && !invariants.getEqualDoubletons().contains(new Doubleton<>(term1, term2))) {
				return false;
			}
		}
		return true;
	}

	private Term getEqualTerm(final ArrayIndex index1, final ArrayIndex index2,
			final EqualityAnalysisResult invariants) {
		Term result = mScript.term("true");
		for (int i = 0; i < index1.size(); i++) {
			final Term term1 = index1.get(i);
			final Term term2 = index2.get(i);
			if (term1 == term2) {
				continue;
			}
			final Doubleton<Term> doubleton = new Doubleton<>(term1, term2);
			if (invariants.getDistinctDoubletons().contains(doubleton)) {
				return mScript.term("false");
			}
			if (!invariants.getEqualDoubletons().contains(doubleton)) {
				result = Util.and(mScript, result, SmtUtils.binaryEquality(mScript, term1, term2));
			}
		}
		return result;
	}

	private Term indexEqualityInequalityImpliesValueEquality(final ArrayIndex index, final ArrayIndex equal,
			final Collection<ArrayIndex> unequal, final Term value1, final Term value2,
			final EqualityAnalysisResult invariants) {
		Term lhs = getEqualTerm(index, equal, invariants);
		for (final ArrayIndex i : unequal) {
			lhs = Util.and(mScript, lhs, Util.not(mScript, getEqualTerm(index, i, invariants)));
		}
		final Term rhs = SmtUtils.binaryEquality(mScript, value1, value2);
		final Term result = Util.or(mScript, SmtUtils.not(mScript, lhs), rhs);
		return result;
	}

	private Set<ArrayIndex> getInOutVarIndices(final ArrayIndex index, final TransFormulaLR transformula,
			final Set<Term> assignedVars) {
		Set<List<Term>> lists = new HashSet<>();
		lists.add(new ArrayList<Term>());
		for (final Term t : index) {
			final Set<List<Term>> newLists = new HashSet<>();
			final Term termIn = getLocalTerm(t, transformula, assignedVars, true);
			final Term termOut = getLocalTerm(t, transformula, assignedVars, false);
			for (final List<Term> list : lists) {
				final List<Term> listIn = new ArrayList<>(list);
				listIn.add(termIn);
				newLists.add(listIn);
				final List<Term> listOut = new ArrayList<>(list);
				listOut.add(termOut);
				newLists.add(listOut);
			}
			lists = newLists;
		}
		final Set<ArrayIndex> result = new HashSet<>();
		for (final List<Term> list : lists) {
			result.add(new ArrayIndex(list));
		}
		return result;
	}
}

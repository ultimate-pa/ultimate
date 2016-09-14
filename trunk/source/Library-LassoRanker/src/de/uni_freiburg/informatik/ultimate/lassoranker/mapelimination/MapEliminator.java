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

import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLRUtils.allVariablesAreInVars;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLRUtils.allVariablesAreOutVars;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLRUtils.allVariablesAreVisible;
import static de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLRUtils.translateTermVariablesToDefinitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
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
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final ILogger mLogger;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	// Stores for each variable, which indices contain it
	private final HashRelation<Term, ArrayIndex> mVariablesToIndices;

	// Stores for each array, which indices access it (bidirectional)
	private final HashRelation<ApplicationTermTemplate, ArrayIndex> mFunctionsToIndices;
	private final HashRelation<ArrayIndex, ApplicationTermTemplate> mIndicesToFunctions;

	// Additional conjuncts, that refine the created aux-vars
	private List<Term> mAdditionalConjuncts;

	// The created aux-vars (needed for quantifier-elimination)
	private final Set<TermVariable> mAuxVars;

	// Stores information about the arrays that get assigned to another array (then these arrays have the same indices)
	private final Set<Doubleton<Term>> mRelatedArays;

	// Stores all doubletons of terms, which might be compared
	private final Set<Doubleton<Term>> mDoubletons;

	// Stores all function-names of the uninterpreted functions (to know, what function-calls have to be replaced)^
	private final Set<String> mUninterpretedFunctions;

	// Stores for each transformula, which arrays/uf-calls are accssed in it
	private final Map<TransFormulaLR, HashRelation<ApplicationTermTemplate, ArrayIndex>> mTransFormulasToLocalIndices;

	// Settings
	private final boolean mAddInequalities;
	private final boolean mOnlyTrivialImplicationsIndexAssignment;
	private final boolean mOnlyTrivialImplicationsArrayWrite;
	private final boolean mOnlyIndicesInFormula;

	/**
	 * Creates a new map eliminator and preprocesses (stores the indices and arrays used in the {@code transformulas})
	 *
	 * @param services
	 *            UltimateServices
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            Boogie2SmtSymbolTable
	 * @param replacementVarFactory
	 *            ReplacementVarFactory
	 * @param simplificationTechnique
	 *            SimplicationTechnique
	 * @param xnfConversionTechnique
	 *            XnfConversionTechnique
	 * @param transformulas
	 *            The transformulas, that should be processed
	 * @param addInequalities
	 *            If true, inequalities provided by the IndexAnalysis are also added as conjuncts to the transformula
	 *            (should be disabled for the LassoRanker).
	 * @param onlyTrivialImplicationsIndexAssignment
	 *            If true, implications such as (i = j) => (a[i] = a[j]), that occur during handling assignments of
	 *            indices, are only added as conjuncts to the transformula, if the invariant i = j holds (so in this
	 *            case only a[i] = a[j] is added).
	 * @param onlyTrivialImplicationsArrayWrite
	 *            If true, implications such as (i = j) => (a[i] = a[j]), that occur during handling array-writes, are
	 *            only added as conjuncts to the transformula, if the invariant i = j holds (so in this case only a[i] =
	 *            a[j] is added)
	 * @param onlyIndicesInFormula
	 *            If true, implications such as (i = j) => (a[i] = a[j]) are only added as conjuncts to the
	 *            transformula, if all free-vars of i and j occur in the transformula
	 */
	public MapEliminator(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final Boogie2SmtSymbolTable symbolTable, final ReplacementVarFactory replacementVarFactory,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Collection<TransFormulaLR> transformulas, final boolean addInequalities,
			final boolean onlyTrivialImplicationsIndexAssignment, final boolean onlyTrivialImplicationsArrayWrite,
			final boolean onlyIndicesInFormula) {
		super();

		mServices = services;
		mScript = managedScript.getScript();
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mManagedScript = managedScript;
		mReplacementVarFactory = replacementVarFactory;
		mSymbolTable = symbolTable;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;

		mTransFormulasToLocalIndices = new HashMap<>();

		mVariablesToIndices = new HashRelation<>();
		mFunctionsToIndices = new HashRelation<>();
		mIndicesToFunctions = new HashRelation<>();

		mAuxVars = new HashSet<>();
		mAdditionalConjuncts = new ArrayList<>();

		mRelatedArays = new HashSet<>();
		mUninterpretedFunctions = new HashSet<>();

		mAddInequalities = addInequalities;
		mOnlyTrivialImplicationsIndexAssignment = onlyTrivialImplicationsIndexAssignment;
		mOnlyTrivialImplicationsArrayWrite = onlyTrivialImplicationsArrayWrite;
		mOnlyIndicesInFormula = onlyIndicesInFormula;

		findAllIndices(transformulas);
		mDoubletons = computeDoubletons(mFunctionsToIndices);
	}

	/**
	 * Finds the array accesses in the transformulas and merges the indices if necessary
	 *
	 * @param transformulas
	 */
	private void findAllIndices(final Collection<TransFormulaLR> transformulas) {
		// Get all array indices from each transformula (only necessary, if it contains arrays)
		for (final TransFormulaLR tf : transformulas) {
			mTransFormulasToLocalIndices.put(tf, new HashRelation<>());
			findIndices(tf);
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
	}

	/**
	 * A method that finds arrays and their indices in the given {@code transformula} and stores them in the maps
	 *
	 * @param transformula
	 */
	private void findIndices(final TransFormulaLR transformula) {
		final Term term = transformula.getFormula();
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectDeep(term, false)) {
			final ArrayWrite arrayWrite = new ArrayWrite(select.getArray());
			findIndicesArrayWrite(arrayWrite, transformula);
			addArrayAccessToRelation(arrayWrite.getOldArray(), select.getIndex(), transformula);
		}
		for (final ApplicationTerm t : new ApplicationTermFinder("=", false).findMatchingSubterms(term)) {
			if (t.getParameters()[0].getSort().isArraySort()) {
				final ArrayWrite arrayWrite = new ArrayWrite(t);
				// The new array can be also a store-expression, so also find indices in this expression
				final ArrayWrite arrayWrite2 = new ArrayWrite(arrayWrite.getNewArray());
				findIndicesArrayWrite(arrayWrite, transformula);
				findIndicesArrayWrite(arrayWrite2, transformula);
				final Term array1 = arrayWrite.getOldArray();
				final Term array2 = arrayWrite2.getOldArray();
				if (allVariablesAreVisible(array1, transformula) && allVariablesAreVisible(array2, transformula)) {
					final Term globalArray1 = translateTermVariablesToDefinitions(mScript, transformula, array1);
					final Term globalArray2 = translateTermVariablesToDefinitions(mScript, transformula, array2);
					// If the two arrays are different, add them to the set of related arrays
					// (the indices need to be shared then)
					if (globalArray1 != globalArray2) {
						mRelatedArays.add(new Doubleton<Term>(globalArray1, globalArray2));
					}
				}
			}
		}
		for (final NonTheorySymbol<?> s : new NonTheorySymbolFinder().findNonTheorySymbols(term)) {
			final Object symbol = s.getSymbol();
			if (symbol instanceof FunctionSymbol) {
				final String function = ((FunctionSymbol) symbol).getName();
				for (final ApplicationTerm t : new ApplicationTermFinder(function, false).findMatchingSubterms(term)) {
					final ArrayIndex index = new ArrayIndex(Arrays.asList(t.getParameters()));
					addCallToRelation(function, index, transformula);
				}
			}
		}
	}

	private void findIndicesArrayWrite(final ArrayWrite arrayWrite, final TransFormulaLR transformula) {
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			addArrayAccessToRelation(arrayWrite.getOldArray(), store.getIndex(), transformula);
		}
	}

	/**
	 * Adds the info, that {@code array} is accessed by {@code index} to the hash relations
	 */
	private void addArrayAccessToRelation(final Term array, final ArrayIndex index, final TransFormulaLR transformula) {
		if (allVariablesAreVisible(array, transformula) && isIndexAdded(index, transformula)) {
			final ArrayIndex globalIndex = new ArrayIndex(
					translateTermVariablesToDefinitions(mScript, transformula, index));
			final Term globalArray = translateTermVariablesToDefinitions(mScript, transformula, array);
			for (final TermVariable var : globalIndex.getFreeVars()) {
				mVariablesToIndices.addPair(var, globalIndex);
			}
			final SelectTemplate template = new SelectTemplate(globalArray, mScript);
			mFunctionsToIndices.addPair(template, globalIndex);
			mIndicesToFunctions.addPair(globalIndex, template);
			final Term inVarArray = getLocalTerm(globalArray, transformula, true);
			final Term outVarArray = getLocalTerm(globalArray, transformula, false);
			mTransFormulasToLocalIndices.get(transformula).addPair(new SelectTemplate(inVarArray, mScript), index);
			mTransFormulasToLocalIndices.get(transformula).addPair(new SelectTemplate(outVarArray, mScript), index);
		}
	}

	/**
	 * Adds the info, that the function with name {@code functionName} is applied to {@code index} to the hash relations
	 */
	private void addCallToRelation(final String functionName, final ArrayIndex index,
			final TransFormulaLR transformula) {
		if (!index.isEmpty()) {
			mUninterpretedFunctions.add(functionName);
		}
		if (isIndexAdded(index, transformula)) {
			final ArrayIndex globalIndex = new ArrayIndex(
					translateTermVariablesToDefinitions(mScript, transformula, index));
			for (final TermVariable var : globalIndex.getFreeVars()) {
				mVariablesToIndices.addPair(var, globalIndex);
			}
			final FunctionTemplate template = new FunctionTemplate(functionName, mScript);
			mFunctionsToIndices.addPair(template, globalIndex);
			mIndicesToFunctions.addPair(globalIndex, template);
			mTransFormulasToLocalIndices.get(transformula).addPair(template, index);
		}
	}

	/**
	 * Returns true iff the index should be added to the hash-relations. This is the case, if it contains neither
	 * aux-vars nor store-expressions
	 */
	private static boolean isIndexAdded(final ArrayIndex index, final TransFormulaLR transformula) {
		if (!allVariablesAreVisible(index, transformula)) {
			return false;
		}
		for (final Term t : index) {
			if (!new ApplicationTermFinder("store", true).findMatchingSubterms(t).isEmpty()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Given a TransFormula with possibly array accesses or calls of uninterpreted functions, returns a new
	 * TransFormula, where these are replaced. In general an overapproximation is returned.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor
	 * <p>
	 * This method ignores the index analysis
	 *
	 * @param transformula
	 *            The old TransFormulaLR, which might contain arrays accesses
	 * @return A TransFormulaLR, where array accesses and calls of uninterpreted functions are replaced
	 */
	public TransFormulaLR getRewrittenTransFormula(final TransFormulaLR transformula) {
		final EqualityAnalysisResult emptyResult = new EqualityAnalysisResult(mDoubletons);
		return getRewrittenTransFormula(transformula, emptyResult, emptyResult);
	}

	/**
	 * Given a TransFormula with possibly array accesses or calls of uninterpreted functions, returns a new
	 * TransFormula, where these are replaced. In general an overapproximation is returned.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor
	 *
	 * @param transformula
	 *            The old TransFormulaLR, which might contain arrays accesses
	 * @param equalityAnalysisBefore
	 *            The invariants that are valid before the transformula
	 * @param equalityAnalysisAfter
	 *            The invariants that are valid after the transformula
	 * @return A TransFormulaLR, where array accesses and calls of uninterpreted functions are replaced
	 */
	public TransFormulaLR getRewrittenTransFormula(final TransFormulaLR transformula,
			final EqualityAnalysisResult equalityAnalysisBefore, final EqualityAnalysisResult equalityAnalysisAfter) {
		assert mTransFormulasToLocalIndices.containsKey(transformula) : "This transformula wasn't preprocessed";
		final TransFormulaLR newTF = new TransFormulaLR(transformula);
		final Term originalTerm = newTF.getFormula();
		final Set<Term> assignedVars = new HashSet<>();
		for (final IProgramVar var : transformula.getAssignedVars()) {
			assignedVars.add(ReplacementVarUtils.getDefinition(var));
		}
		final HashRelation<ApplicationTermTemplate, ArrayIndex> localIndices = mTransFormulasToLocalIndices
				.get(transformula);
		for (final ApplicationTermTemplate globalTemplate : mFunctionsToIndices.getDomain()) {
			for (final ApplicationTermTemplate template : getLocalTemplates(globalTemplate, newTF)) {
				for (final ArrayIndex index : getInAndOutVarIndices(mFunctionsToIndices.getImage(globalTemplate),
						newTF)) {
					localIndices.addPair(template, index);
				}
			}
		}
		final IndexAnalyzer indexAnalyzer = new IndexAnalyzer(originalTerm, computeDoubletons(localIndices),
				mSymbolTable, newTF, equalityAnalysisBefore, equalityAnalysisAfter, mLogger, mReplacementVarFactory);
		final EqualityAnalysisResult invariants = indexAnalyzer.getResult();
		// Replace store-expressions
		final Term storeFreeTerm = replaceStoreExpressions(originalTerm, newTF, invariants);
		final List<Term> conjuncts = new ArrayList<Term>();
		conjuncts.addAll(Arrays.asList(SmtUtils.getConjuncts(storeFreeTerm)));
		conjuncts.addAll(mAdditionalConjuncts);
		conjuncts.addAll(getReplacementVarEqualities(newTF, localIndices, invariants));
		if (!mOnlyTrivialImplicationsIndexAssignment) {
			conjuncts.addAll(getAllImplicationsForIndexAssignment(assignedVars, newTF, invariants));
		}
		conjuncts.addAll(invariants.constructListOfEqualities(mScript));
		if (mAddInequalities) {
			conjuncts.addAll(invariants.constructListOfNotEquals(mScript));
		}
		final Term newTerm = SmtUtils.and(mScript, conjuncts);
		final Set<ApplicationTerm> storeTerms = new ApplicationTermFinder("store", true).findMatchingSubterms(newTerm);
		assert storeTerms.isEmpty() : "The formula contains still store-expressions";
		final Term replacedTerm = replaceReadExpressions(newTF, newTerm);
		setFormulaAndSimplify(newTF, replacedTerm);
		return newTF;
	}

	/**
	 * Returns all equalites of replacement-variables based on the index analysis. To reduce the number of conjuncts,
	 * UnionFind is used.
	 *
	 * @param transformula
	 *            A TransFormulaLR
	 * @param localIndices
	 *            A HashRelation, which maps all ApplicationTermTemplates, which are considered to the needed local
	 *            indices.
	 * @param invariants
	 *            The valid invariants at this transformula
	 * @return A list of terms (= conjuncts) with equalities that are valid at this transformula
	 */
	private List<Term> getReplacementVarEqualities(final TransFormulaLR transformula,
			final HashRelation<ApplicationTermTemplate, ArrayIndex> localIndices,
			final EqualityAnalysisResult invariants) {
		final List<Term> result = new ArrayList<>();
		for (final ApplicationTermTemplate template : localIndices.getDomain()) {
			final UnionFind<ArrayIndex> unionFind = new UnionFind<>();
			final Set<ArrayIndex> indicesSet = localIndices.getImage(template);
			final ArrayIndex[] indices = indicesSet.toArray(new ArrayIndex[indicesSet.size()]);
			for (int i = 0; i < indices.length; i++) {
				for (int j = i + 1; j < indices.length; j++) {
					if (areIndicesEqual(indices[i], indices[j], invariants)) {
						unionFind.findAndConstructEquivalenceClassIfNeeded(indices[i]);
						unionFind.findAndConstructEquivalenceClassIfNeeded(indices[j]);
						unionFind.union(indices[i], indices[j]);
					}
				}
			}
			for (final ArrayIndex index1 : unionFind.getAllRepresentatives()) {
				for (final ArrayIndex index2 : unionFind.getEquivalenceClassMembers(index1)) {
					if (index1 == index2) {
						continue;
					}
					result.add(SmtUtils.binaryEquality(mScript, template.getTerm(index1), template.getTerm(index2)));
				}
			}
		}
		return result;
	}

	/**
	 * This methods eliminates aux-var from the term, sets it to the transformula and simplifies the transformula then
	 *
	 * @param transformula
	 * @param conjuncts
	 */
	private void setFormulaAndSimplify(final TransFormulaLR transformula, final Term term) {
		// store-expressions have already be replaced
		// It remains to replace select-expressions and uf-calls by introducing replacementVars
		Term newTerm;
		if (mAuxVars.isEmpty()) {
			newTerm = term;
		} else {
			// If aux-vars have been created, eliminate them
			final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, mAuxVars, term);
			newTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, quantified,
					mSimplificationTechnique, mXnfConversionTechnique);
			// To be safe add all created aux-vars to the transformula (if not needed they're removed again)
			transformula.addAuxVars(mAuxVars);
			mAuxVars.clear();
			mAdditionalConjuncts.clear();
		}
		assert SmtUtils.isArrayFree(newTerm) : "The rewritten transformula still contains arrays!";
		transformula.setFormula(SmtUtils.simplify(mManagedScript, newTerm, mServices, mSimplificationTechnique));
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
			// Make sure, constants are not removed from in-/out-vars
			if (SmtUtils.isUninterpretedFunctionCall(inVar)) {
				continue;
			}
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

	/***
	 * Replaces all "simple" select-expressions (without store) and uf-calls int the {@code term} with the replacement-
	 * or aux-vars
	 *
	 * @param transformula
	 * @param term
	 * @return A new term that is free of select's and uf-calls
	 */
	private Term replaceReadExpressions(final TransFormulaLR transformula, final Term term) {
		addReplacementVarsToTransFormula(transformula);
		final Map<Term, Term> substitution = new HashMap<>();
		for (final ApplicationTerm select : new ApplicationTermFinder("select", true).findMatchingSubterms(term)) {
			if (!select.getSort().isArraySort()) {
				substitution.put(select, getReplacementVar(select, transformula));
			}
		}
		for (final String functionName : mUninterpretedFunctions) {
			for (final Term functionCall : new ApplicationTermFinder(functionName, true).findMatchingSubterms(term)) {
				substitution.put(functionCall, getReplacementVar(functionCall, transformula));
			}
		}
		return new Substitution(mManagedScript, substitution).transform(term);
	}

	/***
	 * Adds all replacement-vars as in- and out-vars to the transformula.
	 *
	 * @param transformula
	 */
	private void addReplacementVarsToTransFormula(final TransFormulaLR transformula) {
		for (final ApplicationTermTemplate template : mFunctionsToIndices.getDomain()) {
			for (final ArrayIndex index : mFunctionsToIndices.getImage(template)) {
				final Term term = template.getTerm(index);
				final IProgramVar var = mReplacementVarFactory.getOrConstuctReplacementVar(term);
				boolean containsAssignedVar = false;
				for (final TermVariable tv : term.getFreeVars()) {
					final IProgramVar progVar = mSymbolTable.getBoogieVar(tv);
					if (transformula.getInVars().get(progVar) != transformula.getOutVars().get(progVar)) {
						containsAssignedVar = true;
						break;
					}
				}
				final Term termVar = getFreshTermVar(term);
				if (!transformula.getInVars().containsKey(var)) {
					transformula.addInVar(var, termVar);
				}
				if (!transformula.getOutVars().containsKey(var)) {
					// If the term contains an assigned var, different in- and out-vars are created, otherwise the same
					if (containsAssignedVar) {
						transformula.addOutVar(var, getFreshTermVar(term));
					} else {
						transformula.addOutVar(var, termVar);
					}
				}
			}
		}
	}

	/***
	 * Returns the corresponding replacementVar (or auxVar) for the given {@code term}. The replacementVars have to be
	 * already to it added by calling {@code addReplacementVarsToTransFormula}
	 *
	 * @param term
	 * @param transformula
	 * @return A replacement- or aux-var
	 */
	private Term getReplacementVar(final Term term, final TransFormulaLR transformula) {
		if (!allVariablesAreInVars(term, transformula) && !allVariablesAreOutVars(term, transformula)) {
			return getAndAddAuxVar(term);
		}
		final Term definition = translateTermVariablesToDefinitions(mScript, transformula, term);
		final IProgramVar var = mReplacementVarFactory.getOrConstuctReplacementVar(definition);
		assert transformula.getInVars().containsKey(var) && transformula.getOutVars().containsKey(var) : var
				+ " was not added to the transformula!";
		if (allVariablesAreInVars(term, transformula)) {
			return transformula.getInVars().get(var);
		} else {
			return transformula.getOutVars().get(var);
		}
	}

	/**
	 * This methods replaces all store-expressions in the {@code term} and adds the neeeded in-/out-vars to the
	 * {@code transformula} (The returned term can still contain select-expressions or uninterpreted functions!)
	 *
	 * @param term
	 *            The term to be replaced
	 * @param transformula
	 *            The new TransFormulaLR (in-/out-vars are added)
	 * @param invariants
	 * @return A term, that doen't contain store-expressions
	 */
	private Term replaceStoreExpressions(final Term term, final TransFormulaLR transformula,
			final EqualityAnalysisResult invariants) {
		final Map<Term, Term> substitutionMap = new HashMap<>();
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectDeep(term, false)) {
			if (SmtUtils.isFunctionApplication(select.getArray(), "store")) {
				final Term selectTerm = select.getSelectTerm();
				substitutionMap.put(selectTerm,
						replaceStoreExpressionsInArrayRead(selectTerm, transformula, invariants));
			}
		}
		for (final ApplicationTerm t : new ApplicationTermFinder("=", false).findMatchingSubterms(term)) {
			if (t.getParameters()[0].getSort().isArraySort()) {
				substitutionMap.put(t, replaceStoreExpressionsInArrayWrite(t, transformula, invariants));
			}
		}
		final Substitution substitution = new Substitution(mManagedScript, substitutionMap);
		mAdditionalConjuncts = substitution.transform(mAdditionalConjuncts);
		return substitution.transform(substitution.transform(term));
	}

	/**
	 * Replaces store-expressions in read-expressions (e.g. (select (store a i x) j)) with aux-vars, for which
	 * additional conjuncts are added to mAdditionalConjuncts.
	 *
	 * @param term
	 *            A term of the form: (select (store ...) ...)
	 * @param transformula
	 * @param invariants
	 * @return An aux-var
	 */
	private TermVariable replaceStoreExpressionsInArrayRead(final Term term, final TransFormulaLR transformula,
			final EqualityAnalysisResult invariants) {
		final MultiDimensionalSelect multiDimensionalSelect = new MultiDimensionalSelect(term);
		final ArrayIndex index = multiDimensionalSelect.getIndex();
		final ArrayWrite arrayWrite = new ArrayWrite(multiDimensionalSelect.getArray());
		final Set<ArrayIndex> processedIndices = new HashSet<>();
		final TermVariable auxVar = getAndAddAuxVar(term);
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			final ArrayIndex assignedIndex = store.getIndex();
			if (processedIndices.contains(assignedIndex) || !allVariablesAreVisible(assignedIndex, transformula)) {
				continue;
			}
			final Term value = store.getValue();
			if (areIndicesEqual(index, assignedIndex, invariants)
					&& areAllIndicesUnequal(index, processedIndices, invariants)) {
				mAdditionalConjuncts.add(SmtUtils.binaryEquality(mScript, auxVar, value));
			} else if (!mOnlyTrivialImplicationsArrayWrite) {
				final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex, processedIndices,
						auxVar, value, invariants, transformula);
				mAdditionalConjuncts.add(newTerm);
			}
			processedIndices.add(assignedIndex);
		}
		final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, arrayWrite.getOldArray(), index);
		final Term arrayRead = indexEqualityInequalityImpliesValueEquality(index, index, processedIndices, auxVar,
				selectTerm, invariants, transformula);
		mAdditionalConjuncts.add(arrayRead);
		return auxVar;
	}

	/**
	 * Replaces write accesses of arrays with a term that only contains select-expressions
	 *
	 * @param term
	 *            A term of the form: (= b (store ... (store a i_1 x_1) i_n x_n))
	 * @param transformula
	 * @param invariants
	 * @return A term store-free term
	 */
	private Term replaceStoreExpressionsInArrayWrite(final Term term, final TransFormulaLR transformula,
			final EqualityAnalysisResult invariants) {
		final ArrayWrite arrayWrite = new ArrayWrite(term);
		final Term oldArray = arrayWrite.getOldArray();
		final Term newArray = arrayWrite.getNewArray();
		// If the old or new array is an aux-var, just return true
		// If both arrays are store-expressions, also just return true
		if (!allVariablesAreVisible(oldArray, transformula) || !allVariablesAreVisible(newArray, transformula)
				|| SmtUtils.isFunctionApplication(newArray, "store")) {
			return mScript.term("true");
		}
		final List<Term> result = new ArrayList<>();
		final boolean oldIsInVar = transformula.getInVarsReverseMapping().containsKey(oldArray);
		final boolean newIsInVar = transformula.getInVarsReverseMapping().containsKey(newArray);
		final Term globalOldArray = translateTermVariablesToDefinitions(mScript, transformula, oldArray);
		final Term globalNewArray = translateTermVariablesToDefinitions(mScript, transformula, newArray);
		final SelectTemplate oldTemplate = new SelectTemplate(globalOldArray, mScript);
		final SelectTemplate newTemplate = new SelectTemplate(globalNewArray, mScript);
		final Set<ArrayIndex> processedIndices = new HashSet<>();
		for (final MultiDimensionalStore store : arrayWrite.getStoreList()) {
			final ArrayIndex assignedIndex = store.getIndex();
			if (processedIndices.contains(assignedIndex) || !allVariablesAreVisible(assignedIndex, transformula)) {
				continue;
			}
			final Term value = store.getValue();
			for (final ArrayIndex globalIndex : mFunctionsToIndices.getImage(newTemplate)) {
				final ArrayIndex index = getLocalIndex(globalIndex, transformula, newIsInVar);
				if (processedIndices.contains(index)) {
					continue;
				}
				if (areIndicesEqual(index, assignedIndex, invariants)
						&& areAllIndicesUnequal(index, processedIndices, invariants)) {
					final Term select = getLocalTerm(newTemplate.getTerm(globalIndex), transformula, newIsInVar);
					result.add(SmtUtils.binaryEquality(mScript, select, value));
				} else if (!mOnlyTrivialImplicationsArrayWrite) {
					final Term select = getLocalTerm(newTemplate.getTerm(globalIndex), transformula, newIsInVar);
					final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex,
							processedIndices, select, value, invariants, transformula);
					result.add(newTerm);
				}

			}
			processedIndices.add(assignedIndex);
		}
		// For un-assigned indices i add: newArray[i] = oldArray[i]
		for (final ArrayIndex globalIndex : mFunctionsToIndices.getImage(oldTemplate)) {
			final Term selectOld = getLocalTerm(oldTemplate.getTerm(globalIndex), transformula, oldIsInVar);
			final Term selectNew = getLocalTerm(newTemplate.getTerm(globalIndex), transformula, newIsInVar);
			final ArrayIndex index1 = getLocalIndex(globalIndex, transformula, oldIsInVar);
			final ArrayIndex index2 = getLocalIndex(globalIndex, transformula, newIsInVar);
			if (areIndicesEqual(index1, index2, invariants)
					&& areAllIndicesUnequal(index2, processedIndices, invariants)) {
				result.add(SmtUtils.binaryEquality(mScript, selectNew, selectOld));
			} else if (!mOnlyTrivialImplicationsArrayWrite) {
				final Term newTerm = indexEqualityInequalityImpliesValueEquality(index1, index2, processedIndices,
						selectNew, selectOld, invariants, transformula);
				result.add(newTerm);
			}
		}
		return SmtUtils.and(mScript, result);
	}

	/**
	 * Returns for all assigned terms additional conjuncts. If an index i contains an assigned var and i and j are
	 * indices of a, the implication: (i = j) => (a[i] = a[j]) is contained in the result
	 *
	 * @param assignedVars
	 *            The assigned vars, for which such implications are created (if necessary)
	 * @param transformula
	 * @param invariants
	 * @return
	 */
	private List<Term> getAllImplicationsForIndexAssignment(final Set<Term> assignedVars,
			final TransFormulaLR transformula, final EqualityAnalysisResult invariants) {
		final List<Term> result = new ArrayList<>();
		for (final Term t : assignedVars) {
			for (final ArrayIndex globalIndexWritten : mVariablesToIndices.getImage(t)) {
				final ArrayIndex indexWrittenIn = getLocalIndex(globalIndexWritten, transformula, true);
				final ArrayIndex indexWrittenOut = getLocalIndex(globalIndexWritten, transformula, false);
				for (final ApplicationTermTemplate template : mIndicesToFunctions.getImage(globalIndexWritten)) {
					final Term written = template.getTerm(globalIndexWritten);
					final Term writtenIn = getLocalTerm(written, transformula, true);
					final Term writtenOut = getLocalTerm(written, transformula, false);
					// If the index didn't change, also the array cells don't change
					if (!assignedVars.contains(template.getIdentifier())) {
						final Term unchanged = indexEqualityImpliesValueEquality(indexWrittenOut, indexWrittenIn,
								writtenOut, writtenIn, invariants, transformula);
						result.add(unchanged);
						if (areIndicesEqual(indexWrittenIn, indexWrittenOut, invariants)) {
							continue;
						}
					}
					for (final ArrayIndex globalIndexRead : mFunctionsToIndices.getImage(template)) {
						if (globalIndexWritten == globalIndexRead) {
							continue;
						}
						// Compare with the other indices (in- and out-var-version)
						final Term read = template.getTerm(globalIndexRead);
						final Term readIn = getLocalTerm(read, transformula, true);
						final Term readOut = getLocalTerm(read, transformula, false);
						final ArrayIndex indexReadIn = getLocalIndex(globalIndexRead, transformula, true);
						final ArrayIndex indexReadOut = getLocalIndex(globalIndexRead, transformula, false);
						if (!assignedVars.contains(template.getIdentifier())) {
							final Term assignmentIn = indexEqualityImpliesValueEquality(indexWrittenOut, indexReadIn,
									writtenOut, readIn, invariants, transformula);
							result.add(assignmentIn);
						}
						final Term assignmentOut = indexEqualityImpliesValueEquality(indexWrittenOut, indexReadOut,
								writtenOut, readOut, invariants, transformula);
						result.add(assignmentOut);
					}
				}
			}
		}
		return result;
	}

	/**
	 * Given a global term (=definition), adds the in- and out-vars to the transformula and returns the term with in- or
	 * out-vars
	 *
	 * @param term
	 *            A SMT-Term with global variables
	 * @param transformula
	 *            A TransFormulaLR
	 * @param returnInVar
	 *            Switch to return only in- or out-vars
	 * @return The local term (with in- or out-vars) for the given global term
	 */
	private Term getLocalTerm(final Term term, final TransFormulaLR transformula, final boolean returnInVar) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final TermVariable var : term.getFreeVars()) {
			final IProgramVar programVar = mSymbolTable.getBoogieVar(var);
			// Add the missing in-/out-vars to the transformula if necessary
			final TermVariable freshTermVar = getFreshTermVar(var);
			if (!transformula.getInVars().containsKey(programVar)) {
				transformula.addInVar(programVar, freshTermVar);
			}
			if (!transformula.getOutVars().containsKey(programVar)) {
				transformula.addOutVar(programVar, freshTermVar);
			}
			// Put the in-/out-var-version of this variable to the substitution-map
			if (returnInVar) {
				substitution.put(var, transformula.getInVars().get(programVar));
			} else {
				substitution.put(var, transformula.getOutVars().get(programVar));
			}
		}
		return new Substitution(mManagedScript, substitution).transform(term);
	}

	/**
	 * Given an array index with global terms (=definitions), adds the in- and out-vars to the transformula and returns
	 * the index with in- or out-vars
	 *
	 * @param term
	 *            An array-index with global variables
	 * @param transformula
	 *            A TransFormulaLR
	 * @param returnInVar
	 *            Switch to return only in- or out-vars
	 * @return The local index (with in- or out-vars) for the given global index
	 */
	private ArrayIndex getLocalIndex(final ArrayIndex index, final TransFormulaLR transformula,
			final boolean returnInVar) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : index) {
			list.add(getLocalTerm(t, transformula, returnInVar));
		}
		return new ArrayIndex(list);
	}

	private Set<ApplicationTermTemplate> getLocalTemplates(final ApplicationTermTemplate template,
			final TransFormulaLR transformula) {
		if (template instanceof SelectTemplate) {
			final Term array = (Term) template.getIdentifier();
			final SelectTemplate inVarTemplate = new SelectTemplate(getLocalTerm(array, transformula, true), mScript);
			final SelectTemplate outVarTemplate = new SelectTemplate(getLocalTerm(array, transformula, false), mScript);
			return new HashSet<>(Arrays.asList(inVarTemplate, outVarTemplate));
		}
		return Collections.singleton(template);
	}

	/**
	 * Return for a given set of global indices, all in- and out-var-versions of this index for the given transformula
	 */
	private Set<ArrayIndex> getInAndOutVarIndices(final Set<ArrayIndex> indices, final TransFormulaLR transformula) {
		final Set<ArrayIndex> result = new HashSet<>();
		for (final ArrayIndex index : indices) {
			result.add(getLocalIndex(index, transformula, true));
			result.add(getLocalIndex(index, transformula, false));
		}
		return result;
	}

	/**
	 * Get a fresh TermVariable with the given term as name (in a nicer representation, especially for select-terms)
	 *
	 * @param term
	 * @return A fresh TermVariable
	 */
	private TermVariable getFreshTermVar(final Term term) {
		return mManagedScript.constructFreshTermVariable(niceTermString(term), term.getSort());
	}

	/**
	 * Get an aux-var with the given term as name (in a nicer representation, especially for select-terms) and add it to
	 * the set of aux-vars. For different terms the methods returns different aux-vars.
	 *
	 * @param term
	 * @return An aux-var
	 */
	private TermVariable getAndAddAuxVar(final Term term) {
		final TermVariable auxVar = mReplacementVarFactory.getOrConstructAuxVar(niceTermString(term), term.getSort());
		mAuxVars.add(auxVar);
		return auxVar;
	}

	private static String niceTermString(final Term term) {
		final String result;
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final StringBuilder stringBuilder = new StringBuilder();
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			stringBuilder.append("array_").append((niceTermString(select.getArray()))).append('[');
			final ArrayIndex index = select.getIndex();
			for (int i = 0; i < index.size(); i++) {
				stringBuilder.append(niceTermString(index.get(i))).append(i == index.size() - 1 ? ']' : ',');
			}
			result = stringBuilder.toString();
		} else if (term instanceof TermVariable) {
			final TermVariable termVariable = (TermVariable) term;
			result = termVariable.getName();
		} else if (term instanceof ApplicationTerm) {
			final StringBuilder stringBuilder = new StringBuilder();
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final FunctionSymbol function = applicationTerm.getFunction();
			if (!function.isIntern()) {
				stringBuilder.append("uf_");
			}
			stringBuilder.append('(').append(function.getName()).append(' ');
			final Term[] params = applicationTerm.getParameters();
			for (int i = 0; i < params.length; i++) {
				stringBuilder.append(niceTermString(params[i])).append(i == params.length - 1 ? ')' : ' ');
			}
			result = stringBuilder.toString();
		} else {
			result = term.toString();
		}
		return SmtUtils.removeSmtQuoteCharacters(result);
	}

	private static Set<Doubleton<Term>> computeDoubletons(
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

	private static boolean areIndicesEqual(final ArrayIndex index1, final ArrayIndex index2,
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

	private static boolean areIndicesUnequal(final ArrayIndex index1, final ArrayIndex index2,
			final EqualityAnalysisResult invariants) {
		for (int i = 0; i < index1.size(); i++) {
			final Term term1 = index1.get(i);
			final Term term2 = index2.get(i);
			if (invariants.getDistinctDoubletons().contains(new Doubleton<>(term1, term2))) {
				return true;
			}
		}
		return false;
	}

	private static boolean areAllIndicesUnequal(final ArrayIndex index, final Collection<ArrayIndex> indices,
			final EqualityAnalysisResult invariants) {
		for (final ArrayIndex index2 : indices) {
			if (!areIndicesUnequal(index, index2, invariants)) {
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
			final EqualityAnalysisResult invariants, final TransFormulaLR transformula) {
		// If mOnlyIndicesInFormula is enabled and one of the indices doesn't occur in the formula, no implications
		// should be created, so "true" is returned
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		if (mOnlyIndicesInFormula) {
			if (!index.freeVarsAreSubset(freeVars) || !equal.freeVarsAreSubset(freeVars)) {
				return mScript.term("true");
			}
			for (final ArrayIndex i : unequal) {
				if (!i.freeVarsAreSubset(freeVars)) {
					return mScript.term("true");
				}
			}
		}
		Term lhs = getEqualTerm(index, equal, invariants);
		for (final ArrayIndex i : unequal) {
			lhs = Util.and(mScript, lhs, Util.not(mScript, getEqualTerm(index, i, invariants)));
		}
		final Term rhs = SmtUtils.binaryEquality(mScript, value1, value2);
		final Term result = Util.or(mScript, SmtUtils.not(mScript, lhs), rhs);
		return result;
	}

	private Term indexEqualityImpliesValueEquality(final ArrayIndex index, final ArrayIndex equal, final Term value1,
			final Term value2, final EqualityAnalysisResult invariants, final TransFormulaLR transformula) {
		final List<ArrayIndex> emptyList = Collections.emptyList();
		return indexEqualityInequalityImpliesValueEquality(index, equal, emptyList, value1, value2, invariants,
				transformula);
	}
}

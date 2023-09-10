/*
 * Copyright (C) 2016 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination;

import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.allVariablesAreVisible;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.translateTermVariablesToDefinitions;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.addReplacementVar;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getAndAddAuxVar;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getInVarIndex;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getInVarTerm;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getOutVarIndex;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getOutVarTerm;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getReplacementVar;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IndexAnalyzer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminator {
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;
	private final ILogger mLogger;
	private final IIcfgSymbolTable mSymbolTable;

	private final MapEliminationSettings mSettings;
	private final MapEliminationPreAnalysis mAnalysis;

	/**
	 * Creates a new map eliminator and preprocesses (stores the indices and arrays used in the {@code transformulas}).
	 *
	 * @param services
	 *            UltimateServices
	 * @param logger
	 *            The logger
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            Symbol Table
	 * @param replacementVarFactory
	 *            ReplacementVarFactory
	 * @param transformulas
	 *            The transformulas that should be processed
	 * @param settings
	 *            Settings for the map-elimination
	 */
	public MapEliminator(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable,
			final ReplacementVarFactory replacementVarFactory, final Collection<ModifiableTransFormula> transformulas,
			final MapEliminationSettings settings) {
		mSettings = settings;
		mServices = services;
		mScript = managedScript.getScript();
		mLogger = logger;
		mLogger.info("Using MapEliminator with " + mSettings);
		mManagedScript = managedScript;
		mReplacementVarFactory = replacementVarFactory;
		mSymbolTable = symbolTable;

		mAnalysis = new MapEliminationPreAnalysis(managedScript, transformulas);
	}

	/**
	 * Given a TransFormula with possibly array accesses or calls of uninterpreted functions, returns a new
	 * TransFormula, where these are replaced. In general an overapproximation is returned.
	 * <p>
	 * The given TransFormula has to be in the collection given to the constructor and it has to be in NNF and
	 * quantifier-free.
	 *
	 * @param transformula
	 *            The old TransFormula (quantifier-free, in NNF), which might contain maps
	 * @param equalityAnalysisBefore
	 *            The invariants that are valid before the transformula
	 * @param equalityAnalysisAfter
	 *            The invariants that are valid after the transformula
	 * @return A TransFormula, where array accesses and calls of uninterpreted functions are replaced
	 */
	public ModifiableTransFormula eliminateMaps(final ModifiableTransFormula transformula,
			final EqualityAnalysisResult equalityAnalysisBefore, final EqualityAnalysisResult equalityAnalysisAfter) {
		final ModifiableTransFormula newTF = new ModifiableTransFormula(transformula);
		final Term term = newTF.getFormula();
		if (!QuantifierUtils.isQuantifierFree(term)) {
			throw new UnsupportedOperationException("Quantifiers are not supported");
		}
		if (!SmtUtils.isNNF(term)) {
			throw new UnsupportedOperationException("Only formulae in NNF are supported");
		}
		final HashRelation<MapTemplate, ArrayIndex> localIndices =
				getLocalIndices(newTF, mAnalysis.getLocalIndices(transformula));
		final IndexAnalyzer indexAnalyzer = new IndexAnalyzer(term, mAnalysis.getIndexDoubletons(localIndices),
				mSymbolTable, newTF, equalityAnalysisBefore, equalityAnalysisAfter, mLogger, mManagedScript);
		final EqualityAnalysisResult invariants = indexAnalyzer.getResult();
		final Set<TermVariable> auxVars = new HashSet<>();
		final Term storeFreeTerm = replaceStoreTerms(term, newTF, invariants, auxVars);
		assert !SmtUtils.containsFunctionApplication(storeFreeTerm, "store") : "The formula contains still store-terms";
		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(storeFreeTerm);
		conjuncts.addAll(getAdditionalEqualities(localIndices, invariants));
		if (!mSettings.onlyTrivialImplicationsForModifiedArguments()) {
			conjuncts.addAll(getAllImplicationsForIndexAssignment(newTF, invariants));
		}
		conjuncts.addAll(invariants.constructListOfEqualities(mScript));
		if (mSettings.addInequalities()) {
			conjuncts.addAll(invariants.constructListOfNotEquals(mScript));
		}
		final Term mapFreeTerm = replaceMapReads(newTF, SmtUtils.and(mScript, conjuncts), auxVars);
		assert SmtUtils.isArrayFree(mapFreeTerm) : "The formula contains still arrays";
		assert !SmtUtils.containsUninterpretedFunctionApplication(mapFreeTerm) : "The formula contains still UFs";
		setFormulaAndSimplify(newTF, mapFreeTerm, auxVars);
		return newTF;
	}

	private HashRelation<MapTemplate, ArrayIndex> getLocalIndices(final ModifiableTransFormula transformula,
			final HashRelation<MapTemplate, ArrayIndex> occurringIndices) {
		final HashRelation<MapTemplate, ArrayIndex> result = new HashRelation<>();
		for (final MapTemplate globalTemplate : occurringIndices.getDomain()) {
			for (final MapTemplate template : getLocalTemplates(globalTemplate, transformula)) {
				for (final ArrayIndex index : occurringIndices.getImage(globalTemplate)) {
					result.addPair(template, index);
				}
			}
		}
		for (final MapTemplate globalTemplate : mAnalysis.getAllTemplates()) {
			for (final MapTemplate template : getLocalTemplates(globalTemplate, transformula)) {
				for (final ArrayIndex index : getInAndOutVarIndices(mAnalysis.getIndices(globalTemplate),
						transformula)) {
					result.addPair(template, index);
				}
			}
		}
		return result;
	}

	private Collection<MapTemplate> getLocalTemplates(final MapTemplate template,
			final ModifiableTransFormula transformula) {
		if (template instanceof ArrayTemplate) {
			final Term array = (Term) template.getIdentifier();
			final ArrayTemplate inVarTemplate =
					new ArrayTemplate(getInVarTerm(array, transformula, mManagedScript, mSymbolTable), mScript);
			final ArrayTemplate outVarTemplate =
					new ArrayTemplate(getOutVarTerm(array, transformula, mManagedScript, mSymbolTable), mScript);
			return Arrays.asList(inVarTemplate, outVarTemplate);
		}
		return Arrays.asList(template);
	}

	/**
	 * Returns all equalities of based on the index analysis. To reduce the number of conjuncts, UnionFind is used.
	 *
	 * @param localIndices
	 *            A HashRelation, which maps all MapTemplates, which are considered to the needed local indices.
	 * @param invariants
	 *            The valid invariants at this transformula
	 * @return A list of terms (= conjuncts) with equalities that are valid at this transformula
	 */
	private List<Term> getAdditionalEqualities(final HashRelation<MapTemplate, ArrayIndex> localIndices,
			final EqualityAnalysisResult invariants) {
		final List<Term> result = new ArrayList<>();
		for (final MapTemplate template : localIndices.getDomain()) {
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
				final Term term1 = template.getTerm(index1);
				if (term1.getSort().isArraySort()) {
					continue;
				}
				for (final ArrayIndex index2 : unionFind.getEquivalenceClassMembers(index1)) {
					if (index1 == index2) {
						continue;
					}
					final Term term2 = template.getTerm(index2);
					result.add(SmtUtils.binaryEquality(mScript, term1, term2));
				}
			}
		}
		return result;
	}

	/**
	 * This methods eliminates aux-var from the term, sets it to the transformula and simplifies the transformula then.
	 */
	private void setFormulaAndSimplify(final ModifiableTransFormula transformula, final Term term,
			final Set<TermVariable> auxVars) {
		final Term newTerm;
		if (auxVars.isEmpty()) {
			newTerm = term;
		} else {
			// If aux-vars have been created, eliminate them
			final Term quantifier = SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, auxVars, term);
			newTerm = PartialQuantifierElimination.eliminate(mServices, mManagedScript, quantifier,
					mSettings.getSimplificationTechnique());
			// Add the remaining aux-vars to the transformula
			transformula.addAuxVars(auxVars);
			auxVars.clear();
		}
		transformula.setFormula(
				SmtUtils.simplify(mManagedScript, newTerm, mServices, mSettings.getSimplificationTechnique()));
		clearTransFormula(transformula);
	}

	/**
	 * Removes unnecessary variables from the transformula.
	 */
	private static void clearTransFormula(final ModifiableTransFormula transformula) {
		final List<IProgramVar> inVarsToRemove = new ArrayList<>();
		final List<IProgramVar> outVarsToRemove = new ArrayList<>();
		final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(transformula.getFormula().getFreeVars()));
		final List<TermVariable> auxVarsToRemove =
				transformula.getAuxVars().stream().filter(tv -> !freeVars.contains(tv)).collect(Collectors.toList());
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getInVars().entrySet()) {
			final Term inVar = entry.getValue();
			final IProgramVar var = entry.getKey();
			if (inVar.getSort().isArraySort()) {
				inVarsToRemove.add(var);
			} else if (!freeVars.contains(inVar) && transformula.getOutVars().get(var) == inVar
					&& !SmtUtils.isConstant(inVar)) {
				inVarsToRemove.add(var);
				outVarsToRemove.add(var);
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : transformula.getOutVars().entrySet()) {
			final Term outVar = entry.getValue();
			if (outVar.getSort().isArraySort()) {
				outVarsToRemove.add(entry.getKey());
			}
		}
		inVarsToRemove.forEach(transformula::removeInVar);
		outVarsToRemove.forEach(transformula::removeOutVar);
		auxVarsToRemove.forEach(transformula::removeAuxVar);
	}

	/**
	 * Replaces all read-accesses of maps (select-terms without store and UF-calls) in {@code term} with replacement- or
	 * aux-vars. So this method produces a map-free term.
	 *
	 * @param transformula
	 *            A TransFormula
	 * @param term
	 *            A store-free term
	 * @return A new map-free term
	 */
	private Term replaceMapReads(final ModifiableTransFormula transformula, final Term term,
			final Set<TermVariable> auxVars) {
		// Create for all map/index-pairs a new replacementVar
		for (final MapTemplate template : mAnalysis.getAllTemplates()) {
			for (final ArrayIndex index : mAnalysis.getIndices(template)) {
				final Term mapTerm = template.getTerm(index);
				addReplacementVar(mapTerm, transformula, mManagedScript, mReplacementVarFactory, mSymbolTable);
			}
		}
		final Map<Term, Term> substitution = mAnalysis.findMapReads(term).collect(Collectors.toMap(x -> x,
				x -> getReplacementVar(x, transformula, mManagedScript, mReplacementVarFactory, auxVars)));
		return Substitution.apply(mManagedScript, substitution, term);
	}

	/**
	 * This methods replaces all store-terms and array-equalities in the {@code term} and adds the neeeded in-/out-vars
	 * to the {@code transformula} (The returned term can still contain select-terms or uninterpreted functions).
	 *
	 * @param term
	 *            The term to be replaced
	 * @param transformula
	 *            The new TransFormula (in-/out-vars are added)
	 * @param invariants
	 *            The valid invariants
	 * @param auxVars
	 * @return A term, that doen't contain store-terms
	 */
	private Term replaceStoreTerms(final Term term, final ModifiableTransFormula transformula,
			final EqualityAnalysisResult invariants, final Set<TermVariable> auxVars) {
		final Map<Term, Term> substitutionMap = new HashMap<>();
		final List<Term> conjuncts = new ArrayList<>();
		// First remove all array inequalities by replacing them with true as an overapproximation
		final Term replacedTerm = replaceArrayInequalities(term);
		for (final MultiDimensionalSelect mds : MultiDimensionalSelect.extractSelectDeep(replacedTerm)) {
			if (SmtUtils.isFunctionApplication(mds.getArray(), "store") && !SmtSortUtils.isArraySort(mds.getSort())) {
				final Term selectTerm = mds.toTerm(mScript);
				substitutionMap.put(selectTerm,
						replaceSelectStoreTerm(selectTerm, transformula, invariants, conjuncts, auxVars));
			}
		}
		for (final Term t : SmtUtils.extractApplicationTerms("=", replacedTerm, false)) {
			if (((ApplicationTerm) t).getParameters()[0].getSort().isArraySort()) {
				substitutionMap.put(t, replaceArrayEquality(t, transformula, invariants));
			}
		}
		conjuncts.add(replacedTerm);
		// TODO: 20211226 Matthias: I am wondering why the substitution is applied twice.
		// Because we often have two-dimensional arrays? Shouldn't we apply the
		// substitution until a fixpoint is reached?
		return Substitution.apply(mManagedScript, substitutionMap,
				Substitution.apply(mManagedScript, substitutionMap, SmtUtils.and(mScript, conjuncts)));
	}

	/**
	 * Replaces all array inequalities with true as an overapproximation to avoid unsoundness. This requires a formula
	 * in NNF.
	 */
	private Term replaceArrayInequalities(final Term term) {
		final Map<Term, Term> substitutionMap = new HashMap<>();
		for (final Term t : SmtUtils.extractApplicationTerms("not", term, false)) {
			final Term subterm = ((ApplicationTerm) t).getParameters()[0];
			if (SmtUtils.isFunctionApplication(subterm, "=")) {
				final ApplicationTerm equality = (ApplicationTerm) subterm;
				if (equality.getParameters()[0].getSort().isArraySort()) {
					substitutionMap.put(t, mScript.term("true"));
				}
			}
		}
		return Substitution.apply(mManagedScript, substitutionMap, term);
	}

	/**
	 * Replaces a select-store-term (e.g. (select (store a i x) j)) with an aux-var. For this aux-var additional
	 * equalities are added to as conjuncts to {@code auxVarEqualities}.
	 *
	 * @param auxVars
	 */
	private TermVariable replaceSelectStoreTerm(final Term term, final ModifiableTransFormula transformula,
			final EqualityAnalysisResult invariants, final List<Term> auxVarEqualities,
			final Set<TermVariable> auxVars) {
		final MultiDimensionalSelect multiDimensionalSelect = MultiDimensionalSelect.of(term);
		final ArrayIndex index = multiDimensionalSelect.getIndex();
		final ArrayWrite arrayWrite = new ArrayWrite(multiDimensionalSelect.getArray(), mScript);
		final Set<ArrayIndex> processedIndices = new HashSet<>();
		final TermVariable auxVar = getAndAddAuxVar(term, auxVars, mReplacementVarFactory);
		for (final Pair<ArrayIndex, Term> pair : arrayWrite.getIndexValuePairs()) {
			final ArrayIndex assignedIndex = pair.getFirst();
			if (processedIndices.contains(assignedIndex)) {
				continue;
			}
			final Term value = pair.getSecond();
			final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex, processedIndices,
					auxVar, value, invariants, transformula);
			// If the implication is not trivial (no "or"-term) and onlyTrivialImplicationsArrayWrite is enabled,
			// don't add the implication to the conjuncts
			if (!SmtUtils.isFunctionApplication(newTerm, "or") || !mSettings.onlyTrivialImplicationsArrayWrite()) {
				auxVarEqualities.add(newTerm);
			}
			processedIndices.add(assignedIndex);
		}
		final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, arrayWrite.getOldArray(), index);
		final Term arrayRead = indexEqualityInequalityImpliesValueEquality(index, index, processedIndices, auxVar,
				selectTerm, invariants, transformula);
		if (!SmtUtils.isFunctionApplication(arrayRead, "or") || !mSettings.onlyTrivialImplicationsArrayWrite()) {
			auxVarEqualities.add(arrayRead);
		}
		return auxVar;
	}

	/**
	 * Replaces an array-equality with a term that only contains select-terms.
	 *
	 * @param term
	 *            A term of the form: (= b (store ... (store a i_1 x_1) i_n x_n))
	 * @param transformula
	 *            A TransFormula
	 * @param invariants
	 *            The valid invariants
	 * @return A term store-free term
	 */
	private Term replaceArrayEquality(final Term term, final ModifiableTransFormula transformula,
			final EqualityAnalysisResult invariants) {
		final ArrayWrite arrayWrite = new ArrayWrite(term, mScript);
		final Term oldArray = arrayWrite.getOldArray();
		final Term newArray = arrayWrite.getNewArray();
		// If the old or new array is an aux-var, just return true
		// If both arrays are store-terms, also just return true
		if (!allVariablesAreVisible(oldArray, transformula) || !allVariablesAreVisible(newArray, transformula)
				|| SmtUtils.isFunctionApplication(newArray, "store")) {
			return mScript.term("true");
		}
		final List<Term> result = new ArrayList<>();
		final boolean oldIsInVar = transformula.getInVarsReverseMapping().containsKey(oldArray);
		final boolean newIsInVar = transformula.getInVarsReverseMapping().containsKey(newArray);
		final Term globalOldArray = translateTermVariablesToDefinitions(mManagedScript, transformula, oldArray);
		final Term globalNewArray = translateTermVariablesToDefinitions(mManagedScript, transformula, newArray);
		final ArrayTemplate oldTemplate = new ArrayTemplate(globalOldArray, mScript);
		final ArrayTemplate newTemplate = new ArrayTemplate(globalNewArray, mScript);
		final Set<ArrayIndex> processedIndices = new HashSet<>();
		for (final Pair<ArrayIndex, Term> pair : arrayWrite.getIndexValuePairs()) {
			final ArrayIndex assignedIndex = pair.getFirst();
			if (processedIndices.contains(assignedIndex)
					|| assignedIndex.size() != SmtUtils.getDimension(oldArray.getSort())) {
				continue;
			}
			final Term value = pair.getSecond();
			for (final ArrayIndex globalIndex : mAnalysis.getIndices(newTemplate)) {
				final Term globalSelect = newTemplate.getTerm(globalIndex);
				final Term select;
				final ArrayIndex index;
				if (newIsInVar) {
					select = getInVarTerm(globalSelect, transformula, mManagedScript, mSymbolTable);
					index = getInVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
				} else {
					select = getOutVarTerm(globalSelect, transformula, mManagedScript, mSymbolTable);
					index = getOutVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
				}
				if (processedIndices.contains(index)) {
					continue;
				}
				final Term newTerm = indexEqualityInequalityImpliesValueEquality(index, assignedIndex, processedIndices,
						select, value, invariants, transformula);
				// If the implication is not trivial (no "or"-term) and onlyTrivialImplicationsArrayWrite is enabled,
				// don't add the implication to the conjuncts
				if (!SmtUtils.isFunctionApplication(newTerm, "or") || !mSettings.onlyTrivialImplicationsArrayWrite()) {
					result.add(newTerm);
				}

			}
			processedIndices.add(assignedIndex);
		}
		// For un-assigned indices i add: newArray[i] = oldArray[i]
		for (final ArrayIndex globalIndex : mAnalysis.getIndices(oldTemplate)) {
			final Term selectOld;
			final Term selectNew;
			final ArrayIndex index1;
			final ArrayIndex index2;
			if (oldIsInVar) {
				selectOld = getInVarTerm(oldTemplate.getTerm(globalIndex), transformula, mManagedScript, mSymbolTable);
				index1 = getInVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
			} else {
				selectOld = getOutVarTerm(oldTemplate.getTerm(globalIndex), transformula, mManagedScript, mSymbolTable);
				index1 = getOutVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
			}
			if (newIsInVar) {
				selectNew = getInVarTerm(newTemplate.getTerm(globalIndex), transformula, mManagedScript, mSymbolTable);
				index2 = getInVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
			} else {
				selectNew = getOutVarTerm(newTemplate.getTerm(globalIndex), transformula, mManagedScript, mSymbolTable);
				index2 = getOutVarIndex(globalIndex, transformula, mManagedScript, mSymbolTable);
			}
			final Term newTerm = indexEqualityInequalityImpliesValueEquality(index1, index2, processedIndices,
					selectNew, selectOld, invariants, transformula);
			// If the implication is not trivial (no "or"-term) and onlyTrivialImplicationsArrayWrite is enabled,
			// don't add the implication to the conjuncts
			if (!SmtUtils.isFunctionApplication(newTerm, "or") || !mSettings.onlyTrivialImplicationsArrayWrite()) {
				result.add(newTerm);
			}
		}
		return SmtUtils.and(mScript, result);
	}

	/**
	 * Returns for all assigned terms additional conjuncts. If an index i contains an assigned var and i and j are
	 * indices of a, the implication: (i = j) => (a[i] = a[j]) is contained in the result
	 */
	private List<Term> getAllImplicationsForIndexAssignment(final ModifiableTransFormula transformula,
			final EqualityAnalysisResult invariants) {
		final List<Term> result = new ArrayList<>();
		for (final IProgramVar var : transformula.getAssignedVars()) {
			final Term definition = ReplacementVarUtils.getDefinition(var);
			for (final ArrayIndex globalIndexWritten : mAnalysis.getIndicesWithVariable(definition)) {
				final ArrayIndex indexWrittenIn =
						getInVarIndex(globalIndexWritten, transformula, mManagedScript, mSymbolTable);
				final ArrayIndex indexWrittenOut =
						getOutVarIndex(globalIndexWritten, transformula, mManagedScript, mSymbolTable);
				for (final MapTemplate template : mAnalysis.getTemplate(globalIndexWritten)) {
					final boolean isAssigned = template.isAssigned(transformula);
					final Term written = template.getTerm(globalIndexWritten);
					final Term writtenOut = getOutVarTerm(written, transformula, mManagedScript, mSymbolTable);
					if (!isAssigned) {
						final Term writtenIn = getInVarTerm(written, transformula, mManagedScript, mSymbolTable);
						result.add(indexEqualityImpliesValueEquality(indexWrittenOut, indexWrittenIn, writtenOut,
								writtenIn, invariants, transformula));
					}
					for (final ArrayIndex globalIndexRead : mAnalysis.getIndices(template)) {
						if (globalIndexWritten.equals(globalIndexRead)) {
							continue;
						}
						// Compare with the other indices (in- and out-var-version)
						final Term read = template.getTerm(globalIndexRead);
						if (!isAssigned) {
							final Term readIn = getInVarTerm(read, transformula, mManagedScript, mSymbolTable);
							final ArrayIndex indexReadIn =
									getInVarIndex(globalIndexRead, transformula, mManagedScript, mSymbolTable);
							result.add(indexEqualityImpliesValueEquality(indexWrittenOut, indexReadIn, writtenOut,
									readIn, invariants, transformula));
						}
						final Term readOut = getOutVarTerm(read, transformula, mManagedScript, mSymbolTable);
						final ArrayIndex indexReadOut =
								getOutVarIndex(globalIndexRead, transformula, mManagedScript, mSymbolTable);
						result.add(indexEqualityImpliesValueEquality(indexWrittenOut, indexReadOut, writtenOut, readOut,
								invariants, transformula));
					}
				}
			}
		}
		return result;
	}

	/**
	 * Return for a given set of global indices, all in- and out-var-versions of this index for the given transformula.
	 */
	private Collection<ArrayIndex> getInAndOutVarIndices(final Set<ArrayIndex> indices,
			final ModifiableTransFormula transformula) {
		final Set<ArrayIndex> result = new HashSet<>();
		for (final ArrayIndex index : indices) {
			result.add(getInVarIndex(index, transformula, mManagedScript, mSymbolTable));
			result.add(getOutVarIndex(index, transformula, mManagedScript, mSymbolTable));
		}
		return result;
	}

	/**
	 * Return set of unordered pairs ({@link Doubleton}s) of all Terms {x,y} such that x and y occur as entry of a
	 * (potentially multi-dimensional) argument i_x i_y of the same (or equivalent) map.
	 */
	public Set<Doubleton<Term>> getDoubletons() {
		return mAnalysis.getAllDoubletons();
	}

	private static boolean areIndicesEqual(final ArrayIndex index1, final ArrayIndex index2,
			final EqualityAnalysisResult invariants) {
		if (index1.size() != index2.size()) {
			return false;
		}
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
		if (index1.size() != index2.size()) {
			return mScript.term("false");
		}
		final List<Term> result = new ArrayList<>();
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
				result.add(SmtUtils.binaryEquality(mScript, term1, term2));
			}
		}
		return SmtUtils.and(mScript, result);
	}

	private Term indexEqualityInequalityImpliesValueEquality(final ArrayIndex index, final ArrayIndex equal,
			final Collection<ArrayIndex> unequal, final Term value1, final Term value2,
			final EqualityAnalysisResult invariants, final ModifiableTransFormula transformula) {
		final List<TermVariable> freeVarsFormula = Arrays.asList(transformula.getFormula().getFreeVars());
		final Term inequality = Util.not(mScript, getEqualTerm(index, equal, invariants));
		final List<TermVariable> freeVarsInequality = Arrays.asList(inequality.getFreeVars());
		if (SmtUtils.isTrueLiteral(inequality)
				|| (!freeVarsFormula.containsAll(freeVarsInequality) && mSettings.onlyArgumentsInFormula())) {
			return mScript.term("true");
		}
		final List<Term> disjuncts = new ArrayList<>();
		disjuncts.add(inequality);
		for (final ArrayIndex i : unequal) {
			final Term equality = getEqualTerm(index, i, invariants);
			final List<TermVariable> freeVarsEquality = Arrays.asList(equality.getFreeVars());
			if (SmtUtils.isTrueLiteral(equality)
					|| (!freeVarsFormula.containsAll(freeVarsEquality) && mSettings.onlyArgumentsInFormula())) {
				return mScript.term("true");
			}
			disjuncts.add(equality);
		}
		// TODO: Allow combination of different sorts
		// For example (select (select (store a x b) y) z) should be handled correctly
		if (!value1.getSort().equals(value2.getSort())) {
			throw new AssertionError(String.format("%s tries to combine %s and %s", this.getClass().getSimpleName(),
					value1.getSort(), value2.getSort()));
		}
		disjuncts.add(SmtUtils.binaryEquality(mScript, value1, value2));
		return SmtUtils.or(mScript, disjuncts);
	}

	private Term indexEqualityImpliesValueEquality(final ArrayIndex index, final ArrayIndex equal, final Term value1,
			final Term value2, final EqualityAnalysisResult invariants, final ModifiableTransFormula transformula) {
		return indexEqualityInequalityImpliesValueEquality(index, equal, List.of(), value1, value2, invariants,
				transformula);
	}
}

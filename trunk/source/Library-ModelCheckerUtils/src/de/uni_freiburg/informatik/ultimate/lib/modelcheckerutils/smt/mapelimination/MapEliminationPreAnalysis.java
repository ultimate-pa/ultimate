package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.mapelimination;

import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.allVariablesAreVisible;
import static de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.translateTermVariablesToDefinitions;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MapEliminationPreAnalysis {
	private final Script mScript;
	private final ManagedScript mManagedScript;

	// Stores for each variable, which indices contain it
	private final HashRelation<Term, ArrayIndex> mVariablesToIndices;

	// Stores for each map, which indices access it (bidirectional)
	private final HashRelation<MapTemplate, ArrayIndex> mMapsToIndices;
	private final HashRelation<ArrayIndex, MapTemplate> mIndicesToMaps;

	// Stores information about the arrays that get assigned to another array (then these arrays have the same indices)
	private final Set<Doubleton<Term>> mRelatedArays;

	// Stores all function-names of the uninterpreted functions (to know, what function-calls have to be replaced)^
	private final Set<String> mUninterpretedFunctions;

	// Stores for each transformula, which arrays/uf-calls are accessed in it
	private final Map<ModifiableTransFormula, HashRelation<MapTemplate, ArrayIndex>> mTransFormulasToLocalIndices;
	private final Set<Doubleton<Term>> mDoubletons;

	public MapEliminationPreAnalysis(final ManagedScript managedScript,
			final Collection<ModifiableTransFormula> transformulas) {
		mScript = managedScript.getScript();
		mManagedScript = managedScript;

		mTransFormulasToLocalIndices = new HashMap<>();
		mVariablesToIndices = new HashRelation<>();
		mMapsToIndices = new HashRelation<>();
		mIndicesToMaps = new HashRelation<>();
		mRelatedArays = new HashSet<>();
		mUninterpretedFunctions = new HashSet<>();

		findAllIndices(transformulas);

		mDoubletons = getIndexDoubletons(mMapsToIndices);
	}

	/**
	 * Finds the array accesses in the transformulas and merges the indices if necessary.
	 */
	private void findAllIndices(final Collection<ModifiableTransFormula> transformulas) {
		// Get all array indices from each transformula (only necessary, if it contains arrays)
		for (final ModifiableTransFormula tf : transformulas) {
			mTransFormulasToLocalIndices.put(tf, new HashRelation<>());
			findIndices(tf);
		}
		// Merge the indices of the related arrays using union-find
		final UnionFind<Term> unionFind = new UnionFind<>();
		final Map<Term, ArrayTemplate> templates = new HashMap<>();
		for (final Doubleton<Term> doubleton : mRelatedArays) {
			final Term array1 = doubleton.getOneElement();
			final Term array2 = doubleton.getOtherElement();
			templates.put(array1, new ArrayTemplate(array1, mScript));
			templates.put(array2, new ArrayTemplate(array2, mScript));
			unionFind.findAndConstructEquivalenceClassIfNeeded(array1);
			unionFind.findAndConstructEquivalenceClassIfNeeded(array2);
			unionFind.union(array1, array2);
		}
		for (final Set<Term> equivalenceClass : unionFind.getAllEquivalenceClasses()) {
			final Set<ArrayIndex> indices = new HashSet<>();
			for (final Term array : equivalenceClass) {
				indices.addAll(mMapsToIndices.getImage(templates.get(array)));
			}
			for (final Term array : equivalenceClass) {
				for (final ArrayIndex index : indices) {
					mMapsToIndices.addPair(templates.get(array), index);
					mIndicesToMaps.addPair(index, templates.get(array));
				}
			}
		}
	}

	/**
	 * A method that finds arrays and their indices in the given {@code transformula} and stores them in the maps.
	 */
	private void findIndices(final ModifiableTransFormula transformula) {
		final Term term = transformula.getFormula();
		for (final MultiDimensionalSelect select : MultiDimensionalSelect.extractSelectDeep(term)) {
			final ArrayWrite arrayWrite = new ArrayWrite(select.getArray(), mScript);
			findIndicesArrayWrite(arrayWrite, transformula);
			addArrayAccessToRelation(arrayWrite.getOldArray(), select.getIndex(), transformula);
		}
		for (final Term t : SmtUtils.extractApplicationTerms("=", term, false)) {
			if (((ApplicationTerm) t).getParameters()[0].getSort().isArraySort()) {
				final ArrayWrite arrayWrite = new ArrayWrite(t, mScript);
				// The new array can be also a store-term, so also find indices in this term
				final ArrayWrite arrayWrite2 = new ArrayWrite(arrayWrite.getNewArray(), mScript);
				findIndicesArrayWrite(arrayWrite, transformula);
				findIndicesArrayWrite(arrayWrite2, transformula);
				final Term array1 = arrayWrite.getOldArray();
				final Term array2 = arrayWrite2.getOldArray();
				if (!allVariablesAreVisible(array1, transformula) || !allVariablesAreVisible(array2, transformula)) {
					continue;
				}
				final Term globalArray1 = translateTermVariablesToDefinitions(mManagedScript, transformula, array1);
				final Term globalArray2 = translateTermVariablesToDefinitions(mManagedScript, transformula, array2);
				// If the two arrays are different, add them to the set of related arrays
				// (the indices need to be shared then)
				if (globalArray1 != globalArray2) {
					mRelatedArays.add(new Doubleton<>(globalArray1, globalArray2));
				}
			}
		}
		for (final NonTheorySymbol<?> s : new NonTheorySymbolFinder().findNonTheorySymbols(term)) {
			final Object symbol = s.getSymbol();
			if (symbol instanceof FunctionSymbol) {
				final String function = ((FunctionSymbol) symbol).getName();
				for (final Term t : SmtUtils.extractApplicationTerms(function, term, false)) {
					final ArrayIndex index = new ArrayIndex(Arrays.asList(((ApplicationTerm) t).getParameters()));
					addCallToRelation(function, index, transformula);
				}
			}
		}
	}

	private void findIndicesArrayWrite(final ArrayWrite arrayWrite, final ModifiableTransFormula transformula) {
		for (final Pair<ArrayIndex, Term> pair : arrayWrite.getIndexValuePairs()) {
			addArrayAccessToRelation(arrayWrite.getOldArray(), pair.getFirst(), transformula);
		}
	}

	/**
	 * Adds the info, that {@code array} is accessed by {@code index} to the hash relations.
	 */
	private void addArrayAccessToRelation(final Term array, final ArrayIndex index,
			final ModifiableTransFormula transformula) {
		if (!allVariablesAreVisible(array, transformula) || index.size() != SmtUtils.getDimension(array.getSort())) {
			return;
		}
		for (final Term t : index) {
			if (SmtUtils.containsFunctionApplication(t, "store")) {
				return;
			}
		}
		final Term globalArray = translateTermVariablesToDefinitions(mManagedScript, transformula, array);
		mTransFormulasToLocalIndices.get(transformula).addPair(new ArrayTemplate(globalArray, mScript), index);
		if (allVariablesAreVisible(index, transformula)) {
			final ArrayIndex globalIndex =
					new ArrayIndex(translateTermVariablesToDefinitions(mManagedScript, transformula, index));
			for (final TermVariable var : globalIndex.getFreeVars()) {
				mVariablesToIndices.addPair(var, globalIndex);
			}
			final ArrayTemplate template = new ArrayTemplate(globalArray, mScript);
			mMapsToIndices.addPair(template, globalIndex);
			mIndicesToMaps.addPair(globalIndex, template);
		}
	}

	/**
	 * Adds the info, that the function with name {@code functionName} is applied to {@code index} to the hash
	 * relations.
	 */
	private void addCallToRelation(final String functionName, final ArrayIndex index,
			final ModifiableTransFormula transformula) {
		if (index.isEmpty()) {
			return;
		}
		for (final Term t : index) {
			if (SmtUtils.containsFunctionApplication(t, "store")) {
				return;
			}
		}
		final UFTemplate template = new UFTemplate(functionName, mScript);
		mTransFormulasToLocalIndices.get(transformula).addPair(template, index);
		mUninterpretedFunctions.add(functionName);
		if (allVariablesAreVisible(index, transformula)) {
			final ArrayIndex globalIndex =
					new ArrayIndex(translateTermVariablesToDefinitions(mManagedScript, transformula, index));
			for (final TermVariable var : globalIndex.getFreeVars()) {
				mVariablesToIndices.addPair(var, globalIndex);
			}
			mMapsToIndices.addPair(template, globalIndex);
			mIndicesToMaps.addPair(globalIndex, template);
		}
	}

	public Set<MapTemplate> getAllTemplates() {
		return mMapsToIndices.getDomain();
	}

	public Set<MapTemplate> getTemplate(final ArrayIndex index) {
		return mIndicesToMaps.getImage(index);
	}

	public Set<ArrayIndex> getIndices(final MapTemplate template) {
		return mMapsToIndices.getImage(template);
	}

	public Set<ArrayIndex> getIndicesWithVariable(final Term variable) {
		return mVariablesToIndices.getImage(variable);
	}

	public HashRelation<MapTemplate, ArrayIndex> getLocalIndices(final ModifiableTransFormula transformula) {
		return mTransFormulasToLocalIndices.get(transformula);
	}

	public Stream<Term> findMapReads(final Term term) {
		final Stream<ApplicationTerm> arrays =
				SmtUtils.extractApplicationTerms("select", term, true).stream().filter(x -> !x.getSort().isArraySort());
		final Stream<Term> functions =
				mUninterpretedFunctions.stream().flatMap(x -> SmtUtils.extractApplicationTerms(x, term, true).stream());
		return Stream.concat(arrays, functions);
	}

	public Set<Doubleton<Term>> getIndexDoubletons(final HashRelation<MapTemplate, ArrayIndex> mapsToIndices) {
		final Set<Doubleton<Term>> result = new HashSet<>();
		for (final MapTemplate template : mapsToIndices.getDomain()) {
			final Set<ArrayIndex> indicesSet = mapsToIndices.getImage(template);
			final ArrayIndex[] indices = indicesSet.toArray(new ArrayIndex[indicesSet.size()]);
			for (int i = 0; i < indices.length; i++) {
				for (int j = i + 1; j < indices.length; j++) {
					final ArrayIndex index1 = indices[i];
					final ArrayIndex index2 = indices[j];
					for (int k = 0; k < index1.size(); k++) {
						final Term term1 = index1.get(k);
						final Term term2 = index2.get(k);
						if (term1 != term2) {
							result.add(new Doubleton<>(term1, term2));
						}
					}
				}
			}
		}
		return result;
	}

	public Set<Doubleton<Term>> getAllDoubletons() {
		return mDoubletons;
	}
}

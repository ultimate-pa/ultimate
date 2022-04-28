package de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.algorithm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * Class to create a set of horn-clauses from a given set of provided transitions.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HornClauseSystem {
	private static final String FUNCTION_NAME = "Inv";
	private static final boolean USE_SYMMETRY = false;

	private final TermTransferrer mTermTransferrer;
	private final ManagedScript mManagedScript;

	private int mDimension;
	private final List<IProgramVar> mGlobalVariables;
	private final Map<String, List<IProgramVar>> mLocalVariables;
	private final NestedMap2<String, Integer, Term> mDefaultLocVars;
	private final NestedMap3<String, Integer, IProgramVar, TermVariable> mDefaultVarMaps;
	private final NestedMap2<String, IcfgLocation, Integer> mLocationIndices;
	private final Map<String, Integer> mNumberOfThreads;
	private final Term mBottom;

	public HornClauseSystem(final Map<String, Integer> numberOfThreads, final ManagedScript managedScript,
			final CfgSmtToolkit cfgSmtToolkit, final Predicate<IProgramVar> variableFilter) {
		final IIcfgSymbolTable symbolTable = cfgSmtToolkit.getSymbolTable();
		mManagedScript = managedScript;
		mTermTransferrer = new TermTransferrer(cfgSmtToolkit.getManagedScript().getScript(), getScript());
		mGlobalVariables = symbolTable.getGlobals().stream().filter(variableFilter).collect(Collectors.toList());
		mNumberOfThreads = new LinkedHashMap<>(numberOfThreads);
		mDimension = mGlobalVariables.size();
		mLocalVariables = new LinkedHashMap<>();
		mDefaultLocVars = new NestedMap2<>();
		mDefaultVarMaps = new NestedMap3<>();
		mLocationIndices = new NestedMap2<>();
		mBottom = numeral(-1);
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			final List<IProgramVar> localVars =
					symbolTable.getLocals(proc).stream().filter(variableFilter).collect(Collectors.toList());
			final int n = entry.getValue();
			for (int i = 0; i < n; i++) {
				for (final IProgramVar var : localVars) {
					mDefaultVarMaps.put(proc, i, var,
							mManagedScript.constructFreshTermVariable(var.getGloballyUniqueId(), var.getSort()));
				}
				mDefaultLocVars.put(proc, i, constructAuxVar("loc", proc));
			}
			mLocalVariables.put(proc, localVars);
			mDimension += (localVars.size() + 1) * n;
		}
		mManagedScript.lock(this);
		declareFunction();
		if (USE_SYMMETRY) {
			assertSymmetry();
		}
	}

	public HornClauseSystem(final Map<String, Integer> numberOfThreads, final ManagedScript managedScript,
			final CfgSmtToolkit cfgSmtToolkit) {
		this(numberOfThreads, managedScript, cfgSmtToolkit, x -> true);
	}

	// Order Inv(global, location_1, local_1, ..., location_n, local_n)
	private void declareFunction() {
		final Sort[] paramSorts = new Sort[mDimension];
		int i = 0;
		for (final var v : mGlobalVariables) {
			paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
		}
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final List<IProgramVar> localVars = mLocalVariables.get(entry.getKey());
			for (int j = 0; j < entry.getValue(); j++) {
				// Location
				paramSorts[i++] = getIntSort();
				// Local variables
				for (final IProgramVar v : localVars) {
					paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
				}
			}
		}
		mManagedScript.declareFun(this, FUNCTION_NAME, paramSorts, SmtSortUtils.getBoolSort(mManagedScript));
	}

	private void assertSymmetry() {
		for (final Entry<String, List<IProgramVar>> entry : mLocalVariables.entrySet()) {
			final String proc = entry.getKey();
			final int count = mNumberOfThreads.get(proc);
			for (int i = 0; i < count; i++) {
				for (int j = i + 1; j < count; j++) {
					final NestedMap3<String, Integer, IProgramVar, Term> localVarMap = new NestedMap3<>();
					for (final IProgramVar var : mLocalVariables.get(proc)) {
						localVarMap.put(proc, i, var, mDefaultVarMaps.get(proc, j, var));
						localVarMap.put(proc, j, var, mDefaultVarMaps.get(proc, i, var));
					}
					final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
					locationMap.put(proc, i, mDefaultLocVars.get(proc, j));
					locationMap.put(proc, j, mDefaultLocVars.get(proc, i));
					assertClause(getPredicate(new NestedMap2<>()), getPredicate(Map.of(), localVarMap, locationMap));
				}
			}
		}
	}

	private Term numeral(final long n) {
		return getScript().numeral(BigInteger.valueOf(n));
	}

	private TermVariable constructAuxVar(final String prefix, final String basename) {
		return mManagedScript.constructFreshTermVariable(prefix + "_" + basename, getIntSort());
	}

	private Sort getIntSort() {
		return SmtSortUtils.getIntSort(mManagedScript);
	}

	private Script getScript() {
		return mManagedScript.getScript();
	}

	private Term[] getParams(final Map<IProgramVar, ? extends Term> globalVarMap,
			final NestedMap3<String, Integer, IProgramVar, Term> localVarMap,
			final NestedMap2<String, Integer, Term> locationMap) {
		final Term[] params = new Term[mDimension];
		int i = 0;
		for (final IProgramVar v : mGlobalVariables) {
			final Term term = globalVarMap.get(v);
			params[i++] = mTermTransferrer.transform(term == null ? v.getTerm() : term);
		}
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			for (int j = 0; j < entry.getValue(); j++) {
				final Term loc = locationMap.get(proc, j);
				params[i++] = loc == null ? mDefaultLocVars.get(proc, j) : loc;
				for (final IProgramVar v : mLocalVariables.get(proc)) {
					final Term localVarTerm = localVarMap.get(proc, j, v);
					params[i++] = mTermTransferrer
							.transform(localVarTerm == null ? mDefaultVarMaps.get(proc, j, v) : localVarTerm);
				}
			}
		}
		return params;
	}

	private Term getPredicate(final Map<IProgramVar, ? extends Term> globalVarMap,
			final NestedMap3<String, Integer, IProgramVar, Term> localVarMap,
			final NestedMap2<String, Integer, Term> locationMap) {
		return getScript().term(FUNCTION_NAME, getParams(globalVarMap, localVarMap, locationMap));
	}

	private Term getPredicate(final NestedMap2<String, Integer, Term> locationMap) {
		return getPredicate(Collections.emptyMap(), new NestedMap3<>(), locationMap);
	}

	private void assertClause(final Term... terms) {
		final Term clause = Util.implies(getScript(), terms);
		final List<TermVariable> freeVars = Arrays.asList(clause.getFreeVars());
		mManagedScript.assertTerm(this, SmtUtils.quantifier(getScript(), QuantifiedFormula.FORALL, freeVars, clause));
	}

	private Term getLocIndexTerm(final IcfgLocation loc, final String proc) {
		Integer index = mLocationIndices.get(proc, loc);
		if (index == null) {
			final Map<IcfgLocation, Integer> otherIndices = mLocationIndices.get(proc);
			index = otherIndices == null ? 0 : otherIndices.size();
			mLocationIndices.put(proc, loc, index);
		}
		return numeral(index);
	}

	public void assertInitially(final Collection<IcfgLocation> initialLocations) {
		final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			for (int i = 0; i < entry.getValue(); i++) {
				locationMap.put(entry.getKey(), i, mBottom);
			}
		}
		for (final IcfgLocation loc : initialLocations) {
			final String proc = loc.getProcedure();
			locationMap.put(proc, 0, getLocIndexTerm(loc, proc));
		}
		assertClause(getPredicate(locationMap));
	}

	private int getMaxIndexToCheck(final String proc) {
		if (USE_SYMMETRY) {
			return 0;
		}
		return mNumberOfThreads.get(proc) - 1;
	}

	public void assertSafety(final Collection<IcfgLocation> errorLocations) {
		for (final IcfgLocation loc : errorLocations) {
			final String proc = loc.getProcedure();
			for (int i = 0; i <= getMaxIndexToCheck(proc); i++) {
				final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
				locationMap.put(proc, i, getLocIndexTerm(loc, proc));
				assertClause(SmtUtils.not(getScript(), getPredicate(locationMap)));
			}
		}
	}

	private static NestedMap3<String, Integer, IProgramVar, Term> constructLocalVarMap(final String proc,
			final Map<IProgramVar, ? extends Term> varMap) {
		final NestedMap3<String, Integer, IProgramVar, Term> result = new NestedMap3<>();
		varMap.forEach((k, v) -> result.put(proc, 0, k, v));
		return result;
	}

	private List<Map<String, Integer>> getCartesianProductOfIndices(final Collection<String> procs) {
		List<Map<String, Integer>> result = List.of(Map.of());
		for (final String p : procs) {
			final List<Map<String, Integer>> newResult = new ArrayList<>();
			for (int i = 0; i <= getMaxIndexToCheck(p); i++) {
				for (final Map<String, Integer> map : result) {
					final Map<String, Integer> newMap = new HashMap<>(map);
					newMap.put(p, i);
					newResult.add(newMap);
				}
			}
			result = newResult;
		}
		return result;
	}

	public void assertInductivity(final List<IcfgLocation> pre, final IIcfgTransition<?> edge,
			final List<IcfgLocation> post) {
		final Set<String> containedProcs =
				Stream.concat(pre.stream(), post.stream()).map(IcfgLocation::getProcedure).collect(Collectors.toSet());
		for (final Map<String, Integer> indexMap : getCartesianProductOfIndices(containedProcs)) {
			final NestedMap2<String, Integer, Term> locMapIn = new NestedMap2<>();
			final NestedMap2<String, Integer, Term> locMapOut = new NestedMap2<>();
			for (final IcfgLocation loc : pre) {
				final String proc = loc.getProcedure();
				final int index = indexMap.get(proc);
				locMapIn.put(proc, index, getLocIndexTerm(loc, proc));
				locMapOut.put(proc, index, mBottom);
			}
			for (final IcfgLocation loc : post) {
				final String proc = loc.getProcedure();
				final int index = indexMap.get(proc);
				locMapOut.put(proc, index, getLocIndexTerm(loc, proc));
				if (!locMapIn.containsKey(proc)) {
					locMapIn.put(proc, index, mBottom);
				}
			}
			final TransFormula transformula = edge.getTransformula();
			final Map<IProgramVar, TermVariable> inVars = transformula.getInVars();
			final Map<IProgramVar, TermVariable> outVars = transformula.getOutVars();
			final Term prePred =
					getPredicate(inVars, constructLocalVarMap(edge.getPrecedingProcedure(), inVars), locMapIn);
			final Term transition = mTermTransferrer.transform(transformula.getFormula());
			final Term postPred =
					getPredicate(outVars, constructLocalVarMap(edge.getSucceedingProcedure(), outVars), locMapOut);
			assertClause(prePred, transition, postPred);
		}
	}

	public void assertInductivity(final IIcfgTransition<?> edge) {
		assertInductivity(List.of(edge.getSource()), edge, List.of(edge.getTarget()));
	}

	public void assertNonInterference(final IIcfgTransition<?> edge) {
		final String proc = edge.getPrecedingProcedure();
		final int n = mNumberOfThreads.get(proc);
		final TransFormula transformula = edge.getTransformula();
		final Map<IProgramVar, TermVariable> inVars = transformula.getInVars();
		final Term[] terms = new Term[n + 3];
		for (int i = 0; i < n; i++) {
			final NestedMap3<String, Integer, IProgramVar, Term> localVarMap = new NestedMap3<>();
			for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
				localVarMap.put(proc, i, entry.getKey(), entry.getValue());
			}
			final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
			locationMap.put(proc, i, getLocIndexTerm(edge.getSource(), proc));
			terms[i] = getPredicate(inVars, localVarMap, locationMap);
		}
		terms[n] = getPredicate(inVars, new NestedMap3<>(), new NestedMap2<>());
		terms[n + 1] = mTermTransferrer.transform(transformula.getFormula());
		terms[n + 2] = getPredicate(transformula.getOutVars(), new NestedMap3<>(), new NestedMap2<>());
		assertClause(terms);
	}

	public LBool checkSat() {
		return mManagedScript.checkSat(this);
	}

	// TODO: Return a model for a satisfiable system!
}

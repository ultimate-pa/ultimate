package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Class to create horn-clauses for given edges to create thread-modular proofs.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcConcurrent {
	private static final String FUNCTION_NAME = "Inv";

	private final ManagedScript mManagedScript;

	private final NestedMap2<String, IcfgLocation, Integer> mLocationIndices;
	private final Map<String, Integer> mNumberOfThreads;
	private final Term mBottomLocation;
	private final HcPredicateSymbol mPredicate;
	private final HcSymbolTable mHcSymbolTable;
	private final List<HcHeadVar> mDefaultHeadVars;
	private final BidirectionalMap<Integer, IHcReplacementVar> mPositions2Vars;

	public IcfgToChcConcurrent(final Map<String, Integer> numberOfThreads, final ManagedScript managedScript,
			final CfgSmtToolkit cfgSmtToolkit, final HcSymbolTable hcSymbolTable,
			final Predicate<IProgramVar> variableFilter) {
		final IIcfgSymbolTable symbolTable = cfgSmtToolkit.getSymbolTable();
		mHcSymbolTable = hcSymbolTable;
		mManagedScript = managedScript;
		final List<IProgramVar> globalVariables =
				symbolTable.getGlobals().stream().filter(variableFilter).collect(Collectors.toList());
		mNumberOfThreads = new LinkedHashMap<>(numberOfThreads);
		mLocationIndices = new NestedMap2<>();
		mBottomLocation = numeral(-1);
		final Map<String, List<IProgramVar>> localVariables = new HashMap<>();
		mPositions2Vars = new BidirectionalMap<>();
		for (final String proc : mNumberOfThreads.keySet()) {
			localVariables.put(proc,
					symbolTable.getLocals(proc).stream().filter(variableFilter).collect(Collectors.toList()));
		}
		initializeDefaultVars(globalVariables, localVariables);
		final List<Sort> sorts = IntStream.range(0, mPositions2Vars.size())
				.mapToObj(x -> mPositions2Vars.get(x).getSort()).collect(Collectors.toList());
		mPredicate = hcSymbolTable.getOrConstructHornClausePredicateSymbol(FUNCTION_NAME, sorts);
		mDefaultHeadVars = IntStream.range(0, mPositions2Vars.size())
				.mapToObj(x -> constructHeadVar(mPositions2Vars.get(x), x)).collect(Collectors.toList());
	}

	private HcHeadVar constructHeadVar(final IHcReplacementVar rv, final int index) {
		return mHcSymbolTable.getOrConstructHeadVar(mPredicate, index, rv.getSort(), rv);
	}

	private void initializeDefaultVars(final Collection<IProgramVar> globalVariables,
			final Map<String, List<IProgramVar>> localVariables) {
		int i = 0;
		for (final IProgramVar v : globalVariables) {
			mPositions2Vars.put(i++, new HcGlobalVar(v));
		}
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			final List<IProgramVar> localVars = localVariables.get(proc);
			for (int j = 0; j < entry.getValue(); j++) {
				// Location
				mPositions2Vars.put(i++, new HcLocationVar(proc, j, getIntSort()));
				for (final IProgramVar v : localVars) {
					mPositions2Vars.put(i++, new HcLocalVar(v, j));
				}
			}
		}
	}

	private Sort getIntSort() {
		return SmtSortUtils.getIntSort(getScript());
	}

	private List<Term> getDefaultArgs() {
		return mDefaultHeadVars.stream().map(HcVar::getTerm).collect(Collectors.toList());
	}

	private Term numeral(final long n) {
		return getScript().numeral(BigInteger.valueOf(n));
	}

	private Script getScript() {
		return mManagedScript.getScript();
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

	public HornClause getInitialClause(final Collection<IcfgLocation> initialLocations) {
		final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			for (int i = 0; i < entry.getValue(); i++) {
				locationMap.put(entry.getKey(), i, mBottomLocation);
			}
		}
		for (final IcfgLocation loc : initialLocations) {
			final String proc = loc.getProcedure();
			locationMap.put(proc, 0, getLocIndexTerm(loc, proc));
		}
		return constructHornClause(getConstraintFromLocationMap(locationMap), List.of(), Set.of());
	}

	private HornClause constructHornClause(final Term constraint, final List<List<Term>> bodyArguments,
			final Set<HcVar> bodyVars) {
		return new HornClause(mManagedScript, mHcSymbolTable, constraint, mPredicate, mDefaultHeadVars,
				Collections.nCopies(bodyArguments.size(), mPredicate), bodyArguments, bodyVars);
	}

	private Term getConstraintFromLocationMap(final NestedMap2<String, Integer, Term> locationMap) {
		final List<Term> constraints = new ArrayList<>();
		for (final var triple : locationMap.entrySet()) {
			final HcLocationVar locVar = new HcLocationVar(triple.getFirst(), triple.getSecond(), getIntSort());
			final int index = mPositions2Vars.inverse().get(locVar);
			final Term term = mDefaultHeadVars.get(index).getTerm();
			constraints.add(SmtUtils.binaryEquality(getScript(), term, triple.getThird()));
		}
		return SmtUtils.and(getScript(), constraints);
	}

	public Collection<HornClause> getSafetyClauses(final Collection<IcfgLocation> errorLocations) {
		final List<HornClause> result = new ArrayList<>();
		final Set<HcVar> vars = new HashSet<>(mDefaultHeadVars);
		final List<Term> bodyArgs = getDefaultArgs();
		for (final IcfgLocation loc : errorLocations) {
			final String proc = loc.getProcedure();
			for (int i = 0; i < mNumberOfThreads.get(proc); i++) {
				final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
				locationMap.put(proc, i, getLocIndexTerm(loc, proc));
				final Term constraint = getConstraintFromLocationMap(locationMap);
				result.add(new HornClause(mManagedScript, mHcSymbolTable, constraint, List.of(mPredicate),
						List.of(bodyArgs), vars));
			}
		}
		return result;
	}

	private List<Map<String, Integer>> getCartesianProductOfIndices(final Collection<String> procs) {
		List<Map<String, Integer>> result = List.of(Map.of());
		for (final String p : procs) {
			final List<Map<String, Integer>> newResult = new ArrayList<>();
			for (int i = 0; i < mNumberOfThreads.get(p); i++) {
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

	public Collection<HornClause> getInductivityClauses(final List<IcfgLocation> pre, final IIcfgTransition<?> edge,
			final List<IcfgLocation> post) {
		final List<HornClause> result = new ArrayList<>();
		final Set<String> containedProcs =
				Stream.concat(pre.stream(), post.stream()).map(IcfgLocation::getProcedure).collect(Collectors.toSet());
		for (final Map<String, Integer> indexMap : getCartesianProductOfIndices(containedProcs)) {
			final NestedMap2<String, Integer, Term> locMapIn = new NestedMap2<>();
			final NestedMap2<String, Integer, Term> locMapOut = new NestedMap2<>();
			for (final IcfgLocation loc : pre) {
				final String proc = loc.getProcedure();
				locMapIn.put(proc, indexMap.get(proc), getLocIndexTerm(loc, proc));
			}
			for (final IcfgLocation loc : post) {
				final String proc = loc.getProcedure();
				locMapOut.put(proc, indexMap.get(proc), getLocIndexTerm(loc, proc));
			}
			final TransFormula transformula = edge.getTransformula();
			final Map<Term, Term> substitution = new HashMap<>();
			final List<Term> constraints = new ArrayList<>();
			final List<Term> bodyArgs = getDefaultArgs();
			final Set<HcVar> bodyVars = new HashSet<>();
			for (final var entry : mPositions2Vars.entrySet()) {
				final int index = entry.getKey();
				final IHcReplacementVar rv = entry.getValue();
				IProgramVar pv = null;
				if (rv instanceof HcLocalVar) {
					final HcLocalVar lv = (HcLocalVar) rv;
					if (Objects.equals(indexMap.get(lv.getProcedure()), lv.getIndex())) {
						pv = lv.getVariable();
					}
				}
				if (rv instanceof HcGlobalVar) {
					final HcGlobalVar gv = (HcGlobalVar) rv;
					pv = gv.getVariable();
				}
				if (rv instanceof HcLocationVar) {
					final HcLocationVar lv = (HcLocationVar) rv;
					final String procedure = lv.getProcedure();
					final int index2 = lv.getIndex();
					Term locIn = locMapIn.get(procedure, index2);
					Term locOut = locMapOut.get(procedure, index2);
					if (locIn == null && locOut == null) {
						continue;
					}
					if (locIn == null) {
						locIn = mBottomLocation;
					}
					if (locOut == null) {
						locOut = mBottomLocation;
					}
					constraints
							.add(SmtUtils.binaryEquality(getScript(), mDefaultHeadVars.get(index).getTerm(), locOut));
					if (!locIn.equals(locOut)) {
						bodyArgs.set(index, locIn);
					}
				}
				if (pv == null) {
					continue;
				}
				final TermVariable inVar = transformula.getInVars().get(pv);
				final TermVariable outVar = transformula.getOutVars().get(pv);
				substitution.put(outVar, mDefaultHeadVars.get(index).getTerm());
				if (!Objects.equals(inVar, outVar)) {
					final HcBodyVar bv = mHcSymbolTable.getOrConstructBodyVar(mPredicate, index, pv);
					final Term term = bv.getTerm();
					bodyArgs.set(index, term);
					substitution.put(inVar, term);
					bodyVars.add(bv);
				}
			}
			// Replace all other variables with aux-vars
			final Term formula = transformula.getFormula();
			for (final TermVariable v : formula.getFreeVars()) {
				if (substitution.containsKey(v)) {
					continue;
				}
				// TODO: Using the number of bodyVars as index is a hack!
				final HcBodyVar auxVar =
						mHcSymbolTable.getOrConstructBodyVar(mPredicate, bodyVars.size(), v.getSort(), v);
				substitution.put(v, auxVar.getTerm());
				bodyVars.add(auxVar);
			}
			constraints.add(Substitution.apply(mManagedScript, substitution, formula));
			result.add(constructHornClause(SmtUtils.and(getScript(), constraints), List.of(bodyArgs), bodyVars));
		}
		return result;
	}

	public Collection<HornClause> getInductivityClauses(final IIcfgTransition<?> edge) {
		return getInductivityClauses(List.of(edge.getSource()), edge, List.of(edge.getTarget()));
	}

	public HornClause getNonInterferenceClause(final IIcfgTransition<?> edge) {
		final String procedure = edge.getPrecedingProcedure();
		final int n = mNumberOfThreads.get(procedure);
		final List<List<Term>> bodyArguments = new ArrayList<>();
		for (int i = 0; i <= n; i++) {
			bodyArguments.add(getDefaultArgs());
		}
		final TransFormula transformula = edge.getTransformula();
		final Map<Term, Term> substitution = new HashMap<>();
		final Set<HcVar> bodyVars = new HashSet<>();
		for (final var entry : mPositions2Vars.entrySet()) {
			final int index = entry.getKey();
			final IHcReplacementVar rv = entry.getValue();
			if (rv instanceof HcLocalVar) {
				final HcLocalVar lv = (HcLocalVar) rv;
				if (lv.getProcedure().equals(procedure)) {
					final IProgramVar pv = lv.getVariable();
					final TermVariable inVar = transformula.getInVars().get(pv);
					final TermVariable outVar = transformula.getOutVars().get(pv);
					if (inVar != null) {
						final HcBodyVar bodyVar = mHcSymbolTable.getOrConstructBodyVar(mPredicate, index, pv);
						bodyVars.add(bodyVar);
						final Term bodyVarTerm = bodyVar.getTerm();
						substitution.put(inVar, bodyVarTerm);
						for (int i = 0; i < n; i++) {
							final int newIndex = mPositions2Vars.inverse().get(new HcLocalVar(pv, i));
							bodyArguments.get(i + 1).set(newIndex, bodyVarTerm);
						}
					}
					if (outVar != null && !outVar.equals(inVar)) {
						// TODO: Should this be a HcBodyAuxVar instead? => ChcToBoogie crashes then...
						final HcBodyVar auxVar = mHcSymbolTable.getOrConstructBodyVar(mPredicate, index, pv);
						substitution.put(outVar, auxVar.getTerm());
						bodyVars.add(auxVar);
					}
				}
			}
			if (rv instanceof HcGlobalVar) {
				final IProgramVar pv = ((HcGlobalVar) rv).getVariable();
				final TermVariable inVar = transformula.getInVars().get(pv);
				final TermVariable outVar = transformula.getOutVars().get(pv);
				substitution.put(outVar, mDefaultHeadVars.get(index).getTerm());
				if (!Objects.equals(inVar, outVar)) {
					final HcBodyVar bv = mHcSymbolTable.getOrConstructBodyVar(mPredicate, index, pv);
					final Term term = bv.getTerm();
					for (int i = 0; i <= n; i++) {
						bodyArguments.get(i).set(index, term);
					}
					substitution.put(inVar, term);
					bodyVars.add(bv);
				}
			}
			if (rv instanceof HcLocationVar) {
				final HcLocationVar lv = (HcLocationVar) rv;
				if (lv.getProcedure().equals(procedure)) {
					final Term loc = getLocIndexTerm(edge.getSource(), procedure);
					for (int i = 0; i < n; i++) {
						final int newIndex =
								mPositions2Vars.inverse().get(new HcLocationVar(procedure, i, getIntSort()));
						bodyArguments.get(i + 1).set(newIndex, loc);
					}
				}
			}
		}
		// Replace all other variables with aux-vars
		final Term formula = transformula.getFormula();
		for (final TermVariable v : formula.getFreeVars()) {
			if (substitution.containsKey(v)) {
				continue;
			}
			// TODO: Using the number of bodyVars as index is a hack!
			final HcBodyVar auxVar = mHcSymbolTable.getOrConstructBodyVar(mPredicate, bodyVars.size(), v.getSort(), v);
			substitution.put(v, auxVar.getTerm());
			bodyVars.add(auxVar);
		}
		return constructHornClause(Substitution.apply(mManagedScript, substitution, transformula.getFormula()),
				bodyArguments, bodyVars);
	}

	public interface IHcReplacementVar {
		Sort getSort();
	}
}

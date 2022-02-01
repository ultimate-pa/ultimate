package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class to check thread modularity of an icfg using horn clause constraints.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ThreadGeneralization {
	private static final String FUNCTION_NAME = "Inv";

	private final TermTransferrer mTermTransferrer;
	private final ManagedScript mManagedScript;

	private final Map<String, List<IcfgLocation>> mLocations;
	private final Map<String, IcfgLocation> mEntryLocations;
	private final HashRelation<String, IcfgLocation> mErrorLocations;

	private final Map<String, Integer> mNumberOfThreads;
	private final Set<String> mDuplicatedThreads;
	private final Set<String> mInitialProcedures;

	private final List<IProgramVar> mGlobalVariables;
	private final Map<String, List<IProgramVar>> mLocalVariables;

	private int mDimension;
	private final NestedMap3<String, Integer, IProgramVar, TermVariable> mDefaultVarMaps;
	private final NestedMap2<String, Integer, TermVariable> mDefaultLocVars;

	private final LBool mSat;

	private final Map<String, TermVariable> mThreadCounters;

	public ThreadGeneralization(final IIcfg<IcfgLocation> icfg, final Collection<String> duplicatedThreads,
			final ManagedScript managedScript) {
		mManagedScript = managedScript;
		final CfgSmtToolkit cfgSmtToolkit = icfg.getCfgSmtToolkit();
		mTermTransferrer = new TermTransferrer(cfgSmtToolkit.getManagedScript().getScript(), getScript());
		mInitialProcedures = icfg.getInitialNodes().stream().map(x -> x.getProcedure()).collect(Collectors.toSet());
		final ConcurrencyInformation concurrency = cfgSmtToolkit.getConcurrencyInformation();
		final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forks = concurrency.getThreadInstanceMap().keySet();
		mNumberOfThreads = getThreadCounts(mInitialProcedures, forks);
		mEntryLocations = icfg.getProcedureEntryNodes();
		final IIcfgSymbolTable symbolTable = cfgSmtToolkit.getSymbolTable();
		mGlobalVariables = new ArrayList<>(symbolTable.getGlobals());
		if (duplicatedThreads == null) {
			mDuplicatedThreads = mNumberOfThreads.keySet().stream()
					.filter(x -> !mInitialProcedures.contains(x) || mNumberOfThreads.get(x) > 1)
					.collect(Collectors.toSet());
		} else {
			mDuplicatedThreads = new HashSet<>(duplicatedThreads);
		}
		// TODO: This is a workaround to force 2-thread-modularity. Make this an option?
		mDuplicatedThreads.forEach(x -> mNumberOfThreads.put(x, mNumberOfThreads.get(x) + 1));
		final Set<IcfgLocation> inUseErrorLocs = new HashSet<>(concurrency.getInUseErrorNodeMap().values());
		mErrorLocations = new HashRelation<>();
		mDimension = mGlobalVariables.size();
		mDefaultVarMaps = new NestedMap3<>();
		mDefaultLocVars = new NestedMap2<>();
		mLocalVariables = new HashMap<>();
		mLocations = new HashMap<>();
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			final int count = entry.getValue();
			final List<IProgramVar> localVars = new ArrayList<>(symbolTable.getLocals(proc));
			mLocalVariables.put(proc, localVars);
			mDimension += (localVars.size() + 1) * count;
			final List<IcfgLocation> locations =
					new IcfgLocationIterator<>(mEntryLocations.get(proc)).asStream().collect(Collectors.toList());
			mLocations.put(proc, locations);
			final Set<IcfgLocation> errLocs = icfg.getProcedureErrorNodes().get(proc);
			if (errLocs != null) {
				errLocs.stream().filter(x -> !inUseErrorLocs.contains(x))
						.forEach(x -> mErrorLocations.addPair(proc, x));
			}
			for (int j = 0; j < count; j++) {
				final int i = j;
				getFreshLocalVarMap(proc).forEach((k, v) -> mDefaultVarMaps.put(proc, i, k, v));
				mDefaultLocVars.put(proc, i, constructAuxVar("loc", proc));
			}
		}
		mThreadCounters = forks.stream().map(x -> x.getNameOfForkedProcedure())
				.collect(Collectors.toMap(x -> x, x -> constructAuxVar("count", x)));
		mDimension += mThreadCounters.size();
		mSat = mDuplicatedThreads.isEmpty() ? LBool.SAT : checkHornClauses();
	}

	public ThreadGeneralization(final IIcfg<IcfgLocation> icfg, final ManagedScript managedScript) {
		this(icfg, null, managedScript);
	}

	private Map<String, Integer> getThreadCounts(final Collection<String> initialProcedures,
			final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> forks) {
		final Map<String, Integer> result =
				initialProcedures.stream().collect(LinkedHashMap::new, (map, item) -> map.put(item, 1), Map::putAll);
		final Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> usedForks = new HashSet<>();
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> f : forks) {
				if (usedForks.contains(f) || !result.containsKey(f.getPrecedingProcedure())) {
					continue;
				}
				final String newProc = f.getNameOfForkedProcedure();
				result.put(newProc, result.getOrDefault(newProc, 0) + 1);
				usedForks.add(f);
				changed = true;
			}
		}
		return result;
	}

	public boolean isSat() {
		return mSat == LBool.SAT;
	}

	private LBool checkHornClauses() {
		mManagedScript.lock(this);
		declareFunction();
		assertInitialClause();
		assertSafetyClauses();
		assertInductivity();
		assertNonInterference();
		final LBool result = mManagedScript.checkSat(this);
		mManagedScript.unlock(this);
		return result;
	}

	private Script getScript() {
		return mManagedScript.getScript();
	}

	private TermVariable constructAuxVar(final String prefix, final String basename) {
		return mManagedScript.constructFreshTermVariable(prefix + "_" + basename, getIntSort());
	}

	private Sort getIntSort() {
		return SmtSortUtils.getIntSort(mManagedScript);
	}

	private void assertClause(final Term... terms) {
		final Term clause = Util.implies(getScript(), terms);
		final TermVariable[] freeVars = clause.getFreeVars();
		if (freeVars.length == 0) {
			mManagedScript.assertTerm(this, clause);
		} else {
			final Term quantified = getScript().quantifier(QuantifiedFormula.FORALL, freeVars, clause);
			mManagedScript.assertTerm(this, quantified);
		}
	}

	// Order Inv(global, location_1, local_1, ..., location_n, local_n)
	private void declareFunction() {
		final Sort[] paramSorts = new Sort[mDimension];
		int i = 0;
		for (final var v : mGlobalVariables) {
			paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
		}
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			// Thread counters, if forked
			if (mThreadCounters.containsKey(proc)) {
				paramSorts[i++] = getIntSort();
			}
			for (int j = 0; j < entry.getValue(); j++) {
				// Location
				paramSorts[i++] = getIntSort();
				// Local variables
				for (final IProgramVar v : mLocalVariables.get(proc)) {
					paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
				}
			}
		}
		mManagedScript.declareFun(this, FUNCTION_NAME, paramSorts, SmtSortUtils.getBoolSort(mManagedScript));
	}

	private Term getLocIndexTerm(final IcfgLocation loc, final String procedure) {
		return getScript().numeral(BigInteger.valueOf(mLocations.get(procedure).indexOf(loc)));
	}

	private Term getPredicate(final Map<IProgramVar, ? extends Term> globalVarMap,
			final NestedMap2<String, Integer, Term> locationMap,
			final NestedMap3<String, Integer, IProgramVar, Term> localVarMap, final Map<String, Term> threadCounters) {
		final Term[] params = new Term[mDimension];
		int i = 0;
		for (final IProgramVar v : mGlobalVariables) {
			final Term term = globalVarMap.get(v);
			params[i++] = mTermTransferrer.transform(term == null ? v.getTerm() : term);
		}
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			final TermVariable defaultThreadCounter = mThreadCounters.get(proc);
			if (defaultThreadCounter != null) {
				params[i++] = threadCounters.getOrDefault(proc, defaultThreadCounter);
			}
			for (int j = 0; j < entry.getValue(); j++) {
				final Term locationVar = locationMap.get(proc, j);
				params[i++] = locationVar == null ? mDefaultLocVars.get(proc, j) : locationVar;
				for (final IProgramVar v : mLocalVariables.get(proc)) {
					final Term localVarTerm = localVarMap.get(proc, j, v);
					params[i++] = mTermTransferrer
							.transform(localVarTerm == null ? mDefaultVarMaps.get(proc, j, v) : localVarTerm);
				}
			}
		}
		return getScript().term(FUNCTION_NAME, params);
	}

	private Map<IProgramVar, TermVariable> getFreshLocalVarMap(final String proc) {
		// TODO: This is only a workaround to avoid name clashes in the different scripts!
		return mLocalVariables.get(proc).stream().collect(Collectors.toMap(x -> x,
				x -> mManagedScript.constructFreshTermVariable("fresh_" + x.getGloballyUniqueId(), x.getSort())));
	}

	private void assertInitialClause() {
		final NestedMap2<String, Integer, Term> locationMap = new NestedMap2<>();
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			final Term locTerm = getLocIndexTerm(mEntryLocations.get(proc), proc);
			for (int i = 0; i < entry.getValue(); i++) {
				locationMap.put(proc, i, locTerm);
			}
		}
		final Term zero = getScript().numeral(BigInteger.ZERO);
		final Term one = getScript().numeral(BigInteger.ONE);
		final Map<String, Term> threadCounters = mThreadCounters.keySet().stream()
				.collect(Collectors.toMap(x -> x, x -> mInitialProcedures.contains(x) ? one : zero));
		assertClause(getPredicate(Collections.emptyMap(), locationMap, new NestedMap3<>(), threadCounters));
	}

	private void assertSafetyClauses() {
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			for (final IcfgLocation e : mErrorLocations.getImage(proc)) {
				final Term errorLocTerm = getLocIndexTerm(e, proc);
				for (int i = 0; i < entry.getValue(); i++) {
					final Term predicate = getPredicate(Collections.emptyMap(),
							constructLocationMap(proc, i, errorLocTerm), new NestedMap3<>(), Collections.emptyMap());
					assertClause(predicate, getScript().term("false"));
				}
			}
		}
	}

	private static String getForkedThread(final IIcfgTransition<?> edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return ((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure();
		}
		if (edge instanceof IIcfgForkTransitionThreadOther<?>) {
			final var fork = (IIcfgForkTransitionThreadOther<?>) edge;
			return getForkedThread(fork.getCorrespondingIIcfgForkTransitionCurrentThread());
		}
		return null;
	}

	private Pair<Term, Map<String, Term>> getTransition(final IcfgEdge edge) {
		Term transition = mTermTransferrer.transform(edge.getTransformula().getFormula());
		final String thread = edge.getPrecedingProcedure();
		final Term one = getScript().numeral(BigInteger.ONE);
		final Map<String, Term> threadCounters = new HashMap<>();
		if (edge.getSource().equals(mEntryLocations.get(thread))) {
			final Term threadCounter = mThreadCounters.get(thread);
			if (threadCounter != null) {
				final Term positive = SmtUtils.geq(getScript(), threadCounter, one);
				transition = SmtUtils.and(getScript(), transition, positive);
				final Term threadCounterDec = SmtUtils.minus(getScript(), threadCounter, one);
				threadCounters.put(thread, threadCounterDec);
			}
		}
		final String forkedThread = getForkedThread(edge);
		if (forkedThread != null && threadCounters.remove(forkedThread) == null) {
			final Term threadCounter = mThreadCounters.get(forkedThread);
			final Term threadCounterInc = SmtUtils.sum(getScript(), getIntSort(), threadCounter, one);
			threadCounters.put(forkedThread, threadCounterInc);
		}
		return new Pair<>(transition, threadCounters);
	}

	private static NestedMap2<String, Integer, Term> constructLocationMap(final String proc, final int n,
			final Term term) {
		final NestedMap2<String, Integer, Term> result = new NestedMap2<>();
		result.put(proc, n, term);
		return result;
	}

	private static NestedMap3<String, Integer, IProgramVar, Term> constructVarMap(final String proc, final int n,
			final Map<IProgramVar, ? extends Term> varMap) {
		final NestedMap3<String, Integer, IProgramVar, Term> result = new NestedMap3<>();
		varMap.forEach((k, v) -> result.put(proc, n, k, v));
		return result;
	}

	private void assertInductivity() {
		for (final Entry<String, Integer> entry : mNumberOfThreads.entrySet()) {
			final String proc = entry.getKey();
			for (final IcfgLocation loc : mLocations.get(proc)) {
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					final UnmodifiableTransFormula tf = edge.getTransformula();
					final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
					final Pair<Term, Map<String, Term>> transition = getTransition(edge);
					for (int i = 0; i < entry.getValue(); i++) {
						final Map<IProgramVar, TermVariable> outVars = tf.getOutVars();
						final Term prePredicate =
								getPredicate(inVars, constructLocationMap(proc, i, getLocIndexTerm(loc, proc)),
										constructVarMap(proc, i, inVars), Collections.emptyMap());
						final Term postPredicate = getPredicate(outVars,
								constructLocationMap(proc, i, getLocIndexTerm(edge.getTarget(), proc)),
								constructVarMap(proc, i, outVars), transition.getSecond());
						assertClause(prePredicate, transition.getFirst(), postPredicate);
					}
				}
			}
		}
	}

	private void assertNonInterference() {
		for (final String proc : mDuplicatedThreads) {
			for (final IcfgLocation loc : mLocations.get(proc)) {
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					final UnmodifiableTransFormula tf = edge.getTransformula();
					final Pair<Term, Map<String, Term>> transition = getTransition(edge);
					if (getForkedThread(edge) != null) {
						// TODO: Do we need to check this?
						continue;
					}
					final int size = mNumberOfThreads.get(proc);
					final Term[] terms = new Term[size + 3];
					terms[0] = getPredicate(tf.getInVars(), new NestedMap2<>(), new NestedMap3<>(),
							Collections.emptyMap());
					for (int i = 0; i < size; i++) {
						terms[i + 1] =
								getPredicate(tf.getInVars(), constructLocationMap(proc, i, getLocIndexTerm(loc, proc)),
										constructVarMap(proc, i, tf.getInVars()), Collections.emptyMap());

					}
					terms[size + 1] = transition.getFirst();
					terms[size + 2] = getPredicate(tf.getOutVars(), new NestedMap2<>(), new NestedMap3<>(),
							transition.getSecond());
					assertClause(terms);
				}
			}
		}
	}
}

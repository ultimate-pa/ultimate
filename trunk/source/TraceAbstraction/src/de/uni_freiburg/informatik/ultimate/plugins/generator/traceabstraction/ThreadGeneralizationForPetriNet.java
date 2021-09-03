package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.DebugPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Class to check thread modularity of a petri-net using horn clause constraints.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ThreadGeneralizationForPetriNet {
	private static final String FUNCTION_NAME = "Inv";
	private static final boolean DUPLICATE_INDUCTIVITY = true;
	private static final boolean ADD_SYMMETRY = false;

	private final TermTransferrer mTermTransferrer;
	private final ManagedScript mManagedScript;

	private final Set<IcfgLocation> mInUseErrorLocs;
	private final Map<String, String> mInstances2Templates;
	private final Map<String, List<String>> mTemplates2Instances;
	private final Term mBottom;
	private final List<IProgramVar> mGlobalVariables;
	private final Map<String, List<IProgramVar>> mLocalVariables;
	private final NestedMap2<String, DebugIdentifier, Integer> mLocationIndices;
	private final NestedMap2<String, IProgramVar, Integer> mLocalVarIndices;
	private final Map<String, Term> mDefaultLocVars;
	private final NestedMap2<String, IProgramVar, TermVariable> mDefaultVarMaps;
	private final Set<String> mProcedures;
	private int mDimension;
	private final LBool mResult;

	public ThreadGeneralizationForPetriNet(final IPetriNet<? extends IIcfgTransition<?>, IPredicate> petriNet,
			final IIcfg<IcfgLocation> icfg, final ManagedScript managedScript, final int numberOfThreads) {
		mManagedScript = managedScript;
		mBottom = numeral(-1);
		final CfgSmtToolkit cfgSmtToolkit = icfg.getCfgSmtToolkit();
		mTermTransferrer = new TermTransferrer(cfgSmtToolkit.getManagedScript().getScript(), getScript());
		final IIcfgSymbolTable symbolTable = cfgSmtToolkit.getSymbolTable();
		final var instanceMap = cfgSmtToolkit.getConcurrencyInformation().getThreadInstanceMap();
		mProcedures = getReachableProcedures(icfg.getInitialNodes(), instanceMap);
		mLocalVariables = new HashMap<>();
		mLocalVarIndices = new NestedMap2<>();
		mDefaultLocVars = new HashMap<>();
		mDefaultVarMaps = new NestedMap2<>();
		final Set<IProgramVar> readVariables = petriNet.getTransitions().stream()
				.flatMap(x -> x.getSymbol().getTransformula().getInVars().keySet().stream())
				.collect(Collectors.toSet());
		final Predicate<IProgramVar> keepVariable = readVariables::contains;
		mGlobalVariables = symbolTable.getGlobals().stream().filter(keepVariable).collect(Collectors.toList());
		mDimension = mGlobalVariables.size();
		for (final String proc : mProcedures) {
			final List<IProgramVar> localVars = symbolTable.getLocals(proc).stream().filter(keepVariable)
					.sorted((x, y) -> x.getIdentifier().compareTo(y.getIdentifier())).collect(Collectors.toList());
			mLocalVariables.put(proc, localVars);
			for (int i = 0; i < localVars.size(); i++) {
				final IProgramVar var = localVars.get(i);
				mLocalVarIndices.put(proc, var, i);
				// TODO: This "fresh"-name is only a workaround to avoid name clashes in the different scripts!
				mDefaultVarMaps.put(proc, var,
						mManagedScript.constructFreshTermVariable("fresh_" + var.getGloballyUniqueId(), var.getSort()));
			}
			mDimension += localVars.size() + 1;
			mDefaultLocVars.put(proc, constructAuxVar("loc", proc));
		}
		mLocationIndices = new NestedMap2<>();
		mInstances2Templates = new HashMap<>();
		mTemplates2Instances = new HashMap<>();
		final Set<String> unboundedThreadInstances = new HashSet<>();
		for (final List<ThreadInstance> threadInstances : instanceMap.values()) {
			if (threadInstances.size() >= numberOfThreads) {
				unboundedThreadInstances.add(threadInstances.get(0).getThreadInstanceName());
			}
			for (final ThreadInstance thread : threadInstances) {
				final String instance = thread.getThreadInstanceName();
				final String template = thread.getThreadTemplateName();
				mInstances2Templates.put(instance, template);
				List<String> instances = mTemplates2Instances.get(template);
				if (instances == null) {
					instances = new ArrayList<>();
					mTemplates2Instances.put(template, instances);
				}
				instances.add(instance);
			}
		}
		declareFunction();
		assertInitial(petriNet.getInitialPlaces());
		mInUseErrorLocs = new HashSet<>(cfgSmtToolkit.getConcurrencyInformation().getInUseErrorNodeMap().values());
		assertSafety(petriNet.getAcceptingPlaces());
		for (final ITransition<? extends IIcfgTransition<?>, IPredicate> t : petriNet.getTransitions()) {
			final IIcfgTransition<?> symbol = t.getSymbol();
			final var transition = (Transition<? extends IIcfgTransition<?>, IPredicate>) t;
			final String proc = symbol.getPrecedingProcedure();
			// Exclude "copied" actions in different thread copies (needs symmetry then)
			if (!DUPLICATE_INDUCTIVITY && mInstances2Templates.containsKey(proc)
					&& !unboundedThreadInstances.contains(proc)) {
				assert ADD_SYMMETRY;
				continue;
			}
			assertInductivity(transition);
			if (unboundedThreadInstances.contains(proc)) {
				assertNonInterference(transition);
			}
		}
		assertAuxiliary();
		mResult = mManagedScript.checkSat(this);
	}

	public LBool getResult() {
		return mResult;
	}

	private void assertAuxiliary() {
		// Set boundaries for the locations
		final List<Term> conjuncts = new ArrayList<>();
		for (final String proc : mLocationIndices.keySet()) {
			final Term size = numeral(mLocationIndices.get(proc).size());
			for (final String instance : mTemplates2Instances.getOrDefault(proc, Collections.singletonList(proc))) {
				final Term var = mDefaultLocVars.get(instance);
				conjuncts.add(SmtUtils.geq(getScript(), var, mBottom));
				conjuncts.add(SmtUtils.less(getScript(), var, size));
			}
		}
		assertClause(getPredicate(Collections.emptyMap()), SmtUtils.and(getScript(), conjuncts));
		// Clauses to ensure symmetry
		if (ADD_SYMMETRY) {
			for (final List<String> instances : mTemplates2Instances.values()) {
				for (int i = 0; i < instances.size(); i++) {
					final String thread1 = instances.get(i);
					final List<IProgramVar> vars1 = mLocalVariables.get(thread1);
					final Term loc1 = mDefaultLocVars.get(thread1);
					for (int j = i + 1; j < instances.size(); j++) {
						final String thread2 = instances.get(j);
						final Term loc2 = mDefaultLocVars.get(thread2);
						final NestedMap2<String, IProgramVar, Term> localVarMap = new NestedMap2<>();
						final List<IProgramVar> vars2 = mLocalVariables.get(thread2);
						for (int k = 0; k < vars1.size(); k++) {
							localVarMap.put(thread1, vars1.get(k), mDefaultVarMaps.get(thread2, vars2.get(k)));
							localVarMap.put(thread2, vars2.get(k), mDefaultVarMaps.get(thread1, vars1.get(k)));
						}
						final Map<String, Term> locMap = Map.of(thread1, loc2, thread2, loc1);
						assertClause(getPredicate(Collections.emptyMap()),
								getPredicate(Collections.emptyMap(), localVarMap, locMap));
					}
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

	private void assertClause(final List<Term> terms) {
		assertClause(terms.stream().toArray(Term[]::new));
	}

	// Order Inv(global, location_1, local_1, ..., location_n, local_n)
	private void declareFunction() {
		final Sort[] paramSorts = new Sort[mDimension];
		int i = 0;
		for (final var v : mGlobalVariables) {
			paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
		}
		for (final String proc : mProcedures) {
			// Location
			paramSorts[i++] = getIntSort();
			// Local variables
			for (final IProgramVar v : mLocalVariables.get(proc)) {
				paramSorts[i++] = mTermTransferrer.transferSort(v.getSort());
			}
		}
		mManagedScript.declareFun(this, FUNCTION_NAME, paramSorts, SmtSortUtils.getBoolSort(mManagedScript));
	}

	private Set<String> getReachableProcedures(final Set<IcfgLocation> initialLocations,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> instanceMap) {
		final Set<String> result = initialLocations.stream().map(x -> x.getProcedure())
				.collect(Collectors.toCollection(LinkedHashSet::new));
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final var entry : instanceMap.entrySet()) {
				if (!result.contains(entry.getKey().getPrecedingProcedure())) {
					continue;
				}
				for (final ThreadInstance i : entry.getValue()) {
					if (result.add(i.getThreadInstanceName())) {
						changed = true;
					}
				}
			}
		}
		return result;
	}

	private Term getPredicate(final Map<IProgramVar, ? extends Term> globalVarMap,
			final NestedMap2<String, IProgramVar, Term> localVarMap, final Map<String, Term> locationMap) {
		final Term[] params = new Term[mDimension];
		int i = 0;
		for (final IProgramVar v : mGlobalVariables) {
			final Term term = globalVarMap.get(v);
			params[i++] = mTermTransferrer.transform(term == null ? v.getTerm() : term);
		}
		for (final String proc : mProcedures) {
			params[i++] = locationMap.getOrDefault(proc, mDefaultLocVars.get(proc));
			for (final IProgramVar v : mLocalVariables.get(proc)) {
				final Term localVarTerm = localVarMap.get(proc, v);
				params[i++] =
						mTermTransferrer.transform(localVarTerm == null ? mDefaultVarMaps.get(proc, v) : localVarTerm);
			}
		}
		return getScript().term(FUNCTION_NAME, params);
	}

	private Term getPredicate(final Map<String, Term> locationMap) {
		return getPredicate(Collections.emptyMap(), new NestedMap2<>(), locationMap);
	}

	private void assertInitial(final Collection<IPredicate> initialPlaces) {
		final Map<String, Term> locationMap = new HashMap<>();
		for (final IPredicate place : initialPlaces) {
			if (place instanceof DebugPredicate) {
				final String threadNotInUse = getThreadNotInUse(((DebugPredicate) place).getDebugMessage());
				if (threadNotInUse != null) {
					locationMap.put(threadNotInUse, mBottom);
				}
				// TODO: Do we need to check for threadInUse-places?
			} else if (place instanceof SPredicate) {
				final IcfgLocation loc = ((SPredicate) place).getProgramPoint();
				final String proc = loc.getProcedure();
				locationMap.put(proc, getLocIndexTerm(loc, proc));
			}
		}
		assertClause(getPredicate(locationMap));
	}

	// TODO: Do not use the DebugIdentifier, but BlockEncodingBacktranslator.getLocationMapping to get an identifier
	private Term getLocIndexTerm(final IcfgLocation loc, final String proc) {
		final DebugIdentifier identifier = loc.getDebugIdentifier();
		final String template = mInstances2Templates.getOrDefault(proc, proc);
		Integer index = mLocationIndices.get(template, identifier);
		if (index == null) {
			final Map<DebugIdentifier, Integer> otherIndices = mLocationIndices.get(template);
			index = otherIndices == null ? 0 : otherIndices.size();
			mLocationIndices.put(template, identifier, index);
		}
		return numeral(index);
	}

	private void assertSafety(final Collection<IPredicate> errorPlaces) {
		for (final IPredicate place : errorPlaces) {
			if (place instanceof SPredicate) {
				final IcfgLocation loc = ((SPredicate) place).getProgramPoint();
				if (mInUseErrorLocs.contains(loc)) {
					continue;
				}
				final String proc = loc.getProcedure();
				final Term predicate = getPredicate(Collections.singletonMap(proc, getLocIndexTerm(loc, proc)));
				assertClause(SmtUtils.not(getScript(), predicate));
			}
		}
	}

	private static NestedMap2<String, IProgramVar, Term> constructLocalVarMap(final String proc,
			final Map<IProgramVar, ? extends Term> varMap) {
		final NestedMap2<String, IProgramVar, Term> result = new NestedMap2<>();
		varMap.forEach((k, v) -> result.put(proc, k, v));
		return result;
	}

	private String getThreadNotInUse(final String string) {
		// TODO: Avoid string matching!
		final String notInUse = "NotInUse";
		if (string.endsWith(notInUse)) {
			return string.substring(0, string.length() - notInUse.length());
		}
		return null;
	}

	// TODO: Does setting the arguments (and the thread-id?) work correctly?
	private void assertInductivity(final Transition<? extends IIcfgTransition<?>, IPredicate> transition) {
		final List<Term> terms = new ArrayList<>();
		final Map<String, Term> locMapIn = new HashMap<>();
		final Map<String, Term> locMapOut = new HashMap<>();
		final Set<String> procsIn = new HashSet<>();
		final Set<String> procsOut = new HashSet<>();
		for (final IPredicate place : transition.getPredecessors()) {
			if (place instanceof SPredicate) {
				final IcfgLocation loc = ((SPredicate) place).getProgramPoint();
				final String proc = loc.getProcedure();
				procsIn.add(proc);
				locMapIn.put(proc, getLocIndexTerm(loc, proc));
			} else if (place instanceof DebugPredicate) {
				final String string = ((DebugPredicate) place).getDebugMessage();
				// final String threadInUse = getThreadInUse(string);
				// if (threadInUse != null) {
				// terms.add(SmtUtils.distinct(getScript(), mDefaultLocVars.get(threadInUse), mBottom));
				// }
				final String threadNotInUse = getThreadNotInUse(string);
				if (threadNotInUse != null) {
					final Term old = locMapIn.put(threadNotInUse, mBottom);
					assert old == null;
				}
			}
		}
		for (final IPredicate place : transition.getSuccessors()) {
			if (place instanceof SPredicate) {
				final IcfgLocation loc = ((SPredicate) place).getProgramPoint();
				final String proc = loc.getProcedure();
				procsOut.add(proc);
				locMapOut.put(proc, getLocIndexTerm(loc, proc));
			} else if (place instanceof DebugPredicate) {
				final String threadNotInUse = getThreadNotInUse(((DebugPredicate) place).getDebugMessage());
				if (threadNotInUse != null) {
					locMapOut.put(threadNotInUse, mBottom);
				}
			}
		}
		final IIcfgTransition<?> symbol = transition.getSymbol();
		final TransFormula transformula = symbol.getTransformula();
		final Map<IProgramVar, TermVariable> inVars = transformula.getInVars();
		final Map<IProgramVar, TermVariable> outVars = transformula.getOutVars();
		terms.add(getPredicate(inVars, constructLocalVarMap(symbol.getPrecedingProcedure(), inVars), locMapIn));
		terms.add(mTermTransferrer.transform(transformula.getFormula()));
		terms.add(getPredicate(outVars, constructLocalVarMap(symbol.getSucceedingProcedure(), outVars), locMapOut));
		assertClause(terms);
		// Add the possibility that the fork/join does nothing, i.e. works on an "invisible" thread
		// TODO: Can there be a sync-action that modifies variables that are not local vars of the forked thread?
		if (procsIn.size() > 1 || procsOut.size() > 1) {
			final Set<String> commonProcs = DataStructureUtils.intersection(procsIn, procsOut);
			assertClause(getPredicate(commonProcs.stream().collect(Collectors.toMap(x -> x, locMapIn::get))),
					getPredicate(commonProcs.stream().collect(Collectors.toMap(x -> x, locMapOut::get))));
		}
	}

	private void assertNonInterference(final Transition<? extends IIcfgTransition<?>, IPredicate> transition) {
		final IIcfgTransition<?> symbol = transition.getSymbol();
		final List<Term> terms = new ArrayList<>();
		final TransFormula transformula = symbol.getTransformula();
		final String originalThread = symbol.getPrecedingProcedure();
		final Map<IProgramVar, TermVariable> inVars = transformula.getInVars();
		terms.add(getPredicate(inVars, new NestedMap2<>(), Collections.emptyMap()));
		for (final String thread : mTemplates2Instances.get(mInstances2Templates.get(originalThread))) {
			final List<IProgramVar> newLocalVars = mLocalVariables.get(thread);
			final NestedMap2<String, IProgramVar, Term> localVarMap = new NestedMap2<>();
			for (final Entry<IProgramVar, TermVariable> entry : inVars.entrySet()) {
				final Integer index = mLocalVarIndices.get(originalThread, entry.getKey());
				if (index != null) {
					localVarMap.put(thread, newLocalVars.get(index), entry.getValue());
				}
			}
			terms.add(getPredicate(inVars, localVarMap,
					Collections.singletonMap(thread, getLocIndexTerm(symbol.getSource(), thread))));
		}
		terms.add(mTermTransferrer.transform(transformula.getFormula()));
		terms.add(getPredicate(transformula.getOutVars(), new NestedMap2<>(), Collections.emptyMap()));
		assertClause(terms);
	}

	private Script getScript() {
		return mManagedScript.getScript();
	}
}

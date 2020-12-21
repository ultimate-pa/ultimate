package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ThreadGeneralization {
	private static final String FUNCTION_NAME = "Inv";

	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final boolean mResult;

	public ThreadGeneralization(final ILogger logger, final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> icfg, final Collection<IPredicate> predicates,
			final ConcurrencyInformation oldConcurrency) {
		mLogger = logger;
		// TODO: Name? / correct settings?
		// TODO: Try different solvers?
		// TODO: Create a horn-solver instead (need to define some function first?)
		// final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
		// .setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_TIMEOUT, Logics.HORN)
		// .setSolverMode(SolverMode.External_DefaultMode);
		// final Script script = SolverBuilder.buildAndInitializeSolver(services, solverSettings, "HornClauseSolver");
		// mManagedScript = new ManagedScript(services, script);
		final CfgSmtToolkit cfgSmtToolkit = icfg.getCfgSmtToolkit();
		// TODO: We could refine this!
		final Set<String> initialProcedures =
				icfg.getInitialNodes().stream().map(x -> x.getProcedure()).collect(Collectors.toSet());
		final Set<String> reachableProcedures = oldConcurrency.getThreadInstanceMap().keySet().stream()
				.map(x -> x.getNameOfForkedProcedure()).collect(Collectors.toSet());
		reachableProcedures.addAll(initialProcedures);
		mManagedScript = cfgSmtToolkit.getManagedScript();
		final Map<String, TermVariable> procedureCounters =
				reachableProcedures.stream().collect(Collectors.toMap(x -> x, x -> constructAuxVar("proc_" + x)));
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		final List<IcfgLocation> locations = reachableProcedures.stream()
				.flatMap(x -> new IcfgLocationIterator<>(entryNodes.get(x)).asStream()).collect(Collectors.toList());
		final Map<IcfgLocation, TermVariable> locCounters =
				locations.stream().collect(Collectors.toMap(x -> x, x -> constructAuxVar("lc_" + x)));
		final Set<Term> initialValues =
				reachableProcedures.stream()
						.map(x -> SmtUtils.binaryEquality(getScript(), procedureCounters.get(x),
								getScript().numeral(initialProcedures.contains(x) ? "1" : "0")))
						.collect(Collectors.toSet());
		locCounters.values()
				.forEach(x -> initialValues.add(SmtUtils.binaryEquality(getScript(), x, getScript().numeral("0"))));
		final IIcfgSymbolTable symbolTable = cfgSmtToolkit.getSymbolTable();
		final Set<ILocalProgramVar> localVariables = reachableProcedures.stream()
				.flatMap(x -> symbolTable.getLocals(x).stream()).collect(Collectors.toSet());
		mResult = checkHornClauses() == LBool.SAT;
	}

	public boolean isProofModular() {
		return mResult;
	}

	private LBool checkHornClauses() {
		mManagedScript.lock(this);
		mManagedScript.push(this, 1);
		// declareFunction();
		// TODO: Call assertHornClause for all states/actions etc.
		// assertHornClause(
		// Collections
		// .singleton(new Triple<>(Collections.emptyMap(), mInitialLocation.getDebugIdentifier(), null)),
		// Collections.emptySet(), SmtUtils.not(mManagedScript.getScript(),
		// mHoareAnnotations.get(Collections.singletonList(mForkLocation))));
		final LBool result = mManagedScript.checkSat(this);
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		return result;
	}

	private Script getScript() {
		return mManagedScript.getScript();
	}

	private TermVariable constructAuxVar(final String name) {
		return mManagedScript.constructFreshTermVariable(name, getIntSort());
	}

	private Sort getIntSort() {
		return SmtSortUtils.getIntSort(mManagedScript);
	}

	// private int getDimension() {
	// return mVariables.size() + mLocations.size();
	// }
	//
	// // Order Inv(vars, lc, loc)
	// private void declareFunction() {
	// final Sort[] paramSorts = new Sort[getDimension()];
	// int i = 0;
	// while (i < mVariables.size()) {
	// paramSorts[i] = mVariables.get(i++).getSort();
	// }
	// // Add the location counters + current location number
	// while (i < paramSorts.length) {
	// paramSorts[i++] = getIntSort();
	// }
	// mManagedScript.declareFun(this, FUNCTION_NAME, paramSorts, SmtSortUtils.getBoolSort(mManagedScript));
	// }
	//
	// private void assertHornClause(
	// final Set<Triple<Map<IProgramVar, Term>, DebugIdentifier, DebugIdentifier>> applications,
	// final Set<Triple<Map<IProgramVar, Term>, DebugIdentifier, DebugIdentifier>> negatedApplications,
	// final Term additionalTerm) {
	// final Script script = mManagedScript.getScript();
	// final Set<Term> disjuncts = new HashSet<>(applications.size() + negatedApplications.size() + 1);
	// disjuncts.add(additionalTerm);
	// negatedApplications.forEach(x -> disjuncts.add(SmtUtils.not(script, applyFunction(x))));
	// applications.forEach(x -> disjuncts.add(applyFunction(x)));
	// final Term disjunction = SmtUtils.or(script, disjuncts);
	// mLogger.info(disjunction);
	// final Term quantified = script.quantifier(QuantifiedFormula.FORALL, disjunction.getFreeVars(), disjunction);
	// mManagedScript.assertTerm(this, quantified);
	// }
	//
	// private Term applyFunction(final Triple<Map<IProgramVar, Term>, DebugIdentifier, DebugIdentifier> triple) {
	// final Map<IProgramVar, Term> varMapping = triple.getFirst();
	// final Script script = mManagedScript.getScript();
	// final Term[] params = new Term[getDimension()];
	// int i = 0;
	// for (final IProgramVar g : mVariables) {
	// params[i++] = varMapping.getOrDefault(g, g.getTerm());
	// }
	// final DebugIdentifier currentLocation = triple.getSecond();
	// final Map<DebugIdentifier, Term> loc2Term;
	// if (currentLocation == null) {
	// loc2Term = mLocations;
	// } else {
	// loc2Term = mLocations.keySet().stream().collect(Collectors.toMap(x -> x, x -> script.numeral("0")));
	// loc2Term.put(currentLocation, script.numeral("1"));
	// }
	// for (final DebugIdentifier loc : mLocations.keySet()) {
	// if (loc.equals(mInitialLocation.getDebugIdentifier())) {
	// continue;
	// }
	// Term term = loc2Term.get(loc);
	// if (Objects.equals(triple.getThird(), loc)) {
	// term = SmtUtils.sum(script, getIntSort(), term, script.numeral("1"));
	// }
	// params[i++] = term;
	// }
	// if (currentLocation == null) {
	// params[i] = constructAuxVar("loc");
	// } else {
	// int index = 0;
	// for (final var loc : mLocations.keySet()) {
	// if (loc.equals(currentLocation)) {
	// break;
	// }
	// index++;
	// }
	// if (index == mLocations.size()) {
	// throw new AssertionError(currentLocation + " not contained");
	// }
	// params[i] = script.numeral(BigInteger.valueOf(index));
	// }
	// return script.term(FUNCTION_NAME, params);
	// }
}

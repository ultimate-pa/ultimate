package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MultiDimensionalSelectOverStoreEliminationUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * IInterpolantProvider using weakest precondition. For every state we use the conjunction of wp for all outgoing
 * transitions. For better interpolants, we abstract all variables away (using forall), that are not present in the
 * initial interpolants.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class WpInterpolantProvider<LETTER extends IIcfgTransition<?>> implements IInterpolantProvider<LETTER> {

	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private final ArrayIndexEqualityManager mAiem;
	private final IHoareTripleChecker mHtc;

	public WpInterpolantProvider(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit) {
		mManagedScript = managedScript;
		mServices = services;
		mLogger = logger;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mPredicateUnifier = predicateUnifier;
		mHtc = new IncrementalHoareTripleChecker(csToolkit, false);
		mPredicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));
		// ArrayIndexEqualityManager to eliminate stores with true as context (i.e. without any known equalities)
		mAiem = new ArrayIndexEqualityManager(new ThreeValuedEquivalenceRelation<>(),
				mManagedScript.getScript().term("true"), QuantifiedFormula.EXISTS, mLogger, mManagedScript);
		mAiem.unlockSolver();
	}

	private <STATE> List<STATE> revTopSort(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		final Map<STATE, Set<STATE>> successors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			if (stateMap.containsKey(state)) {
				continue;
			}
			final Set<STATE> succs = new HashSet<>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (!stateMap.containsKey(succ)) {
					succs.add(succ);
				}
			}
			successors.put(state, succs);
		}
		return new TopologicalSorter<>(successors::get).reversedTopologicalOrdering(successors.keySet()).get();
	}

	@Override
	public <STATE> Map<STATE, IPredicate> getInterpolants(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		final Set<TermVariable> ipVars = stateMap.values().stream()
				.flatMap(x -> x.getVars().stream().map(IProgramVar::getTermVariable)).collect(Collectors.toSet());
		for (final STATE state : revTopSort(automaton, stateMap)) {
			// Calculate the conjunction of wp for all successors (if not ignored)
			final List<Pair<IPredicate, LETTER>> succs = new ArrayList<>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final IPredicate succ = stateMap.get(edge.getSucc());
				if (succ != null) {
					succs.add(new Pair<>(succ, edge.getLetter()));
				}
			}
			if (succs.isEmpty()) {
				continue;
			}
			// Quantify variables not contained in the original interpolants away
			final Term wp = SmtUtils.and(mManagedScript.getScript(), succs.stream()
					.map(x -> mPredicateTransformer.weakestPrecondition(x.getFirst(), x.getSecond().getTransformula()))
					.collect(Collectors.toList()));
			final Set<TermVariable> unnecessaryVars =
					Arrays.stream(wp.getFreeVars()).filter(x -> !ipVars.contains(x)).collect(Collectors.toSet());
			final Term quantified =
					SmtUtils.quantifier(mManagedScript.getScript(), QuantifiedFormula.FORALL, unnecessaryVars, wp);
			// TODO: replaceMod is only a workaround!
			final Term modReplaced = replaceMod(quantified);
			Term term = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, modReplaced,
					mSimplificationTechnique, mXnfConversionTechnique);
			// Ignore the interpolant, if it still contains quantifiers
			if (!QuantifierUtils.isQuantifierFree(term)) {
				continue;
			}
			// Eliminate all stores (using case distinction on index equalities)
			final List<MultiDimensionalSelectOverNestedStore> stores = MultiDimensionalSelectOverNestedStore
					.extractMultiDimensionalSelectOverStores(mManagedScript.getScript(), term);
			for (final MultiDimensionalSelectOverNestedStore m : stores) {
				term = MultiDimensionalSelectOverStoreEliminationUtils.replace(mManagedScript, mAiem, term, m);
			}
			// Add the simplified wp conjunction as a predicate
			final IPredicate pred = mPredicateUnifier.getOrConstructPredicate(term);
			for (final Pair<IPredicate, LETTER> pair : succs) {
				// assert mHtc.checkInternal(pred, (IInternalAction) pair.getSecond(),
				// pair.getFirst()) == Validity.VALID : pred + ": " + succs;
				// "Hoare triple {" + pred + "} " + pair.getSecond() + " {"
				// + pair.getFirst() + "} is not valid.";
				// TODO: Only check, revert later
				if (mHtc.checkInternal(pred, (IInternalAction) pair.getSecond(), pair.getFirst()) != Validity.VALID) {
					PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, quantified,
							mSimplificationTechnique, mXnfConversionTechnique);
				}
			}
			stateMap.put(state, pred);
		}
		return stateMap;
	}

	private Term replaceMod(final Term term) {
		Term inner = term;
		final List<Pair<Integer, List<TermVariable>>> quantifiers = new ArrayList<>();
		final Script script = mManagedScript.getScript();
		while (inner instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) inner;
			inner = qf.getSubformula();
			quantifiers.add(new Pair<>(qf.getQuantifier(), Arrays.asList(qf.getVariables())));
		}
		final Map<Term, Term> substitution = new HashMap<>();
		final List<TermVariable> newVars = new ArrayList<>();
		for (final ApplicationTerm a : new ApplicationTermFinder("mod", true).findMatchingSubterms(inner)) {
			final Term p0 = a.getParameters()[0];
			final Term p1 = a.getParameters()[1];
			final TermVariable var = mManagedScript.constructFreshTermVariable("mod_var", p1.getSort());
			final Term relaced = SmtUtils.sum(script, a.getSort(), p0, SmtUtils.mul(script, p1.getSort(), var, p1));
			substitution.put(a, relaced);
			newVars.add(var);
		}
		quantifiers.add(new Pair<>(QuantifiedFormula.EXISTS, newVars));
		Term result = new Substitution(mManagedScript, substitution).transform(inner);
		for (int i = quantifiers.size() - 1; i >= 0; i--) {
			final Pair<Integer, List<TermVariable>> pair = quantifiers.get(i);
			result = SmtUtils.quantifier(script, pair.getFirst(), pair.getSecond(), result);
		}
		return result;
	}
}

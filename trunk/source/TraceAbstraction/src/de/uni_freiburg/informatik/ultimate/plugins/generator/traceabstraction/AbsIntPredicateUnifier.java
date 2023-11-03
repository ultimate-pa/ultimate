package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

public class AbsIntPredicateUnifier<STATE extends IAbstractState<STATE>> extends PredicateUnifier {
	public AbsIntPredicateUnifier(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory predicateFactory,
			final IIcfgSymbolTable symbolTable, 
			final XnfConversionTechnique xnfConversionTechnique, final IPredicate... initialPredicates) {
		super(logger, services, mgdScript, predicateFactory, symbolTable, SimplificationTechnique.NONE,
				xnfConversionTechnique, initialPredicates);
	}

	@Override
	protected IPredicate constructNewPredicate(final Term term, final IPredicate originalPredicate) {
		final IPredicate unifiedPred = super.constructNewPredicate(term, originalPredicate);
		if (unifiedPred instanceof AbsIntPredicate<?>) {
			assert assertValidPredicate((AbsIntPredicate<?>) unifiedPred) : "Created invalid predicate";
			return unifiedPred;
		}
		if (originalPredicate instanceof AbsIntPredicate<?>) {
			final AbsIntPredicate<?> rtr =
					new AbsIntPredicate<>(unifiedPred, ((AbsIntPredicate<?>) originalPredicate).getAbstractStates());
			assert assertValidPredicate(rtr) : "Created invalid predicate";
			return rtr;
		}
		return unifiedPred;
	}

	@Override
	protected IPredicate postProcessPredicateForConjunction(final IPredicate unified,
			final Set<IPredicate> conjunctPredicates) {
		@SuppressWarnings("unchecked")
		final Set<DisjunctiveAbstractState<STATE>> multistates =
				conjunctPredicates.stream().map(a -> ((AbsIntPredicate<STATE>) a).getAbstractStates())
						.map(a -> DisjunctiveAbstractState.createDisjunction(a)).collect(Collectors.toSet());
		final Set<DisjunctiveAbstractState<STATE>> synchronizedMultiStates =
				AbsIntUtil.synchronizeVariables(multistates);
		assert sameVars(synchronizedMultiStates.stream().flatMap(a -> a.getStates().stream())
				.collect(Collectors.toSet())) : "Synchronize failed";
		final DisjunctiveAbstractState<STATE> conjunction = synchronizedMultiStates.stream()
				.reduce((a, b) -> a.intersect(b)).orElseThrow(() -> new AssertionError("No predicates given"));
		final AbsIntPredicate<?> rtr = new AbsIntPredicate<>(unified, conjunction);
		assert assertValidPredicate(rtr) : "Created invalid predicate";
		return rtr;
	}

	@Override
	protected IPredicate postProcessPredicateForDisjunction(final IPredicate unified,
			final Set<IPredicate> disjunctPredicates) {
		if (unified instanceof AbsIntPredicate<?>) {
			return unified;
		}
		final AbsIntPredicate<?> rtr = new AbsIntPredicate<>(unified, toDisjunctiveState(disjunctPredicates));
		assert assertValidPredicate(rtr) : "Created invalid predicate";
		return rtr;
	}

	@SuppressWarnings("unchecked")
	private DisjunctiveAbstractState<STATE> toDisjunctiveState(final Set<IPredicate> preds) {
		if (preds == null || preds.isEmpty()) {
			return new DisjunctiveAbstractState<>();
		}
		final Set<STATE> allStates = new HashSet<>();
		for (final IPredicate pred : preds) {
			final Set<STATE> states = ((AbsIntPredicate<STATE>) pred).getAbstractStates();
			for (final STATE state : states) {
				if (state instanceof DisjunctiveAbstractState<?>) {
					allStates.addAll(((DisjunctiveAbstractState<STATE>) state).getStates());
				} else {
					allStates.add(state);
				}
			}

		}
		return DisjunctiveAbstractState.createDisjunction(AbsIntUtil.synchronizeVariables(allStates));
	}

	private boolean sameVars(final Set<STATE> allStates) {
		final Set<IProgramVarOrConst> someVars = allStates.iterator().next().getVariables();
		return allStates.stream().allMatch(a -> a.getVariables().equals(someVars));
	}

	private boolean assertValidPredicate(final AbsIntPredicate<?> pred) {
		final Script script = mMgdScript.getScript();
		final List<Term> terms =
				pred.getAbstractStates().stream().map(a -> a.getTerm(script)).collect(Collectors.toList());
		final Term stateTerm = SmtUtils.and(script, terms);
		final Term checkTerm = script.term("distinct", pred.getFormula(), stateTerm);
		final LBool result = SmtUtils.checkSatTerm(script, checkTerm);
		if (result == LBool.UNSAT || result == LBool.UNKNOWN) {
			return true;
		}
		mLogger.fatal("Invalid predicate! Predicate and state conjunction should be equal, but it is not.");
		mLogger.fatal("Pred: "
				+ SmtUtils.simplify(mMgdScript, pred.getFormula(), mServices, SimplificationTechnique.SIMPLIFY_DDA)
						.toStringDirect());
		mLogger.fatal("States: " + SmtUtils
				.simplify(mMgdScript, stateTerm, mServices, SimplificationTechnique.SIMPLIFY_DDA).toStringDirect());
		mLogger.fatal("Conjunctive states: ");
		for (final IAbstractState<?> state : pred.getAbstractStates()) {
			mLogger.fatal(state.toLogString());
			mLogger.fatal(SmtUtils
					.simplify(mMgdScript, state.getTerm(script), mServices, SimplificationTechnique.SIMPLIFY_DDA)
					.toStringDirect());
		}
		return false;
	}

}
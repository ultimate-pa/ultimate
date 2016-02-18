package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationAutomatonGenerator {

	private static final boolean CANNIBALIZE = false;
	private static final long PRINT_PREDS_LIMIT = 30;

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final SmtManager mSmtManager;

	public AbstractInterpretationAutomatonGenerator(final IUltimateServiceProvider services,
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
			final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, IPredicate> aiResult,
			final PredicateUnifier predUnifier, final SmtManager smtManager) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		mSmtManager = smtManager;

		mResult = getTermAutomaton(oldAbstraction, aiResult.getTerms(), predUnifier);
	}

	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getTermAutomaton(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final Set<Term> terms,
			final PredicateUnifier predicateUnifier) {
		mLogger.info("Creating automaton from AI predicates (Cannibalize=" + CANNIBALIZE + ").");
		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());
		final Set<IPredicate> predicates = new HashSet<>();
		result.addState(true, false, predicateUnifier.getTruePredicate());
		predicates.add(predicateUnifier.getTruePredicate());

		final IPredicate falsePred = predicateUnifier.getFalsePredicate();
		for (final Term term : terms) {
			if (term == null) {
				continue;
			}

			final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(term, mSmtManager.getBoogie2Smt());
			final IPredicate newPred = predicateUnifier.getOrConstructPredicate(tvp);
			if (!predicates.add(newPred)) {
				continue;
			}
			result.addState(false, newPred == falsePred, newPred);
		}

		if (result.getFinalStates().isEmpty() || !predicates.contains(falsePred)) {
			result.addState(false, true, predicateUnifier.getFalsePredicate());
		}

		if (PRINT_PREDS_LIMIT < predicates.size()) {
			mLogger.info("Using " + predicates.size() + " predicates from AI: " + String.join(",",
					predicates.stream().limit(PRINT_PREDS_LIMIT).map(a -> a.toString()).collect(Collectors.toList()))
					+ "...");
		} else {
			mLogger.info("Using " + predicates.size() + " predicates from AI: "
					+ String.join(",", predicates.stream().map(a -> a.toString()).collect(Collectors.toList())));
		}

		return result;
	}
	
	private NestedWordAutomaton<CodeBlock, IPredicate> getTermAutomaton(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final Map<IPredicate, Term> loc2Term,
			final PredicateUnifier predicateUnifier) {
		mLogger.info("Creating automaton from AI predicates (Cannibalize=" + CANNIBALIZE + ").");
		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());
		final Set<IPredicate> predicates = new HashSet<>();
		result.addState(true, false, predicateUnifier.getTruePredicate());
		predicates.add(predicateUnifier.getTruePredicate());

		final IPredicate falsePred = predicateUnifier.getFalsePredicate();
		for (final Entry<IPredicate, Term> entry : loc2Term.entrySet()) {
			final ISLPredicate loc = (ISLPredicate) entry.getKey();
			final Term term = entry.getValue();
			if (CANNIBALIZE) {
				addStateCannibalize(oldAbstraction, predicateUnifier, result, predicates, falsePred, loc, term);
			} else {
				addState(oldAbstraction, predicateUnifier, result, predicates, falsePred, loc, term);
			}
		}

		if (result.getFinalStates().isEmpty() || !predicates.contains(falsePred)) {
			result.addState(false, true, predicateUnifier.getFalsePredicate());
		}

		if (PRINT_PREDS_LIMIT < predicates.size()) {
			mLogger.info("Using " + predicates.size() + " predicates from AI: " + String.join(",",
					predicates.stream().limit(PRINT_PREDS_LIMIT).map(a -> a.toString()).collect(Collectors.toList()))
					+ "...");
		} else {
			mLogger.info("Using " + predicates.size() + " predicates from AI: "
					+ String.join(",", predicates.stream().map(a -> a.toString()).collect(Collectors.toList())));
		}

		return result;
	}

	private void addState(final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
			final PredicateUnifier predicateUnifier, final NestedWordAutomaton<CodeBlock, IPredicate> result,
			final Set<IPredicate> alreadyUsed, final IPredicate falsePred, final ISLPredicate slPred, final Term term) {
		if (term == null) {
			return;
		}

		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(term, mSmtManager.getBoogie2Smt());
		final IPredicate newPred = predicateUnifier.getOrConstructPredicate(tvp);
		if (!alreadyUsed.add(newPred)) {
			return;
		}
		if (newPred == falsePred) {
			result.addState(oldAbstraction.isInitial(slPred), true, newPred);
		} else {
			result.addState(oldAbstraction.isInitial(slPred), oldAbstraction.isFinal(slPred), newPred);
		}
	}

	private void addStateCannibalize(final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
			final PredicateUnifier predicateUnifier, final NestedWordAutomaton<CodeBlock, IPredicate> result,
			final Set<IPredicate> alreadyUsed, final IPredicate falsePred, final ISLPredicate slPred, final Term term) {
		if (term == null) {
			return;
		}

		final Set<IPredicate> newPreds = predicateUnifier.cannibalize(false, term);

		for (final IPredicate newPred : newPreds) {
			if (!alreadyUsed.add(newPred)) {
				continue;
			}
			if (newPred == falsePred) {
				result.addState(oldAbstraction.isInitial(slPred), true, newPred);
			} else {
				result.addState(oldAbstraction.isInitial(slPred), oldAbstraction.isFinal(slPred), newPred);
			}
		}
	}
}

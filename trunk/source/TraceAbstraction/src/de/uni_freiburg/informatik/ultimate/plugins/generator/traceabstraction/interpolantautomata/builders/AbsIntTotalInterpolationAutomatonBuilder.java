package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * Builder for an interpolant automaton from abstract interpretation counterexamples using total interpolation (all
 * possible edges between abstract states are being inserted).
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class AbsIntTotalInterpolationAutomatonBuilder implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {

	private static final long PRINT_PREDS_LIMIT = 30;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final SmtManager mSmtManager;
	private final IRun<CodeBlock, IPredicate> mCurrentCounterExample;

	public AbsIntTotalInterpolationAutomatonBuilder(final IUltimateServiceProvider services,
	        final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
	        final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
	        final PredicateUnifier predicateUnifier, final SmtManager smtManager,
	        final IRun<CodeBlock, IPredicate> currentCounterExample,
	        final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSmtManager = smtManager;
		mCurrentCounterExample = currentCounterExample;
		mResult = constructAutomaton(oldAbstraction, aiResult, predicateUnifier);
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> constructAutomaton(
	        final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction,
	        final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> aiResult,
	        final PredicateUnifier predicateUnifier) {

		mLogger.info("Creating total interpolated automaton from AI predicates.");

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
		        new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
		        oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());

		final NestedRun<CodeBlock, IPredicate> counterExample = (NestedRun<CodeBlock, IPredicate>) mCurrentCounterExample;
		final Word<CodeBlock> word = counterExample.getWord();

		final int wordLength = word.length();
		assert wordLength > 1 : "Unexpected: length of word smaller or equal to 1.";

		final Map<Call, IPredicate> callHierarchyPredicates = new HashMap<>();

		final IPredicate falsePredicate = predicateUnifier.getFalsePredicate();
		final Set<IPredicate> alreadyThereAsState = new HashSet<>();
		IPredicate previous = predicateUnifier.getTruePredicate();
		alreadyThereAsState.add(previous);
		result.addState(true, false, previous);

		final Map<IAbstractState<?, CodeBlock, IBoogieVar>, IPredicate> stateToPredicate = new HashMap<>();

		for (int i = 0; i < wordLength; i++) {
			final CodeBlock symbol = word.getSymbol(i);

			final Set<IAbstractState<?, CodeBlock, IBoogieVar>> nextStates = (Set<IAbstractState<?, CodeBlock, IBoogieVar>>) aiResult
			        .getLoc2States().get(symbol.getTarget());

			final IPredicate target;
			if (nextStates == null) {
				target = falsePredicate;
			} else {
				final Map<IAbstractState<?, CodeBlock, IBoogieVar>, IPredicate> map = nextStates.stream()
				        .collect(Collectors.toMap(Function.identity(), s -> predicateUnifier.getOrConstructPredicate(
				                s.getTerm(mSmtManager.getScript(), mSmtManager.getBoogie2Smt()))));
				stateToPredicate.putAll(map);

				target = predicateUnifier
				        .getOrConstructPredicateForDisjunction(map.values().stream().collect(Collectors.toSet()));

				if (mLogger.isDebugEnabled()) {
					if (i == 0) {
						mLogger.debug("------------------------------------------------");
					}
					mLogger.debug("Transition: " + symbol);
					mLogger.debug("Original Target States: " + nextStates);
					mLogger.debug("Target Term: " + target);
					mLogger.debug("------------------------------------------------");
				}
			}

			if (alreadyThereAsState.add(target)) {
				result.addState(false, falsePredicate.equals(target), target);
			}

			// Add transition
			if (symbol instanceof Call) {
				result.addCallTransition(previous, symbol, target);
				callHierarchyPredicates.put((Call) symbol, previous);
			} else if (symbol instanceof Return) {
				final Return returnSymbol = (Return) symbol;
				final IPredicate hierarchyState = callHierarchyPredicates.get(returnSymbol.getCorrespondingCall());
				assert hierarchyState != null : "Return does not have a corresponding call.";
				result.addReturnTransition(previous, hierarchyState, symbol, target);
			} else {
				result.addInternalTransition(previous, symbol, target);
			}

			previous = target;
		}

		// Add self-loops to final states
		if (!result.getFinalStates().isEmpty()) {
			for (final IPredicate finalState : result.getFinalStates()) {
				oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
			}
		}

		if (PRINT_PREDS_LIMIT < alreadyThereAsState.size()) {
			mLogger.info("Using "
			        + alreadyThereAsState.size() + " predicates from AI: " + String.join(",", alreadyThereAsState
			                .stream().limit(PRINT_PREDS_LIMIT).map(a -> a.toString()).collect(Collectors.toList()))
			        + "...");
		} else {
			mLogger.info("Using " + alreadyThereAsState.size() + " predicates from AI: " + String.join(",",
			        alreadyThereAsState.stream().map(a -> a.toString()).collect(Collectors.toList())));
		}

		final IAbstractPostOperator<?, CodeBlock, IBoogieVar> postOperator = aiResult.getUsedDomain().getPostOperator();
		final Iterator<CodeBlock> letterIterator = oldAbstraction.getAlphabet().iterator();

		final Set<IAbstractState<?, CodeBlock, IBoogieVar>> allStates = stateToPredicate.keySet();

		while (letterIterator.hasNext()) {
			final CodeBlock currentLetter = letterIterator.next();

			final Iterator<IAbstractState<?, CodeBlock, IBoogieVar>> stateIterator = allStates.iterator();
			while (stateIterator.hasNext()) {
				final IAbstractState<?, CodeBlock, IBoogieVar> current = stateIterator.next();
				final List<IAbstractState> post = applyPostInternally(current, postOperator, currentLetter);

				for (final IAbstractState postState : post) {
					if (allStates.contains(postState)) {
						throw new UnsupportedOperationException("YASADDASD");
					}
				}
			}
		}

		return result;
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private static List<IAbstractState> applyPostInternally(final IAbstractState<?, CodeBlock, IBoogieVar> currentState,
	        final IAbstractPostOperator postOperator, final CodeBlock transition) {
		return postOperator.apply(currentState, transition);
	}
}

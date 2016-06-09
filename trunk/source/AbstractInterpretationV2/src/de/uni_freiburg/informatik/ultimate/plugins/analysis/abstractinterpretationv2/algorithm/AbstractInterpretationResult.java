package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class AbstractInterpretationResult<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION>
		implements IAbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> {

	private final List<AbstractCounterexample<STATE, ACTION, VARDECL, LOCATION>> mCounterexamples;
	private final AbstractInterpretationBenchmark<ACTION, LOCATION> mBenchmark;
	private final Map<LOCATION, Term> mLoc2Term;
	private final Set<Term> mTerms;

	protected AbstractInterpretationResult() {
		mCounterexamples = new ArrayList<>();
		mBenchmark = new AbstractInterpretationBenchmark<>();
		mLoc2Term = new HashMap<LOCATION, Term>();
		mTerms = new LinkedHashSet<>();
	}

	protected void reachedError(final ITransitionProvider<ACTION, LOCATION> transitionProvider,
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> finalItem, final STATE postState) {

		final List<Triple<STATE, LOCATION, ACTION>> abstractExecution = new ArrayList<>();

		ACTION transition = finalItem.getAction();
		abstractExecution.add(new Triple<>(postState, transitionProvider.getTarget(transition), transition));

		STATE post = finalItem.getPreState();
		WorklistItem<STATE, ACTION, VARDECL, LOCATION> current = finalItem.getPredecessor();
		while (current != null) {
			transition = current.getAction();
			abstractExecution.add(new Triple<>(post, transitionProvider.getTarget(transition), transition));
			post = current.getPreState();
			current = current.getPredecessor();
		}

		Collections.reverse(abstractExecution);
		mCounterexamples
				.add(new AbstractCounterexample<>(post, transitionProvider.getSource(transition), abstractExecution));
	}

	protected void saveTerms(IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> rootStateStorage, ACTION start,
			Script script, Boogie2SMT bpl2smt) {
		mLoc2Term.putAll(rootStateStorage.getLoc2Term(start, script, bpl2smt));
		mTerms.addAll(rootStateStorage.getTerms(start, script, bpl2smt));
	}

	@Override
	public Map<LOCATION, Term> getLoc2Term() {
		return mLoc2Term;
	}

	@Override
	public List<AbstractCounterexample<STATE, ACTION, VARDECL, LOCATION>> getCounterexamples() {
		return mCounterexamples;
	}

	@Override
	public boolean hasReachedError() {
		return !mCounterexamples.isEmpty();
	}

	public AbstractInterpretationBenchmark<ACTION, LOCATION> getBenchmark() {
		return mBenchmark;
	}

	@Override
	public Set<Term> getTerms() {
		return mTerms;
	}

	@Override
	public String toString() {
		return toSimplifiedString(a -> a.toStringDirect());
	}

	@Override
	public String toSimplifiedString(Function<Term, String> funSimplify) {
		final StringBuilder sb = new StringBuilder();
		if (hasReachedError()) {
			sb.append("AI reached error location.");
		} else {
			sb.append("AI did not reach error location.");
		}
		if (getTerms() != null) {
			sb.append(" Found terms ");
			sb.append(String.join(", ", getTerms().stream().map(a -> funSimplify.apply(a)).collect(Collectors.toList())));
		}
		return sb.toString();
	}
}

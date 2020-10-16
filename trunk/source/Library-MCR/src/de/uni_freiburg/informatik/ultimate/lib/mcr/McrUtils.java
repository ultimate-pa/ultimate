package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Arrays;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;

public class McrUtils {
	private McrUtils() {
	}

	public static <STATE> List<STATE> topSort(final INestedWordAutomaton<?, STATE> automaton,
			final Map<STATE, ?> stateMap) {
		final Map<STATE, Set<STATE>> successors = buildSuccessorMap(automaton, stateMap);
		return new TopologicalSorter<>(successors::get).topologicalOrdering(successors.keySet()).get();
	}

	public static <STATE> List<STATE> revTopSort(final INestedWordAutomaton<?, STATE> automaton,
			final Map<STATE, ?> stateMap) {
		final Map<STATE, Set<STATE>> successors = buildSuccessorMap(automaton, stateMap);
		return new TopologicalSorter<>(successors::get).reversedTopologicalOrdering(successors.keySet()).get();
	}

	private static <STATE> Map<STATE, Set<STATE>> buildSuccessorMap(final INestedWordAutomaton<?, STATE> automaton,
			final Map<STATE, ?> stateMap) {
		final Map<STATE, Set<STATE>> successors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			if (stateMap.containsKey(state)) {
				continue;
			}
			final Set<STATE> succs = new HashSet<>();
			for (final OutgoingInternalTransition<?, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (!stateMap.containsKey(succ)) {
					succs.add(succ);
				}
			}
			successors.put(state, succs);
		}
		return successors;
	}

	public static Set<TermVariable> getTermVariables(final Collection<IProgramVar> vars) {
		return vars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public static Term abstractVariables(final Term term, final Set<TermVariable> varsToKeep, final int quantifier,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript managedScript,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		final List<TermVariable> quantifiedVars =
				Arrays.stream(term.getFreeVars()).filter(x -> !varsToKeep.contains(x)).collect(Collectors.toList());
		final Term quantified = SmtUtils.quantifier(managedScript.getScript(), quantifier, quantifiedVars, term);
		return PartialQuantifierElimination.tryToEliminate(services, logger, managedScript, quantified,
				simplificationTechnique, xnfConversionTechnique);
	}
}

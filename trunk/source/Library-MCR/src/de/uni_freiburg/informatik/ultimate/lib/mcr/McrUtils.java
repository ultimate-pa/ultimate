package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;

public class McrUtils {
	private McrUtils() {
	}

	public static Set<TermVariable> getTermVariables(final Collection<IProgramVar> vars) {
		return vars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public static Term abstractVariables(final Term term, final Set<TermVariable> varsToKeep, final int quantifier,
			final ManagedScript managedScript, final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique) {
		final Term eliminated = PartialQuantifierElimination.eliminateCompat(services, managedScript, simplificationTechnique, term);
		final Term normalForm;
		switch (quantifier) {
		case QuantifiedFormula.EXISTS:
			normalForm = SmtUtils.toDnf(services, managedScript, eliminated);
			break;
		case QuantifiedFormula.FORALL:
			normalForm = SmtUtils.toCnf(services, managedScript, eliminated);
			break;
		default:
			throw new AssertionError("Invalid Quantifier!");
		}
		final List<TermVariable> quantifiedVars = Arrays.stream(normalForm.getFreeVars())
				.filter(x -> !varsToKeep.contains(x)).collect(Collectors.toList());
		final Term quantified = SmtUtils.quantifier(managedScript.getScript(), quantifier, quantifiedVars, normalForm);
		return PartialQuantifierElimination.eliminateCompat(services, managedScript, simplificationTechnique, quantified);
	}

	public static <STATE> List<STATE> reversedTopologicalOrdering(final INestedWordAutomaton<?, STATE> automaton,
			final Predicate<STATE> ignoreState) {
		final Map<STATE, Set<STATE>> successors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			if (ignoreState.test(state)) {
				continue;
			}
			final Set<STATE> succs = new HashSet<>();
			for (final var edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (!ignoreState.test(succ)) {
					succs.add(succ);
				}
			}
			successors.put(state, succs);
		}
		return new TopologicalSorter<>(successors::get).reversedTopologicalOrdering(successors.keySet()).get();
	}
}

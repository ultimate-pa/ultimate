package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) A collection of useful functions needed in
 *         Q-Vasr-abstraction, and matrix operations.
 *
 */
public class QvasrUtils {
	private QvasrUtils() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Split a {@link Term} in DNF into its conjuncts.
	 *
	 * @param loopRelation
	 * @return
	 */
	public static List<Term> splitDisjunction(final Term loopRelation) {
		final List<Term> result = new ArrayList<>();
		final ApplicationTerm dnfAppTerm = (ApplicationTerm) loopRelation;
		if (!dnfAppTerm.getFunction().getName().equals("or")) {
			result.add(loopRelation);
		} else {
			result.addAll(Arrays.asList(dnfAppTerm.getParameters()));
		}
		return result;
	}

	/**
	 * Embed a new variable into a set of subsets, by adding it to each already existing subsets.
	 *
	 * @param inSet
	 * @param variable
	 * @return
	 */
	public static Set<Set<TermVariable>> joinSet(final Set<Set<TermVariable>> inSet, final Set<TermVariable> variable) {
		final Set<Set<TermVariable>> joinedSet = new HashSet<>(inSet);
		for (final Set<TermVariable> toBeJoined : inSet) {
			final Set<TermVariable> varJoin = new HashSet<>();
			varJoin.addAll(toBeJoined);
			varJoin.addAll(variable);
			joinedSet.add(varJoin);
		}
		return joinedSet;
	}
}

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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
	public static Set<Set<Term>> joinSet(final Set<Set<Term>> inSet, final Set<Term> variable) {
		final Set<Set<Term>> joinedSet = new HashSet<>(inSet);
		for (final Set<Term> toBeJoined : inSet) {
			final Set<Term> varJoin = new HashSet<>();
			varJoin.addAll(toBeJoined);
			varJoin.addAll(variable);
			joinedSet.add(varJoin);
		}
		return joinedSet;
	}
}

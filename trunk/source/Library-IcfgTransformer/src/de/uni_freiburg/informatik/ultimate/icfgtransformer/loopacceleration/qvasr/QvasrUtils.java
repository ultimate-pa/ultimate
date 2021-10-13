package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) A collection of useful functions needed in
 *         Q-Vasr-abstraction
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
			for (final Term disjunct : dnfAppTerm.getParameters()) {
				result.add(disjunct);
			}
		}
		return result;
	}
}

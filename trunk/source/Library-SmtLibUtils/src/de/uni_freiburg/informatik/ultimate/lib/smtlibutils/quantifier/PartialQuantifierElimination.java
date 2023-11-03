/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Try to eliminate existentially quantified variables in terms. Therefore we
 * use that the term ∃v.v=c∧φ[v] is equivalent to term φ[c]. Resp. we use that
 * the term ∀v.v!=c∨φ[v] is equivalent to term φ[c].
 */
public class PartialQuantifierElimination {

	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term term, final SimplificationTechnique simplificationTechnique) {
		final Term tmp = eliminateLight(services, mgdScript, term);
		return QuantifierPushTermWalker.eliminate(services, mgdScript, true, PqeTechniques.ALL, simplificationTechnique,
				tmp);
	}

	public static Term eliminateLight(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final Term term) {
		final Term withoutIte = (new IteRemover(mgdScript)).transform(term);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(withoutIte);
		// FIXME 20230601 Matthias: The following line seems useless. The input should
		// always be in CommuHash Normal Form.
		final Term chnf = new CommuhashNormalForm(services, mgdScript.getScript()).transform(nnf);
		final Term result = QuantifierPushTermWalker.eliminate(services, mgdScript, false, PqeTechniques.LIGHT,
				SimplificationTechnique.NONE, chnf);
		assert (CommuhashUtils.isInCommuhashNormalForm(result, CommuhashUtils.COMMUTATIVE_OPERATORS))
				: "Output not in commuhash form";
		return result;
	}

	/**
	 * Auxiliary method that replaces old calls to quantifier elimination. This
	 * method is a temporary workaround.
	 */
	public static Term eliminateCompat(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Term term) {
		final Term tmp = eliminateLight(services, mgdScript, term);
		return QuantifierPushTermWalker.eliminate(services, mgdScript, applyDistributivity,
				quantifierEliminationTechniques, simplificationTechnique, tmp);
	}

	/**
	 * Auxiliary method that replaces old calls to quantifier elimination. This
	 * method is a temporary workaround.
	 */
	public static Term eliminateCompat(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final SimplificationTechnique simplificationTechnique, final Term term) {
		return eliminateCompat(services, mgdScript, true, PqeTechniques.ALL, simplificationTechnique, term);
	}

}

/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ArrayQuantifierEliminationUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MultiDimensionalSelectOverStoreEliminationUtils {

	public static Term replace(final ManagedScript mgdScript, final ArrayIndexEqualityManager aiem, final Term term,
			final MultiDimensionalSelectOverNestedStore mdsos) {
		final Map<Term, Term> substitutionMapping = Collections.singletonMap(mdsos.toTerm(),
				ArrayQuantifierEliminationUtils.transformMultiDimensionalSelectOverNestedStoreToIte(mdsos, mgdScript,
						aiem));
		final Term resultWithIte = Substitution.apply(mgdScript, substitutionMapping, term);
		final Term result = new IteRemover(mgdScript).transform(resultWithIte);
		return result;
	}

}

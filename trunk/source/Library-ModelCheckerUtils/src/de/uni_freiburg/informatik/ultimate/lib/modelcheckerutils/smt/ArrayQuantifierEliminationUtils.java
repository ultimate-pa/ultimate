/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Provides auxiliary methods for our partitial quantifier elimination for arrays.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ArrayQuantifierEliminationUtils {

	public static Term transformMultiDimensionalSelectOverStoreToIte(final MultiDimensionalSelectOverStore mdsos,
			final ManagedScript mgdScript, final ArrayIndexEqualityManager aiem) {
		final ArrayIndex selectIndex = mdsos.getSelect().getIndex();
		final ArrayIndex storeIndex = mdsos.getStore().getIndex();
		final Term eq = aiem.constructIndexEquality(selectIndex, storeIndex);
		final Term equalsReplacement = mdsos.constructEqualsReplacement();
		final Term notEquasReplacement = mdsos.constructNotEqualsReplacement(mgdScript.getScript());
		return Util.ite(mgdScript.getScript(), eq, equalsReplacement, notEquasReplacement);
	}

	public static Term transformMultiDimensionalSelectOverNestedStoreToIte(
			final MultiDimensionalSelectOverNestedStore mdsos, final ManagedScript mgdScript,
			final ArrayIndexEqualityManager aiem) {
		final ArrayIndex selectIndex = mdsos.getSelect().getIndex();
		final List<ArrayIndex> storeIndices = mdsos.getNestedStore().getIndices();
		Term ite = mdsos.constructNotEqualsReplacement(mgdScript.getScript());
		for (int i = 0; i < storeIndices.size(); i++) {
			final ArrayIndex indexOfCurrentStore = mdsos.getNestedStore().getIndices().get(i);
			final Term eq = aiem.constructIndexEquality(selectIndex, indexOfCurrentStore);
			final Term valueOfCurrentStore = mdsos.getNestedStore().getValues().get(i);
			ite = Util.ite(mgdScript.getScript(), eq, valueOfCurrentStore, ite);
		}
		return ite;
	}


}

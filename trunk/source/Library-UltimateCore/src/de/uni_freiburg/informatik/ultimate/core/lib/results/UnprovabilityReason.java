/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;

/**
 * Objects of this class represent one reason why we were not able to prove something. Such a reason is given as a
 * String (its description) and optionally a {@link ILocation}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class UnprovabilityReason {
	private final String mDescription;
	private final ILocation mLocation;

	public UnprovabilityReason(final String description) {
		this(description, null);
	}

	public UnprovabilityReason(final String description, final ILocation location) {
		mDescription = description;
		mLocation = location;
	}

	@Override
	public String toString() {
		if (mLocation == null) {
			return mDescription;
		}
		return mDescription + " at line " + mLocation.getStartLine();
	}

	public static <TE extends IElement> List<UnprovabilityReason>
			getUnprovabilityReasons(final IProgramExecution<TE, ?> pe) {
		final List<UnprovabilityReason> unproabilityReasons = new ArrayList<>();
		for (final Entry<String, ILocation> entry : Overapprox.getOverapproximations(pe).entrySet()) {
			unproabilityReasons
					.add(new UnprovabilityReason("overapproximation of " + entry.getKey(), entry.getValue()));
		}
		return unproabilityReasons;
	}
}

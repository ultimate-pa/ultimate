/*
 * Copyright (C) 2024 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2024 University of Stuttgart
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
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Special case of {@link Overapprox} that indicates that the annotated
 * statement/edge only overapproximates the values that is assigned to one or
 * more variables. In this case the overapproximation does not impair the sound
 * reporting of erroneous program executions if the variable is used afterwards.
 * TODO: More precise documentation.
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 */
public class OverapproxVariable extends Overapprox {

	private static final long serialVersionUID = -575969312624287029L;

	public OverapproxVariable(final Map<String, ILocation> reason2Loc) {
		super(reason2Loc);
	}

	public OverapproxVariable(final String reason, final ILocation loc) {
		super(reason, loc);
	}
}

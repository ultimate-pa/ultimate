/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * A GlobalBoogieVar is either a OldBoogieVar or a NonOldBoogieVar. The NonOldBoogieVar is a variable that can be
 * modified in the program. The OldBoogieVar is a variable that has always the value that the corresponding
 * NonOldBoogieVar had at the beginning of the last procedure call.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class GlobalBoogieVar extends BoogieVar implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;

	public GlobalBoogieVar(final String identifier, final IBoogieType iType, final TermVariable tv,
			final ApplicationTerm defaultConstant, final ApplicationTerm primedContant) {
		super(identifier, tv, defaultConstant, primedContant);
	}

	@Override
	public String getProcedure() {
		return null;
	}

	@Override
	public boolean isGlobal() {
		return true;
	}
}

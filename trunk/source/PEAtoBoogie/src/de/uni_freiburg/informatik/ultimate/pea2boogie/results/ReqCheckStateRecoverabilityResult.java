/*
 * Copyright (C) 2023 Tobias Wießner <tobias.wiessner@mailbox.org>
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
*
* @author Tobias Wießner <tobias.wiessner@mailbox.org>
*
*/

public class ReqCheckStateRecoverabilityResult<LOC extends IElement, TE extends IAction, E> extends ReqCheckFailResult<LOC>{

	private final String mMessage;
	
	public ReqCheckStateRecoverabilityResult(final LOC element, final String plugin, final IBacktranslationService translatorSequence, final String message) {
		super(element, plugin, translatorSequence);
		mMessage = message;
	}
	
	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getShortDescription());
		sb.append(CoreUtil.getPlatformLineSeparator());
		if (mMessage != null) {
			sb.append("Verification Condition: ");
			sb.append(mMessage);
		}
		return sb.toString();
	}
}

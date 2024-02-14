/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class WitnessGhostDeclaration extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String KEY = WitnessGhostDeclaration.class.getName();

	@Visualizable
	private final Map<String, String> mGhostsAndInitialValues;

	public WitnessGhostDeclaration(final Map<String, String> ghostsAndInitialValues) {
		mGhostsAndInitialValues = ghostsAndInitialValues;
	}

	public Map<String, String> getGhostAndInitialValues() {
		return mGhostsAndInitialValues;
	}

	public void annotate(final IElement node) {
		// Only add an annotation, if the variable was successfully backtranslated
		if (mGhostsAndInitialValues != null && !mGhostsAndInitialValues.isEmpty()) {
			node.getPayload().getAnnotations().put(KEY, this);
		}
	}

	public static WitnessGhostDeclaration getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (WitnessGhostDeclaration) a);
	}
}

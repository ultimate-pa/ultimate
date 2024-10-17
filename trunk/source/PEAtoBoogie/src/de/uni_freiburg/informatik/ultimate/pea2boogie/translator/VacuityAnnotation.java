/*
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
package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 * 
 * Annotation for vacuity checks. This marks whether a vacuous requirement
 * enforces a trivial invariant.
 *
 */

public class VacuityAnnotation extends ModernAnnotations {

	private static final long serialVersionUID = 1L;
	private final CDD mEnforcedInvariant;

	public VacuityAnnotation(final CDD enforcedInv) {
		mEnforcedInvariant = enforcedInv;
	}

	public CDD getInvariant() {
		return mEnforcedInvariant;
	}

	public IAnnotations annotate(final IElement elem) {
		return elem.getPayload().getAnnotations().put(VacuityAnnotation.class.getName(), this);
	}

	public static VacuityAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, VacuityAnnotation.class);
	}
}

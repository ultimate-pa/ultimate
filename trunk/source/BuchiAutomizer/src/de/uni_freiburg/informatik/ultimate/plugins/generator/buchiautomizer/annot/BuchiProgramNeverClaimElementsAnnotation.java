/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark all
 * elements that had to be added during the product construction (helps with
 * backtranslation and result generation).
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @deprecated Was an experiment, will be removed 
 */
@Deprecated
public class BuchiProgramNeverClaimElementsAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = BuchiProgramNeverClaimElementsAnnotation.class.getSimpleName();
	private static final String[] sFieldNames = new String[] { "BelongsToNeverClaim" };
	private static final Object[] sFieldValues = new Object[] { true };

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(String field) {
		return sFieldValues;
	}

	public void annotate(IElement elem) {
		elem.getPayload().getAnnotations().put(sKey, this);
	}

	public static BuchiProgramNeverClaimElementsAnnotation getAnnotation(IElement elem) {
		if (!elem.hasPayload()) {
			return null;
		}
		if (!elem.getPayload().hasAnnotation()) {
			return null;
		}
		return (BuchiProgramNeverClaimElementsAnnotation) elem.getPayload().getAnnotations().get(sKey);
	}

}

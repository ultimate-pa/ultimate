/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.provider;

import org.eclipse.jface.viewers.LabelProvider;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.gui.misc.Entry;
import de.uni_freiburg.informatik.ultimate.gui.misc.GroupEntry;

/**
 * @author dietsch
 * 
 */
public class AnnotationsLabelProvider extends LabelProvider {

	private static final int MAX_LENGTH = 500;

	@Override
	public String getText(Object element) {
		if (element instanceof IElement) {
			final IElement elem = (IElement) element;
			if (elem.hasPayload()) {
				return getText(elem.getPayload());
			}
		}
		if (element instanceof IPayload) {
			return ((IPayload) element).toString();
		}
		if (element instanceof GroupEntry) {
			return ((GroupEntry) element).getName();
		}
		if (element instanceof Entry) {

			final String name = ((Entry) element).getName();
			final String value = ((Entry) element).getValue();

			String str;

			if (name == null || name.isEmpty()) {
				str = value;
			} else if (value == null || value.isEmpty()) {
				str = name;
			} else if (name.equals(value)) {
				str = name;
			} else {
				str = name + " - " + value;
			}
			return str.length() > MAX_LENGTH ? str.substring(0, MAX_LENGTH) : str;
		}

		return "UNKNOWN ELEMENT";
	}
}

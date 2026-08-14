/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.selection;

import org.eclipse.jface.viewers.ISelection;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IElementSelection;

/**
 * Selection implementation carrying a selected {@link IElement} for the Eclipse selection service.
 */
public class SwtSelection implements IElementSelection {

	private IElement mSelectedElement;

	public SwtSelection() {
		mSelectedElement = null;
	}

	@Override
	public IElement getElement() {
		return mSelectedElement;
	}

	@Override
	public boolean isEmpty() {
		return mSelectedElement == null;
	}

	@Override
	public void setElement(final IElement element) {
		mSelectedElement = element;
	}
}

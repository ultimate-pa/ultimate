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

import java.util.ArrayList;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Local {@link ISelectionProvider} for the SWT visualization editor.
 */
public class SwtSelectionProvider implements ISelectionProvider {

	private final ArrayList<ISelectionChangedListener> mListeners = new ArrayList<>();
	private SwtSelection mSelection;

	@Override
	public void addSelectionChangedListener(final ISelectionChangedListener listener) {
		mListeners.add(listener);
	}

	@Override
	public ISelection getSelection() {
		return mSelection;
	}

	@Override
	public void removeSelectionChangedListener(final ISelectionChangedListener listener) {
		mListeners.remove(listener);
	}

	@Override
	public void setSelection(final ISelection selection) {
		if (selection instanceof SwtSelection) {
			mSelection = (SwtSelection) selection;
		}
	}

	/**
	 * Convenience method: set the selection from an {@link IElement} and fire the selection changed event.
	 *
	 * @param element
	 *            The selected element, or {@code null} to clear.
	 */
	public void setSelection(final IElement element) {
		final SwtSelection selection = new SwtSelection();
		selection.setElement(element);
		mSelection = selection;
		fireSelectionEvent();
	}

	public void fireSelectionEvent() {
		if (mSelection != null) {
			for (final ISelectionChangedListener listener : mListeners) {
				listener.selectionChanged(new SelectionChangedEvent(this, mSelection));
			}
		}
	}
}

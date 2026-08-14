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
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.panel;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationTreeProvider;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationsLabelProvider;

/**
 * Panel that displays the payload and annotations of a selected {@link IElement} in a tree structure.
 * <p>
 * Reuses the existing {@link AnnotationTreeProvider} and {@link AnnotationsLabelProvider} from the GuiRCP plug-in.
 */
public class DetailPanel extends Composite {

	private final TreeViewer mTreeViewer;

	public DetailPanel(final Composite parent) {
		super(parent, SWT.NONE);
		setLayout(new FillLayout());
		mTreeViewer = new TreeViewer(this, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
		mTreeViewer.setLabelProvider(new AnnotationsLabelProvider());
		mTreeViewer.setContentProvider(new AnnotationTreeProvider());
	}

	/**
	 * Update the tree to show the payload and annotations of the given element. If {@code null}, the tree is cleared.
	 *
	 * @param element
	 *            The selected {@link IElement}, or {@code null} for no selection.
	 */
	public void update(final IElement element) {
		mTreeViewer.setInput(element);
		if (element != null) {
			mTreeViewer.expandAll();
		}
		mTreeViewer.refresh();
	}

	@Override
	public void dispose() {
		if (!mTreeViewer.getControl().isDisposed()) {
			mTreeViewer.getControl().dispose();
		}
		super.dispose();
	}
}

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
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.graph.GraphCanvas;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.panel.DetailPanel;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.selection.SwtSelectionProvider;

/**
 * SWT-based graph editor that displays the graph on the left and the payload/annotations detail panel on the right.
 */
public class SwtEditor extends EditorPart {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor.SwtEditor";

	private GraphCanvas mGraphCanvas;
	private DetailPanel mDetailPanel;
	private SwtSelectionProvider mSelectionProvider;

	@Override
	public void doSave(final IProgressMonitor monitor) {
		// Not supported
	}

	@Override
	public void doSaveAs() {
		// Not supported
	}

	@Override
	public void init(final IEditorSite site, final IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
		if (input instanceof SwtEditorInput swtInput) {
			setPartName(swtInput.getName());
		}
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void createPartControl(final Composite parent) {
		parent.setLayout(new FillLayout());

		final SashForm sashForm = new SashForm(parent, SWT.HORIZONTAL);
		sashForm.setLayout(new FillLayout());

		// Left: Graph canvas
		mGraphCanvas = new GraphCanvas(sashForm);

		// Right: Detail panel
		mDetailPanel = new DetailPanel(sashForm);

		// Set weights (70% graph, 30% detail)
		sashForm.setWeights(new int[] { 70, 30 });

		// Selection provider
		mSelectionProvider = new SwtSelectionProvider();
		getSite().setSelectionProvider(mSelectionProvider);

		// Wire graph selection to detail panel and selection provider
		mGraphCanvas.setSelectionListener(element -> {
			mDetailPanel.update(element);
			mSelectionProvider.setSelection(element);
		});

		// Load graph data from editor input
		final IEditorInput input = getEditorInput();
		if (input instanceof SwtEditorInput swtInput) {
			mGraphCanvas.setInput(swtInput);
		}
	}

	@Override
	public void setFocus() {
		if (mGraphCanvas != null && !mGraphCanvas.isDisposed()) {
			mGraphCanvas.setFocus();
		}
	}

	@Override
	public void dispose() {
		if (mGraphCanvas != null && !mGraphCanvas.isDisposed()) {
			mGraphCanvas.dispose();
		}
		if (mDetailPanel != null && !mDetailPanel.isDisposed()) {
			mDetailPanel.dispose();
		}
		super.dispose();
	}
}

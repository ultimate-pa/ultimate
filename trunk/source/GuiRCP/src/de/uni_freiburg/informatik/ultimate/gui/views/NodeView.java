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

package de.uni_freiburg.informatik.ultimate.gui.views;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import de.uni_freiburg.informatik.ultimate.gui.interfaces.IElementSelection;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationTreeProvider;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationsLabelProvider;

/**
 * A nodeViewer so we can present selected nodes to the user...
 *
 * @author dietsch
 *
 */
public class NodeView extends ViewPart implements ISelectionListener {
	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.graphview2d.views.NodeView";

	private TreeViewer mTreeViewer;

	@Override
	public void dispose() {
		getSite().getWorkbenchWindow().getSelectionService().removeSelectionListener(this);
		super.dispose();
	}

	protected TreeViewer getTreeViewer() {
		return mTreeViewer;
	}

	@Override
	public void createPartControl(final Composite parent) {
		mTreeViewer = new TreeViewer(parent, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL);
		mTreeViewer.setLabelProvider(new AnnotationsLabelProvider());
		mTreeViewer.setContentProvider(new AnnotationTreeProvider());
		getSite().getPage().addSelectionListener(this);
	}

	@Override
	public void setFocus() {
		mTreeViewer.getControl().setFocus();
	}

	@Override
	public void selectionChanged(final IWorkbenchPart part, final ISelection selection) {
		if (selection instanceof IElementSelection) {
			final UIJob job = new UIJob("Selection changed...") {
				@Override
				public IStatus runInUIThread(final IProgressMonitor mon) {
					getTreeViewer().setSelection(null);
					getTreeViewer().setInput(((IElementSelection) selection).getElement());
					getTreeViewer().expandAll();
					getTreeViewer().refresh();
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.INTERACTIVE);
			job.schedule();
		}
	}
}

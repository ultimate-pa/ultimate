/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jelena Barth
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2009-2015 pashko
 *
 * This file is part of the ULTIMATE JungVisualization plug-in.
 *
 * The ULTIMATE JungVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JungVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JungVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JungVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JungVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor;

import java.util.concurrent.atomic.AtomicInteger;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.MenuActions.Mode;
import edu.uci.ics.jung.visualization.VisualizationViewer;

/**
 * EditorInput for the {@link JungEditor}.
 *
 * @see {@link IEditorInput}
 * @author lena
 *
 */
public class JungEditorInput implements IEditorInput {

	private static AtomicInteger mNextFreeId = new AtomicInteger();
	private final String mName;
	private final VisualizationViewer<VisualizationNode, VisualizationEdge> mVisualizationViewer;
	private final String mId;
	private Mode mCurrentMode;

	/**
	 * @param name
	 *            The name of the EditorInput.
	 * @param visualizationViewer
	 */
	public JungEditorInput(final String name,
			final VisualizationViewer<VisualizationNode, VisualizationEdge> visualizationViewer) {
		assert name != null;
		mName = name;
		mVisualizationViewer = visualizationViewer;
		mId = String.valueOf(mNextFreeId.incrementAndGet());
		mCurrentMode = Mode.PICKING;
	}

	public VisualizationViewer<VisualizationNode, VisualizationEdge> getViewer() {
		return mVisualizationViewer;
	}

	public Mode getMode() {
		return mCurrentMode;
	}

	public void setMode(final Mode mode) {
		mCurrentMode = mode;
	}

	public String getId() {
		return mId;
	}

	@Override
	public boolean exists() {
		return false;
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public String getName() {
		return mName;
	}

	@Override
	public IPersistableElement getPersistable() {
		return null;
	}

	@Override
	public String getToolTipText() {
		return "";
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(final Class adapter) {
		return null;
	}

	/**
	 * Hacky shit (based on Lenas code; didnt want to learn how to do that properly)
	 */
	public void displayContextMenu() {
		// not needed
	}

}

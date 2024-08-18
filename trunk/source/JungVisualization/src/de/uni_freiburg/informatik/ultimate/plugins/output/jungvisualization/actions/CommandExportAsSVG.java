/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.io.File;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import org.apache.batik.anim.dom.SVGDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.apache.batik.svggen.SVGGraphics2DIOException;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;

import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class CommandExportAsSVG extends AbstractHandler {
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		final IEditorInput ei = HandlerUtil.getActiveEditorInput(event);
		if (ei instanceof JungEditorInput) {
			exportAsSVG((JungEditorInput) ei);
		}
		return null;
	}

	/**
	 * Exports the graph of the active editor part to a SVG format and saves it.
	 */
	public void exportAsSVG(JungEditorInput editorInput) {
		assert editorInput != null;
		final String svgFilePath = new RcpPreferenceProvider(Activator.PLUGIN_ID)
				.getString(JungPreferenceValues.LABEL_PATH);
		final String timestamp = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd-HH-mm-ss"));
		final String filename = new File(svgFilePath, timestamp + ".svg").getAbsolutePath();

		final DOMImplementation impl = SVGDOMImplementation.getDOMImplementation();
		final String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
		final Document doc = impl.createDocument(svgNS, "svg", null);

		final SVGGraphics2D g = new SVGGraphics2D(doc);
		final VisualizationViewer<?, ?> vv = editorInput.getViewer();
		vv.setDoubleBuffered(false);
		vv.paint(g.create());
		vv.setDoubleBuffered(true);
		try {
			g.stream(filename);
		} catch (SVGGraphics2DIOException e) {
			e.printStackTrace();
		}
	}
}

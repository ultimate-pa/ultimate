package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import javax.swing.JFileChooser;

import org.apache.batik.dom.GenericDOMImplementation;
import org.apache.batik.dom.svg.SVGDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class CommandExportAsSVG extends AbstractHandler {
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		IEditorInput ei = HandlerUtil.getActiveEditorInput(event);
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
		String svgFilePath = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getString(JungPreferenceValues.LABEL_PATH);

		JFileChooser chooser = new JFileChooser();
		chooser.setSelectedFile(new File(svgFilePath + "/default.svg"));
		chooser.showSaveDialog(null);

		String filename = chooser.getSelectedFile().getPath();

		DOMImplementation impl = GenericDOMImplementation.getDOMImplementation();
		String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
		Document doc = impl.createDocument(svgNS, "svg", null);

		SVGGraphics2D g = new SVGGraphics2D(doc);
		VisualizationViewer<?, ?> vv = editorInput.getViewer();
		vv.setDoubleBuffered(false);
		vv.paint(g);
		vv.setDoubleBuffered(true);

		try {
			FileWriter fileWriter = new FileWriter(filename);
			g.stream(fileWriter);
		} catch (IOException ioEx) {
			ioEx.printStackTrace();
		}
	}
}

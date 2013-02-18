package local.stalin.plugins.output.prefusevisualization.export;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.HashSet;

import javax.imageio.ImageIO;
import javax.swing.JFileChooser;

import local.stalin.core.api.StalinServices;
import local.stalin.plugins.output.prefusevisualization.Activator;

import org.apache.log4j.Logger;

import prefuse.Display;
import prefuse.util.display.ScaleSelector;
import prefuse.util.io.IOLib;
import prefuse.util.io.SimpleFileFilter;

/**
 * This class can export the current Display to an persistent file
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2010-04-12 10:18:09 +0200 (Mo, 12. Apr 2010) $
 * $LastChangedBy: christj $
 * $LastChangedRevision: 2254 $
 * 
 */
public class DisplayExport {
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private Display m_display;
	private JFileChooser m_chooser;
	private ScaleSelector m_scaler;

	/**
	 * Create a new DisplayExport for the given Display.
	 * 
	 * @param display
	 *            the Display to capture
	 */
	public DisplayExport(Display display) {
		this.m_display = display;
	}

	/**
	 * saves the current display to an file
	 */
	public void save() {
		m_scaler = new ScaleSelector();
		m_chooser = new JFileChooser();
		m_chooser.setDialogType(JFileChooser.SAVE_DIALOG);
		m_chooser.setDialogTitle("Export Prefuse Display...");
		m_chooser.setAcceptAllFileFilterUsed(false);

		// file format filter
		HashSet<String> seen = new HashSet<String>();
		String[] fmts = ImageIO.getWriterFormatNames();
		for (int i = 0; i < fmts.length; i++) {
			String s = fmts[i].toLowerCase();
			if (s.length() == 3 && !seen.contains(s)) {
				seen.add(s);
				m_chooser.setFileFilter(new SimpleFileFilter(s, s.toUpperCase()
						+ " Image (*." + s + ")"));
			}
		}
		seen.clear();
		seen = null;

		File f = null;

		int returnVal = m_chooser.showSaveDialog(null);

		if (returnVal == JFileChooser.APPROVE_OPTION) {

			f = m_chooser.getSelectedFile();

		} else {
			return;
		}

		String format = ((SimpleFileFilter) m_chooser.getFileFilter())
				.getExtension();
		String ext = IOLib.getExtension(f);

		if (!format.equals(ext)) {
			f = new File(f.toString() + "." + format);
		}

		// get the display scale
		double scale = m_scaler.getScale();

		try {
			OutputStream out = new BufferedOutputStream(new FileOutputStream(f));

			m_display.saveImage(out, format, scale);

			out.flush();
			out.close();

			s_Logger.info("image saved as \"" + f.getName() + "\" with "
					+ format + " format ... ");
		} catch (Exception e) {
			s_Logger.error("image save error ... ");
		}
	}
}
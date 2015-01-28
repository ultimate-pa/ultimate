package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.SwingConstants;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.Platform;

import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;

public class CommandShowKeyHelp extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		openKeyHelp();
		return null;
	}

	/**
	 * Opens a help window.
	 */
	public void openKeyHelp() {
		URL loc = Platform.getBundle(Activator.PLUGIN_ID).getEntry("data/KeyHelp.html");
		String s = "Help file not found.";

		try {
			InputStream is = loc.openStream();
			BufferedReader in = new BufferedReader(new InputStreamReader(is));
			s = "";
			String temp = in.readLine();
			while (temp != null) {
				s += temp;
				temp = in.readLine();
			}
		} catch (IOException e1) {
			e1.printStackTrace(System.err);
		}

		JFrame hf = new JFrame("Key Help");
		JLabel label = new JLabel(s, SwingConstants.CENTER);

		hf.getContentPane().add(label);
		hf.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		hf.setAlwaysOnTop(true);
		hf.setResizable(false);
		hf.setFocusableWindowState(false);
		hf.pack();
		hf.setVisible(true);
	}

}

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
		final URL loc = Platform.getBundle(Activator.PLUGIN_ID).getEntry("data/KeyHelp.html");
		String s = "Help file not found.";

		try {
			final InputStream is = loc.openStream();
			final BufferedReader in = new BufferedReader(new InputStreamReader(is));
			s = "";
			String temp = in.readLine();
			while (temp != null) {
				s += temp;
				temp = in.readLine();
			}
		} catch (final IOException e1) {
			e1.printStackTrace(System.err);
		}

		final JFrame hf = new JFrame("Key Help");
		final JLabel label = new JLabel(s, SwingConstants.CENTER);

		hf.getContentPane().add(label);
		hf.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		hf.setAlwaysOnTop(true);
		hf.setResizable(false);
		hf.setFocusableWindowState(false);
		hf.pack();
		hf.setVisible(true);
	}

}

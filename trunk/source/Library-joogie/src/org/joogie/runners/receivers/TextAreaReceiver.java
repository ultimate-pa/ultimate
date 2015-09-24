/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.runners.receivers;

import javax.swing.JTextArea;

/**
 * Text Area Output Receiver of a Runner
 * 
 * @author arlt
 */
public class TextAreaReceiver implements Receiver {

	/**
	 * Text Area
	 */
	private JTextArea textArea;

	/**
	 * C-tor
	 * 
	 * @param textArea
	 *            TextArea
	 */
	public TextAreaReceiver(JTextArea textArea) {
		this.textArea = textArea;
		this.textArea.setText(null);
	}

	@Override
	public void receive(String text) {
		textArea.append(text);
	}

	@Override
	public void onBegin() {
		// do nothing
	}

	@Override
	public void onEnd() {
		// do nothing
	}

}

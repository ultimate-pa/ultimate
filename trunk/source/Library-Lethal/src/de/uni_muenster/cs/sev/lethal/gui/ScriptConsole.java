/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.gui;

import de.uni_muenster.cs.sev.lethal.gui.ScriptEditor.ScriptRunThread;
import de.uni_muenster.cs.sev.lethal.gui.ScriptEditor.TextAreaOutputStream;

import java.awt.*;
import java.awt.event.*;
import java.io.OutputStream;

import javax.swing.*;
import javax.swing.text.BadLocationException;

import de.uni_muenster.cs.sev.lethal.script.Script;
import de.uni_muenster.cs.sev.lethal.script.ScriptParser;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptParseException;

/**
 * Quick script editor for hacking without the need to create a ScriptItem.
 * @author Philipp
 *
 */
public class ScriptConsole extends JPanel {

	private MainWindow mainWindow;
	
	private JToggleButton expandButton = new JToggleButton("Script Console", Resources.loadIcon("script-console.png"));
	private JTextArea inputField = new JTextArea();
	private JTextArea outputField = new JTextArea("(output empty)");
	private JSplitPane splitter = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, new JScrollPane(inputField) , new JScrollPane(outputField));
	
	private JToolBar toolbar = new JToolBar(SwingConstants.HORIZONTAL);
	private JButton runButton = new JButton("Run", Resources.loadIcon("script-run-tiny.png"));
	private JButton stopButton = new JButton("Stop", Resources.loadIcon("script-stop-tiny.png"));
	
	private Thread runThread;
	
	private boolean layoutDone = false;
	
	/**
	 * Creates a new ScriptConsole.
	 * @param mainWindow application main window.
	 */
	public ScriptConsole(MainWindow mainWindow){
		this.mainWindow = mainWindow;
		
		this.setLayout(new GridBagLayout());
		
		this.setExpanded(false);
		
		this.inputField.setFont(new Font("Monospaced", Font.PLAIN, inputField.getFont().getSize()));
		this.outputField.setFont(this.inputField.getFont());
		
		
		splitter.setPreferredSize(new Dimension(this.inputField.getPreferredSize().width, 8 * this.inputField.getFontMetrics(this.inputField.getFont()).getHeight()));
		
		this.add(this.expandButton, new GridBagConstraints(0, 0, 1, 1, 0, 0, GridBagConstraints.NORTHWEST, GridBagConstraints.VERTICAL, new Insets(0,0,0,0), 0, 0));
		this.add(this.toolbar,      new GridBagConstraints(1, 0, 1, 1, 0, 1, GridBagConstraints.NORTH, GridBagConstraints.HORIZONTAL, new Insets(0,0,0,0), 0, 0));
		this.add(new Container(),   new GridBagConstraints(2, 0, 1, 1, 1, 0, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(0,0,0,0), 0, 0)); //dummy to strech the 1,0 cell when not expanded.
		
		this.add(splitter,         new GridBagConstraints(0, 1, 3, 1, 1, 1, GridBagConstraints.CENTER, GridBagConstraints.BOTH, new Insets(0,0,0,0), 0, 0));
		
		this.outputField.setEnabled(false);
		this.outputField.setBackground(Color.BLACK);
		this.outputField.setForeground(Color.WHITE);
		
		this.expandButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				setExpanded(!getExpanded());
			}
		});
		
		this.toolbar.add(this.runButton);
		this.toolbar.add(this.stopButton);
		
		this.runButton.addActionListener(new ActionListener(){
			@Override public void actionPerformed(ActionEvent e) {run();}
		});
		this.stopButton.addActionListener(new ActionListener(){
			@Override public void actionPerformed(ActionEvent e) {stop();}
		});
	}

	private void run(){
		this.outputField.setText("");
		final Script script;
		try{
			script = ScriptParser.parseScript(this.inputField.getText());
		} catch (ScriptParseException ex){
			this.outputField.append("Parse Exception: " + ex.getMessage() + "\n");
			try {
				this.outputField.select(this.outputField.getLineStartOffset(ex.getLine()-1), this.outputField.getLineEndOffset(ex.getLine()-1));
				this.outputField.requestFocusInWindow();
			} catch (BadLocationException e) {
				e.printStackTrace();
			}
			return;
		}

		final OutputStream out = new TextAreaOutputStream(this.outputField);

		this.runThread = new ScriptRunThread(mainWindow.getCurrentProject(), script, out) {
			@Override
			protected void updateRunning(boolean running) {
				setRunning(running);
			}
		};

		this.runThread.start();
	}
	private void stop(){
		this.runThread.stop();
	}

	private void setRunning(boolean running){
		this.runButton.setEnabled(!running);
		this.stopButton.setEnabled(running);
	}
	
	private void setExpanded(boolean exp){
		this.splitter.setVisible(exp);
		this.toolbar.setVisible(exp);
		this.mainWindow.validate();
		if (exp && !layoutDone) {splitter.setDividerLocation(0.6); layoutDone = true;}
	}
	private boolean getExpanded(){
		return this.splitter.isVisible();
	}
	
}

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

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.BadLocationException;
import javax.swing.undo.UndoManager;

import java.awt.*;
import java.awt.event.*;

import java.io.*;

import de.uni_muenster.cs.sev.lethal.script.Script;
import de.uni_muenster.cs.sev.lethal.script.ScriptParser;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptParseException;
import de.uni_muenster.cs.sev.lethal.script.exceptions.ScriptRuntimeError;

/**
 * GUI Editor for scripts.
 * @author Philipp
 *
 */
public class ScriptEditor extends Editor {

	private JButton runButton  = new JButton("Run",  Resources.loadIcon("script-run.png") );
	private JButton stopButton = new JButton("Stop", Resources.loadIcon("script-stop.png"));

	private UndoManager undoManager = new UndoManager();

	private JTextArea editorTextField = new JTextArea();

	private JButton undoButton = new JButton("Undo", Resources.loadIcon("edit-undo.png"));
	private JButton redoButton = new JButton("Redo", Resources.loadIcon("edit-redo.png"));

	/** Text field for script output. */
	private JTextArea console = new JTextArea();

	/** @see ScriptItem */
	private ScriptItem item;

	private Thread runThread;

	/**
	 * Creates a new Script editor for editing a script item.
	 * @param item script item to edit
	 */
	public ScriptEditor(ScriptItem item) {
		super(item);
		this.item = item;
		
		this.toolbar.add(this.undoButton);
		this.toolbar.add(this.redoButton);
		this.toolbar.addSeparator();
		this.toolbar.add(this.runButton);
		this.toolbar.add(this.stopButton);
		this.stopButton.setEnabled(false);

		Container codeEditorContainer  = new Container();
		Container consoleContainer     = new Container();

		JSplitPane tbSplitter = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
		tbSplitter.setResizeWeight(0.6);

		tbSplitter.setLeftComponent(codeEditorContainer);
		tbSplitter.setRightComponent(consoleContainer);

		this.add(tbSplitter, BorderLayout.CENTER);



		codeEditorContainer.setLayout(new BorderLayout());
		codeEditorContainer.add(new JLabel("Code Editor"), BorderLayout.NORTH);
		codeEditorContainer.add(new JScrollPane(this.editorTextField), BorderLayout.CENTER);
		this.editorTextField.setText(this.item.getScript());
		this.editorTextField.setFont(Font.decode(Font.MONOSPACED));
		this.editorTextField.getDocument().addUndoableEditListener(undoManager);

		consoleContainer.setLayout(new BorderLayout());
		consoleContainer.add(new JLabel("Text Output"), BorderLayout.NORTH);
		consoleContainer.add(new JScrollPane(this.console), BorderLayout.CENTER);
		this.console.setFont(Font.decode(Font.MONOSPACED));


		this.editorTextField.getDocument().addDocumentListener(new DocumentListener(){
			public void changedUpdate(DocumentEvent e){setDirty(true);updateUndoButtons();}
			public void insertUpdate(DocumentEvent e) {setDirty(true);updateUndoButtons();}
			public void removeUpdate(DocumentEvent e) {setDirty(true);updateUndoButtons();}

		});

		undoButton.setEnabled(false);
		undoButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				ScriptEditor.this.undoManager.undo();
				updateUndoButtons();
			}
		});
		InputMap inputMap = this.undoButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_Z, InputEvent.CTRL_DOWN_MASK), "UNDO");
		this.undoButton.getActionMap().put("UNDO", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				ScriptEditor.this.undoManager.undo();
				updateUndoButtons();
			}
		});
		
		redoButton.setEnabled(false);
		redoButton.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				ScriptEditor.this.undoManager.redo();
				updateUndoButtons();
			}
		});
		inputMap = this.redoButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_Y, InputEvent.CTRL_DOWN_MASK), "REDO");
		this.redoButton.getActionMap().put("REDO", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				ScriptEditor.this.undoManager.redo();
				updateUndoButtons();
			}
		});
		
		runButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				run();
			}
		});
		inputMap = this.runButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_F5, 0), "RUN");
		this.runButton.getActionMap().put("RUN", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				run();
			}
		});
		
		stopButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				stop();
			}
		});
		inputMap = this.stopButton.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
		inputMap.put(KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.CTRL_DOWN_MASK), "STOP");
		this.stopButton.getActionMap().put("STOP", new AbstractAction(){
			public void actionPerformed(ActionEvent e) {
				stop();
			}
		});
	}

	private void updateUndoButtons(){
		ScriptEditor.this.undoButton.setEnabled(ScriptEditor.this.undoManager.canUndo());
		ScriptEditor.this.redoButton.setEnabled(ScriptEditor.this.undoManager.canRedo());
	}

	@Override
	protected boolean saveToItem(){
		this.item.setScript(this.editorTextField.getText());
		setDirty(false);
		return true;
	}

	private void run(){
		this.console.setText("");
		final Script script;
		try{
			script = ScriptParser.parseScript(this.editorTextField.getText());
		} catch (ScriptParseException ex){
			this.console.append("Parse Exception: " + ex.getMessage() + "\n");
			try {
				this.editorTextField.select(this.editorTextField.getLineStartOffset(ex.getLine()-1), this.editorTextField.getLineEndOffset(ex.getLine()-1));
				this.editorTextField.requestFocusInWindow();
			} catch (BadLocationException e) {
				e.printStackTrace();
			}
			return;
		}

		final OutputStream out = new TextAreaOutputStream(this.console);

		this.runThread = new ScriptRunThread(item.getProject(), script, out) {
			@Override
			protected void updateRunning(boolean running) {
				setRunning(running);
			}
		};

		this.runThread.start();
	}
	
	private void stop(){
		//stopButton.setEnabled(false);
		runThread.stop();
	}

	private void setRunning(boolean running){
		this.runButton.setEnabled(!running);
		this.stopButton.setEnabled(running);
	}

	@Override
	public ScriptItem getItem(){
		return this.item;
	}
	
	@Override
	public String getName() {
		return "Script Editor";
	}

	//Output stream that writes to a text area.
	static class TextAreaOutputStream extends OutputStream{
		private final int MAX_LENGTH = 40960;
		
		private JTextArea textArea;
		
		public TextAreaOutputStream(JTextArea textArea){
			this.textArea = textArea;
		}
		
		@Override
		public void write(int b) throws IOException {
			addString(new String(new byte[]{(byte)b}));
		}
		@Override
		public void write(byte b[], int off, int len){
			addString(new String(b,off,len));
		}
		@Override
		public void write(byte b[]){
			addString(new String(b));
		}
		
		private void addString(String s){
			String old = textArea.getText();
			int spaceLeft = MAX_LENGTH - old.length(); 
			if (spaceLeft < s.length()){
				textArea.setText(old.substring(s.length() - spaceLeft) + s);
			} else {
				textArea.append(s);
			}
			textArea.setSelectionStart(textArea.getText().length());
		}
	}
	
	static abstract class ScriptRunThread extends Thread{
		
		protected Script script;
		protected OutputStream out;
		protected Project project;
		
		public ScriptRunThread(Project project, Script script, OutputStream out) {
			super();
			this.project = project;
			this.script = script;
			this.out = out;
		}

		@Override
		public void run() {
			updateRunning(true);
			try {
				script.execute(new PrintStream(out), project);
			} catch (ScriptRuntimeError ex){
				try {
					out.write(("Script runtime error: " + ex.getMessage() + "\n").getBytes());
				} catch (IOException e) {
					e.printStackTrace();
				}
			} catch (ThreadDeath ex){
				try {
					out.write(("--- Aborted ---").getBytes());
				} catch (IOException e) {
					e.printStackTrace();
				}
			} catch (Throwable ex) {
				try{
					out.write("Internal Error: ".getBytes());
					ex.printStackTrace(new PrintStream(out));
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			
			updateRunning(false);
		}
		
		protected abstract void updateRunning(boolean running);
	}
}

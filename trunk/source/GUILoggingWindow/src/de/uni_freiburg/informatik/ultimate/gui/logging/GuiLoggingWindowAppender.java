/*
 * Copyright (C) 2015 Christian Ortolf
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE GUILoggingWindow plug-in.
 * 
 * The ULTIMATE GUILoggingWindow plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE GUILoggingWindow plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE GUILoggingWindow plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE GUILoggingWindow plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE GUILoggingWindow plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.logging;

import java.io.IOException;
import java.io.Writer;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;
import org.apache.log4j.WriterAppender;

import de.uni_freiburg.informatik.ultimate.gui.views.LoggingView;

/**
 * The Logging window finally
 * 
 * use init()  for initializing purpose .. will open the matching editor in the gui
 * 
 * with write and clear the test in the editor will do some output..
 * 
 * 
 * @author Christian Ortolf
 *
 */
public class GuiLoggingWindowAppender extends WriterAppender {

	private class AppendUIJob extends UIJob {
		private StringBuilder appendedString = new StringBuilder();

		public AppendUIJob() {
			super("Append Logs");
			setPriority(UIJob.INTERACTIVE); 
		}
		public synchronized IStatus runInUIThread(IProgressMonitor mon) {
			LoggingView le = getEditor();
			if (le != null) {
				le.write(appendedString.toString());
				appendedString = new StringBuilder();
			}
			return Status.OK_STATUS;
		}
		
		public synchronized void appendLog(char[] arg0, int offset, int count) {
			appendedString.append(arg0, offset, count);
			if (this.getState() == Job.NONE) {
				this.schedule(100L);
			}
		}
	}
	AppendUIJob myJob;
	
	public GuiLoggingWindowAppender(){}
	
	/**
	 * gets an LoggingEditor and creates if it not exists...
	 * then clears that editor
	 */
	public void clear() {
		UIJob job = new UIJob("clear LoggingEditor") {
			public IStatus runInUIThread(IProgressMonitor mon) {
				LoggingView le = getEditor();
				if (le != null)
					le.clear();
				return Status.OK_STATUS;
			}
		};
		job.schedule(); // start job.
	
	}

	/**
	 * creates .. the writer for later usage..   logging window is opened on first log message
	 */
	public int init() {
		final AppendUIJob job = new AppendUIJob();
		myJob = job;
		setWriter(new Writer(){
			
			/**
			 * no ressources are on this writer.. so nothing is done on close
			 */
			//@Override
			public void close() throws IOException {}

			/**
			 * everything is written immediately
			 */
			//@Override
			public void flush() throws IOException {}

			//@Override
			public void write(char[] arg0, int offset, int count) throws IOException {
				job.appendLog(arg0, offset, count);
			}
			
		});
		setImmediateFlush(false);
		return 0;
	}

	/**
	 * 
	 * @return
	 */
	private LoggingView getEditor() {
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window == null || window.getActivePage() == null)
			return null;
		try {
			return (LoggingView)window.getActivePage().findViewReference(LoggingView.ID).getView(true);
		} catch (NullPointerException ex){
			try {
				window.getActivePage().showView(LoggingView.ID);
			} catch (PartInitException pie) {
				MessageDialog.openError(window.getShell(), "Error",
						"Error opening LoggingEditor:\n" + pie.getMessage());
			}
		}
		System.err.println("Error");
		return null;
	}
}

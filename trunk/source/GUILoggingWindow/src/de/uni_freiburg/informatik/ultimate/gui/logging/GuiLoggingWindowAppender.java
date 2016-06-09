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
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

import de.uni_freiburg.informatik.ultimate.gui.views.LoggingView;

/**
 * An appender that fills Ultimate's LoggingView with log messages.
 * 
 * @author Christian Ortolf
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class GuiLoggingWindowAppender {

	public static void clear() {
		new LogWindowClearerUIJob().schedule();
	}

	public static Writer createWriter() {
		return new AppendUIJobWriter(new LoggingUIJob());
	}

	private static LoggingView getEditor() {
		final IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window == null) {
			return null;
		}
		
		final IWorkbenchPage activePage = window.getActivePage();
		if (activePage == null) {
			return null;
		}

		final IViewReference reference = activePage.findViewReference(LoggingView.ID);
		if (reference == null) {
			try {
				window.getActivePage().showView(LoggingView.ID);
			} catch (final PartInitException pie) {
				MessageDialog.openError(window.getShell(), "Error opening LoggingEditor", pie.getMessage());
				return null;
			}
		} else {
			return (LoggingView) reference.getView(true);
		}
		return null;
	}

	private final static class AppendUIJobWriter extends Writer {
		private final LoggingUIJob mJob;

		private AppendUIJobWriter(LoggingUIJob job) {
			mJob = job;
		}

		@Override
		public void close() throws IOException {
		}

		@Override
		public void flush() throws IOException {
		}

		@Override
		public void write(char[] arg0, int offset, int count) throws IOException {
			mJob.appendLog(arg0, offset, count);
		}
	}

	private final static class LogWindowClearerUIJob extends UIJob {
		private LogWindowClearerUIJob() {
			super(LogWindowClearerUIJob.class.getSimpleName());
		}

		@Override
		public IStatus runInUIThread(final IProgressMonitor mon) {
			final LoggingView le = getEditor();
			if (le != null) {
				le.clear();
			}
			return Status.OK_STATUS;
		}
	}

	private final static class LoggingUIJob extends UIJob {
		private StringBuilder mBuffer = new StringBuilder();

		public LoggingUIJob() {
			super(LoggingUIJob.class.getSimpleName());
			setPriority(UIJob.INTERACTIVE);
		}

		@Override
		public synchronized IStatus runInUIThread(IProgressMonitor mon) {
			final LoggingView le = getEditor();
			if (le != null) {
				le.write(mBuffer.toString());
				mBuffer = new StringBuilder();
			}
			return Status.OK_STATUS;
		}

		public synchronized void appendLog(char[] arg0, int offset, int count) {
			mBuffer.append(arg0, offset, count);
			if (getState() == Job.NONE) {
				schedule(100L);
			}
		}
	}
}

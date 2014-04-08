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
